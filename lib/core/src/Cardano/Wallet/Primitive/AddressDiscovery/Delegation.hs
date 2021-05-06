{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Cardano.Wallet.Primitive.AddressDiscovery.Delegation
    ( -- * Creation
      DelegationState (..)
    , initialDelegationState
    , unsafeDeserializeDelegationState

      -- * Operations
    , presentableKeys
    , usableKeys
    , activeKeys

    -- * For Testing
    , keyAtIx
    , lastActiveIx
    , PointerUTxO (..)

      -- * Chain following model
    , Tx (..)
    , Cert (..)
    , applyTx
    , setPortfolioOf
    )
    where

import Prelude

import Cardano.Crypto.Wallet
    ( XPub )
import Cardano.Wallet.Primitive.AddressDerivation
    ( Depth (..)
    , DerivationType (..)
    , Index (..)
    , MkKeyFingerprint (paymentKeyFingerprint)
    , Role (..)
    , SoftDerivation (..)
    , ToRewardAccount (..)
    )
import Cardano.Wallet.Primitive.Types.Address
    ( Address )
import Cardano.Wallet.Primitive.Types.Coin
    ( Coin (..) )
import Cardano.Wallet.Primitive.Types.Hash
    ( Hash (..) )
import Cardano.Wallet.Primitive.Types.RewardAccount
    ( RewardAccount )
import Cardano.Wallet.Primitive.Types.Tx
    ( TxIn (..), TxOut (..) )
import Control.DeepSeq
    ( NFData )
import Data.Maybe
    ( maybeToList )
import GHC.Generics
    ( Generic )
import Quiet
    ( Quiet (..) )

import qualified Cardano.Wallet.Primitive.Types.TokenBundle as TB

--------------------------------------------------------------------------------
-- Stake Key State
--------------------------------------------------------------------------------

data DelegationState k = DelegationState
    { -- | The account public key from which the stake keys should be derived.
      rewardAccountKey :: k 'AccountK XPub

      -- | The next unregistered stake key.
      --
      -- The active stake keys can be described as the half-open interval
      --    @@ [0, nextKeyIx ) @@
      -- having a length of @nextKeyIx@.
      --
      -- E.g. a state with nextKeyIx=0 has no keys, and nextKeyIx=2 has the keys
      -- [0,1].
    , nextKeyIx :: !(Index 'Soft 'AddressK)

      -- | By threading a long a "pointer UTxO", we leverage the ledger rules to
      -- ensure transactions cannot be re-ordered in a way that breaks the
      -- rules/assumtions for how stake-keys are managed.
    , pointer :: !(Maybe PointerUTxO)

      -- | For compatibility with single-stake-key wallets, we track whether
      -- stake key 0 is registered or not separately.
      --
      -- See the implementaiton of @applyTx@ for how it is used.
    , isKey0Reg :: Bool
    } deriving (Generic)


instance (NFData (k 'AccountK XPub), NFData (k 'AddressK XPub))
    => NFData (DelegationState k)

deriving instance
    ( Show (k 'AccountK XPub)
    , Show (k 'AddressK XPub)
    ) => Show (DelegationState k)

deriving instance
    ( Eq (k 'AccountK XPub)
    , Eq (k 'AddressK XPub)
    ) => Eq (DelegationState k)

accountAtIx
    :: (SoftDerivation k, ToRewardAccount k)
    => DelegationState k
    -> Index 'Soft 'AddressK
    -> RewardAccount
accountAtIx s = toRewardAccount . deriveAddressPublicKey (rewardAccountKey s) MutableAccount

keyAtIx
    :: (SoftDerivation k)
    => DelegationState k
    -> Index 'Soft 'AddressK
    -> k 'AddressK XPub
keyAtIx s = deriveAddressPublicKey (rewardAccountKey s) MutableAccount

nextKey
    :: (SoftDerivation k, ToRewardAccount k)
    => DelegationState k
    -> RewardAccount
nextKey s = accountAtIx s $ nextKeyIx s

lastActiveIx
    :: DelegationState k
    -> Maybe (Index 'Soft 'AddressK)
lastActiveIx s
    | nextKeyIx s == minBound = Nothing
    | otherwise               = Just $ pred $ nextKeyIx s

lastActiveKey
    :: (SoftDerivation k, ToRewardAccount k)
    => DelegationState k
    -> Maybe RewardAccount
lastActiveKey s = accountAtIx s <$> lastActiveIx s

data PointerUTxO = PointerUTxO TxIn Coin (Index 'Soft 'AddressK)
    deriving (Generic, Eq, Show)
    deriving anyclass NFData

--------------------------------------------------------------------------------
-- Constructors
--------------------------------------------------------------------------------

-- | Construct the initial delegation state.
initialDelegationState
    :: k 'AccountK XPub
    -> DelegationState k
initialDelegationState accK = DelegationState accK minBound Nothing False

unsafeDeserializeDelegationState
    :: k 'AccountK XPub
    -> Index 'Soft 'AddressK
    -> Maybe PointerUTxO
    -> Bool
    -> DelegationState k
unsafeDeserializeDelegationState = DelegationState

--------------------------------------------------------------------------------
-- Chain
--------------------------------------------------------------------------------

data Tx = Tx
    { certs :: [Cert]
    , inputs :: [(TxIn, Coin)]
    , outputs :: [TxOut]
    }
    deriving (Eq, Generic)
    deriving Show via (Quiet Tx)

-- FIXME: This logic might belong in the DBLayer, in which this really is the
-- MVar implementation and out of place.

data Cert
    = RegisterKey RewardAccount
    | Delegate RewardAccount
      -- ^ Which pool we're delegating to is here (and for now) irrelevant.
      -- The main thing is that there exists a witness on-chain for this stake
      -- key (registration certs don't require witnesses)
    | DeRegisterKey RewardAccount
    deriving (Eq, Show, Generic)

--
--
-- a portfolio of 3 keys:
-- [0, 1, 2]
-- should have a nextKeyIx of 3
--
-- portfolio of 0 keys, should have a nextKeyIx of 0
--
-- FIXME: toEnum safety
setPortfolioOf
    :: (SoftDerivation k, ToRewardAccount k)
    => DelegationState k
    -> (k 'AddressK XPub -> Address)
    -> (RewardAccount -> Bool) -- TODO: Need a Set or Map for the real implementation with LSQ
    -> Int
    -> Maybe Tx
setPortfolioOf s mkAddress isReg n =
    let s' = s { nextKeyIx = toEnum n }
        mkTxIn (PointerUTxO i c _) = (i, c)

        minUTxOVal = Coin 1 -- FIXME
        -- TODO: Need to rely on wallet to return as change, if the minUTxOVal
        -- changes. Not sure if this is the case.
        txWithCerts [] = Nothing
        txWithCerts cs = Just $ Tx
            { certs = cs
            , inputs = maybeToList (mkTxIn <$> pointer s)
            , outputs =
                [ TxOut
                    (mkAddress $ keyAtIx s $ nextKeyIx s')
                    (TB.fromCoin minUTxOVal)
                ]
            }
    in
        txWithCerts $ reRegKey0IfNeeded
            ++ deRegKey0IfNeeded
            ++ case compare (toEnum n) (nextKeyIx s) of
                GT -> deleg [nextKeyIx s .. toEnum (n - 1)]
                EQ -> []
                LT -> dereg $ reverse [toEnum n .. (pred $ nextKeyIx s)]
  where
    deleg = (>>= \ix ->
        if isReg (acct ix)
        then [Delegate (acct ix)]
        else [RegisterKey (acct ix),  Delegate (acct ix)]
        )

    reRegKey0IfNeeded =
        if not (isKey0Reg s) && n > 0 && fromEnum (nextKeyIx s) > 1
        then [RegisterKey (acct minBound), Delegate (acct minBound)]
        else []

    deRegKey0IfNeeded =
        [ DeRegisterKey (acct minBound)
        | (isKey0Reg s)
        , n == 0
        , fromEnum (nextKeyIx s) == 0
        ]

    dereg ixs =
        [ DeRegisterKey (acct ix)
        | ix <- ixs
        , isReg . acct $ ix
        -- We need to /at least/ check @isReg (key 0)@, because the user could
        -- have deregistered it using old wallet software.
        ]

    acct = toRewardAccount . keyAtIx s

applyTx
    :: forall k. ( SoftDerivation k
        , ToRewardAccount k
        , MkKeyFingerprint k Address
        , MkKeyFingerprint k (k 'AddressK XPub))
    => Tx
    -> Hash "Tx"
    -> DelegationState k
    -> DelegationState k
applyTx (Tx cs _ins outs) h s0 =
    let
        s = foldl (flip applyCert) s0 cs
        isOurOut i (TxOut addr _b) =
            case (paymentKeyFingerprint @k $ keyAtIx s i, paymentKeyFingerprint addr) of
            (Right fp, Right fp')
                | fp == fp' -> True
                | otherwise -> False
            _ -> False
        -- To workaround rollback + old wallets, we also look for the pointer at
        -- 0 and 1, aside from nextKeyIx.
        f o = any (`isOurOut` o) [ nextKeyIx s, minBound, succ minBound ]
        pointerOuts = filter (f . snd) $ zip [0..] outs
    in case pointerOuts of
        [] -> s --error "panic: no pointer utxo on-chain" -- What should we do?
        [(ix,TxOut _addr tb)]
            -> s { pointer = Just $ PointerUTxO (TxIn h ix) (TB.getCoin tb) (nextKeyIx s) }
        (_x:_) -> error "todo"
            -- There shouldn't be more than one pointer, but theoretically
            -- possible. If a user sends funds to an address corresponding to
            -- the stake key (why would they do this though?), we could mistake
            -- it for the pointer.
            --
            -- TODO: Is this actually bad though? Or is it good because it will
            -- then be sent back as change? Any other problems?
  where
    modifyIx
        :: (Index 'Soft 'AddressK -> Index 'Soft 'AddressK)
        -> DelegationState k
        -> DelegationState k
    modifyIx f s = s { nextKeyIx = f (nextKeyIx s) }

    applyCert c s = modifyKey0 $ flip modifyIx s $ case c of
        RegisterKey _ -> id
        Delegate k
            | k == nextKey s            -> succ
            | otherwise                 -> id
        DeRegisterKey k
            | Just k == lastActiveKey s && hitGap k -> pred . pred -- i.e. to 0
            | Just k == lastActiveKey s -> pred
              -- TODO: Reason explicitly about the safety of this @pred@.
            | otherwise                 -> id
      where
        modifyKey0 s' = case c of
            RegisterKey k
                | k == acct 0 -> s' { isKey0Reg = True }
                | otherwise   -> s'
            DeRegisterKey k
                | k == acct 0 -> s' { isKey0Reg = False }
                | otherwise   -> s'
            _                 -> s'

        acct = toRewardAccount . keyAtIx s . toEnum

        hitGap k = k == acct 1 && not (isKey0Reg s)


--------------------------------------------------------------------------------
-- Operations
--------------------------------------------------------------------------------

-- | All stake keys worth listing to the user.
--
-- Now returns
-- 1. Active stake keys
-- 2. The next unregistered stake key
--
-- NOTE: Now it rarely tracks unexpected stake key registrations.
presentableKeys :: SoftDerivation k => DelegationState k -> [k 'AddressK XPub]
presentableKeys s = case lastActiveIx s of
    Just i -> map (keyAtIx s) [minBound .. (succ i)]
    Nothing -> [keyAtIx s minBound]

-- Keys meant to be used in addresses.
--
-- NOTE: Returned keys may not necessarily be registered and delegating. If the
-- user has no registered stake key, the first key (index 0) should still be
-- used in addresses, and is deemed "presentable".
usableKeys :: SoftDerivation k => DelegationState k -> [k 'AddressK XPub]
usableKeys s = case lastActiveIx s of
    Just i -> map (keyAtIx s) [minBound .. i]
    Nothing -> [keyAtIx s minBound]

-- | For testing.
activeKeys :: SoftDerivation k => DelegationState k -> [k 'AddressK XPub]
activeKeys s = case lastActiveIx s of
    Just i -> map (keyAtIx s) [minBound .. i]
    Nothing -> []

