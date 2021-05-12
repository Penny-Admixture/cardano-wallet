{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Module for `DelegationState`.
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
-- Delegation State
--------------------------------------------------------------------------------

-- | Delegation state
--
-- === Goals
-- 1. Allow a wallet to have an arbitrary number of stake keys
-- 2. Ensure those stake keys can be automatically discovered on-chain
-- 3. Ensure the wallet is always aware of all stake keys it registers, even in
-- the case of concurrent user actions on multiple wallet instances, and old
-- wallet software.
--
-- === Diagram
-- Diagram of states, where the list denotes active (registered /and/ delegating)
-- keys.
--
-- Here we assume the minUTxOValue is 1 ada.
--
-- Note that intermediate steps for the `PointerUTxO` should be skipped within a
-- transaction.
-- E.g. to transition from [] to [0,1,2] we should deposit 1 ada to key 3,
-- skipping key 2.
--
-- See the implementation of `setPortfolioOf` and `applyTx` for more details.
--
-- @
-- ┌────────────────────┐           ┌────────────────────┐                     ┌────────────────────┐            ┌─────────────────────┐
-- │                    │           │                    │                     │                    │            │                     │
-- │                    │           │                    │       Pointer       │                    │            │                     │
-- │                    │──────────▶│                    │ ──────deposit──────▶│                    │ ─────────▶ │                     │ ─────────▶
-- │                    │           │                    │                     │       [0,1]        │            │       [0,1,2]       │
-- │         []         │           │        [0]         │                     │1 ada held by key 2 │            │ 1 ada held by key 3 │
-- │                    │           │                    │                     │                    │            │                     │
-- │                    │           │                    │       Pointer       │                    │            │                     │
-- │                    │◀──────────│                    │ ◀─────deposit ──────│                    │◀────────── │                     │◀──────────
-- │                    │           │                    │       returned      │                    │            │                     │
-- └────────────────────┘◀──┐       └────────────────────┘                     └────────────────────▲            ▲─────────────────────▲            ▲
--                          └───┐                                                     │       ▲     └─┐         ┌┘      │       ▲      └─┐         ┌┘
-- Normal states                └───┐                                                 │       │       └─┐     ┌─┘       │       │        └─┐     ┌─┘
--                                  └───┐                                             │       │         └─┐ ┌─┘         │       │          └─┐ ┌─┘
-- ╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳└───┐╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳│╳╳╳╳╳╳╳│╳╳╳╳╳╳╳╳╳╳╳│ │╳╳╳╳╳╳╳╳╳╳╳│╳╳╳╳╳╳╳│╳╳╳╳╳╳▶     ├─┤
--                                          └───┐                                     │       │         ┌─┘ └─┐         │       │          ┌─┘ └─┐
-- States caused by                             └────┐Pointer                         ▼       │       ┌─┘     └─┐       ▼       │        ┌─┘     └─┐
-- old wallet                                        └deposit                  ┌────────────────────┐─┘         └┬─────────────────────┐─┘         └─
-- de-registering                                     returned─┐               │                    │            │                     │
-- stake-key 0                                                 └────┐          │                    │ ─────────▶ │                     │ ─────────▶
-- of multi-stake                                                   └────┐     │                    │            │                     │
-- key wallet                                                            └──── │        [1]         │            │        [1,2]        │
--                                                                             │1 ada held by key 2 │            │ 1 ada held by key 3 │
--                                                                             │                    │            │                     │
--                                                                             │                    │◀────────── │                     │◀──────────
--                                                                             │                    │            │                     │
--                                                                             │                    │            │                     │
--                                                                             └────────────────────┘            └─────────────────────┘
-- @
data DelegationState k = DelegationState
    { -- | The account public key from which the stake keys should be derived.
      rewardAccountKey :: k 'AccountK XPub

      -- | The next unregistered stake key.
      --
      -- The active stake keys can be described as the half-open interval
      --    @[0, nextKeyIx )@
      -- having a length of @nextKeyIx@.
      --
      -- E.g. a state with @nextKeyIx=0@ has no keys, and @nextKeyIx=2@ has the keys
      -- @[0,1]@.
    , nextKeyIx :: !(Index 'Soft 'AddressK)

      -- | By threading a long a "pointer UTxO", we leverage the ledger rules to
      -- ensure transactions cannot be re-ordered in a way that breaks the
      -- rules/assumtions for how stake-keys are managed.
    , pointer :: !(Maybe PointerUTxO)

      -- | For compatibility with single-stake-key wallets, we track whether
      -- stake key 0 is registered or not separately.
      --
      -- See the implementaiton of `applyTx` for how it is used.
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

keyAtIx
    :: (SoftDerivation k)
    => DelegationState k
    -> Index 'Soft 'AddressK
    -> k 'AddressK XPub
keyAtIx s = deriveAddressPublicKey (rewardAccountKey s) MutableAccount

lastActiveIx
    :: DelegationState k
    -> Maybe (Index 'Soft 'AddressK)
lastActiveIx s
    | nextKeyIx s == minBound = Nothing
    | otherwise               = Just $ pred $ nextKeyIx s

data PointerUTxO = PointerUTxO { pTxIn :: TxIn, pCoin :: Coin }
    deriving (Generic, Eq, Show)
    deriving anyclass NFData

-- | Returns the index corresponding to the payment key the `PointerUTxO`
-- should be locked with.
--
-- Our current implementation we require the `PointerUTxO` to be created in the
-- @[0] -> [0,1] transition@, i.e. @nextKeyIx 1 -> nextKeyIx 2@.
pointerIx
    :: DelegationState k
    -> Maybe (Index 'Soft 'AddressK)
pointerIx s
    | nextKeyIx s == minBound       = Nothing
    | nextKeyIx s == succ minBound  = Nothing
    | otherwise                     = Just $ nextKeyIx s

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

-- | A transaction type specific to `DelegationState`.
--
-- Intented to be converted both from and to a more real transaction type.
--
-- When constructing a real transaction from `Tx`, these `outputs`
-- should appear before other outputs. In the theoretical event that there's
-- also a user-specified output with the same payment key as the pointer output,
-- `applyTx` will track the first one as the new pointer.
data Tx = Tx
    { certs :: [Cert]
    , inputs :: [(TxIn, Coin)]
    , outputs :: [TxOut]
    }
    deriving (Eq, Generic)
    deriving Show via (Quiet Tx)

data Cert
    = RegisterKey RewardAccount
    | Delegate RewardAccount
      -- ^ Which pool we're delegating to is here (and for now) irrelevant.
      -- The main thing is that there exists a witness on-chain for this stake
      -- key (registration certs don't require witnesses)
      --
      -- TODO: We may also want to add the PoolId here.
    | DeRegisterKey RewardAccount
    deriving (Eq, Show, Generic)

-- | Given a `DelegationState`, produce a `Tx` registering or de-registering
-- stake-keys, in order to have @n@ stake-keys.
--
-- E.g. @setPortfolioOf s0 _ _ 2@ creates a tx which after application causes
-- the state to have @activeKeys == [0,1]@
--
-- Returns @Nothing@ if the target @n@ is already reached.
setPortfolioOf
    :: (SoftDerivation k, ToRewardAccount k)
    => DelegationState k
    -> Coin
        -- ^ minUTxOVal
    -> (k 'AddressK XPub -> Address)
        -- ^ A way to construct an Address
    -> (RewardAccount -> Bool)
        -- ^ Whether or not the key is registered.
        --
        -- TODO: Need a Set or Map for the real implementation with LSQ.
    -> Int
        -- ^ Target number of stake keys.
    -> Maybe Tx
setPortfolioOf s minUTxOVal mkAddress isReg n =
    let s' = s { nextKeyIx = toEnum n }
        mkTxIn (PointerUTxO i c) = (i, c)
        -- Note: If c > minUTxOVal we need to rely on the wallet to return the
        -- difference to the user as change.
        txWithCerts [] = Nothing
        txWithCerts cs = Just $ Tx
            { certs = cs
            , inputs = maybeToList (mkTxIn <$> pointer s)
            , outputs = maybeToList $
                (\i -> TxOut
                    (mkAddress $ keyAtIx s i)
                    (TB.fromCoin minUTxOVal)
                ) <$> pointerIx s'
            }
    in
        txWithCerts $ repairKey0
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

    repairKey0 = reRegKey0IfNeeded ++ deRegKey0IfNeeded
      where
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

-- | Apply a `Tx` to a `DelegationState`.
--
-- We do it in two steps:
-- 1. Apply certificates
-- 2. Look for new UTxO pointer based on the new state.
--
-- Because of this (and possibly more reasons), we may accept invalid sequences
-- of `Tx`s from alternative implementations than `setPortfolioOf`.
applyTx
    :: forall k. ( SoftDerivation k
        , ToRewardAccount k
        , MkKeyFingerprint k Address
        , MkKeyFingerprint k (k 'AddressK XPub))
    => Tx
    -> Hash "Tx"
    -> DelegationState k
    -> DelegationState k
applyTx (Tx cs ins outs) h s0 = updatePointer $ foldl (flip applyCert) (HasChanged s0 False) cs
  where
    -- | Removes the pointer if it was spent, and looks for the creation of a
    -- new pointer output using the `pointerIx` (essensially `nextKeyIx`)
    -- payment key.
    updatePointer
        :: HasChanged (DelegationState k)
        -> DelegationState k
    --updatePointer (HasChanged s False) = s
    updatePointer (HasChanged s _) = case (pointerIns, pointerOuts) of
        ([],[]) -> s
        ([_],[]) -> s { pointer = Nothing }
        (_, (ix,TxOut _addr tb) : _rest)
            -- Outputs with the same payment key as the pointer could in theory
            -- exist, if they manually send funds to it, and their wallet
            -- software allows them to do it while also re-delegating.
            --
            -- TODO: If the pointer UTxO contains tokens, we might want to crash.
            -- TODO: We might also want to trace a warning if _rest /= []
            -> s { pointer = Just $ PointerUTxO (TxIn h ix) (TB.getCoin tb) }
        (_:_, []) -> error "applyTx: looks as if the same input was spent twice\
                        \, which is completely impossible."
      where
        isOurOut (TxOut addr _b) =
            case (paymentKeyFingerprint @k . keyAtIx s <$> pointerIx s, paymentKeyFingerprint addr) of
            (Just (Right fp), Right fp')
                | fp == fp' -> True
                | otherwise -> False
            _ -> False
        pointerIns = filter (\(x,_) -> Just x == (pTxIn <$> pointer s)) ins
        pointerOuts = filter (isOurOut . snd) $ zip [0..] outs


    modifyIx
        :: (Index 'Soft 'AddressK -> Index 'Soft 'AddressK)
        -> HasChanged (DelegationState k)
        -> HasChanged (DelegationState k)
    modifyIx f (HasChanged s changed) =
        let
            ix = nextKeyIx s
            ix' = f ix
            changed' = ix' /= ix
        in
        HasChanged (s { nextKeyIx = ix' }) (changed || changed')


    -- TODO: Instead of all this HasChanged logic, we should probably just have
    -- one @State@ and be very exact about what we expect about the pointer.

    applyCert c hc@(HasChanged s _) = modifyKey0 $ flip modifyIx hc $ case c of
        RegisterKey _ -> id
        Delegate k
            | k == nextKey s            -> succ
            | otherwise                 -> id
        DeRegisterKey k
            | Just k == lastActiveKey s && hitGap k -> pred . pred -- i.e. to 0
            | Just k == lastActiveKey s -> pred
            | otherwise                 -> id
      where
        modifyKey0 (HasChanged s' hc') = case c of
            RegisterKey k
                | k == acct 0 -> HasChanged (s' { isKey0Reg = True }) True
                | otherwise   -> HasChanged s' hc'
            DeRegisterKey k
                | k == acct 0 -> HasChanged (s' { isKey0Reg = False }) True
                | otherwise   -> HasChanged s' hc'
            _                 -> HasChanged s' hc'

        acct = toRewardAccount . keyAtIx s . toEnum

        lastActiveKey s' = toRewardAccount . keyAtIx s' <$> lastActiveIx s'
        nextKey s' = toRewardAccount . keyAtIx s' $ nextKeyIx s'

        hitGap k = k == acct 1 && not (isKey0Reg s)

-- Helper to annotate whether @a@ has changed with respect to some other value
-- @a@.
data HasChanged a = HasChanged a Bool
    deriving (Functor)


--------------------------------------------------------------------------------
-- Operations
--------------------------------------------------------------------------------

-- | All stake keys worth listing to the user.
--
-- May include:
-- 1. Active stake keys
-- 2. The next un-active key
--
-- NOTE: In theory we might want also present stake keys that are unexpectedly
-- registered, as they could be de-registered to reclaim the deposit, but this
-- should in-practice never happen.
--
-- If @sn@ denotes the state with @n@ registered and delegating keys:
-- >>> presentableKeys s0
-- [0]
-- >>> presentableKeys s1
-- [0, 1]
-- >>> presentableKeys s2
-- [0, 1, 2]
presentableKeys :: SoftDerivation k => DelegationState k -> [k 'AddressK XPub]
presentableKeys s = case lastActiveIx s of
    Just i -> map (keyAtIx s) [minBound .. (succ i)]
    Nothing -> [keyAtIx s minBound]

-- Keys meant to be used in addresses.
--
-- If @sn@ denotes the state with @n@ registered and delegating keys:
-- >>> usableKeys s0
-- [0]
-- >>> usableKeys s1
-- [0]
-- >>> usableKeys s2
-- [0, 1]
--
-- Note that for @s0@, we have no active stake keys, but we still want to use
-- key 0 as part of addresses.
usableKeys :: SoftDerivation k => DelegationState k -> [k 'AddressK XPub]
usableKeys s = case lastActiveIx s of
    Just i -> map (keyAtIx s) [minBound .. i]
    Nothing -> [keyAtIx s minBound]

-- | For testing. Returns all registered and delegating stake keys.
activeKeys :: SoftDerivation k => DelegationState k -> [k 'AddressK XPub]
activeKeys s = case lastActiveIx s of
    Just i -> map (keyAtIx s) [minBound .. i]
    Nothing -> []
