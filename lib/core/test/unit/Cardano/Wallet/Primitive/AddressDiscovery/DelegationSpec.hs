{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Cardano.Wallet.Primitive.AddressDiscovery.DelegationSpec where

import Cardano.Address.Derivation
    ( XPub )
import Cardano.Wallet.Primitive.AddressDerivation
    ( Depth (..)
    , DerivationType (..)
    , HardDerivation (..)
    , KeyFingerprint (..)
    , MkKeyFingerprint (..)
    , MkKeyFingerprint
    , NetworkDiscriminant (..)
    , PaymentAddress (..)
    , RewardAccount (..)
    , RewardAccount
    , SoftDerivation (..)
    , ToRewardAccount (..)
    )
import Cardano.Wallet.Primitive.AddressDiscovery.Delegation
import Cardano.Wallet.Primitive.Types.Address
    ( Address (..) )
import Cardano.Wallet.Primitive.Types.Coin
    ( Coin (..) )
import Cardano.Wallet.Primitive.Types.Hash
    ( Hash (..) )
import Cardano.Wallet.Primitive.Types.Tx
    ( TxIn (..), TxOut (..) )
import Control.Arrow
    ( first )
import Crypto.Hash.Utils
    ( blake2b224 )
import Data.Map
    ( Map )
import Data.Set
    ( Set )
import Fmt
import GHC.Generics
    ( Generic )
import Prelude
import Test.Hspec
import Test.QuickCheck
    ( Arbitrary (..)
    , NonNegative (..)
    , Property
    , counterexample
    , forAllShow
    , frequency
    , genericShrink
    , property
    , sublistOf
    , withMaxSuccess
    , (.&&.)
    , (===)
    )
import Test.QuickCheck.Arbitrary.Generic
    ( genericArbitrary )

import qualified Cardano.Wallet.Primitive.Types.TokenBundle as TB
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as B8
import qualified Data.Map as Map
import qualified Data.Set as Set

spec :: Spec
spec = do
    let acc = toRewardAccount @StakeKey' . toEnum
    let regAndDeleg i = applyTx (Tx
            [ RegisterKey $ acc i
            , Delegate $ acc i
            ] [] []) (error "hash not needed")

    let s0 = initialDelegationState accK
    describe "initialDelegationState" $ do
        it "presentableKeys is [0]" $ do
            (presentableKeys s0) `shouldBe` [toEnum 0]
        it "usableKeys is [0]" $ do
            usableKeys s0 `shouldBe` [toEnum 0]

    let s1 = regAndDeleg 0 s0
    describe "registering and delegating key 0" $ do
        it "presentableKeys == [0, 1]" $ do
            (presentableKeys s1) `shouldBe` [toEnum 0, toEnum 1]
        it "usableKeys is still [0]" $ do
            usableKeys s1 `shouldBe` [toEnum 0]

    let s2 = regAndDeleg 1 s1
    describe "registering and delegating key 1" $ do
        it "presentableKeys == [0, 1, 2]" $ do
            (presentableKeys s2) `shouldBe` [toEnum 0, toEnum 1, toEnum 2]
        it "usableKeys == [0, 1]" $ do
            usableKeys s2 `shouldBe` [toEnum 0, toEnum 1]

    let s3 = regAndDeleg 5 s2
    describe "Impossible gaps in stake keys (shouldn't happen unless\
        \ someone manually constructs txs to mess with the on-chain state)" $ do
        it "presentableKeys == [0, 1, 2] (doesn't find 5)" $ do
            (presentableKeys s3) `shouldBe`
                [toEnum 0, toEnum 1, toEnum 2]
        it "usableKeys == [0, 1]" $ do
            usableKeys s3 `shouldBe` [toEnum 0, toEnum 1]

    it "(presentableKeys s) are consequtive" $ property $ \cmds -> do
        let env = applyCmds env0 cmds
        let keys = map fromEnum $ usableKeys $ wallet env
        isConsecutiveRange keys
    it "adversaries can't affect usableKeys" $ property $ \cmds -> do
        counterexample "\nstate /= state without adversarial cmds" $ do
            let usableKeys' = usableKeys . wallet . applyCmds env0
            usableKeys' cmds
                === usableKeys' (filter (not . isAdversarial) cmds)

    it "adversaries can't affect pointer ix" $ property $ \(NonNegative n) keys -> do
        let env = applyCmds env0 [CmdSetPortfolioOf n]
        let env' = applyCmds env (map CmdMimicPointerOutput keys)
        pointer (wallet env') === pointer (wallet env)

    it "(apply (cmds <> CmdSetPortfolioOf 0) s0) === s0"
        $ property $ \cmds -> do
            let env = applyCmds env0 (cmds ++ [CmdSetPortfolioOf 0])
            activeKeys (wallet env) === activeKeys (wallet env0)

    it "no rejected txs, normally" $ property $ \cmds -> do
        let env = applyCmds env0 cmds
        counterexample (pretty env) $
            rejectedTxs env === []

    -- Lots of weird things can happen when we concider concurrent user-actions
    -- on multiple wallet versions and rollbacks.
    --
    -- Whatever happens, we should be able to recover using a single
    -- @CmdSetPortfolioOf n@, and be concistent with the ledger.
    it "can recover from dropped transactions" $ withMaxSuccess 2000 $ property $ \cmds (NonNegative n) ->
        forAllSubchains (applyCmds env0 cmds) $ \env' -> do
            let env = applyCmds env' [CmdSetPortfolioOf n]

            let isSubsetOf a b = counterexample (show a <> " ⊄ " <> show b)
                    $ a `Set.isSubsetOf` b

            let allActiveKeysRegistered e =
                    Set.map toRewardAccount (Set.fromList (activeKeys $ wallet e))
                        `isSubsetOf` regs (ledger e)

            counterexample (pretty env) $
                length (activeKeys $ wallet env) === n
                    .&&. allActiveKeysRegistered env

-- | Take an arbitrary subset of the txs of an @Env@ to generate a new @Env@.
--
-- NOTE: Can drop txs, but not reorder them.
forAllSubchains :: Env -> (Env -> Property) -> Property
forAllSubchains env prop =  do
    forAllShow (sublistOf (reverse $ txs env)) (fmt . blockListF) $ \subchain ->  do
        prop $ applyTxs env0 subchain

accK :: StakeKey' 'AccountK XPub
accK = StakeKey' 0

isConsecutiveRange :: (Eq a, Num a) => [a] -> Bool
isConsecutiveRange [_] = True
isConsecutiveRange [] = True
isConsecutiveRange (a:b:t)
    | b == a + 1 = isConsecutiveRange (b:t)
    | otherwise  = False


--
-- Mock Stake Keys
--

-- | Mock key type for testing.
--
-- FIXME: We should do /some/ testing with @ShelleyKey@ though.
newtype StakeKey' (depth :: Depth) key = StakeKey' Word
    deriving newtype (Eq, Enum, Ord, Show, Bounded)

type StakeKey = StakeKey' 'AddressK XPub

instance ToRewardAccount StakeKey' where
    toRewardAccount (StakeKey' i) = RewardAccount . B8.pack $ show i
    someRewardAccount = error "someRewardAccount: not implemented"

instance HardDerivation StakeKey' where
    type AddressIndexDerivationType StakeKey' = 'Soft
    deriveAccountPrivateKey _ _ _ =
        error "deriveAccountPrivateKey: not implemented"
    deriveAddressPrivateKey _ _ _ _ =
        error "deriveAddressPrivateKey not implemented"

instance SoftDerivation StakeKey' where
    deriveAddressPublicKey _acc _role i = StakeKey' $ toEnum $ fromEnum i

instance MkKeyFingerprint StakeKey' Address where
    paymentKeyFingerprint (Address addr) = Right $ KeyFingerprint $ B8.drop 4 addr

instance PaymentAddress 'Mainnet StakeKey' where
    liftPaymentAddress (KeyFingerprint fp) = Address fp
    paymentAddress k = Address $ "addr" <> unRewardAccount (toRewardAccount k)

instance MkKeyFingerprint StakeKey' (StakeKey' 'AddressK XPub) where
    paymentKeyFingerprint k =
        Right $ KeyFingerprint $ unRewardAccount (toRewardAccount k)

--
-- Mock chain of delegation certificates
--

instance Arbitrary RewardAccount where
    arbitrary = toRewardAccount @StakeKey' <$> arbitrary

instance Arbitrary Cert where
    arbitrary = genericArbitrary
    shrink = genericShrink

instance Arbitrary (StakeKey' depth key) where
    arbitrary = StakeKey' <$> arbitrary

--
-- Mock chain data
--

data Cmd
    = CmdSetPortfolioOf Int
    -- ^ Calls @setPortfolioOf@ which registers or de-registers keys to reach
    -- the new target.
    --
    -- If the target is already met, the command has no effect.
    --
    -- Delegation certificates are /not/ generated for existing keys.
    --
    -- TODO: Also test arbitrary re-delegations.
    | CmdOldWalletToggleFirstKey

      -- ^ A wallet implementation without multi-stake-key support could decide
      -- to either
      -- 1. register stake-key 0 witout adding a pointer UTxO
      -- 2. de-register stake-key 0 despite despite e.g. key 1 being active
      -- depending on whether it is registered or not.
      --
      -- Having a "toggle"-command instead of two separate commands, makes
      -- generating valid arbitrary values easier.
    | CmdAdversarialReg RewardAccount
      -- ^ Someone could pay 2 ada to (re-)register your stake key. Your wallet
      -- shouldn't be affected negatively from it.
    | CmdMimicPointerOutput RewardAccount
      -- ^ Someone could send funds to the same UTxO
    deriving (Generic, Eq)

isAdversarial :: Cmd -> Bool
isAdversarial (CmdSetPortfolioOf _) = False
isAdversarial (CmdAdversarialReg _) = True
isAdversarial CmdOldWalletToggleFirstKey = False
isAdversarial (CmdMimicPointerOutput _) = True -- Kind of

instance Show Cmd where
    show (CmdSetPortfolioOf n) = "CmdSetPortfolioOf " <> show n
    show (CmdAdversarialReg (RewardAccount a)) = "CmdAdversarialReg " <> B8.unpack a
    show CmdOldWalletToggleFirstKey = "CmdOldWalletToggleFirstKey"
    show (CmdMimicPointerOutput (RewardAccount a)) = "CmdMimicPointerOutput " <> B8.unpack a

instance Buildable Tx where
    build (Tx cs [] []) = "Tx " <> listF cs
    build (Tx cs ins outs) = "Tx " <> listF cs <> " " <> listF' (inF . fst) ins <> " -> " <> listF' outF outs

inF :: TxIn -> Builder
inF (TxIn h ix) = build h <> "." <> build (fromEnum ix)

outF :: TxOut -> Builder
outF (TxOut (Address addr) _tb) = build $ B8.unpack addr

instance Buildable (DelegationState StakeKey') where
    build s = blockMapF
        [ ("accK" :: String, build $ show $ rewardAccountKey s )
        , ("nextKeyIx", build $ fromEnum $ nextKeyIx s)
        , ("isKey0Reg", build $ isKey0Reg s)
        , ("pointer", build $ pointer s)
        ]

instance Buildable PointerUTxO where
    build (PointerUTxO i _c) = "PointerUTxO " <> inF i

instance Buildable Env where
    build env = "Env:\n" <> blockMapF
        [ ("wallet" :: String, build $ wallet env)
        , ("txs", blockListF' "-" txF $ reverse $ txs env)
        , ("rejected txs", blockListF' "-" build $ reverse $ rejectedTxs env)
        , ("ledger", build $ ledger env)
        ]
      where
        txF tx = build (txid tx) <> ": " <> build tx


rewardAccountF :: RewardAccount -> Builder
rewardAccountF (RewardAccount a) = build (B8.unpack a)


instance Buildable Cert where
    build (RegisterKey k) = "RegKey " <> rewardAccountF k
    build (Delegate k) = "Deleg " <> rewardAccountF k
    build (DeRegisterKey k) = "DeReg " <> rewardAccountF k

instance Arbitrary Cmd where
    -- We don't want to generate too many adversarial registrations (we don't
    -- expect them to happen in reality), but at least some, and enough to cause
    -- consistent failures if something is wrong.
    arbitrary = frequency
        [ (85, CmdSetPortfolioOf . getNonNegative <$> arbitrary)
        , (5, CmdAdversarialReg <$> arbitrary)
        , (10, pure CmdOldWalletToggleFirstKey)
        , (10, CmdMimicPointerOutput <$> arbitrary)
        ]
    shrink = genericShrink

data Env = Env
    { wallet :: DelegationState StakeKey'
    , ledger :: Ledger
    , txs :: [Tx]
        -- ^ All accepted transactions so far in the chain. Newest first.
    , rejectedTxs :: [String]
        -- ^ User-generated txs that were rejected. I.e. not adversarial ones.
        -- Newest first.
    } deriving (Show, Eq)

env0 :: Env
env0 = Env (initialDelegationState accK) initialLedger [] []

stepCmd :: Cmd -> Env -> Env
stepCmd (CmdSetPortfolioOf n) env =
    case setPortfolioOf (wallet env) minUTxOVal mkAddr (acctIsReg (ledger env)) n of
        Just tx -> tryApplyTx tx env
        Nothing -> env
  where
    mkAddr k = Address $ "addr" <> unRewardAccount (toRewardAccount k)
    minUTxOVal = Coin 1

stepCmd (CmdAdversarialReg k) env
    | k `Set.member` regs (ledger env)
        = env -- We don't want tx errors to appear in @rejectedTxs@.
    | otherwise
        = tryApplyTx (Tx [RegisterKey k] [] []) env
stepCmd CmdOldWalletToggleFirstKey env =
            let
                key0 = toRewardAccount (keyAtIx (wallet env) minBound)
                isReg =  key0 `Set.member` (regs (ledger env))
                tx = Tx [if isReg then DeRegisterKey key0 else RegisterKey key0] [] []
            in tryApplyTx tx env
stepCmd (CmdMimicPointerOutput (RewardAccount acc)) env =
            let
                addr = liftPaymentAddress @'Mainnet @StakeKey' $ KeyFingerprint acc
                c = Coin 1
                out = TxOut addr (TB.fromCoin c)
                tx = Tx [] [] [out]
            in tryApplyTx tx env

tryApplyTx :: Tx -> Env -> Env
tryApplyTx tx env = case ledgerApplyTx tx h (ledger env) of
    Right l' -> env
        { ledger = l'
        , wallet = applyTx tx (txid tx) $ wallet env
        , txs = tx : txs env
        }
    Left e -> env { rejectedTxs = e : rejectedTxs env }
  where
    h = txid tx


applyCmds :: Env -> [Cmd] -> Env
applyCmds = foldl (flip stepCmd)

applyTxs :: Env -> [Tx] -> Env
applyTxs = foldl (flip tryApplyTx)

txid :: Tx -> Hash "Tx"
txid = Hash . BS.take 4 . blake2b224 . B8.pack . show


--
-- Mock ledger
--

data Ledger = Ledger
    { regs :: Set RewardAccount
    , utxos :: Map TxIn TxOut
    } deriving (Show, Eq)

instance Buildable Ledger where
    build l = blockMapF
        [ ("regs" :: String, listF' rewardAccountF (regs l))
        , ("utxos", mapF' inF outF (utxos l))
        ]

initialLedger :: Ledger
initialLedger = Ledger Set.empty Map.empty

acctIsReg :: Ledger -> RewardAccount -> Bool
acctIsReg l a = a `Set.member` (regs l)

ledgerApplyTx :: Tx -> (Hash "Tx") -> Ledger -> Either String Ledger
ledgerApplyTx tx h l' =
        (foldl (\x y -> x >>= ledgerApplyCert y) (Right l') (certs tx))
        -- Can be commented out to see the effects of no pointer UTxO on
        -- the tests:
            >>= ledgerApplyInsOus

  where
    ledgerApplyInsOus :: Ledger -> Either String Ledger
    ledgerApplyInsOus (Ledger r utxo) =
        let
            -- TODO: There could be duplicates, which we should forbid
            ins = Set.fromList $ map fst $ inputs tx
            newOuts = Map.fromList $
                zipWith
                    (curry $ first (TxIn h))
                    [0 ..]
                    (outputs tx)

            canSpend = ins `Set.isSubsetOf` Map.keysSet utxo

        in
            if canSpend
            then Right $ Ledger r $ Map.union newOuts $ utxo `Map.withoutKeys` ins
            else Left $ "invalid utxo spending in tx: " <> pretty tx

    ledgerApplyCert :: Cert -> Ledger -> Either String Ledger
    ledgerApplyCert (Delegate k) l
        | k `Set.member` (regs l)
            = pure l
        | otherwise
            = Left $ "Can't delegate: " <> show k <> " not in " <> show l
    ledgerApplyCert (RegisterKey k) l
        | k `Set.member` (regs l)
            = Left $ "Can't register: " <> show k <> " already in: " <> show l
        | otherwise
            = pure $ l { regs = Set.insert k (regs l) }
    ledgerApplyCert (DeRegisterKey k) l
        | k `Set.member` (regs l)
            = pure $ l { regs = Set.delete k (regs l) }
        | otherwise
            = Left $ "Can't deregister: " <> show k <> " not in " <> show l
