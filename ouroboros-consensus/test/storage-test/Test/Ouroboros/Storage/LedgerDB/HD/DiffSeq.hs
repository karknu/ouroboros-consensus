{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeApplications           #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Test.Ouroboros.Storage.LedgerDB.HD.DiffSeq (tests) where

import           Control.Monad (liftM)
import qualified Data.FingerTree.RootMeasured.Strict as RMFT
import           Data.Map.Diff.Strict (Diff, DiffEntry (..))
import           Data.Map.Diff.Strict.Internal (Diff (..), NEDiffHistory (..))
import           Data.Maybe.Strict (StrictMaybe (..))
import           Data.Sequence.NonEmpty (NESeq (..))
import           Data.Typeable
import           Ouroboros.Consensus.Storage.LedgerDB.DiffSeq
import qualified Ouroboros.Consensus.Storage.LedgerDB.DiffSeq as DS
                     (Length (..), SlotNoLB (..), SlotNoUB (..))
import           Test.Cardano.Ledger.Binary.Arbitrary ()
import           Test.QuickCheck.Classes
import           Test.QuickCheck.Classes.Semigroup.Cancellative
import           Test.Tasty
import           Test.Tasty.QuickCheck
import           Test.Util.Orphans.Arbitrary ()

tests :: TestTree
tests = testGroup "DiffSeq" [
    lawsTestOne (Proxy @(RootMeasure Key Val)) [
        semigroupLaws
      , monoidLaws
      , leftReductiveLaws
      , rightReductiveLaws
      , leftCancellativeLaws
      , rightCancellativeLaws
      ]
  , lawsTestOne (Proxy @(InternalMeasure Key Val)) [
        semigroupLaws
      , monoidLaws
      ]
  ]

type Key = Small Int
type Val = Small Int

{------------------------------------------------------------------------------
  Running laws in test trees
------------------------------------------------------------------------------}

lawsTest :: Laws -> TestTree
lawsTest Laws{lawsTypeclass, lawsProperties} = testGroup lawsTypeclass $
    fmap (uncurry testProperty) lawsProperties

lawsTestOne :: Typeable a => Proxy a -> [Proxy a -> Laws] -> TestTree
lawsTestOne p tts =
    testGroup (show $ typeOf p) (fmap (\f -> lawsTest $ f p) tts)

{------------------------------------------------------------------------------
  Diffs
------------------------------------------------------------------------------}

deriving newtype instance (Ord k, Arbitrary k, Arbitrary v)
                       => Arbitrary (Diff k v)

instance (Arbitrary v) => Arbitrary (NEDiffHistory v) where
  arbitrary = NEDiffHistory <$>
    ((:<||) <$> arbitrary <*> arbitrary)

instance (Arbitrary v) => Arbitrary (DiffEntry v) where
  arbitrary = oneof [
      Insert <$> arbitrary
    , Delete <$> arbitrary
    ]

{-------------------------------------------------------------------------------
  DiffSeq
-------------------------------------------------------------------------------}

instance (RMFT.SuperMeasured vt vi a, Arbitrary a)
      => Arbitrary (RMFT.StrictFingerTree vt vi a) where
  arbitrary = RMFT.fromList <$> arbitrary

instance (Ord k, Arbitrary k, Arbitrary v)
      => Arbitrary (RootMeasure k v) where
  arbitrary = RootMeasure <$> arbitrary <*> arbitrary

instance Arbitrary (InternalMeasure k v) where
  arbitrary = InternalMeasure <$> arbitrary <*> arbitrary <*> arbitrary

deriving newtype instance Arbitrary DS.Length
deriving newtype instance Arbitrary DS.SlotNoUB
deriving newtype instance Arbitrary DS.SlotNoLB

instance Arbitrary1 StrictMaybe where
  liftArbitrary arb = frequency [(1, return SNothing), (3, liftM SJust arb)]

  liftShrink shr (SJust x) = SNothing : [ SJust x' | x' <- shr x ]
  liftShrink _   SNothing  = []
