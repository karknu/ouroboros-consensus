{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE UndecidableInstances #-}

module Bench.Consensus.Mempool (
    -- * Commands
    MempoolCmd (..)
    -- ** Queries on commands
  , txsAdded
  , txsAddedInCmds
    -- * Commands execution
  , run
  ) where

import           Bench.Consensus.Mempool.TestBlock ()
import           Bench.Consensus.MempoolWithMockedLedgerItf
                     (MempoolWithMockedLedgerItf, getMempool)
import           Control.DeepSeq (NFData)
import           Control.Monad (void)
import           Data.Foldable (traverse_)
import           GHC.Generics (Generic)
import qualified Ouroboros.Consensus.Ledger.SupportsMempool as Ledger
import           Ouroboros.Consensus.Mempool (Mempool (..))
import           Ouroboros.Consensus.Mempool.API (AddTxOnBehalfOf (..))

{-------------------------------------------------------------------------------
  Commands
-------------------------------------------------------------------------------}

data MempoolCmd blk = TryAdd [Ledger.GenTx blk]
  deriving (Generic)

deriving anyclass instance (NFData (Ledger.GenTx blk)) => NFData (MempoolCmd blk)

txsAdded :: MempoolCmd blk -> [Ledger.GenTx blk]
txsAdded (TryAdd xs) = xs

txsAddedInCmds :: [MempoolCmd blk] -> [Ledger.GenTx blk]
txsAddedInCmds = concatMap txsAdded

{-------------------------------------------------------------------------------
  Commands execution
-------------------------------------------------------------------------------}

-- TODO: the interpretation of running the command should be defined elsewhere,
-- and tested by state-mathine tests.
run ::
     Monad m
  => MempoolWithMockedLedgerItf m blk -> [MempoolCmd blk] -> m ()
run mempool = traverse_ (runCmd mempool)

runCmd ::
     Monad m
  => MempoolWithMockedLedgerItf m blk -> MempoolCmd blk -> m ()
runCmd mempoolWithMockedItf = \case
    TryAdd txs -> void $ mapM (addTx mempool AddTxForRemotePeer) txs -- TODO: we might want to benchmark the 'Intervene' case
  where
    mempool = getMempool mempoolWithMockedItf
