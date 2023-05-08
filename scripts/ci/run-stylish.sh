#!/usr/bin/env bash

set -e

echo "The custom options for formatting this repo are:"
stylish-haskell --defaults | diff - ./.stylish-haskell.yaml | grep -E "^>.*[[:alnum:]]" | grep -v "#"
printf "\nFormatting haskell files...\n"

export LC_ALL=C.UTF-8
fd -p $(pwd)/ouroboros-consensus \
    -e hs \
    -E Setup.hs \
    -E ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Storage/LedgerDB/InMemory.hs \
    -E ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Storage/LedgerDB/OnDisk.hs \
    -E ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Storage/LedgerDB/Types.hs \
    -E ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Mempool/Impl/Pure.hs \
    -E ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Mempool/Impl/Types.hs\
    -E ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Mempool/Impl.hs \
    -E ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Mempool/TxLimits.hs \
    -E ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Util/Counting.hs \
    -E ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Util/SOP.hs \
    -E ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Util/OptNP.hs \
    -E ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/HardFork/Combinator/Util/Functors.hs \
    -E ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/HardFork/Combinator/Util/InPairs.hs \
    -E ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/HardFork/Combinator/Util/Match.hs \
    -E ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/HardFork/Combinator/Util/Telescope.hs \
    -E ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/HardFork/Combinator/Util/DerivingVia.hs \
    -E ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/HardFork/Combinator/Util/Tails.hs \
    -E ouroboros-consensus/src/consensus-testlib/Test/Util/Classify.hs \
    -E ouroboros-consensus-cardano/app/DBAnalyser/Parsers.hs \
    -X stylish-haskell \
    -c .stylish-haskell.yaml -i


# We don't want these deprecation warnings to be removed accidentally
grep "module.*DEPRECATED" ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Storage/LedgerDB/InMemory.hs >/dev/null 2>&1
grep "module.*DEPRECATED" ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Storage/LedgerDB/OnDisk.hs   >/dev/null 2>&1
grep "module.*DEPRECATED" ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Storage/LedgerDB/Types.hs    >/dev/null 2>&1
grep "module.*DEPRECATED" ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Mempool/Impl/Pure.hs         >/dev/null 2>&1
grep "module.*DEPRECATED" ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Mempool/Impl/Types.hs        >/dev/null 2>&1
grep "module.*DEPRECATED" ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Mempool/Impl.hs              >/dev/null 2>&1
grep "module.*DEPRECATED" ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Mempool/TxLimits.hs          >/dev/null 2>&1
grep "module.*DEPRECATED" ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Util/Counting.hs                         >/dev/null 2>&1
grep "module.*DEPRECATED" ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Util/SOP.hs                              >/dev/null 2>&1
grep "module.*DEPRECATED" ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Util/OptNP.hs                            >/dev/null 2>&1
grep "module.*DEPRECATED" ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/HardFork/Combinator/Util/Functors.hs     >/dev/null 2>&1
grep "module.*DEPRECATED" ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/HardFork/Combinator/Util/InPairs.hs      >/dev/null 2>&1
grep "module.*DEPRECATED" ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/HardFork/Combinator/Util/Match.hs        >/dev/null 2>&1
grep "module.*DEPRECATED" ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/HardFork/Combinator/Util/Telescope.hs    >/dev/null 2>&1
grep "module.*DEPRECATED" ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/HardFork/Combinator/Util/DerivingVia.hs  >/dev/null 2>&1
grep "module.*DEPRECATED" ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/HardFork/Combinator/Util/Tails.hs        >/dev/null 2>&1
grep "module.*DEPRECATED" ouroboros-consensus/src/consensus-testlib/Test/Util/Classify.hs                       >/dev/null 2>&1
grep "#if __GLASGOW_HASKELL__ < 900
import           Data.Foldable (asum)
#endif" ouroboros-consensus-cardano/app/DBAnalyser/Parsers.hs                           >/dev/null 2>&1
