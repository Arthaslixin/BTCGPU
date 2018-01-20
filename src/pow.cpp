// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "pow.h"

#include "arith_uint256.h"
#include "chain.h"
#include "chainparams.h"
#include "crypto/equihash.h"
#include "primitives/block.h"
#include "streams.h"
#include "uint256.h"
#include "util.h"
#include <algorithm>

unsigned int GetNextWorkRequired(const CBlockIndex* pindexLast, const CBlockHeader *pblock,
                                 const Consensus::Params& params)
{
    assert(pindexLast != nullptr);
    int nHeight = pindexLast->nHeight + 1;
    bool postfork = nHeight >= params.BTGHeight;

    if (postfork == false) {
        // Original Bitcion PoW.
        return BitcoinGetNextWorkRequired(pindexLast, pblock, params);
    }
    else if (nHeight < params.BTGHeight + params.BTGPremineWindow) {
        // PoW limit for premine period.
        unsigned int nProofOfWorkLimit = UintToArith256(params.PowLimit(true)).GetCompact();
        return nProofOfWorkLimit;
    }
    else if (nHeight < params.BTGHeight + params.BTGPremineWindow + params.nDigishieldAveragingWindow) {
        // Pow limit start for warm-up period.
        return UintToArith256(params.powLimitStart).GetCompact();
    }
    else if (nHeight < params.BTGJacobEmaHeight) {
        // Regular Digishield v3.
        return DigishieldGetNextWorkRequired(pindexLast, pblock, params);
    } else {
        // Jacob's EMA.
        return JacobEmaGetNextWorkRequired(pindexLast, pblock, params);
    }
}

unsigned int JacobEmaGetNextWorkRequired(const CBlockIndex* pindexLast, const CBlockHeader *pblock,
                                         const Consensus::Params& params)
{
    assert(pindexLast != nullptr);
    unsigned int nProofOfWorkLimit = UintToArith256(params.PowLimit(true)).GetCompact();

    if (params.fPowAllowMinDifficultyBlocks) {
        // Special difficulty rule for testnet:
        // If the new block's timestamp is more than 2* 10 minutes
        // then allow mining of a min-difficulty block.
        if (pblock->GetBlockTime() > pindexLast->GetBlockTime() + params.nPowTargetSpacing*2)
            return nProofOfWorkLimit;
    }

    int T = params.nPowTargetSpacing;   // 600
    int N = params.nJacobEmaAveragingWindow;   // 50
    int limit = std::min(7, std::max((N * 100 / 89) - N, 10));
    uint32_t previous_target = pindexLast->nBits;

    // Find the max timestamp within last `limit` blocks.
    int height_first = pindexLast->nHeight - limit + 1;
    assert(height_first >= 0);
    int64_t max_time = 0;
    for (int i = height_first; i < pindexLast->nHeight; ++i) {
        int64_t block_time = pindexLast->GetAncestor(i)->GetBlockTime();
        if (block_time > max_time) {
            max_time = block_time;
        }
    }

    arith_uint256 solve_time = pindexLast->GetBlockTime() - max_time;   // ~600
    solve_time = std::max((arith_uint256)(T / 200), std::min((arith_uint256)(T * limit), solve_time));

    

    // (T, N, solve_time) --> int32/64


    // next_D = previous_D * ( T/ST + e^(-ST*2/T/N) * (1-T/ST) )
    // 1 / target = (1 / previous_target) * ( T/ST + e^(-ST*2/T/N) * (1-T/ST) )

    // target = previous_target / ( T/ST + e^(-ST*2/T/N) * (1-T/ST) )
    //        = previous_target * ( .... )


    const CBlockIndex* pindexFirst = pindexLast->GetAncestor(height_first);
    assert(pindexFirst);

    return JacobEmaCalculateNextWorkRequired(T, N , solve_time, previous_target);
}

unsigned int JacobEmaCalculateNextWorkRequired(int T, int N, arith_uint256 solve_time, uint32_t previous_target)
{
    uint32_t target_high = (previous_target >> 24) & 0xFF;
    arith_uint256 target_low = previous_target & 0xFFFFFF;
    arith_uint256 num = target_low << 192;
    arith_uint256 exp = (solve_time << 128) / T * 2 / N;
    int n = 15;
    arith_uint256 u256_1 = arith_uint256(1) << 128;
    arith_uint256 expResult = u256_1;
    while(n > 0){
        expResult = (u256_1 - exp * expResult / n) >> 128;
        n--;
    }
    arith_uint256 den = (solve_time - arith_uint256(T)) * expResult + (arith_uint256(T) << 128);
    arith_uint256 tar = (num * solve_time / den) >> (192 - 128);
    tar = tar << (8 * (target_high - 3));
    uint32_t result = tar.GetCompact();
    return result;
}

// arith_uint256 SimNegExpU256(arith_uint256 x, int n)
// {
//     arith_uint256 u256_1 = pow(2,128);
//     arith_uint256 r = u256_1;
//     while(n > 0){
//         r = u256_1 - x * r / n / pow(2, 128);
//         n--;
//     }
//     return r;
// }

unsigned int DigishieldGetNextWorkRequired(const CBlockIndex* pindexLast, const CBlockHeader *pblock,
                                           const Consensus::Params& params)
{
    assert(pindexLast != nullptr);
    if (params.fPowNoRetargeting)
        return pindexLast->nBits;
    unsigned int nProofOfWorkLimit = UintToArith256(params.PowLimit(true)).GetCompact();  // Always postfork.

    const CBlockIndex* pindexFirst = pindexLast;
    arith_uint256 bnTot {0};
    for (int i = 0; pindexFirst && i < params.nDigishieldAveragingWindow; i++) {
        arith_uint256 bnTmp;
        bnTmp.SetCompact(pindexFirst->nBits);
        bnTot += bnTmp;
        pindexFirst = pindexFirst->pprev;
    }
    
    if (pindexFirst == NULL)
        return nProofOfWorkLimit;
    
    arith_uint256 bnAvg {bnTot / params.nDigishieldAveragingWindow};
    return DigishieldCalculateNextWorkRequired(bnAvg, pindexLast->GetMedianTimePast(), pindexFirst->GetMedianTimePast(),
                                               params);
}

unsigned int DigishieldCalculateNextWorkRequired(arith_uint256 bnAvg, int64_t nLastBlockTime, int64_t nFirstBlockTime,
                                                 const Consensus::Params& params)
{
    // Limit adjustment
    int64_t nActualTimespan = nLastBlockTime - nFirstBlockTime;
    
    if (nActualTimespan < params.DigishieldMinActualTimespan())
        nActualTimespan = params.DigishieldMinActualTimespan();
    if (nActualTimespan > params.DigishieldMaxActualTimespan())
        nActualTimespan = params.DigishieldMaxActualTimespan();

    // Retarget
    const arith_uint256 bnPowLimit = UintToArith256(params.PowLimit(true));
    arith_uint256 bnNew {bnAvg};
    bnNew /= params.DigishieldAveragingWindowTimespan();
    bnNew *= nActualTimespan;
    
    if (bnNew > bnPowLimit)
        bnNew = bnPowLimit;

    return bnNew.GetCompact();
}

unsigned int BitcoinGetNextWorkRequired(const CBlockIndex* pindexLast, const CBlockHeader *pblock, const Consensus::Params& params)
{
    assert(pindexLast != nullptr);
    unsigned int nProofOfWorkLimit = UintToArith256(params.PowLimit(false)).GetCompact();
    
    // Only change once per difficulty adjustment interval
    if ((pindexLast->nHeight+1) % params.DifficultyAdjustmentInterval() != 0)
    {
        if (params.fPowAllowMinDifficultyBlocks)
        {
            // Special difficulty rule for testnet:
            // If the new block's timestamp is more than 2* 10 minutes
            // then allow mining of a min-difficulty block.
            if (pblock->GetBlockTime() > pindexLast->GetBlockTime() + params.nPowTargetSpacing*2)
                return nProofOfWorkLimit;
            else
            {
                // Return the last non-special-min-difficulty-rules-block
                const CBlockIndex* pindex = pindexLast;
                while (pindex->pprev && pindex->nHeight % params.DifficultyAdjustmentInterval() != 0 && pindex->nBits == nProofOfWorkLimit)
                    pindex = pindex->pprev;
                return pindex->nBits;
            }
        }
        return pindexLast->nBits;
    }

    // Go back by what we want to be 14 days worth of blocks
    int nHeightFirst = pindexLast->nHeight - (params.DifficultyAdjustmentInterval()-1);
    assert(nHeightFirst >= 0);
    const CBlockIndex* pindexFirst = pindexLast->GetAncestor(nHeightFirst);
    assert(pindexFirst);

    return BitcoinCalculateNextWorkRequired(pindexLast, pindexFirst->GetBlockTime(), params);
}

unsigned int BitcoinCalculateNextWorkRequired(const CBlockIndex* pindexLast, int64_t nFirstBlockTime, const Consensus::Params& params)
{
    if (params.fPowNoRetargeting)
        return pindexLast->nBits;
    
    // Limit adjustment step
    int64_t nActualTimespan = pindexLast->GetBlockTime() - nFirstBlockTime;
    if (nActualTimespan < params.nPowTargetTimespanLegacy/4)
        nActualTimespan = params.nPowTargetTimespanLegacy/4;
    if (nActualTimespan > params.nPowTargetTimespanLegacy*4)
        nActualTimespan = params.nPowTargetTimespanLegacy*4;
    
    // Retarget
    const arith_uint256 bnPowLimit = UintToArith256(params.PowLimit(false));
    arith_uint256 bnNew;
    bnNew.SetCompact(pindexLast->nBits);
    bnNew *= nActualTimespan;
    bnNew /= params.nPowTargetTimespanLegacy;
    
    if (bnNew > bnPowLimit)
        bnNew = bnPowLimit;
    
    return bnNew.GetCompact();
}

bool CheckEquihashSolution(const CBlockHeader *pblock, const CChainParams& params)
{
    unsigned int n = params.EquihashN();
    unsigned int k = params.EquihashK();

    // Hash state
    crypto_generichash_blake2b_state state;
    EhInitialiseState(n, k, state);

    // I = the block header minus nonce and solution.
    CEquihashInput I{*pblock};
    // I||V
    CDataStream ss(SER_NETWORK, PROTOCOL_VERSION);
    ss << I;
    ss << pblock->nNonce;

    // H(I||V||...
    crypto_generichash_blake2b_update(&state, (unsigned char*)&ss[0], ss.size());

    bool isValid;
    EhIsValidSolution(n, k, state, pblock->nSolution, isValid);
    if (!isValid)
        return error("CheckEquihashSolution(): invalid solution");

    return true;
}

bool CheckProofOfWork(uint256 hash, unsigned int nBits, bool postfork, const Consensus::Params& params)
{
    bool fNegative;
    bool fOverflow;
    arith_uint256 bnTarget;

    bnTarget.SetCompact(nBits, &fNegative, &fOverflow);

    // Check range
    if (fNegative || bnTarget == 0 || fOverflow || bnTarget > UintToArith256(params.PowLimit(postfork)))
        return false;

    // Check proof of work matches claimed amount
    if (UintToArith256(hash) > bnTarget)
        return false;

    return true;
}
