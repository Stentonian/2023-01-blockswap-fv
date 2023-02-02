using MocksETH as sETHToken
using MocksETHBad as sETHTokenBad

methods {
    //// Regular methods
    totalETHReceived() returns (uint256) envfree
    isKnotRegistered(bytes32) returns (bool) envfree
    isNoLongerPartOfSyndicate(bytes32) returns (bool) envfree

    //// Resolving external calls
  // stakeHouseUniverse
  stakeHouseKnotInfo(bytes32) returns (address,address,address,uint256,uint256,bool) => DISPATCHER(true)
    memberKnotToStakeHouse(bytes32) returns (address) => DISPATCHER(true) // not used directly by Syndicate
    // stakeHouseRegistry
    getMemberInfo(bytes32) returns (address,uint256,uint16,bool) => DISPATCHER(true) // not used directly by Syndicate
    // slotSettlementRegistry
  stakeHouseShareTokens(address) returns (address)  => DISPATCHER(true)
  currentSlashedAmountOfSLOTForKnot(bytes32) returns (uint256)  => DISPATCHER(true)
  numberOfCollateralisedSlotOwnersForKnot(bytes32) returns (uint256)  => DISPATCHER(true)
  getCollateralisedOwnerAtIndex(bytes32, uint256) returns (address) => DISPATCHER(true)
  totalUserCollateralisedSLOTBalanceForKnot(address, address, bytes32) returns (uint256) => DISPATCHER(true)
    // sETH
    sETHToken.balanceOf(address) returns (uint256) envfree
    // sETH bad
    sETHTokenBad.balanceOf(address) returns (uint256) envfree
    // ERC20
    name()                                returns (string)  => DISPATCHER(true)
    symbol()                              returns (string)  => DISPATCHER(true)
    decimals()                            returns (string) envfree => DISPATCHER(true)
    totalSupply()                         returns (uint256) => DISPATCHER(true)
    balanceOf(address)                    returns (uint256) => DISPATCHER(true)
    allowance(address,address)            returns (uint)    => DISPATCHER(true)
    approve(address,uint256)              returns (bool)    => DISPATCHER(true)
    transfer(address,uint256)             returns (bool)    => DISPATCHER(true)
    transferFrom(address,address,uint256) returns (bool)    => DISPATCHER(true)

    //// Harnessing
    // harnessed variables
    accruedEarningPerCollateralizedSlotOwnerOfKnot(bytes32,address) returns (uint256) envfree
    calculateNewAccumulatedETHPerCollateralizedSharePerKnot() returns (uint256) envfree
    accumulatedETHPerCollateralizedSlotPerKnot() returns (uint256) envfree
    accumulatedETHPerFreeFloatingShare() returns (uint256) envfree
    totalETHProcessedPerCollateralizedKnot(bytes32) returns (uint256) envfree
    sETHStakedBalanceForKnot(bytes32,address) returns (uint256) envfree
    sETHTotalStakeForKnot(bytes32) returns (uint256) envfree
    sETHUserClaimForKnot(bytes32,address) returns (uint256) envfree
    numberOfRegisteredKnots() returns (uint256) envfree
    totalFreeFloatingShares() returns (uint256) envfree
    calculateETHForFreeFloatingOrCollateralizedHolders() returns (uint256) envfree
    getUnprocessedETHForAllFreeFloatingSlot() returns (uint256) envfree
    calculateNewAccumulatedETHPerFreeFloatingShare() returns (uint256) envfree
    lastAccumulatedETHPerFreeFloatingShare(bytes32) returns (uint256) envfree
    // harnessed functions
    deRegisterKnots(bytes32)
    deRegisterKnots(bytes32,bytes32)
    stake(bytes32,uint256,address)
    stake(bytes32,bytes32,uint256,uint256,address)
    unstake(address,address,bytes32,uint256)
    unstake(address,address,bytes32,bytes32,uint256,uint256)
    claimAsStaker(address,bytes32)
    claimAsStaker(address,bytes32,bytes32)
    claimAsCollateralizedSLOTOwner(address,bytes32)
    claimAsCollateralizedSLOTOwner(address,bytes32,bytes32)
    registerKnotsToSyndicate(bytes32)
    registerKnotsToSyndicate(bytes32,bytes32)
    addPriorityStakers(address)
    addPriorityStakers(address,address)
    batchUpdateCollateralizedSlotOwnersAccruedETH(bytes32)
    batchUpdateCollateralizedSlotOwnersAccruedETH(bytes32,bytes32)
    getSETHTokenBalance(bytes32, address) returns (uint256) envfree
}

/// We defined additional functions to get around the complexity of defining dynamic arrays in cvl. We filter them in
/// normal rules and invariants as they serve no purpose.
definition notHarnessCall(method f) returns bool =
    f.selector != batchUpdateCollateralizedSlotOwnersAccruedETH(bytes32).selector
    && f.selector != batchUpdateCollateralizedSlotOwnersAccruedETH(bytes32,bytes32).selector
    && f.selector != deRegisterKnots(bytes32).selector
    && f.selector != deRegisterKnots(bytes32,bytes32).selector
    && f.selector != stake(bytes32,uint256,address).selector
    && f.selector != stake(bytes32,bytes32,uint256,uint256,address).selector
    && f.selector != unstake(address,address,bytes32,uint256).selector
    && f.selector != unstake(address,address,bytes32,bytes32,uint256,uint256).selector
    && f.selector != claimAsStaker(address,bytes32).selector
    && f.selector != claimAsStaker(address,bytes32,bytes32).selector
    && f.selector != claimAsCollateralizedSLOTOwner(address,bytes32).selector
    && f.selector != claimAsCollateralizedSLOTOwner(address,bytes32,bytes32).selector
    && f.selector != registerKnotsToSyndicate(bytes32).selector
    && f.selector != registerKnotsToSyndicate(bytes32,bytes32).selector
    && f.selector != addPriorityStakers(address).selector
    && f.selector != addPriorityStakers(address,address).selector;


function isKnotActive(bytes32 blsKey) returns bool {
    return (isKnotRegistered(blsKey) && !isNoLongerPartOfSyndicate(blsKey));
}

/// Corrollary that can be used as requirement after sETH solvency is proven.
function sETHSolvencyCorrollary(address user1, address user2, bytes32 knot) returns bool {
    return sETHStakedBalanceForKnot(knot,user1) + sETHStakedBalanceForKnot(knot,user2) <= sETHTotalStakeForKnot(knot);
}

/**
 * An unregistered knot can not be deregistered.
 */
rule canNotDegisterUnregisteredKnot(method f) filtered {
    f -> notHarnessCall(f)
} {
    bytes32 knot; env e;
    require !isKnotRegistered(knot);

    deRegisterKnots@withrevert(e, knot);

    assert lastReverted, "deRegisterKnots must revert if knot is not registered";
}

/**
 * Total ETH received must not decrease.
 */
rule totalEthReceivedMonotonicallyIncreases(method f) filtered {
    f -> notHarnessCall(f)
}{

    uint256 totalEthReceivedBefore = totalETHReceived();

    env e; calldataarg args;
    f(e, args);

    uint256 totalEthReceivedAfter = totalETHReceived();

    assert totalEthReceivedAfter >= totalEthReceivedBefore, "total ether received must not decrease";
}

/**
 * The number of knots registered must not increase unless register function is called.
 */
rule numberOfRegisteredKnotsOnlyIncrementedByRegister(method f) filtered {
    f -> notHarnessCall(f)
}{
    uint256 numberOfRegisteredKnotsBefore = numberOfRegisteredKnots();

    env e; calldataarg args;
    f(e, args);

    uint256 numberOfRegisteredKnotsAfter = numberOfRegisteredKnots();

    assert(numberOfRegisteredKnotsAfter > numberOfRegisteredKnotsBefore => f.selector == registerKnotsToSyndicate(bytes32[]).selector || f.selector == initialize(address, uint256, address[], bytes32[]).selector, "knots registered must not increase unless registered function called");
}

/**
 * Difference in sETH balances (for contract and user) is same as amount staked.
 */
rule sETHBalanceIncreasesAfterStake() {
    address staker; bytes32 blsKey; uint256 sETHAmount; env e;

    require e.msg.sender != currentContract;

    uint256 stakerBalanceBefore = getSETHTokenBalance(blsKey, e.msg.sender);
    uint256 syndicateBalanceBefore = getSETHTokenBalance(blsKey, currentContract);
    stake(e, blsKey, sETHAmount, staker);
    uint256 stakerBalanceAfter = getSETHTokenBalance(blsKey, e.msg.sender);
    uint256 syndicateBalanceAfter = getSETHTokenBalance(blsKey, currentContract);

    assert stakerBalanceBefore - stakerBalanceAfter  == sETHAmount;
    assert syndicateBalanceAfter - syndicateBalanceBefore == sETHAmount;
}

/**
 * Difference in sETH balance for contract is same as amount unstaked.
 *
 * This rule should break for bug1.patch
 */
rule sETHBalanceDecreasesAfterUnstake() {
    address staker; bytes32 blsKey; uint256 sETHAmount; env e;

    uint256 stakerBalanceBefore = getSETHTokenBalance(blsKey, staker);
    uint256 syndicateBalanceBefore = getSETHTokenBalance(blsKey, currentContract);
    unstake(e, staker, staker, blsKey, sETHAmount);
    uint256 stakerBalanceAfter = getSETHTokenBalance(blsKey, staker);
    uint256 syndicateBalanceAfter = getSETHTokenBalance(blsKey, currentContract);

    assert syndicateBalanceBefore - syndicateBalanceAfter  == sETHAmount;
    assert stakerBalanceAfter - stakerBalanceBefore == sETHAmount;
}

/**
 * This rule should break for bug5.patch
 */
rule viewFunctionPreCalculationMatchesActualCalculation() {
    uint256 newAccumulatedETHPerCollateralizedSharePerKnot = calculateNewAccumulatedETHPerCollateralizedSharePerKnot();

    env e;
    updateAccruedETHPerShares(e);

    assert(newAccumulatedETHPerCollateralizedSharePerKnot == accumulatedETHPerCollateralizedSlotPerKnot());
}

/**
 * After a user has staked certain values need to have increased.
 */
rule valuesShouldIncreaseOnStake() {
    address staker; bytes32 blsKey; uint256 sETHAmount; env e;

    uint256 sETHTotalStakeForKnotBefore = sETHTotalStakeForKnot(blsKey);
    uint256 sETHStakedBalanceForKnotBefore = sETHStakedBalanceForKnot(blsKey, staker);
    uint256 totalFreeFloatingSharesBefore = totalFreeFloatingShares();
    uint256 sETHUserClaimForKnotBefore = sETHUserClaimForKnot(blsKey, staker);

    // test
    uint256 unprocessedETHForAllFreeFloatingSlot = getUnprocessedETHForAllFreeFloatingSlot();
    uint256 eTHForFreeFloatingOrCollateralizedHolders = calculateETHForFreeFloatingOrCollateralizedHolders();
    uint256 newAccumulatedETHPerFreeFloatingShare = calculateNewAccumulatedETHPerFreeFloatingShare();

    stake(e, blsKey, sETHAmount, staker);

    uint256 sETHTotalStakeForKnotAfter = sETHTotalStakeForKnot(blsKey);
    uint256 sETHStakedBalanceForKnotAfter = sETHStakedBalanceForKnot(blsKey, staker);
    uint256 totalFreeFloatingSharesAfter = totalFreeFloatingShares();
    uint256 sETHUserClaimForKnotAfter = sETHUserClaimForKnot(blsKey, staker);

    assert sETHAmount > 0 => sETHTotalStakeForKnotAfter - sETHTotalStakeForKnotBefore > 0;
    assert sETHAmount > 0 => sETHStakedBalanceForKnotAfter - sETHStakedBalanceForKnotBefore > 0;
    assert sETHAmount > 0 => totalFreeFloatingSharesAfter - totalFreeFloatingSharesBefore > 0;

    uint256 accumulatedETHPerFreeFloatingShare = accumulatedETHPerFreeFloatingShare();

    assert sETHAmount > 0 && accumulatedETHPerFreeFloatingShare > 10^24 => sETHUserClaimForKnotAfter - sETHUserClaimForKnotBefore > 0;
}

/**
 * After a user has unstaked certain values need to have decreased.
 */
rule valuesShouldDecreaseOnUnstake() {
    bytes32 blsKey; uint256 sETHAmount; env e;

    require e.msg.sender != currentContract;

    uint256 totalEthReceived1 = totalETHReceived();
    uint256 accumulatedETHPerFreeFloatingShare1 = accumulatedETHPerFreeFloatingShare();
    uint256 lastAccumulatedETHPerFreeFloatingShare1 = lastAccumulatedETHPerFreeFloatingShare(blsKey);

    uint256 sETHStakedBalanceForKnot = sETHStakedBalanceForKnot(blsKey, e.msg.sender);
    uint256 sETHUserClaimForKnot = sETHUserClaimForKnot(blsKey, e.msg.sender);

    require sETHUserClaimForKnot == 0;
    require sETHStakedBalanceForKnot == 0;
    require accumulatedETHPerFreeFloatingShare1 > 10^24;
    require lastAccumulatedETHPerFreeFloatingShare1 == 0;

    stake(e, blsKey, sETHAmount, e.msg.sender);

    uint256 sETHTotalStakeForKnotBefore = sETHTotalStakeForKnot(blsKey);
    uint256 sETHStakedBalanceForKnotBefore = sETHStakedBalanceForKnot(blsKey, e.msg.sender);
    uint256 totalFreeFloatingSharesBefore = totalFreeFloatingShares();
    uint256 sETHUserClaimForKnotBefore = sETHUserClaimForKnot(blsKey, e.msg.sender);

    // test
    uint256 unprocessedETHForAllFreeFloatingSlot = getUnprocessedETHForAllFreeFloatingSlot();
    uint256 eTHForFreeFloatingOrCollateralizedHolders = calculateETHForFreeFloatingOrCollateralizedHolders();
    uint256 newAccumulatedETHPerFreeFloatingShare = calculateNewAccumulatedETHPerFreeFloatingShare();
    uint256 totalEthReceived2 = totalETHReceived();
    uint256 accumulatedETHPerFreeFloatingShare2 = accumulatedETHPerFreeFloatingShare();

    unstake(e, e.msg.sender, e.msg.sender, blsKey, sETHAmount);

    uint256 sETHTotalStakeForKnotAfter = sETHTotalStakeForKnot(blsKey);
    uint256 sETHStakedBalanceForKnotAfter = sETHStakedBalanceForKnot(blsKey, e.msg.sender);
    uint256 totalFreeFloatingSharesAfter = totalFreeFloatingShares();
    uint256 sETHUserClaimForKnotAfter = sETHUserClaimForKnot(blsKey, e.msg.sender);
    uint256 totalEthReceived3 = totalETHReceived();
    uint256 accumulatedETHPerFreeFloatingShare3 = accumulatedETHPerFreeFloatingShare();

    assert sETHAmount > 0 => sETHTotalStakeForKnotBefore - sETHTotalStakeForKnotAfter > 0;
    assert sETHAmount > 0 => sETHStakedBalanceForKnotBefore - sETHStakedBalanceForKnotAfter > 0;
    assert sETHAmount > 0 => sETHUserClaimForKnotBefore - sETHUserClaimForKnotAfter > 0;

    bool knotStillPartOfSyndicate = !isNoLongerPartOfSyndicate(blsKey);

    assert sETHAmount > 0 && knotStillPartOfSyndicate => totalFreeFloatingSharesBefore - totalFreeFloatingSharesAfter > 0;
}

/**
 * Address 0 must have zero sETH balance.
 */
invariant addressZeroHasNoBalance()
    sETHToken.balanceOf(0) == 0
