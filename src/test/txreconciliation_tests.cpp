// Copyright (c) 2021-2022 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <node/txreconciliation.h>

#include <test/util/setup_common.h>

#include <boost/test/unit_test.hpp>

BOOST_FIXTURE_TEST_SUITE(txreconciliation_tests, BasicTestingSetup)

BOOST_AUTO_TEST_CASE(RegisterPeerTest)
{
    TxReconciliationTracker tracker(TXRECONCILIATION_VERSION);
    const uint64_t salt = 0;

    // Prepare a peer for reconciliation.
    tracker.PreRegisterPeer(0);

    // Invalid version.
    BOOST_CHECK_EQUAL(tracker.RegisterPeer(/*peer_id=*/0, /*is_peer_inbound=*/true,
                                           /*peer_recon_version=*/0, salt),
                      ReconciliationRegisterResult::PROTOCOL_VIOLATION);

    // Valid registration (inbound and outbound peers).
    BOOST_REQUIRE(!tracker.IsPeerRegistered(0));
    BOOST_REQUIRE_EQUAL(tracker.RegisterPeer(0, true, 1, salt), ReconciliationRegisterResult::SUCCESS);
    BOOST_CHECK(tracker.IsPeerRegistered(0));
    BOOST_REQUIRE(!tracker.IsPeerRegistered(1));
    tracker.PreRegisterPeer(1);
    BOOST_REQUIRE(tracker.RegisterPeer(1, false, 1, salt) == ReconciliationRegisterResult::SUCCESS);
    BOOST_CHECK(tracker.IsPeerRegistered(1));

    // Reconciliation version is higher than ours, should be able to register.
    BOOST_REQUIRE(!tracker.IsPeerRegistered(2));
    tracker.PreRegisterPeer(2);
    BOOST_REQUIRE(tracker.RegisterPeer(2, true, 2, salt) == ReconciliationRegisterResult::SUCCESS);
    BOOST_CHECK(tracker.IsPeerRegistered(2));

    // Try registering for the second time.
    BOOST_REQUIRE(tracker.RegisterPeer(1, false, 1, salt) == ReconciliationRegisterResult::ALREADY_REGISTERED);

    // Do not register if there were no pre-registration for the peer.
    BOOST_REQUIRE_EQUAL(tracker.RegisterPeer(100, true, 1, salt), ReconciliationRegisterResult::NOT_FOUND);
    BOOST_CHECK(!tracker.IsPeerRegistered(100));
}

BOOST_AUTO_TEST_CASE(ForgetPeerTest)
{
    TxReconciliationTracker tracker(TXRECONCILIATION_VERSION);
    NodeId peer_id0 = 0;

    // Removing peer after pre-registring works and does not let to register the peer.
    tracker.PreRegisterPeer(peer_id0);
    tracker.ForgetPeer(peer_id0);
    BOOST_CHECK_EQUAL(tracker.RegisterPeer(peer_id0, true, 1, 1), ReconciliationRegisterResult::NOT_FOUND);

    // Removing peer after it is registered works.
    tracker.PreRegisterPeer(peer_id0);
    BOOST_REQUIRE(!tracker.IsPeerRegistered(peer_id0));
    BOOST_REQUIRE_EQUAL(tracker.RegisterPeer(peer_id0, true, 1, 1), ReconciliationRegisterResult::SUCCESS);
    BOOST_CHECK(tracker.IsPeerRegistered(peer_id0));
    tracker.ForgetPeer(peer_id0);
    BOOST_CHECK(!tracker.IsPeerRegistered(peer_id0));
}

BOOST_AUTO_TEST_CASE(IsPeerRegisteredTest)
{
    TxReconciliationTracker tracker(TXRECONCILIATION_VERSION);
    NodeId peer_id0 = 0;

    BOOST_REQUIRE(!tracker.IsPeerRegistered(peer_id0));
    tracker.PreRegisterPeer(peer_id0);
    BOOST_REQUIRE(!tracker.IsPeerRegistered(peer_id0));

    BOOST_REQUIRE_EQUAL(tracker.RegisterPeer(peer_id0, true, 1, 1), ReconciliationRegisterResult::SUCCESS);
    BOOST_CHECK(tracker.IsPeerRegistered(peer_id0));

    tracker.ForgetPeer(peer_id0);
    BOOST_CHECK(!tracker.IsPeerRegistered(peer_id0));
}

BOOST_AUTO_TEST_CASE(AddToSetTest)
{
    TxReconciliationTracker tracker(TXRECONCILIATION_VERSION);
    NodeId peer_id0 = 0;
    FastRandomContext frc{/*fDeterministic=*/true};

    Wtxid wtxid{Wtxid::FromUint256(frc.rand256())};

    BOOST_REQUIRE(!tracker.IsPeerRegistered(peer_id0));
    BOOST_REQUIRE(!tracker.AddToSet(peer_id0, wtxid));

    tracker.PreRegisterPeer(peer_id0);
    BOOST_REQUIRE_EQUAL(tracker.RegisterPeer(peer_id0, true, 1, 1), ReconciliationRegisterResult::SUCCESS);
    BOOST_CHECK(tracker.IsPeerRegistered(peer_id0));

    BOOST_REQUIRE(tracker.AddToSet(peer_id0, wtxid));

    tracker.ForgetPeer(peer_id0);
    Wtxid wtxid2{Wtxid::FromUint256(frc.rand256())};
    BOOST_REQUIRE(!tracker.AddToSet(peer_id0, wtxid2));

    NodeId peer_id1 = 1;
    tracker.PreRegisterPeer(peer_id1);
    BOOST_REQUIRE_EQUAL(tracker.RegisterPeer(peer_id1, true, 1, 1), ReconciliationRegisterResult::SUCCESS);
    BOOST_CHECK(tracker.IsPeerRegistered(peer_id1));

    for (size_t i = 0; i < 3000; ++i)
        BOOST_REQUIRE(tracker.AddToSet(peer_id1, Wtxid::FromUint256(frc.rand256())));
    BOOST_REQUIRE(!tracker.AddToSet(peer_id1, Wtxid::FromUint256(frc.rand256())));
}

BOOST_AUTO_TEST_CASE(TryRemovingFromSetTest)
{
    TxReconciliationTracker tracker(TXRECONCILIATION_VERSION);
    NodeId peer_id0 = 0;
    FastRandomContext frc{/*fDeterministic=*/true};

    Wtxid wtxid{Wtxid::FromUint256(frc.rand256())};

    BOOST_REQUIRE(!tracker.IsPeerRegistered(peer_id0));
    BOOST_REQUIRE(!tracker.TryRemovingFromSet(peer_id0, wtxid));

    tracker.PreRegisterPeer(peer_id0);
    BOOST_REQUIRE_EQUAL(tracker.RegisterPeer(peer_id0, true, 1, 1), ReconciliationRegisterResult::SUCCESS);
    BOOST_CHECK(tracker.IsPeerRegistered(peer_id0));

    BOOST_REQUIRE(!tracker.TryRemovingFromSet(peer_id0, wtxid));
    BOOST_REQUIRE(tracker.AddToSet(peer_id0, wtxid));
    BOOST_REQUIRE(tracker.TryRemovingFromSet(peer_id0, wtxid));
    BOOST_REQUIRE(!tracker.TryRemovingFromSet(peer_id0, wtxid));

    BOOST_REQUIRE(tracker.AddToSet(peer_id0, wtxid));
    tracker.ForgetPeer(peer_id0);
    BOOST_REQUIRE(!tracker.TryRemovingFromSet(peer_id0, wtxid));
}

BOOST_AUTO_TEST_CASE(ShouldFanoutToTest)
{
    TxReconciliationTracker tracker(1);
    NodeId peer_id0 = 0;
    CSipHasher hasher(0x0706050403020100ULL, 0x0F0E0D0C0B0A0908ULL);
    FastRandomContext frc{/*fDeterministic=*/true};

    // If peer is not registered for reconciliation, it should be always chosen for flooding.
    BOOST_REQUIRE(!tracker.IsPeerRegistered(peer_id0));
    for (int i = 0; i < 100; ++i) {
        BOOST_CHECK(tracker.ShouldFanoutTo(Wtxid::FromUint256(frc.rand256()), CSipHasher(hasher), peer_id0,
                                           /*inbounds_nonrcncl_tx_relay=*/0, /*outbounds_nonrcncl_tx_relay=*/0));
    }

    tracker.PreRegisterPeer(peer_id0);
    BOOST_REQUIRE(!tracker.IsPeerRegistered(peer_id0));
    // Same after pre-registering.
    for (int i = 0; i < 100; ++i) {
        BOOST_CHECK(tracker.ShouldFanoutTo(Wtxid::FromUint256(frc.rand256()), CSipHasher(hasher), peer_id0,
                                           /*inbounds_nonrcncl_tx_relay=*/0, /*outbounds_nonrcncl_tx_relay=*/0));
    }

    // Once the peer is registered, it should be selected for flooding of some transactions.
    // Since there is only one reconciling peer, it will be selected for all transactions.
    BOOST_REQUIRE_EQUAL(tracker.RegisterPeer(peer_id0, /*is_peer_inbound=*/false, 1, 1), ReconciliationRegisterResult::SUCCESS);
    for (int i = 0; i < 100; ++i) {
        BOOST_CHECK(tracker.ShouldFanoutTo(Wtxid::FromUint256(frc.rand256()), CSipHasher(hasher), peer_id0,
                                           /*inbounds_nonrcncl_tx_relay=*/0, /*outbounds_nonrcncl_tx_relay=*/0));
    }

    // Don't select a fanout target if it was already fanouted sufficiently.
    for (int i = 0; i < 100; ++i) {
        BOOST_CHECK(!tracker.ShouldFanoutTo(Wtxid::FromUint256(frc.rand256()), CSipHasher(hasher), peer_id0,
                                            /*inbounds_nonrcncl_tx_relay=*/0, /*outbounds_nonrcncl_tx_relay=*/1));
    }

    tracker.ForgetPeer(peer_id0);
    // A forgotten (reconciliation-wise) peer should be always selected for fanout again.
    for (int i = 0; i < 100; ++i) {
        BOOST_CHECK(tracker.ShouldFanoutTo(Wtxid::FromUint256(frc.rand256()), CSipHasher(hasher), peer_id0,
                                           /*inbounds_nonrcncl_tx_relay=*/0, /*outbounds_nonrcncl_tx_relay=*/0));
    }

    // Now for inbound connections.
    for (int i = 1; i < 31; ++i) {
        tracker.PreRegisterPeer(i);
        BOOST_REQUIRE_EQUAL(tracker.RegisterPeer(i, /*is_peer_inbound=*/true, 1, 1), ReconciliationRegisterResult::SUCCESS);
    }

    // Relay to a fraction of registered inbound peers.
    for (int j = 0; j < 100; ++j) {
        size_t total_fanouted = 0;
        auto wtxid = Wtxid::FromUint256(frc.rand256());
        for (int i = 1; i < 31; ++i) {
            total_fanouted += tracker.ShouldFanoutTo(wtxid, CSipHasher(hasher), i,
                                                     /*inbounds_nonrcncl_tx_relay=*/0, /*outbounds_nonrcncl_tx_relay=*/0);
        }
        BOOST_CHECK_EQUAL(total_fanouted, 3);
    }

    // Don't relay if there is sufficient non-reconciling peers
    for (int j = 0; j < 100; ++j) {
        size_t total_fanouted = 0;
        for (int i = 1; i < 31; ++i) {
            total_fanouted += tracker.ShouldFanoutTo(Wtxid::FromUint256(frc.rand256()), CSipHasher(hasher), i,
                                                     /*inbounds_nonrcncl_tx_relay=*/4, /*outbounds_nonrcncl_tx_relay=*/0);
        }
        BOOST_CHECK_EQUAL(total_fanouted, 0);
    }
}

BOOST_AUTO_TEST_SUITE_END()
