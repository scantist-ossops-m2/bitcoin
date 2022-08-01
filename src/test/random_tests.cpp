// Copyright (c) 2017-2020 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <random.h>

#include <test/util/setup_common.h>

#include <boost/test/unit_test.hpp>

#include <algorithm>
#include <random>

BOOST_FIXTURE_TEST_SUITE(random_tests, BasicTestingSetup)

BOOST_AUTO_TEST_CASE(osrandom_tests)
{
    BOOST_CHECK(Random_SanityCheck());
}

BOOST_AUTO_TEST_CASE(fastrandom_tests)
{
    // Check that deterministic FastRandomContexts are deterministic
    g_mock_deterministic_tests = true;
    FastRandomContext ctx1(true);
    FastRandomContext ctx2(true);

    for (int i = 10; i > 0; --i) {
        BOOST_CHECK_EQUAL(GetRand<uint64_t>(), uint64_t{10393729187455219830U});
        BOOST_CHECK_EQUAL(GetRand<int>(), int{769702006});
        BOOST_CHECK_EQUAL(GetRandMicros(std::chrono::hours{1}).count(), 2917185654);
        BOOST_CHECK_EQUAL(GetRandMillis(std::chrono::hours{1}).count(), 2144374);
    }
    {
        constexpr SteadySeconds time_point{1s};
        FastRandomContext ctx{true};
        BOOST_CHECK_EQUAL(7, ctx.rand_uniform_delay(time_point, 9s).time_since_epoch().count());
        BOOST_CHECK_EQUAL(-6, ctx.rand_uniform_delay(time_point, -9s).time_since_epoch().count());
        BOOST_CHECK_EQUAL(1, ctx.rand_uniform_delay(time_point, 0s).time_since_epoch().count());
        BOOST_CHECK_EQUAL(1467825113502396065, ctx.rand_uniform_delay(time_point, 9223372036854775807s).time_since_epoch().count());
        BOOST_CHECK_EQUAL(-970181367944767837, ctx.rand_uniform_delay(time_point, -9223372036854775807s).time_since_epoch().count());
        BOOST_CHECK_EQUAL(24761, ctx.rand_uniform_delay(time_point, 9h).time_since_epoch().count());
    }
    BOOST_CHECK_EQUAL(ctx1.rand32(), ctx2.rand32());
    BOOST_CHECK_EQUAL(ctx1.rand32(), ctx2.rand32());
    BOOST_CHECK_EQUAL(ctx1.rand64(), ctx2.rand64());
    BOOST_CHECK_EQUAL(ctx1.randbits(3), ctx2.randbits(3));
    BOOST_CHECK(ctx1.randbytes(17) == ctx2.randbytes(17));
    BOOST_CHECK(ctx1.rand256() == ctx2.rand256());
    BOOST_CHECK_EQUAL(ctx1.randbits(7), ctx2.randbits(7));
    BOOST_CHECK(ctx1.randbytes(128) == ctx2.randbytes(128));
    BOOST_CHECK_EQUAL(ctx1.rand32(), ctx2.rand32());
    BOOST_CHECK_EQUAL(ctx1.randbits(3), ctx2.randbits(3));
    BOOST_CHECK(ctx1.rand256() == ctx2.rand256());
    BOOST_CHECK(ctx1.randbytes(50) == ctx2.randbytes(50));

    // Check that a nondeterministic ones are not
    g_mock_deterministic_tests = false;
    for (int i = 10; i > 0; --i) {
        BOOST_CHECK(GetRand<uint64_t>() != uint64_t{10393729187455219830U});
        BOOST_CHECK(GetRand<int>() != int{769702006});
        BOOST_CHECK(GetRandMicros(std::chrono::hours{1}) != std::chrono::microseconds{2917185654});
        BOOST_CHECK(GetRandMillis(std::chrono::hours{1}) != std::chrono::milliseconds{2144374});
    }
    {
        FastRandomContext ctx3, ctx4;
        BOOST_CHECK(ctx3.rand64() != ctx4.rand64()); // extremely unlikely to be equal
    }
    {
        FastRandomContext ctx3, ctx4;
        BOOST_CHECK(ctx3.rand256() != ctx4.rand256());
    }
    {
        FastRandomContext ctx3, ctx4;
        BOOST_CHECK(ctx3.randbytes(7) != ctx4.randbytes(7));
    }
}

BOOST_AUTO_TEST_CASE(fastrandom_randbits)
{
    FastRandomContext ctx1;
    FastRandomContext ctx2;
    for (int bits = 0; bits < 63; ++bits) {
        for (int j = 0; j < 1000; ++j) {
            uint64_t rangebits = ctx1.randbits(bits);
            BOOST_CHECK_EQUAL(rangebits >> bits, 0U);
            uint64_t range = ((uint64_t)1) << bits | rangebits;
            uint64_t rand = ctx2.randrange(range);
            BOOST_CHECK(rand < range);
        }
    }
}

/** Does-it-compile test for compatibility with standard C++11 RNG interface. */
BOOST_AUTO_TEST_CASE(stdrandom_test)
{
    FastRandomContext ctx;
    std::uniform_int_distribution<int> distribution(3, 9);
    for (int i = 0; i < 100; ++i) {
        int x = distribution(ctx);
        BOOST_CHECK(x >= 3);
        BOOST_CHECK(x <= 9);

        std::vector<int> test{1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
        std::shuffle(test.begin(), test.end(), ctx);
        for (int j = 1; j <= 10; ++j) {
            BOOST_CHECK(std::find(test.begin(), test.end(), j) != test.end());
        }
        Shuffle(test.begin(), test.end(), ctx);
        for (int j = 1; j <= 10; ++j) {
            BOOST_CHECK(std::find(test.begin(), test.end(), j) != test.end());
        }
    }
}

/** Test that Shuffle reaches every permutation with equal probability. */
BOOST_AUTO_TEST_CASE(shuffle_stat_test)
{
    FastRandomContext ctx(true);
    uint32_t counts[5 * 5 * 5 * 5 * 5] = {0};
    for (int i = 0; i < 12000; ++i) {
        int data[5] = {0, 1, 2, 3, 4};
        Shuffle(std::begin(data), std::end(data), ctx);
        int pos = data[0] + data[1] * 5 + data[2] * 25 + data[3] * 125 + data[4] * 625;
        ++counts[pos];
    }
    unsigned int sum = 0;
    double chi_score = 0.0;
    for (int i = 0; i < 5 * 5 * 5 * 5 * 5; ++i) {
        int i1 = i % 5, i2 = (i / 5) % 5, i3 = (i / 25) % 5, i4 = (i / 125) % 5, i5 = i / 625;
        uint32_t count = counts[i];
        if (i1 == i2 || i1 == i3 || i1 == i4 || i1 == i5 || i2 == i3 || i2 == i4 || i2 == i5 || i3 == i4 || i3 == i5 || i4 == i5) {
            BOOST_CHECK(count == 0);
        } else {
            chi_score += ((count - 100.0) * (count - 100.0)) / 100.0;
            BOOST_CHECK(count > 50);
            BOOST_CHECK(count < 150);
            sum += count;
        }
    }
    BOOST_CHECK(chi_score > 58.1411); // 99.9999% confidence interval
    BOOST_CHECK(chi_score < 210.275);
    BOOST_CHECK_EQUAL(sum, 12000U);
}

// Test that if next(a) == b, then next(x) == b for all x in [a,b).
BOOST_AUTO_TEST_CASE(poisson_rand_consistency_test)
{
    for (int i = 0; i < 1000; ++i) {
        PoissonProcessRandom rng{std::chrono::seconds{1 + i}, InsecureRandBits(64), InsecureRandBits(64)};
        for (int j = 0; j < 10; ++j) {
            std::chrono::microseconds now{InsecureRandBits(55)};
            auto next = rng.Next(now);
            BOOST_CHECK(next > now);
            for (int k = 0; k < 10; ++k) {
                auto test = now + std::chrono::microseconds{InsecureRandRange((next - now).count())};
                BOOST_CHECK(next == rng.Next(test));
            }
        }
    }
}

namespace {

constexpr long double EXPDIST_INVCDF[64] = {
    0.0000000000000000000000000000L, 0.01574835696813916860754951146L, 0.03174869831458030115699628275L, 0.04800921918636060775200362532L,
    0.06453852113757117167292391568L, 0.08134563945395240588734235503L, 0.09844007281325251990288857493L, 0.1158318155251217050991200599L,
    0.1335313926245226231463436209L, 0.1515498981272009378406898176L, 0.1698990367953974729004248965L, 0.1885911698075500223589235897L,
    0.2076393647782445016154410443L, 0.2270574506353460848586128740L, 0.2468600779315257978846419408L, 0.2670627852490452462926872419L,
    0.2876820724517809274392190060L, 0.3087354816496132696824420590L, 0.3302416868705768562794077755L, 0.3522205935893520991121429217L,
    0.3746934494414106936069849079L, 0.3976829676661094330305502154L, 0.4212134650763035505855626269L, 0.4453110166553640526366293557L,
    0.4700036292457355536509370311L, 0.4953214372300254290546600503L, 0.5212969236332860870771331754L, 0.5479651707154474121352970577L,
    0.5753641449035618548784380120L, 0.6035350218702581767972806521L, 0.6325225587435104668366259894L, 0.6623755218931916210462039139L,
    0.6931471805599453094172321215L, 0.7248958788745256105742284042L, 0.7576857016975164810901560371L, 0.7915872533731978293201206964L,
    0.8266785731844679325635757424L, 0.8630462173553427823176570180L, 0.9007865453381898110326731657L, 0.9400072584914711073018740623L,
    0.9808292530117262368564511275L, 1.023388867430522165696639897L, 1.067840630001356003024217029L, 1.114360645636248860002794748L,
    1.163150809805680863068169153L, 1.214444104193231396494365297L, 1.268511325463507164295670133L, 1.325669739303455776253858111L,
    1.386294361119890618834464243L, 1.450832882257461790507388159L, 1.519825753744413241980807864L, 1.593933725898135120449905287L,
    1.673976433571671546273683249L, 1.760987810561301312441449151L, 1.856297990365626172485401274L, 1.961658506023452473712902255L,
    2.079441541679835928251696364L, 2.212972934304358551398039985L, 2.367123614131616855690915370L, 2.549445170925571481902633396L,
    2.772588722239781237668928486L, 3.060270794691562165108147492L, 3.465735902799726547086160607L, 4.158883083359671856503392729L
};

template<bool CONSEC, long ITERS>
void PoissonRandStatTest(const std::chrono::seconds avg_interval)
{
    // Construct a random Poisson process with average interval seconds seconds.
    PoissonProcessRandom rng{avg_interval, InsecureRandBits(64), InsecureRandBits(64)};
    // Accumulator s_i is the sum of the i'th powers of the observed durations (in multiples of avg_interval).
    long double sums[8] = {0.0L, 0.0L, 0.0L, 0.0L, 0.0L, 0.0L, 0.0L, 0.0L};
    uint64_t buckets[64] = {0};
    long double bucket_sums[64][8] = {{0.0L}};
    // Start at a random timestamp.
    std::chrono::microseconds now{InsecureRandBits(53)};
    // Generate ITERS events.
    int prev_cdf = -1;
    for (unsigned long j = 0; j < ITERS; ++j) {
        auto next = rng.Next(now);
        // Compute the interval / avg_interval.
        long double val = std::chrono::duration_cast<std::chrono::duration<long double>>(next - now) / avg_interval;
        // Find which CDF bucket it falls into.
        int cdf = std::upper_bound(std::begin(EXPDIST_INVCDF) + 1, std::end(EXPDIST_INVCDF), val) - (std::begin(EXPDIST_INVCDF) + 1);
        long double p1 = (val -  1.0L);
        long double p2 = (val -  3.0L) * p1 - 1.0L;
        long double p3 = (val -  5.0L) * p2 - 4.0L * p1;
        long double p4 = (val -  7.0L) * p3 - 9.0L * p2;
        long double p5 = (val -  9.0L) * p4 - 16.0L * p3;
        long double p6 = (val - 11.0L) * p5 - 25.0L * p4;
        long double p7 = (val - 13.0L) * p6 - 36.0L * p5;
        long double p8 = (val - 15.0L) * p7 - 49.0L * p6;
        sums[0] += p1;
        sums[1] += p2;
        sums[2] += p3;
        sums[3] += p4;
        sums[4] += p5;
        sums[5] += p6;
        sums[6] += p7;
        sums[7] += p8;
        if (prev_cdf != -1) {
            buckets[prev_cdf] += 1;
            bucket_sums[prev_cdf][0] += p1;
            bucket_sums[prev_cdf][1] += p2;
            bucket_sums[prev_cdf][2] += p3;
            bucket_sums[prev_cdf][3] += p4;
            bucket_sums[prev_cdf][4] += p5;
            bucket_sums[prev_cdf][5] += p6;
            bucket_sums[prev_cdf][6] += p7;
            bucket_sums[prev_cdf][7] += p8;
        }
        prev_cdf = cdf;
        now = next;
        if constexpr (!CONSEC) {
            now += std::chrono::microseconds{InsecureRandRange((6 * avg_interval).count())};
        }
        if (std::chrono::microseconds{0x7FFFFFFFFFFFFF} - now < 60 * avg_interval) {
            now = std::chrono::microseconds{InsecureRandBits(54)};
            rng = PoissonProcessRandom{avg_interval, InsecureRandBits(64), InsecureRandBits(64)};
        }
    }
/*
    fprintf(stderr, "s1: %Lg sigma\n", sums[0] / sqrtl(ITERS * 1.0L));
    fprintf(stderr, "s2: %Lg sigma\n", sums[1] / sqrtl(ITERS * 4.0L));
    fprintf(stderr, "s3: %Lg sigma\n", sums[2] / sqrtl(ITERS * 36.0L));
    fprintf(stderr, "s4: %Lg sigma\n", sums[3] / sqrtl(ITERS * 576.0L));
    fprintf(stderr, "s5: %Lg sigma\n", sums[4] / sqrtl(ITERS * 14400.0L));
    fprintf(stderr, "s6: %Lg sigma\n", sums[5] / sqrtl(ITERS * 518400.0L));
    fprintf(stderr, "s7: %Lg sigma\n", sums[6] / sqrtl(ITERS * 25401600.0L));
    fprintf(stderr, "s8: %Lg sigma\n", sums[7] / sqrtl(ITERS * 1625702400.0L));
*/
    BOOST_CHECK(fabsl(sums[0]) < 10.0L * sqrtl(ITERS * 1.0L));
    BOOST_CHECK(fabsl(sums[1]) < 10.0L * sqrtl(ITERS * 4.0L));
    BOOST_CHECK(fabsl(sums[2]) < 10.0L * sqrtl(ITERS * 36.0L));
    BOOST_CHECK(fabsl(sums[3]) < 10.0L * sqrtl(ITERS * 576.0L));
    BOOST_CHECK(fabsl(sums[4]) < 10.0L * sqrtl(ITERS * 14400.0L));
    BOOST_CHECK(fabsl(sums[5]) < 10.0L * sqrtl(ITERS * 518400.0L));
    BOOST_CHECK(fabsl(sums[6]) < 10.0L * sqrtl(ITERS * 25401600.0L));
    BOOST_CHECK(fabsl(sums[7]) < 10.0L * sqrtl(ITERS * 1625702400.0L));

    for (int i = 0; i < 64; ++i) {
        constexpr long double exp = (ITERS - 1) / 64.0L;
        constexpr long double stddev = sqrtl((ITERS - 1) * (63.0L / 4096.0L));
        long double stddiff = (buckets[i] - exp) / stddev;
/*
        fprintf(stderr, "c%i: %Lg sigma\n", i, stddiff);
*/
        BOOST_CHECK(fabsl(stddiff) < 10.0L);
    }

    for (int i = 0; i < 64; ++i) {
/*
        fprintf(stderr, "c%i s1: %Lg sigma\n", i, bucket_sums[i][0] / sqrtl(buckets[i] * 1.0L));
        fprintf(stderr, "c%i s2: %Lg sigma\n", i, bucket_sums[i][1] / sqrtl(buckets[i] * 4.0L));
        fprintf(stderr, "c%i s3: %Lg sigma\n", i, bucket_sums[i][2] / sqrtl(buckets[i] * 36.0L));
        fprintf(stderr, "c%i s4: %Lg sigma\n", i, bucket_sums[i][3] / sqrtl(buckets[i] * 576.0L));
        fprintf(stderr, "c%i s5: %Lg sigma\n", i, bucket_sums[i][4] / sqrtl(buckets[i] * 14400.0L));
        fprintf(stderr, "c%i s6: %Lg sigma\n", i, bucket_sums[i][5] / sqrtl(buckets[i] * 518400.0L));
        fprintf(stderr, "c%i s7: %Lg sigma\n", i, bucket_sums[i][6] / sqrtl(buckets[i] * 25401600.0L));
        fprintf(stderr, "c%i s8: %Lg sigma\n", i, bucket_sums[i][7] / sqrtl(buckets[i] * 1625702400.0L));
*/
        BOOST_CHECK(fabsl(bucket_sums[i][0]) < 10.0 * sqrtl(buckets[i] * 1.0L));
        BOOST_CHECK(fabsl(bucket_sums[i][1]) < 10.0 * sqrtl(buckets[i] * 4.0L));
        BOOST_CHECK(fabsl(bucket_sums[i][2]) < 10.0 * sqrtl(buckets[i] * 36.0L));
        BOOST_CHECK(fabsl(bucket_sums[i][3]) < 10.0 * sqrtl(buckets[i] * 576.0L));
        BOOST_CHECK(fabsl(bucket_sums[i][4]) < 10.0 * sqrtl(buckets[i] * 14400.0L));
        BOOST_CHECK(fabsl(bucket_sums[i][5]) < 10.0 * sqrtl(buckets[i] * 518400.0L));
        BOOST_CHECK(fabsl(bucket_sums[i][6]) < 10.0 * sqrtl(buckets[i] * 25401600.0L));
        BOOST_CHECK(fabsl(bucket_sums[i][7]) < 10.0 * sqrtl(buckets[i] * 1625702400.0L));
        if (fabsl(bucket_sums[i][0]) > 10.0 * sqrtl(buckets[i] * 1.0L) ||
            fabsl(bucket_sums[i][1]) > 10.0 * sqrtl(buckets[i] * 4.0L) ||
            fabsl(bucket_sums[i][2]) > 10.0 * sqrtl(buckets[i] * 36.0L) ||
            fabsl(bucket_sums[i][3]) > 10.0 * sqrtl(buckets[i] * 576.0L) ||
            fabsl(bucket_sums[i][4]) > 10.0 * sqrtl(buckets[i] * 14400.0L) ||
            fabsl(bucket_sums[i][5]) > 10.0 * sqrtl(buckets[i] * 518400.0L) ||
            fabsl(bucket_sums[i][6]) > 10.0 * sqrtl(buckets[i] * 25401600.0L) ||
            fabsl(bucket_sums[i][7]) > 10.0 * sqrtl(buckets[i] * 1625702400.0L)) {
            fprintf(stderr, "c%i: count=%lu s1=%Lg s2=%Lg s3=%Lg s4=%Lg s5=%Lg s6=%Lg s7=%Lg s8=%Lg\n", i, (unsigned long)buckets[i],
                bucket_sums[i][0] / sqrtl(buckets[i] * 1.0L),
                bucket_sums[i][1] / sqrtl(buckets[i] * 4.0L),
                bucket_sums[i][2] / sqrtl(buckets[i] * 36.0L),
                bucket_sums[i][3] / sqrtl(buckets[i] * 576.0L),
                bucket_sums[i][4] / sqrtl(buckets[i] * 14400.0L),
                bucket_sums[i][5] / sqrtl(buckets[i] * 518400.0L),
                bucket_sums[i][6] / sqrtl(buckets[i] * 25401600.0L),
                bucket_sums[i][7] / sqrtl(buckets[i] * 1625702400.0L));
        }
    }

/*
    BOOST_CHECK(fabsl(s1 - ITERS * 1.0L) < 10.0L * sqrtl(ITERS * 1.0L));
    BOOST_CHECK(fabsl(s2 - ITERS * 2.0L) < 10.0L * sqrtl(ITERS * 20.0L));
    BOOST_CHECK(fabsl(s3 - ITERS * 6.0L) < 10.0L * sqrtl(ITERS * 684.0L));
    BOOST_CHECK(fabsl(s4 - ITERS * 24.0L) < 10.0L * sqrtl(ITERS * 39744.0L));
    BOOST_CHECK(fabsl(s5 - ITERS * 120.0L) < 10.0L * sqrtl(ITERS * 3614400.0L));
    BOOST_CHECK(fabsl(s6 - ITERS * 720.0L) < 10.0L * sqrtl(ITERS * 478483200.0L));
*/
}

} // namespace

// Test statistical properties of consecutive Poisson events.
BOOST_AUTO_TEST_CASE(poisson_rand_stat_consec_test)
{
    for (int i = 0; i < 26; ++i) {
        fprintf(stderr, "consec %i\n", i);
        PoissonRandStatTest<true, 10000L>(std::chrono::seconds{1 << i});
    }
}

// Test statistical properties of independent Poisson events.
BOOST_AUTO_TEST_CASE(poisson_rand_stat_sep_test)
{
    for (int i = 0; i < 26; ++i) {
        fprintf(stderr, "sep %i\n", i);
        PoissonRandStatTest<false, 10000L>(std::chrono::seconds{1 << i});
    }
}

BOOST_AUTO_TEST_SUITE_END()
