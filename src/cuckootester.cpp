#include <cuckoofilter.h>
#include <stdlib.h>
#include <thread>
#include <atomic>
#include <mutex>
#include <optional>
#include <boost/math/special_functions/beta.hpp>

static constexpr double CONFIDENCE_SIDE = 0.999;
static constexpr double CONFIDENCE_MID = 0.999999;
static constexpr double GOAL_LOW = 0.8995;
static constexpr double GOAL_HIGH = 0.9005;
static constexpr double GOAL_MID = 0.9;
static constexpr int GOAL_AIM = 2;
static constexpr int THREADS = 30;

namespace {

int Test(RollingCuckooFilter::Params param, uint64_t max_access_q32) {
    param.m_max_access_q32 = max_access_q32;

    fprintf(stderr, "Testing max_access = %.10f ...", max_access_q32 * 0.00000000023283064365386962890625);
    std::vector<std::thread> threads;
    threads.reserve(THREADS);
    std::mutex mutex;
    uint64_t total_gens = 0;
    uint64_t good_gens = 0;
    std::optional<int> res;
    std::atomic<bool> done{false};

    for (int t = 0; t < THREADS; ++t) {
        threads.emplace_back([&](){
            RollingCuckooFilter filt(param, false);
            uint64_t cnt = 0;
            unsigned loops = (param.m_gen_size + 99) / 100;
            while (true) {
                uint64_t old_thread_total = filt.counted_gens;
                uint64_t old_thread_good = filt.gens_up_to[GOAL_AIM];
                for (unsigned i = 0; i < loops; ++i) {
                    for (unsigned j = 0; j < 100; ++j) {
                        filt.Insert(Span<const unsigned char>((unsigned char*)&cnt, sizeof(cnt)));
                        ++cnt;
                    }
                    if (done.load(std::memory_order_relaxed)) return;
                }
                uint64_t added_thread_total = filt.counted_gens - old_thread_total;
                uint64_t added_thread_good = filt.gens_up_to[GOAL_AIM] - old_thread_good;
                uint64_t thread_total_gens, thread_good_gens;
                {
                    std::unique_lock<std::mutex> lock(mutex);
                    if (res.has_value()) return;
                    total_gens += added_thread_total;
                    good_gens += added_thread_good;
                    thread_total_gens = total_gens;
                    thread_good_gens = good_gens;
                }
                if (total_gens > 30) {
                    double alpha = 0.5 + thread_good_gens;
                    double beta = 0.5 + (thread_total_gens - thread_good_gens);
                    double ib_mid = boost::math::ibeta(alpha, beta, GOAL_MID);
                    if (ib_mid >= CONFIDENCE_SIDE) { std::unique_lock<std::mutex> lock(mutex); res = -1; done.store(true); return; }
                    if (1.0 - ib_mid >= CONFIDENCE_SIDE) { std::unique_lock<std::mutex> lock(mutex); res = 1; done.store(true); return; }
                    double ib_min = boost::math::ibeta(alpha, beta, GOAL_LOW);
                    double ib_max = boost::math::ibeta(alpha, beta, GOAL_HIGH);
                    if (ib_max - ib_min >= CONFIDENCE_MID) { std::unique_lock<std::mutex> lock(mutex); res = 0; done.store(true); return; }
                }
            }
        });
    }
    for (auto& thread : threads) thread.join();
    assert(res.has_value());
    fprintf(stderr, "%s (%lu/%lu gens = %f)\n",
            res.value() == 0 ? "center" : (res.value() == 1 ? "too high" : "too low"),
            (unsigned long)good_gens,
            (unsigned long)total_gens,
            (double)good_gens / total_gens);
    return res.value();
}

}

int main(int argc, char** argv) {
    if (argc < 5) {
        fprintf(stderr, "Usage: %s [gen_size] [gen_cbits] [fp_bits] [alpha]\n", argv[0]);
        return 1;
    }
    uint32_t gen_size = strtoul(argv[1], nullptr, 0);
    unsigned gen_cbits = strtoul(argv[2], nullptr, 0);
    unsigned fpbits = strtoul(argv[3], nullptr, 0);
    double alpha = strtod(argv[4], nullptr);

    RollingCuckooFilter::Params param(gen_size, gen_cbits, fpbits, alpha, 0);
    fprintf(stderr, "# buckets=%lu gens=%lu gen_size=%lu gen_bits=%lu fpr_bits=%lu table_bits=%llu reqalpha=%f alpha=%f\n", (unsigned long)param.m_buckets, (unsigned long)param.Generations(), (unsigned long)param.m_gen_size, (unsigned long)param.m_gen_cbits, (unsigned long)param.m_fpr_bits, (unsigned long long)param.TableBits(), alpha, param.Alpha());

    uint64_t low = 0x100000000;
    uint64_t high = 0x200000000;
    do {
        int res = Test(param, high);
        if (res == 0) {
            low = high-1;
            high = high;
            break;
        } else if (res == 1) {
            break;
        } else {
            low = high;
            high *= 2;
        }
    } while(1);

    while (high > low + (0xFFFFFFFF >> 2)) {
        uint64_t mid = (low + high) >> 1;
        uint64_t dif = (high - low);
        int res = Test(param, mid);
        if (res == 0) {
            break;
        } else if (res == 1) {
            high -= (dif >> 2);
        } else {
            low += (dif >> 2);
        }
    }

    uint64_t result = (high + low) >> 1;

    printf("# buckets=%lu gens=%lu gen_size=%lu gen_bits=%lu fpr_bits=%lu table_bits=%llu reqalpha=%f alpha=%f result=%.10f\n", (unsigned long)param.m_buckets, (unsigned long)param.Generations(), (unsigned long)param.m_gen_size, (unsigned long)param.m_gen_cbits, (unsigned long)param.m_fpr_bits, (unsigned long long)param.TableBits(), alpha, param.Alpha(), result * 0.00000000023283064365386962890625);
    return 0;
}
