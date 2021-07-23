#include <cuckoofilter.h>
#include <util/incbeta.h>
#include <stdlib.h>
#include <thread>
#include <atomic>
#include <mutex>
#include <optional>

static constexpr double CONFIDENCE = 0.9999;
static constexpr double GOAL_MIN = 0.899;
static constexpr double GOAL_MAX = 0.901;
static constexpr double GOAL_MID = (GOAL_MIN + GOAL_MAX) * 0.5;
static constexpr int GOAL_AIM = 2;
static constexpr int THREADS = 30;

namespace {

int Test(RollingCuckooFilter::Params param, uint32_t max_access) {
    param.m_max_kicks = max_access;

    fprintf(stderr, "Testing max_access = %lu ...", (unsigned long)max_access);
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
                    double ib_mid = incbeta(alpha, beta, GOAL_MID);
                    if (ib_mid >= CONFIDENCE) { std::unique_lock<std::mutex> lock(mutex); res = -1; done.store(true); return; }
                    if (1.0 - ib_mid >= CONFIDENCE) { std::unique_lock<std::mutex> lock(mutex); res = 1; done.store(true); return; }
                    double ib_min = incbeta(alpha, beta, GOAL_MIN);
                    double ib_max = incbeta(alpha, beta, GOAL_MAX);
                    if (ib_max - ib_min >= CONFIDENCE) { std::unique_lock<std::mutex> lock(mutex); res = 0; done.store(true); return; }
                }
            }
        });
    }
    for (auto& thread : threads) thread.join();
    assert(res.has_value());
    fprintf(stderr, "%s (%lu/%lu gens)\n",
            res.value() == 0 ? "done" : (res.value() == 1 ? "too high" : "too low"),
            (unsigned long)good_gens,
            (unsigned long)total_gens);
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
    fprintf(stderr, "# buckets=%lu gens=%lu gen_size=%lu gen_bits=%lu fpr_bits=%lu table_bits=%llu alpha=%f\n", (unsigned long)param.m_buckets, (unsigned long)param.Generations(), (unsigned long)param.m_gen_size, (unsigned long)param.m_gen_cbits, (unsigned long)param.m_fpr_bits, (unsigned long long)param.TableBits(), param.Alpha());

    uint32_t low = 0;
    uint32_t high = 1;
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

    while (high > low + 1) {
        uint32_t mid = (low + high) >> 1;
        int res = Test(param, mid);
        if (res == 0) {
            low = mid-1;
            high = mid;
        } else if (res == 1) {
            high = mid;
        } else {
            low = mid;
        }
    }

    printf("alpha=%f cbits=%u fpbits=%u gensize=%lu: maxiter=%lu effalpha=%f gens=%u buckets=%lu fprbits=%u tablebits=%llu\n", alpha, gen_cbits, fpbits, (unsigned long)gen_size, (unsigned long)high, param.Alpha(), (unsigned)param.Generations(), (unsigned long)param.m_buckets, (unsigned)param.m_fpr_bits, (unsigned long long)param.TableBits());
    return 0;
}
