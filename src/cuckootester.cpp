#include <cuckoofilter.h>
#include <util/incbeta.h>
#include <stdlib.h>

static constexpr double CONFIDENCE = 0.9999;
static constexpr double GOAL_MIN = 0.898;
static constexpr double GOAL_MAX = 0.902;
static constexpr double GOAL_MID = (GOAL_MIN + GOAL_MAX) * 0.5;
static constexpr int GOAL_AIM = 2;

namespace {

int Test(RollingCuckooFilter::Params param, uint32_t max_access) {
    param.m_max_kicks = max_access;
    RollingCuckooFilter filt(param, false);
    uint64_t cnt = 0;
    int ret;
    fprintf(stderr, "Testing max_access = %lu ...", (unsigned long)max_access);
    do {
        for (int i = 0; i < 1000; ++i) {
            filt.Insert(Span<const unsigned char>((unsigned char*)&cnt, sizeof(cnt)));
            ++cnt;
        }
        if (filt.counted_gens < 10) continue;
        double alpha = 0.5 + filt.gens_up_to[GOAL_AIM];
        double beta = 0.5 + filt.counted_gens - filt.gens_up_to[GOAL_AIM];
        double ib_mid = incbeta(alpha, beta, GOAL_MID);
        if (ib_mid >= CONFIDENCE) {ret = -1; break;}
        if (1.0 - ib_mid >= CONFIDENCE) {ret = 1; break;}
        double ib_min = incbeta(alpha, beta, GOAL_MIN);
        double ib_max = incbeta(alpha, beta, GOAL_MAX);
        if (ib_max - ib_min >= CONFIDENCE) {ret = 0; break;}
    } while(true);
    fprintf(stderr, "%s (%llu adds, %lu gens, <=0:%f, <=1:%f, <=2:%f, <=4:%f, <=8:%f, <=16:%f)\n", ret == 0 ? "done" : (ret == 1 ? "too high" : "too low"), (unsigned long long)cnt, (unsigned long)filt.counted_gens, (double)filt.gens_up_to[0] / filt.counted_gens, (double)filt.gens_up_to[1] / filt.counted_gens, (double)filt.gens_up_to[2] / filt.counted_gens, (double)filt.gens_up_to[4] / filt.counted_gens, (double)filt.gens_up_to[8] / filt.counted_gens, (double)filt.gens_up_to[16] / filt.counted_gens);
    return ret;
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

    printf("%lu\n", (unsigned long)high);
    return 0;
}
