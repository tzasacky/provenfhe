// pin_prng.cpp -- UNTRUSTED. A deterministic, scriptable PRNG engine for OpenFHE's external-PRNG
// hook (PseudoRandomNumberGenerator::InitPRNGEngine(libPath), distributiongenerator.cpp:59-90 in v1.6.1:
// the library dlopen()s a shared object and calls its C function `createEngineInstance`).
// NOT a cryptographic generator: it exists so that a test harness can (a) reproduce a run,
// (b) rewind the stream and re-draw the values a library call consumed (to export encryption
// randomness without patching OpenFHE), and (c) script the exact 32-bit words the samplers see
// (the forced-witness experiment).
//
// All engine instances share one global stream (OpenFHE built WITH_OPENMP keeps one static
// engine; run with OMP_NUM_THREADS=1 so that the order of draws is deterministic).
//
// Stream: if the script queue is non-empty, the next scripted word; otherwise the next output of
// splitmix64 (upper 32 bits) from the 64-bit state.
//
// C API (declare these `extern "C"` in the program and link against this library, or dlsym them):
//   void     pin_prng_seed(uint64_t seed);        // set the state, clear the script, zero the counter
//   uint64_t pin_prng_get_state(void);            // snapshot (valid only while the script is empty)
//   void     pin_prng_set_state(uint64_t state);  // rewind to a snapshot (clears the script)
//   void     pin_prng_script_push(const uint32_t* words, size_t n);  // append scripted words
//   size_t   pin_prng_script_remaining(void);
//   uint64_t pin_prng_calls(void);                // words drawn since the last seed
#include "utils/prng/prng.h"

#include <cstddef>
#include <cstdint>
#include <deque>
#include <mutex>

namespace {
std::mutex g_mu;
uint64_t g_state = 0x9E3779B97F4A7C15ULL;
uint64_t g_calls = 0;
std::deque<uint32_t> g_script;

uint32_t next_word() {
    std::lock_guard<std::mutex> lk(g_mu);
    g_calls++;
    if (!g_script.empty()) {
        uint32_t w = g_script.front();
        g_script.pop_front();
        return w;
    }
    uint64_t z = (g_state += 0x9E3779B97F4A7C15ULL);
    z          = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z          = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    z          = z ^ (z >> 31);
    return static_cast<uint32_t>(z >> 32);
}

class PinEngine : public PRNG {
public:
    result_type operator()() override {
        return next_word();
    }
};
}  // namespace

extern "C" {
PRNG* createEngineInstance() {
    return new PinEngine();
}
void pin_prng_seed(uint64_t seed) {
    std::lock_guard<std::mutex> lk(g_mu);
    g_state = seed;
    g_calls = 0;
    g_script.clear();
}
uint64_t pin_prng_get_state(void) {
    std::lock_guard<std::mutex> lk(g_mu);
    return g_state;
}
void pin_prng_set_state(uint64_t state) {
    std::lock_guard<std::mutex> lk(g_mu);
    g_state = state;
    g_script.clear();
}
void pin_prng_script_push(const uint32_t* words, size_t n) {
    std::lock_guard<std::mutex> lk(g_mu);
    for (size_t i = 0; i < n; i++)
        g_script.push_back(words[i]);
}
size_t pin_prng_script_remaining(void) {
    std::lock_guard<std::mutex> lk(g_mu);
    return g_script.size();
}
uint64_t pin_prng_calls(void) {
    std::lock_guard<std::mutex> lk(g_mu);
    return g_calls;
}
}
