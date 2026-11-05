// simdjson DOM parse throughput on one file (MB/s, median of five 0.6 s windows). Built outside the sandbox by build.sh.
#include <simdjson.h>
#include <chrono>
#include <cstdio>
#include <algorithm>
int main(int, char **v) {
  simdjson::padded_string s; if (simdjson::padded_string::load(v[1]).get(s)) return 2;
  simdjson::dom::parser p; double r[5];
  for (int w = 0; w < 5; w++) { long it = 0; auto a = std::chrono::steady_clock::now(); double e;
    do { simdjson::dom::element d; if (p.parse(s).get(d)) return 3; it++; e = std::chrono::duration<double>(std::chrono::steady_clock::now() - a).count(); } while (e < 0.6);
    r[w] = it * (double)s.size() / 1e6 / e; }
  std::sort(r, r + 5); std::printf("%.1f\n", r[2]); }
