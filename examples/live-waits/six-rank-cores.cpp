// Copyright (c) 2026 Luna Luteus. Released under Apache 2.0.
// Finite diagnostic for orders one and two. No kernel proof is claimed.
#include <array>
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <map>
#include <numeric>
#include <set>
#include <stdexcept>
#include <vector>
#include <unordered_map>

using Count = std::int64_t;

Count choose(int n, int k) {
  if (k < 0 || n < k) return 0;
  k = std::min(k, n - k);
  Count result = 1;
  for (int j = 1; j <= k; ++j) result = result * (n - k + j) / j;
  return result;
}

template <int D> struct Checker {
  using Hand = std::array<int, D>;
  static constexpr int residues = [] {
    int x = 1;
    for (int i = 0; i < D; ++i) x *= 3;
    return x;
  }();
  std::array<std::vector<Hand>, residues> templates;
  Count comparisons = 0;
  std::unordered_map<std::uint64_t, bool> meld_memo;

  static int key(const Hand& c) {
    int result = 0, power = 1;
    for (int x : c) {
      result += (x % 3) * power;
      power *= 3;
    }
    return result;
  }

  // Enumerate pair positions and normalized sequence counts independently
  // of the left-to-right scan. Three identical sequences can be replaced
  // by one triplet at each of their three ranks, so counts 0,1,2 suffice.
  Checker() {
    int sequences = 1;
    for (int i = 0; i < D - 2; ++i) sequences *= 3;
    std::array<std::set<Hand>, residues> unique;
    for (int code = 0; code < sequences; ++code) {
      Hand melds{};
      int rest = code;
      for (int i = 0; i < D - 2; ++i) {
        int x = rest % 3; rest /= 3;
        for (int j = 0; j < 3; ++j) melds[i+j] += x;
      }
      for (int p = 0; p < D; ++p) {
        Hand c = melds; c[p] += 2;
        unique[key(c)].insert(c);
      }
    }
    for (int i = 0; i < residues; ++i)
      templates[i] = std::vector<Hand>(unique[i].begin(), unique[i].end());
  }

  static bool meldable_scan(Hand c) {
    for (int i = 0; i < D - 2; ++i) {
      int starts = c[i] % 3;
      c[i+1] -= starts;
      c[i+2] -= starts;
      if (c[i+1] < 0 || c[i+2] < 0) return false;
    }
    return c[D-2] % 3 == 0 && c[D-1] % 3 == 0;
  }

  static bool winning_scan(const Hand& c) {
    for (int p = 0; p < D; ++p) if (c[p] >= 2) {
      Hand rest = c;
      rest[p] -= 2;
      if (meldable_scan(rest)) return true;
    }
    return false;
  }

  bool winning_templates(const Hand& c) const {
    for (const Hand& base : templates[key(c)]) {
      bool fits = true;
      for (int i = 0; i < D; ++i) fits = fits && base[i] <= c[i];
      if (fits) return true;
    }
    return false;
  }

  // A literal exhaustive recursion uses the lowest remaining tile in either
  // a triplet or a sequence. It does not use sequence normalization.
  bool meldable_recursive(Hand c) {
    std::uint64_t encoded = 0;
    int first = D;
    for (int i = 0; i < D; ++i) {
      if (c[i] < 0 || c[i] >= 32) throw std::runtime_error("recursive key range exceeded");
      encoded = (encoded << 5) | static_cast<std::uint64_t>(c[i]);
      if (first == D && c[i]) first = i;
    }
    if (first == D) return true;
    auto known = meld_memo.find(encoded);
    if (known != meld_memo.end()) return known->second;
    bool result = false;
    if (c[first] >= 3) {
      Hand next = c;
      next[first] -= 3;
      result = meldable_recursive(next);
    }
    if (!result && first+2 < D && c[first+1] && c[first+2]) {
      Hand next = c;
      for (int j = 0; j < 3; ++j) --next[first+j];
      result = meldable_recursive(next);
    }
    meld_memo.emplace(encoded, result);
    return result;
  }

  bool winning_recursive(const Hand& c) {
    for (int p = 0; p < D; ++p) if (c[p] >= 2) {
      Hand rest = c;
      rest[p] -= 2;
      if (meldable_recursive(rest)) return true;
    }
    return false;
  }

  bool full(const Hand& c) {
    if (std::accumulate(c.begin(), c.end(), 0) % 3 != 1) return false;
    bool result = true;
    for (int draw = 0; draw < D; ++draw) {
      Hand next = c;
      ++next[draw];
      bool scan = winning_scan(next), table = winning_templates(next);
      bool recursive = winning_recursive(next);
      ++comparisons;
      if (scan != table || scan != recursive)
        throw std::runtime_error("winning algorithms disagree");
      result = result && scan;
    }
    return result;
  }
};

template <int D> void experiment() {
  Checker<D> check;
  using Hand = typename Checker<D>::Hand;
  std::map<std::pair<int,int>, Count> histogram;
  int candidates = 1;
  for (int i = 0; i < D; ++i) candidates *= 9;
  Count congruent = 0, cores = 0;
  for (int code = 0; code < candidates; ++code) {
    Hand c{};
    int rest = code;
    for (int& x : c) { x = rest % 9; rest /= 9; }
    int size = std::accumulate(c.begin(), c.end(), 0);
    if (size % 3 != 1) continue;
    ++congruent;
    if (!check.full(c)) continue;
    ++cores;
    int active = 0;
    for (int x : c) active += x >= 6;
    ++histogram[{(size-1)/3, active}];
  }
  Count core_comparisons = check.comparisons;
  std::vector<Count> numerator(9*D, 0);
  for (const auto& [cell,count] : histogram) {
    const auto& [grade,active] = cell;
    for (int j = 0; j <= D-active; ++j)
      numerator[grade+j] += count * (j%2 ? -1 : 1) * choose(D-active,j);
  }
  while (!numerator.empty() && numerator.back()==0) numerator.pop_back();
  int degree = static_cast<int>(numerator.size())-1;
  if (degree > 8*(D/3)-1) throw std::runtime_error("numerator degree bound failed");
  Count dense = 0;
  for (const auto& [cell,count] : histogram) if (cell.second==D) dense += count;
  int expected_dense = 1;
  for (int i = 0; i < D-1; ++i) expected_dense *= 3;
  if (dense != expected_dense) throw std::runtime_error("dense core count failed");
  if (std::accumulate(numerator.begin(), numerator.end(), Count{0}) != dense)
    throw std::runtime_error("numerator at one failed");

  auto core_count = [&](int m) {
    Count result = 0;
    for (const auto& [cell,count] : histogram) {
      const auto& [grade,active] = cell;
      int tails = m-grade;
      if (tails >= 0) result += count * (active ? choose(tails+active-1,active-1) : (tails==0));
    }
    return result;
  };
  std::vector<Count> counts;
  for (int m = 0; m <= 40; ++m) {
    Count value = core_count(m), convolution = 0;
    for (int j = 0; j <= degree && j <= m; ++j)
      convolution += numerator[j] * choose(m-j+D-1,D-1);
    if (value != convolution) throw std::runtime_error("series coefficient mismatch");
    if constexpr (D==3)
      if (value != (m ? choose(3*m-2,2) : 0)) throw std::runtime_error("order one formula failed");
    counts.push_back(value);
  }

  // Directly enumerate the entire uncapped fixed-size sample spaces too.
  // Values above eight are included here, independently checking the tails.
  std::vector<Count> direct;
  for (int m = 0; m <= 8; ++m) {
    Hand c{}; Count total = 0, full = 0;
    auto visit = [&](auto&& self, int i, int remaining) -> void {
      if (i==D-1) {
        c[i] = remaining; ++total;
        full += check.full(c);
        return;
      }
      for (int x = 0; x <= remaining; ++x) { c[i]=x; self(self,i+1,remaining-x); }
    };
    visit(visit,0,3*m+1);
    if (total != choose(3*m+D,D-1)) throw std::runtime_error("sample size mismatch");
    if (full != core_count(m)) throw std::runtime_error("direct count mismatch");
    direct.push_back(full);
  }
  std::cout << "{\"order\":" << D/3 << ",\"ranks\":" << D
            << ",\"core_candidates\":" << candidates << ",\"congruent_candidates\":" << congruent
            << ",\"full_cores\":" << cores << ",\"dense_cores\":" << dense
            << ",\"core_draw_cross_checks\":" << core_comparisons
            << ",\"total_draw_cross_checks\":" << check.comparisons
            << ",\"recursive_memo_states\":" << check.meld_memo.size()
            << ",\"numerator_degree\":" << degree << ",\"numerator\":[";
  for (int j=0;j<=degree;++j) { if(j)std::cout<<',';std::cout<<numerator[j]; }
  std::cout << "],\"histogram\":[";
  bool comma=false;
  for (const auto& [cell,count] : histogram) {
    if (comma) std::cout << ',';
    comma = true;
    std::cout<<"{\"grade\":"<<cell.first<<",\"active\":"<<cell.second<<",\"count\":"<<count<<'}';
  }
  std::cout << "],\"counts_m_0_to_40\":[";
  for(int m=0;m<=40;++m){if(m)std::cout<<',';std::cout<<counts[m];}
  std::cout << "],\"direct_counts_m_0_to_8\":[";
  for(int m=0;m<=8;++m){if(m)std::cout<<',';std::cout<<direct[m];}
  std::cout << "]}";
}

int main() {
  std::cout << "{\"scope\":\"Finite diagnostic, not a Lean evaluation of core cardinalities\",\"orders\":[";
  experiment<3>();
  std::cout << ',';
  experiment<6>();
  std::cout << "]}\n";
}
