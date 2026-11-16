/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
import Ninegates

/- An exploratory consequence of the structural library, outside the review branch.
   With four physical copies per rank, every live draw requires c_i <= 3.
   The resulting meld-count bound m < 3n is sharp for every positive order. -/

open Mahjong Mahjong.VirtualHand

namespace Mahjong.VirtualHand

lemma IsLiveFullWait.meldCount_lt_copyCapacity {n cap m : ℕ} {c : VirtualHand n}
    (live : IsLiveFullWait cap m c) : m < n * (cap - 1) := by
  have bounded : Bounded (cap - 1) c := by
    refine ⟨live.1.1, fun i ↦ ?_⟩
    have upper := (isLiveFullWait_iff.mp live).2 i
    have lower := live.1.1 i
    omega
  have upper := bounded.size_le
  have shape : 3 * (n : ℤ) * ((cap - 1 : ℕ) : ℤ) =
      3 * ((n * (cap - 1) : ℕ) : ℤ) := by push_cast; ring
  rw [shape, live.1.2.1] at upper
  have strict : (m : ℤ) < ((n * (cap - 1) : ℕ) : ℤ) := by omega
  exact_mod_cast strict

namespace LiveMaximum

def hand (n : ℕ) : VirtualHand n :=
  Standard.A n + (2 : ℤ) • segment 1 (3 * n - 2)

lemma hand_full {n : ℕ} (positive : 0 < n) : IsFullWait (3 * n - 1) (hand n) := by
  have sequential : Sequential (segment (n := n) 1 (3 * n - 2)) :=
    sequential_segment (by omega) (by omega) (by omega)
  have count : size ((2 : ℤ) • segment (n := n) 1 (3 * n - 2)) =
      3 * ((2 * (n - 1) : ℕ) : ℤ) := by
    rw [map_smul, size_segment (by omega)]
    simp only [smul_eq_mul]
    push_cast
    omega
  have full := (Standard.A_full_positive positive).add_meldable
    (sequential.smul (show (0 : ℤ) ≤ 2 by norm_num)).meldable count
  have index : n + 1 + 2 * (n - 1) = 3 * n - 1 := by omega
  rw [index] at full
  exact full

lemma hand_live {n : ℕ} (positive : 0 < n) : IsLiveFullWait 4 (3 * n - 1) (hand n) := by
  apply isLiveFullWait_iff.mpr
  refine ⟨hand_full positive, fun i ↦ ?_⟩
  have bound := i.isLt
  simp only [hand, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Standard.A_apply, segment_apply]
  split_ifs <;> omega

lemma hand_apply {n : ℕ} (positive : 0 < n) (i : Rank n) :
    hand n i = if i.val = 3 * n - 2 then 1 else 3 := by
  have bound := i.isLt
  simp only [hand, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Standard.A_apply, segment_apply]
  split_ifs <;> omega

lemma upper {n m : ℕ} :
    (∃ c : VirtualHand n, IsLiveFullWait 4 m c) → m ≤ 3 * n - 1 := by
  rintro ⟨c, live⟩
  have upper := live.meldCount_lt_copyCapacity
  norm_num only at upper
  omega

/-- Add one layer of sequences over each of two initial interior intervals. -/
def layered (n a b : ℕ) : VirtualHand n :=
  Standard.A n + segment 1 (3 * a + 1) + segment 1 (3 * b + 1)

lemma layered_live {n a b : ℕ} (positive : 0 < n)
    (bound_a : a ≤ n - 1) (bound_b : b ≤ n - 1) :
    IsLiveFullWait 4 (n + 1 + a + b) (layered n a b) := by
  have sequence_a : Sequential (segment (n := n) 1 (3 * a + 1)) :=
    sequential_segment (by omega) (by omega) (by omega)
  have sequence_b : Sequential (segment (n := n) 1 (3 * b + 1)) :=
    sequential_segment (by omega) (by omega) (by omega)
  have count_a : size (segment (n := n) 1 (3 * a + 1)) = 3 * (a : ℤ) := by
    rw [size_segment (by omega)]
    push_cast
    omega
  have count_b : size (segment (n := n) 1 (3 * b + 1)) = 3 * (b : ℤ) := by
    rw [size_segment (by omega)]
    push_cast
    omega
  have first := (Standard.A_full_positive positive).add_meldable sequence_a.meldable count_a
  apply isLiveFullWait_iff.mpr
  refine ⟨first.add_meldable sequence_b.meldable count_b, fun i ↦ ?_⟩
  have bound := i.isLt
  simp only [layered, Pi.add_apply, Standard.A_apply, segment_apply]
  split_ifs <;> omega

lemma exists_live_iff (n m : ℕ) :
    (∃ c : VirtualHand n, IsLiveFullWait 4 m c) ↔ n < m ∧ m < 3 * n := by
  constructor
  · rintro ⟨c, live⟩
    refine ⟨live.1.meldCount_gt_order, ?_⟩
    have bound := live.meldCount_lt_copyCapacity
    norm_num only at bound
    omega
  · rintro ⟨lower, upper⟩
    have positive : 0 < n := by omega
    let k := m - (n + 1)
    let a := min k (n - 1)
    let b := k - a
    have range : k ≤ 2 * (n - 1) := by dsimp [k]; omega
    have bound_a : a ≤ n - 1 := Nat.min_le_right _ _
    have bound_b : b ≤ n - 1 := by dsimp [b, a]; omega
    have sum : n + 1 + a + b = m := by dsimp [k, a, b] at *; omega
    refine ⟨layered n a b, ?_⟩
    simpa only [sum] using layered_live positive bound_a bound_b

lemma maximum {n : ℕ} (positive : 0 < n) :
    (∃ c : VirtualHand n, IsLiveFullWait 4 (3 * n - 1) c) ∧
      ∀ m, (∃ c : VirtualHand n, IsLiveFullWait 4 m c) → m ≤ 3 * n - 1 :=
  ⟨⟨hand n, hand_live positive⟩, fun _ ↦ upper⟩

end LiveMaximum

end Mahjong.VirtualHand
