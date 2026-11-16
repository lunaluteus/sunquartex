/-
Copyright (c) 2026 Luna Luteus. Released under Apache 2.0.
Authors: Luna Luteus
-/
import Ninegates

/-!
# Sharp copy-cap stabilization at arbitrary order

Every full-sided wait on `3 * n` ranks with `m` melds satisfies
`c i ≤ 3 * (m - n) + 1`, interpreting the difference in the integers.
For `n ≥ 2` this is attained, so the exact cap at which all full waits are live
is `3 * (m - n) + 2`. The finite counting function stabilizes at the same cap.

The base bound and explicit family `Standard.B` come from Xue and Zhong,
*Beyond Nine Gates*, arXiv:2611.06944v1, formalized in ninegates-lean4 at
7b379afe7f54f34c59c8abdfc8e6fa5f0bee952a. The induction uses canonical
sequence coefficients at most two to remove a common triplet from a sparse hand.
-/

open Mahjong Mahjong.VirtualHand

namespace Mahjong.VirtualHand.CopyCapStability

private lemma two_large_neighbours {n : ℕ} {c : VirtualHand n} (meldable : Meldable c)
    (i : Rank n) (large : 6 ≤ c i) (absent : canonicalTriplet c i = 0) :
    ∃ a b : Rank n, a ≠ i ∧ b ≠ i ∧ a ≠ b ∧ 4 ≤ c a ∧ 4 ≤ c b := by
  have here := tripletGreedy_identity c i
  have current := canonicalSequence_bounds c (i.val + 1)
  have previous := canonicalSequence_bounds c i.val
  have older := canonicalSequence_bounds c (i.val - 1)
  have all_two : canonicalSequence c (i.val + 1) = 2 ∧
      canonicalSequence c i.val = 2 ∧ canonicalSequence c (i.val - 1) = 2 := by omega
  have first : 0 < i.val := by
    by_contra no_room
    have zero : i.val = 0 := by omega
    rw [zero, canonicalSequence_zero] at all_two
    omega
  have last : i.val + 1 < 3 * n := by
    have end_zero := ((meldable_iff_tripletGreedy c).mp meldable).1.1
    have bound := i.isLt
    by_contra no_room
    have equal : i.val + 1 = 3 * n := by omega
    rw [equal, end_zero] at all_two
    omega
  let a : Rank n := ⟨i.val - 1, by have := i.isLt; omega⟩
  let b : Rank n := ⟨i.val + 1, last⟩
  have ha : a.val + 1 = i.val := by dsimp [a]; omega
  have hb : b.val - 1 = i.val := by dsimp [b]
  have at_a := tripletGreedy_identity c a
  have at_b := tripletGreedy_identity c b
  have ta := meldable.canonicalTriplet_nonnegative a
  have tb := meldable.canonicalTriplet_nonnegative b
  have sa := (canonicalSequence_bounds c (a.val - 1)).1
  have sb := (canonicalSequence_bounds c (b.val + 1)).1
  rw [ha] at at_a
  rw [hb] at at_b
  have same_a : canonicalSequence c a.val = canonicalSequence c (i.val - 1) := rfl
  have same_b : canonicalSequence c b.val = canonicalSequence c (i.val + 1) := rfl
  rw [same_a] at at_a
  rw [same_b] at at_b
  refine ⟨a, b, ?_, ?_, ?_, by omega, by omega⟩
  · intro equal
    have := congrArg Fin.val equal
    dsimp [a] at this
    omega
  · intro equal
    have := congrArg Fin.val equal
    dsimp [b] at this
    omega
  · intro equal
    have := congrArg Fin.val equal
    dsimp [a, b] at this
    omega

private lemma sub_triplet_sparse {n m : ℕ} {c : VirtualHand n} (full : IsFullWait m c)
    (i : Rank n) (large : 8 ≤ c i) (sparse : ∀ j, j ≠ i → c j ≤ 3) :
    IsFullWait (m - 1) (c - triplet i) := by
  have positive_m : 0 < m := by have := full.meldCount_gt_order; omega
  apply isFullWait_iff.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro j
    have positive : 0 ≤ c j := full.1 j
    change 0 ≤ c j - triplet i j
    simp only [triplet_apply, single_apply]
    split_ifs with same
    · subst j; omega
    · omega
  · rw [map_sub, full.2.1, size_triplet]
    omega
  · intro p
    obtain ⟨q, edge⟩ := (isFullWait_iff.mp full).2.2 p
    let d := c + single p - pair q
    have hd : Meldable d := edge
    have di : 6 ≤ d i := by
      have single_positive : 0 ≤ single p i := nonnegative_single p i
      have pair_bound : pair q i ≤ 2 := by
        simp only [pair_apply, single_apply]
        split_ifs <;> norm_num
      change 6 ≤ c i + single p i - pair q i
      omega
    have occurs : 1 ≤ canonicalTriplet d i := by
      by_contra missing
      have nonnegative := hd.canonicalTriplet_nonnegative i
      have absent : canonicalTriplet d i = 0 := by omega
      obtain ⟨a, b, ai, bi, ab, large_a, large_b⟩ := two_large_neighbours hd i di absent
      have drawn (j : Rank n) (different : j ≠ i) (big : 4 ≤ d j) : j = p := by
        have small := sparse j different
        have pair_positive : 0 ≤ pair q j := by
          simp only [pair_apply, single_apply]
          split_ifs <;> norm_num
        by_contra not_drawn
        have zero : single p j = 0 := single_of_ne not_drawn
        change 4 ≤ c j + single p j - pair q j at big
        rw [zero] at big
        omega
      exact ab ((drawn a ai large_a).trans (drawn b bi large_b).symm)
    refine ⟨q, ?_⟩
    change Meldable (c - triplet i + single p - pair q)
    have shape : c - triplet i + single p - pair q = d - triplet i := by dsimp [d]; abel
    rw [shape]
    exact (hd.sub_triplet_iff i).mpr occurs

private lemma size_interior {n : ℕ} (positive : 0 < n) :
    size (interiorOnes : VirtualHand n) = 3 * (n : ℤ) - 2 := by
  rw [interiorOnes_eq_segment, size_segment (by omega)]
  omega

private lemma two_le_size {n : ℕ} {c : VirtualHand n} (positive : Nonnegative c)
    (i j : Rank n) (different : i ≠ j) : c i + c j ≤ size c := by
  have bound := Finset.sum_le_sum_of_subset_of_nonneg (f := c)
    (Finset.subset_univ ({i, j} : Finset (Rank n))) (fun k _ _ ↦ positive k)
  change c i + c j ≤ ∑ k, c k
  simpa [different] using bound

private lemma sparse_of_large {n m : ℕ} {c : VirtualHand n} (full : IsFullWait m c)
    (i : Rank n) (large : 3 * ((m : ℤ) - n) + 2 ≤ c i) :
    ∀ j, j ≠ i → c j ≤ 3 := by
  intro j different
  have excess_bound := two_le_size full.excess_nonnegative i j different.symm
  have bi := interiorOnes_bounds i
  have bj := interiorOnes_bounds j
  rw [excess_apply, excess_apply] at excess_bound
  change c i - interiorOnes i + (c j - interiorOnes j) ≤ size (c - interiorOnes) at excess_bound
  rw [map_sub, full.2.1, size_interior full.order_pos] at excess_bound
  omega

/-- Every coordinate of a full wait is bounded by its excess meld count. -/
theorem coordinate_bound {n m : ℕ} {c : VirtualHand n} (full : IsFullWait m c)
    (i : Rank n) : c i ≤ 3 * ((m : ℤ) - n) + 1 := by
  induction m using Nat.strong_induction_on generalizing c with
  | h m ih =>
    have lower := full.meldCount_gt_order
    by_cases first : m = n + 1
    · subst m
      have bound : c i ≤ 4 := full.valid_succ.2 i
      omega
    · by_contra too_large
      have large : 3 * ((m : ℤ) - n) + 2 ≤ c i := by omega
      have removable := sub_triplet_sparse full i (by omega) (sparse_of_large full i large)
      have smaller := ih (m - 1) (by omega) removable
      change c i - triplet i i ≤ _ at smaller
      simp only [triplet_apply, single_self, mul_one] at smaller
      omega

/-- Above this copy cap every full-sided wait is live. -/
theorem live_iff_full {n cap m : ℕ} (bound : 3 * (m - n) + 2 ≤ cap)
    (c : VirtualHand n) : IsLiveFullWait cap m c ↔ IsFullWait m c := by
  refine ⟨fun live ↦ live.1, fun full ↦ isLiveFullWait_iff.mpr ⟨full, fun i ↦ ?_⟩⟩
  have at_i := coordinate_bound full i
  have order := full.meldCount_gt_order
  omega

/-- The live-wait count stabilizes to the unrestricted full-wait count. -/
theorem live_card_stable {n cap m : ℕ} (bound : 3 * (m - n) + 2 ≤ cap) :
    Nat.card {c : VirtualHand n // IsLiveFullWait cap m c} =
      Nat.card {c : VirtualHand n // IsFullWait m c} :=
  Nat.card_congr (Equiv.subtypeEquivRight (live_iff_full bound))

/-- At every order at least two, some full wait attains the coordinate bound. -/
theorem exists_extremal {n m : ℕ} (order : 2 ≤ n) (melds : n < m) :
    ∃ c : VirtualHand n, IsFullWait m c ∧ ∃ i : Rank n,
      c i = 3 * ((m : ℤ) - n) + 1 := by
  let i : Rank n := ⟨3 * n - 4, by omega⟩
  have base : Standard.B n i = 4 := by
    have positive : 0 < 3 * n - 4 := by omega
    have interior : (3 * n - 4) + 1 < 3 * n := by omega
    simp [Standard.B, interiorOnes, singleAt_apply, i, positive, interior, Nat.ne_of_gt positive]
  have build (k : ℕ) : ∃ c : VirtualHand n,
      IsFullWait (n + 1 + k) c ∧ c i = 4 + 3 * (k : ℤ) := by
    induction k with
    | zero => exact ⟨Standard.B n, by simpa using Standard.B_full order, by simpa using base⟩
    | succ k ih =>
      obtain ⟨c, full, count⟩ := ih
      refine ⟨c + triplet i, by simpa [Nat.add_assoc] using full.add_triplet i, ?_⟩
      change c i + triplet i i = _
      rw [count]
      simp only [triplet_apply, single_self, mul_one, Nat.cast_add, Nat.cast_one]
      ring
  obtain ⟨c, full, count⟩ := build (m - (n + 1))
  have index : n + 1 + (m - (n + 1)) = m := by omega
  rw [index] at full
  exact ⟨c, full, i, by omega⟩

/-- For order at least two and a permitted meld count, the uniform cap is sharp. -/
theorem all_full_live_iff {n cap m : ℕ} (order : 2 ≤ n) (melds : n < m) :
    (∀ c : VirtualHand n, IsFullWait m c → IsLiveFullWait cap m c) ↔
      3 * (m - n) + 2 ≤ cap := by
  constructor
  · intro all_live
    obtain ⟨c, full, i, count⟩ := exists_extremal order melds
    have upper := (isLiveFullWait_iff.mp (all_live c full)).2 i
    rw [count] at upper
    omega
  · intro bound c full
    exact (live_iff_full bound c).mpr full

/-- At the least permitted meld count, cap five admits all eight classified hands. -/
theorem live_card_succ {n cap : ℕ} (order : 2 ≤ n) (bound : 5 ≤ cap) :
    Nat.card {c : VirtualHand n // IsLiveFullWait cap (n + 1) c} = 8 := by
  rw [live_card_stable (by omega)]
  exact fullWait_card_eight order

private lemma finite_full (n m : ℕ) : Finite {c : VirtualHand n // IsFullWait m c} := by
  let encode : {c : VirtualHand n // IsFullWait m c} → (Rank n → Fin (3 * (m - n) + 2)) :=
    fun c i ↦ ⟨(c.val i).toNat, by
      have lower := c.property.1 i
      have upper := coordinate_bound c.property i
      have order := c.property.meldCount_gt_order
      omega⟩
  have injective : Function.Injective encode := by
    intro c d same
    apply Subtype.ext
    funext i
    have equal := congrArg (fun x : Rank n → Fin (3 * (m - n) + 2) ↦ (x i).val) same
    have lower_c := c.property.1 i
    have lower_d := d.property.1 i
    change (c.val i).toNat = (d.val i).toNat at equal
    simpa only [Int.toNat_of_nonneg lower_c, Int.toNat_of_nonneg lower_d] using
      congrArg (fun k : ℕ ↦ (k : ℤ)) equal
  exact Finite.of_injective encode injective

/-- Below the uniform cap, some full wait is missing from the finite live set. -/
theorem live_card_lt {n cap m : ℕ} (order : 2 ≤ n) (melds : n < m)
    (small : cap < 3 * (m - n) + 2) :
    Nat.card {c : VirtualHand n // IsLiveFullWait cap m c} <
      Nat.card {c : VirtualHand n // IsFullWait m c} := by
  let Full := {c : VirtualHand n // IsFullWait m c}
  let Live := {c : VirtualHand n // IsLiveFullWait cap m c}
  let inclusion : Live → Full := fun c ↦ ⟨c.val, c.property.1⟩
  have injective : Function.Injective inclusion := by
    intro c d same
    exact Subtype.ext (congrArg (fun x : Full ↦ x.val) same)
  have finiteFull : Finite Full := finite_full n m
  have finiteLive : Finite Live := Finite.of_injective inclusion injective
  let := Fintype.ofFinite Full
  let := Fintype.ofFinite Live
  have not_surjective : ¬Function.Surjective inclusion := by
    intro onto
    obtain ⟨c, full, i, count⟩ := exists_extremal order melds
    obtain ⟨d, equal⟩ := onto ⟨c, full⟩
    have value : d.val = c := congrArg Subtype.val equal
    have upper := (isLiveFullWait_iff.mp d.property).2 i
    rw [value, count] at upper
    omega
  have strict := Fintype.card_lt_of_injective_not_surjective inclusion injective not_surjective
  rwa [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at strict

/-- The bound is also the exact copy cap at which the counting function stabilizes. -/
theorem live_card_stable_iff {n cap m : ℕ} (order : 2 ≤ n) (melds : n < m) :
    Nat.card {c : VirtualHand n // IsLiveFullWait cap m c} =
      Nat.card {c : VirtualHand n // IsFullWait m c} ↔ 3 * (m - n) + 2 ≤ cap := by
  constructor
  · intro equal
    by_contra small
    have strict := live_card_lt order melds (Nat.lt_of_not_ge small)
    omega
  · exact live_card_stable

end Mahjong.VirtualHand.CopyCapStability
