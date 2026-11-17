/-
Copyright (c) 2026 Luna Luteus. Released under Apache 2.0.
Authors: Luna Luteus
-/
import Ninegates

/-!
# Boundary-sensitive triplet removal

The canonical sequence hand is bounded by the paper's abundance profile.
A meldable hand therefore has a removable triplet at a coordinate strictly
above that profile; allowing for the pair gives a full-wait threshold three
above the profile. This yields rank-dependent finite core caps.
-/

open Mahjong

namespace Mahjong.VirtualHand

/-- Exceeding the local sequence bound forces a canonical triplet. -/
theorem Meldable.sub_triplet_of_threshold {n : ℕ} {c : VirtualHand n}
    (meldable : Meldable c) (i : Rank n) (large : abundanceThreshold i + 1 ≤ c i) :
    Meldable (c - triplet i) := by
  apply (meldable.sub_triplet_iff i).mpr
  obtain ⟨p, ⟨nonnegative, canonical, equal⟩, _⟩ := meldable.unique_canonical
  have upper := canonical.sequenceHand_le_threshold i
  change sequenceHand p.seqNum i ≤ abundanceThreshold i at upper
  have at_i := congrFun equal i
  rw [Placement.toHand_eq] at at_i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at at_i
  rw [← equal, canonical.canonicalTriplet_eq]
  omega

/-- A full wait permits removal three tiles above the local abundance profile. -/
theorem IsFullWait.sub_triplet_of_threshold {n m : ℕ} {c : VirtualHand n}
    (full : IsFullWait m c) (i : Rank n) (large : abundanceThreshold i + 3 ≤ c i) :
    IsFullWait (m - 1) (c - triplet i) := by
  have positive_m : 0 < m := by have lower := full.meldCount_gt_order; omega
  have threshold := (abundanceThreshold_bounds i).1
  apply isFullWait_iff.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro j
    have positive : 0 ≤ c j := full.1 j
    change 0 ≤ c j - triplet i j
    simp only [triplet_apply, single_apply]
    split_ifs with same
    · subst j
      omega
    · omega
  · rw [map_sub, full.2.1, size_triplet]
    omega
  · intro p
    obtain ⟨q, edge⟩ := (isFullWait_iff.mp full).2.2 p
    have remainder_large : abundanceThreshold i + 1 ≤ (c + single p - pair q) i := by
      have positive : 0 ≤ single p i := nonnegative_single p i
      have pair_bound : pair q i ≤ 2 := by
        simp only [pair_apply, single_apply]
        split_ifs <;> norm_num
      change abundanceThreshold i + 1 ≤ c i + single p i - pair q i
      omega
    have removed := edge.sub_triplet_of_threshold i remainder_large
    refine ⟨q, ?_⟩
    change Meldable (c - triplet i + single p - pair q)
    have shape : c - triplet i + single p - pair q =
        (c + single p - pair q) - triplet i := by abel
    rw [shape]
    exact removed

/-- Every minimal full wait satisfies the rank-dependent core caps. -/
theorem IsMinimalFullWait.boundary_bounded {n m : ℕ} {c : VirtualHand n}
    (minimal : IsMinimalFullWait m c) :
    Nonnegative c ∧ ∀ i, c i ≤ abundanceThreshold i + 2 := by
  refine ⟨minimal.full.1, ?_⟩
  intro i
  by_contra outside
  have removable := minimal.full.sub_triplet_of_threshold i (by omega)
  have triplet_meldable : Meldable (triplet i) := by
    refine ⟨⟨0, single i⟩, ⟨le_refl _, nonnegative_single i⟩, ?_⟩
    simp [Placement.toHand_eq, triplet]
  have empty := minimal.minimal removable triplet_meldable
    (show c = c - triplet i + triplet i by abel)
  have count := congrArg size empty
  simp at count

private lemma threshold_size_large {n : ℕ} (order : 2 ≤ n) :
    size (abundanceThreshold : VirtualHand n) = 18 * (n : ℤ) - 12 := by
  let a : Rank n := ⟨0, by omega⟩
  let b : Rank n := ⟨1, by omega⟩
  let c : Rank n := ⟨3 * n - 2, by omega⟩
  let d : Rank n := ⟨3 * n - 1, by omega⟩
  have hand : (abundanceThreshold : VirtualHand n) =
      (fun _ ↦ 6) - (4 : ℤ) • (single a + single d) -
        (2 : ℤ) • (single b + single c) := by
    ext i
    have bound := i.isLt
    simp only [abundanceThreshold_apply, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, single_apply, Fin.ext_iff]
    dsimp only [a, b, c, d]
    split_ifs <;> omega
  rw [hand]
  simp only [map_sub, map_smul, map_add, size_const, size_single, smul_eq_mul]
  ring

/-- Total mass of the abundance profile at every positive order. -/
theorem abundanceThreshold_size {n : ℕ} (positive : 0 < n) :
    size (abundanceThreshold : VirtualHand n) =
      if n = 1 then 8 else 18 * (n : ℤ) - 12 := by
  by_cases one : n = 1
  · subst n
    rw [ite_eq_left rfl, abundanceThreshold_orderOne]
    norm_num [size, Fin.sum_univ_succ]
  · rw [ite_eq_right one]
    exact threshold_size_large (by omega)

/-- Boundary information improves the coarse minimal meld-count upper bound. -/
theorem IsMinimalFullWait.meldCount_lt_boundary {n m : ℕ} {c : VirtualHand n}
    (minimal : IsMinimalFullWait m c) (order : 2 ≤ n) : m < 8 * n - 4 := by
  have bound : (∑ i : Rank n, c i) ≤ ∑ i : Rank n, (abundanceThreshold i + 2) :=
    Finset.sum_le_sum (fun i _ ↦ minimal.boundary_bounded.2 i)
  change size c ≤ ∑ i : Rank n, (abundanceThreshold i + 2) at bound
  rw [Finset.sum_add_distrib] at bound
  have total := abundanceThreshold_size (show 0 < n by omega)
  rw [ite_eq_right (by omega : n ≠ 1)] at total
  change size (abundanceThreshold : VirtualHand n) = _ at total
  change size c ≤ size abundanceThreshold + ∑ _ : Rank n, (2 : ℤ) at bound
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at bound
  rw [total, minimal.full.2.1] at bound
  omega

end Mahjong.VirtualHand
