/-
Copyright (c) 2026 Luna Luteus. Released under Apache 2.0.
Authors: Luna Luteus
-/
import SixRankCriteria
import TopLayer

/-! A free triplet coordinate for every six-rank deficit-two pattern. -/

open Mahjong Mahjong.VirtualHand

namespace Mahjong.VirtualHand.TripletCore.SixRankTop

private lemma free_swap {first second i : Rank 2}
    (free : ∀ (t : Rank 2 → ℕ) (k : ℕ),
      IsFullWait (5 + ∑ j, Function.update t i k j)
        (lift (residueBase first second) (Function.update t i k)) ↔
      IsFullWait (5 + ∑ j, Function.update t i 0 j)
        (lift (residueBase first second) (Function.update t i 0))) :
    ∀ (t : Rank 2 → ℕ) (k : ℕ),
      IsFullWait (5 + ∑ j, Function.update t i k j)
        (lift (residueBase second first) (Function.update t i k)) ↔
      IsFullWait (5 + ∑ j, Function.update t i 0 j)
        (lift (residueBase second first) (Function.update t i 0)) := by
  simpa only [residueBase_comm second first] using free

/-- Every deficit pattern has a coordinate whose entire triplet multiplicity is irrelevant. -/
theorem exists_free_coordinate (first second : Rank 2) :
    ∃ i : Rank 2, ∀ (t : Rank 2 → ℕ) (k : ℕ),
      IsFullWait (5 + ∑ j, Function.update t i k j)
        (lift (residueBase first second) (Function.update t i k)) ↔
      IsFullWait (5 + ∑ j, Function.update t i 0 j)
        (lift (residueBase first second) (Function.update t i 0)) := by
  fin_cases first <;> fin_cases second
  · refine ⟨3, ?_⟩
    intro t k
    exact (full_deficit_00 (Function.update t 3 k)).trans
      (full_deficit_00 (Function.update t 3 0)).symm
  · refine ⟨0, ?_⟩
    intro t k
    exact (full_deficit_01 (Function.update t 0 k)).trans
      (full_deficit_01 (Function.update t 0 0)).symm
  · refine ⟨0, ?_⟩
    intro t k
    exact (full_deficit_02 (Function.update t 0 k)).trans
      (full_deficit_02 (Function.update t 0 0)).symm
  · refine ⟨1, ?_⟩
    intro t k
    exact (full_deficit_03 (Function.update t 1 k)).trans
      (full_deficit_03 (Function.update t 1 0)).symm
  · refine ⟨0, ?_⟩
    intro t k
    exact (full_deficit_04 (Function.update t 0 k)).trans
      (full_deficit_04 (Function.update t 0 0)).symm
  · refine ⟨0, ?_⟩
    intro t k
    exact (full_deficit_05 (Function.update t 0 k)).trans
      (full_deficit_05 (Function.update t 0 0)).symm
  · refine ⟨0, ?_⟩
    apply free_swap (first := 0) (second := 1)
    intro t k
    exact (full_deficit_01 (Function.update t 0 k)).trans
      (full_deficit_01 (Function.update t 0 0)).symm
  · refine ⟨0, ?_⟩
    intro t k
    exact (full_deficit_11 (Function.update t 0 k)).trans
      (full_deficit_11 (Function.update t 0 0)).symm
  · refine ⟨0, ?_⟩
    intro t k
    exact (full_deficit_12 (Function.update t 0 k)).trans
      (full_deficit_12 (Function.update t 0 0)).symm
  · refine ⟨1, ?_⟩
    intro t k
    exact (full_deficit_13 (Function.update t 1 k)).trans
      (full_deficit_13 (Function.update t 1 0)).symm
  · refine ⟨0, ?_⟩
    intro t k
    exact (full_deficit_14 (Function.update t 0 k)).trans
      (full_deficit_14 (Function.update t 0 0)).symm
  · refine ⟨0, ?_⟩
    intro t k
    exact (full_deficit_15 (Function.update t 0 k)).trans
      (full_deficit_15 (Function.update t 0 0)).symm
  · refine ⟨0, ?_⟩
    apply free_swap (first := 0) (second := 2)
    intro t k
    exact (full_deficit_02 (Function.update t 0 k)).trans
      (full_deficit_02 (Function.update t 0 0)).symm
  · refine ⟨0, ?_⟩
    apply free_swap (first := 1) (second := 2)
    intro t k
    exact (full_deficit_12 (Function.update t 0 k)).trans
      (full_deficit_12 (Function.update t 0 0)).symm
  · refine ⟨0, ?_⟩
    intro t k
    exact (full_deficit_22 (Function.update t 0 k)).trans
      (full_deficit_22 (Function.update t 0 0)).symm
  · refine ⟨1, ?_⟩
    intro t k
    exact (full_deficit_23 (Function.update t 1 k)).trans
      (full_deficit_23 (Function.update t 1 0)).symm
  · refine ⟨0, ?_⟩
    intro t k
    exact (full_deficit_24 (Function.update t 0 k)).trans
      (full_deficit_24 (Function.update t 0 0)).symm
  · refine ⟨0, ?_⟩
    intro t k
    exact (full_deficit_25 (Function.update t 0 k)).trans
      (full_deficit_25 (Function.update t 0 0)).symm
  · refine ⟨1, ?_⟩
    apply free_swap (first := 0) (second := 3)
    intro t k
    exact (full_deficit_03 (Function.update t 1 k)).trans
      (full_deficit_03 (Function.update t 1 0)).symm
  · refine ⟨1, ?_⟩
    apply free_swap (first := 1) (second := 3)
    intro t k
    exact (full_deficit_13 (Function.update t 1 k)).trans
      (full_deficit_13 (Function.update t 1 0)).symm
  · refine ⟨1, ?_⟩
    apply free_swap (first := 2) (second := 3)
    intro t k
    exact (full_deficit_23 (Function.update t 1 k)).trans
      (full_deficit_23 (Function.update t 1 0)).symm
  · refine ⟨1, ?_⟩
    intro t k
    exact (full_deficit_33 (Function.update t 1 k)).trans
      (full_deficit_33 (Function.update t 1 0)).symm
  · refine ⟨2, ?_⟩
    intro t k
    exact (full_deficit_34 (Function.update t 2 k)).trans
      (full_deficit_34 (Function.update t 2 0)).symm
  · refine ⟨1, ?_⟩
    intro t k
    exact (full_deficit_35 (Function.update t 1 k)).trans
      (full_deficit_35 (Function.update t 1 0)).symm
  · refine ⟨0, ?_⟩
    apply free_swap (first := 0) (second := 4)
    intro t k
    exact (full_deficit_04 (Function.update t 0 k)).trans
      (full_deficit_04 (Function.update t 0 0)).symm
  · refine ⟨0, ?_⟩
    apply free_swap (first := 1) (second := 4)
    intro t k
    exact (full_deficit_14 (Function.update t 0 k)).trans
      (full_deficit_14 (Function.update t 0 0)).symm
  · refine ⟨0, ?_⟩
    apply free_swap (first := 2) (second := 4)
    intro t k
    exact (full_deficit_24 (Function.update t 0 k)).trans
      (full_deficit_24 (Function.update t 0 0)).symm
  · refine ⟨2, ?_⟩
    apply free_swap (first := 3) (second := 4)
    intro t k
    exact (full_deficit_34 (Function.update t 2 k)).trans
      (full_deficit_34 (Function.update t 2 0)).symm
  · refine ⟨1, ?_⟩
    intro t k
    exact (full_deficit_44 (Function.update t 1 k)).trans
      (full_deficit_44 (Function.update t 1 0)).symm
  · refine ⟨0, ?_⟩
    intro t k
    exact (full_deficit_45 (Function.update t 0 k)).trans
      (full_deficit_45 (Function.update t 0 0)).symm
  · refine ⟨0, ?_⟩
    apply free_swap (first := 0) (second := 5)
    intro t k
    exact (full_deficit_05 (Function.update t 0 k)).trans
      (full_deficit_05 (Function.update t 0 0)).symm
  · refine ⟨0, ?_⟩
    apply free_swap (first := 1) (second := 5)
    intro t k
    exact (full_deficit_15 (Function.update t 0 k)).trans
      (full_deficit_15 (Function.update t 0 0)).symm
  · refine ⟨0, ?_⟩
    apply free_swap (first := 2) (second := 5)
    intro t k
    exact (full_deficit_25 (Function.update t 0 k)).trans
      (full_deficit_25 (Function.update t 0 0)).symm
  · refine ⟨1, ?_⟩
    apply free_swap (first := 3) (second := 5)
    intro t k
    exact (full_deficit_35 (Function.update t 1 k)).trans
      (full_deficit_35 (Function.update t 1 0)).symm
  · refine ⟨0, ?_⟩
    apply free_swap (first := 4) (second := 5)
    intro t k
    exact (full_deficit_45 (Function.update t 0 k)).trans
      (full_deficit_45 (Function.update t 0 0)).symm
  · refine ⟨2, ?_⟩
    intro t k
    exact (full_deficit_55 (Function.update t 2 k)).trans
      (full_deficit_55 (Function.update t 2 0)).symm

/-- The upper inactive profile minus an arbitrary natural deficit pattern. -/
def defectBase (d : Rank 2 → ℕ) : VirtualHand 2 :=
  fun i ↦ abundanceThreshold i - 1 - (d i : ℤ)

/-- A pair representation of the deficit agrees with the corresponding residue hand. -/
theorem defectBase_eq_residueBase (d : Rank 2 → ℕ) (first second : Rank 2)
    (pattern : ∀ i, d i =
      (if i = first then 1 else 0) + (if i = second then 1 else 0)) :
    defectBase d = residueBase first second := by
  have profile : (fun i : Rank 2 ↦ abundanceThreshold i - 1) =
      ![1, 3, 5, 5, 3, 1] := by
    ext i
    fin_cases i <;> norm_num [abundanceThreshold_apply]
  rw [residueBase, ← profile]
  ext i
  simp only [defectBase, Pi.sub_apply, single_apply, pattern i, Nat.cast_add, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]
  ring

/-- Every nonnegative deficit-two pattern admits a free triplet coordinate. -/
theorem exists_free_coordinate_of_defect (d : Rank 2 → ℕ) (total : ∑ i, d i = 2) :
    ∃ i : Rank 2, ∀ (t : Rank 2 → ℕ) (k : ℕ),
      IsFullWait (5 + ∑ j, Function.update t i k j)
        (lift (defectBase d) (Function.update t i k)) ↔
      IsFullWait (5 + ∑ j, Function.update t i 0 j)
        (lift (defectBase d) (Function.update t i 0)) := by
  obtain ⟨first, second, pattern⟩ := sum_two_representation d total
  rw [defectBase_eq_residueBase d first second pattern]
  exact exists_free_coordinate first second

end Mahjong.VirtualHand.TripletCore.SixRankTop
