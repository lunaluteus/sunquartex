/-
Copyright (c) 2026 Luna Luteus. Released under Apache 2.0.
Authors: Luna Luteus
-/
import SixRankScan

/-!
# Symbolic six-rank top-layer criteria

Each deficit-two residue representative has an explicit full-sidedness criterion
in arbitrary nonnegative triplet multiplicities. The proofs expand the six draws
and pair positions in the canonical scan; they do not enumerate tail values.
Rank indices in the theorem suffixes are zero-based and record the two defects.
-/

open Mahjong Mahjong.VirtualHand

namespace Mahjong.VirtualHand.TripletCore.SixRankTop

/-- The upper inactive profile, with one tile removed at each selected rank. -/
def residueBase (first second : Rank 2) : VirtualHand 2 :=
  ![1, 3, 5, 5, 3, 1] - single first - single second

/-- Every deficit-two representative has the same size. -/
theorem residueBase_size (first second : Rank 2) : size (residueBase first second) = 16 := by
  rw [residueBase, map_sub, map_sub, size_single, size_single]
  norm_num [size, Fin.sum_univ_succ]

/-- The two deficit positions are unordered. -/
theorem residueBase_comm (first second : Rank 2) :
    residueBase first second = residueBase second first := by
  unfold residueBase
  abel

/-- Full-sidedness for defects at ranks 0 and 0, with arbitrary triplet tails. -/
theorem full_deficit_00 (t : Rank 2 → ℕ) :
    IsFullWait (5 + ∑ i, t i) (lift (residueBase 0 0) t) ↔
      (0 < t 0 ∧ 0 < t 1 ∧ 0 < t 2) ∨ (0 < t 0 ∧ 0 < t 2 ∧ 0 < t 4) ∨
       (0 < t 0 ∧ 0 < t 1 ∧ 0 < t 5) ∨ (0 < t 0 ∧ 0 < t 4 ∧ 0 < t 5) := by
  rw [full_lift_iff_canonical _ (by rw [residueBase_size]; norm_num) t]
  norm_num [Fin.forall_fin_succ, Fin.exists_fin_succ,
    virtuallyMeldable_six, canonicalTriplet_six, scanTriplets, scanStates, residueBase,
    Pi.add_apply, Pi.sub_apply, single, pair, Matrix.vecHead, Matrix.vecTail]
  all_goals omega

/-- Full-sidedness for defects at ranks 0 and 1, with arbitrary triplet tails. -/
theorem full_deficit_01 (t : Rank 2 → ℕ) :
    IsFullWait (5 + ∑ i, t i) (lift (residueBase 0 1) t) ↔
      True := by
  rw [full_lift_iff_canonical _ (by rw [residueBase_size]; norm_num) t]
  norm_num [Fin.forall_fin_succ, Fin.exists_fin_succ,
    virtuallyMeldable_six, canonicalTriplet_six, scanTriplets, scanStates, residueBase,
    Pi.add_apply, Pi.sub_apply, single, pair, Matrix.vecHead, Matrix.vecTail]
  all_goals omega

/-- Full-sidedness for defects at ranks 0 and 2, with arbitrary triplet tails. -/
theorem full_deficit_02 (t : Rank 2 → ℕ) :
    IsFullWait (5 + ∑ i, t i) (lift (residueBase 0 2) t) ↔
      0 < t 2 ∨ 0 < t 5 := by
  rw [full_lift_iff_canonical _ (by rw [residueBase_size]; norm_num) t]
  norm_num [Fin.forall_fin_succ, Fin.exists_fin_succ,
    virtuallyMeldable_six, canonicalTriplet_six, scanTriplets, scanStates, residueBase,
    Pi.add_apply, Pi.sub_apply, single, pair, Matrix.vecHead, Matrix.vecTail]
  all_goals omega

/-- Full-sidedness for defects at ranks 0 and 3, with arbitrary triplet tails. -/
theorem full_deficit_03 (t : Rank 2 → ℕ) :
    IsFullWait (5 + ∑ i, t i) (lift (residueBase 0 3) t) ↔
      0 < t 0 ∨ 0 < t 3 := by
  rw [full_lift_iff_canonical _ (by rw [residueBase_size]; norm_num) t]
  norm_num [Fin.forall_fin_succ, Fin.exists_fin_succ,
    virtuallyMeldable_six, canonicalTriplet_six, scanTriplets, scanStates, residueBase,
    Pi.add_apply, Pi.sub_apply, single, pair, Matrix.vecHead, Matrix.vecTail]
  all_goals omega

/-- Full-sidedness for defects at ranks 0 and 4, with arbitrary triplet tails. -/
theorem full_deficit_04 (t : Rank 2 → ℕ) :
    IsFullWait (5 + ∑ i, t i) (lift (residueBase 0 4) t) ↔
      True := by
  rw [full_lift_iff_canonical _ (by rw [residueBase_size]; norm_num) t]
  norm_num [Fin.forall_fin_succ, Fin.exists_fin_succ,
    virtuallyMeldable_six, canonicalTriplet_six, scanTriplets, scanStates, residueBase,
    Pi.add_apply, Pi.sub_apply, single, pair, Matrix.vecHead, Matrix.vecTail]
  all_goals omega

/-- Full-sidedness for defects at ranks 0 and 5, with arbitrary triplet tails. -/
theorem full_deficit_05 (t : Rank 2 → ℕ) :
    IsFullWait (5 + ∑ i, t i) (lift (residueBase 0 5) t) ↔
      True := by
  rw [full_lift_iff_canonical _ (by rw [residueBase_size]; norm_num) t]
  norm_num [Fin.forall_fin_succ, Fin.exists_fin_succ,
    virtuallyMeldable_six, canonicalTriplet_six, scanTriplets, scanStates, residueBase,
    Pi.add_apply, Pi.sub_apply, single, pair, Matrix.vecHead, Matrix.vecTail]
  all_goals omega

/-- Full-sidedness for defects at ranks 1 and 1, with arbitrary triplet tails. -/
theorem full_deficit_11 (t : Rank 2 → ℕ) :
    IsFullWait (5 + ∑ i, t i) (lift (residueBase 1 1) t) ↔
      (0 < t 1 ∧ 0 < t 2) ∨ (0 < t 1 ∧ 0 < t 5) := by
  rw [full_lift_iff_canonical _ (by rw [residueBase_size]; norm_num) t]
  norm_num [Fin.forall_fin_succ, Fin.exists_fin_succ,
    virtuallyMeldable_six, canonicalTriplet_six, scanTriplets, scanStates, residueBase,
    Pi.add_apply, Pi.sub_apply, single, pair, Matrix.vecHead, Matrix.vecTail]
  all_goals omega

/-- Full-sidedness for defects at ranks 1 and 2, with arbitrary triplet tails. -/
theorem full_deficit_12 (t : Rank 2 → ℕ) :
    IsFullWait (5 + ∑ i, t i) (lift (residueBase 1 2) t) ↔
      (0 < t 1 ∧ 0 < t 2) ∨ (0 < t 2 ∧ 0 < t 4) ∨ (0 < t 1 ∧ 0 < t 5) ∨ (0 < t 4 ∧ 0 < t 5) := by
  rw [full_lift_iff_canonical _ (by rw [residueBase_size]; norm_num) t]
  norm_num [Fin.forall_fin_succ, Fin.exists_fin_succ,
    virtuallyMeldable_six, canonicalTriplet_six, scanTriplets, scanStates, residueBase,
    Pi.add_apply, Pi.sub_apply, single, pair, Matrix.vecHead, Matrix.vecTail]
  all_goals omega

/-- Full-sidedness for defects at ranks 1 and 3, with arbitrary triplet tails. -/
theorem full_deficit_13 (t : Rank 2 → ℕ) :
    IsFullWait (5 + ∑ i, t i) (lift (residueBase 1 3) t) ↔
      0 < t 0 ∨ 0 < t 3 := by
  rw [full_lift_iff_canonical _ (by rw [residueBase_size]; norm_num) t]
  norm_num [Fin.forall_fin_succ, Fin.exists_fin_succ,
    virtuallyMeldable_six, canonicalTriplet_six, scanTriplets, scanStates, residueBase,
    Pi.add_apply, Pi.sub_apply, single, pair, Matrix.vecHead, Matrix.vecTail]
  all_goals omega

/-- Full-sidedness for defects at ranks 1 and 4, with arbitrary triplet tails. -/
theorem full_deficit_14 (t : Rank 2 → ℕ) :
    IsFullWait (5 + ∑ i, t i) (lift (residueBase 1 4) t) ↔
      True := by
  rw [full_lift_iff_canonical _ (by rw [residueBase_size]; norm_num) t]
  norm_num [Fin.forall_fin_succ, Fin.exists_fin_succ,
    virtuallyMeldable_six, canonicalTriplet_six, scanTriplets, scanStates, residueBase,
    Pi.add_apply, Pi.sub_apply, single, pair, Matrix.vecHead, Matrix.vecTail]
  all_goals omega

/-- Full-sidedness for defects at ranks 1 and 5, with arbitrary triplet tails. -/
theorem full_deficit_15 (t : Rank 2 → ℕ) :
    IsFullWait (5 + ∑ i, t i) (lift (residueBase 1 5) t) ↔
      True := by
  rw [full_lift_iff_canonical _ (by rw [residueBase_size]; norm_num) t]
  norm_num [Fin.forall_fin_succ, Fin.exists_fin_succ,
    virtuallyMeldable_six, canonicalTriplet_six, scanTriplets, scanStates, residueBase,
    Pi.add_apply, Pi.sub_apply, single, pair, Matrix.vecHead, Matrix.vecTail]
  all_goals omega

/-- Full-sidedness for defects at ranks 2 and 2, with arbitrary triplet tails. -/
theorem full_deficit_22 (t : Rank 2 → ℕ) :
    IsFullWait (5 + ∑ i, t i) (lift (residueBase 2 2) t) ↔
      0 < t 2 ∨ 0 < t 5 := by
  rw [full_lift_iff_canonical _ (by rw [residueBase_size]; norm_num) t]
  norm_num [Fin.forall_fin_succ, Fin.exists_fin_succ,
    virtuallyMeldable_six, canonicalTriplet_six, scanTriplets, scanStates, residueBase,
    Pi.add_apply, Pi.sub_apply, single, pair, Matrix.vecHead, Matrix.vecTail]
  all_goals omega

/-- Full-sidedness for defects at ranks 2 and 3, with arbitrary triplet tails. -/
theorem full_deficit_23 (t : Rank 2 → ℕ) :
    IsFullWait (5 + ∑ i, t i) (lift (residueBase 2 3) t) ↔
      (0 < t 0 ∧ 0 < t 2) ∨ (0 < t 2 ∧ 0 < t 3) ∨ (0 < t 0 ∧ 0 < t 5) ∨ (0 < t 3 ∧ 0 < t 5) := by
  rw [full_lift_iff_canonical _ (by rw [residueBase_size]; norm_num) t]
  norm_num [Fin.forall_fin_succ, Fin.exists_fin_succ,
    virtuallyMeldable_six, canonicalTriplet_six, scanTriplets, scanStates, residueBase,
    Pi.add_apply, Pi.sub_apply, single, pair, Matrix.vecHead, Matrix.vecTail]
  all_goals omega

/-- Full-sidedness for defects at ranks 2 and 4, with arbitrary triplet tails. -/
theorem full_deficit_24 (t : Rank 2 → ℕ) :
    IsFullWait (5 + ∑ i, t i) (lift (residueBase 2 4) t) ↔
      0 < t 2 ∨ 0 < t 5 := by
  rw [full_lift_iff_canonical _ (by rw [residueBase_size]; norm_num) t]
  norm_num [Fin.forall_fin_succ, Fin.exists_fin_succ,
    virtuallyMeldable_six, canonicalTriplet_six, scanTriplets, scanStates, residueBase,
    Pi.add_apply, Pi.sub_apply, single, pair, Matrix.vecHead, Matrix.vecTail]
  all_goals omega

/-- Full-sidedness for defects at ranks 2 and 5, with arbitrary triplet tails. -/
theorem full_deficit_25 (t : Rank 2 → ℕ) :
    IsFullWait (5 + ∑ i, t i) (lift (residueBase 2 5) t) ↔
      0 < t 2 ∨ 0 < t 5 := by
  rw [full_lift_iff_canonical _ (by rw [residueBase_size]; norm_num) t]
  norm_num [Fin.forall_fin_succ, Fin.exists_fin_succ,
    virtuallyMeldable_six, canonicalTriplet_six, scanTriplets, scanStates, residueBase,
    Pi.add_apply, Pi.sub_apply, single, pair, Matrix.vecHead, Matrix.vecTail]
  all_goals omega

/-- Full-sidedness for defects at ranks 3 and 3, with arbitrary triplet tails. -/
theorem full_deficit_33 (t : Rank 2 → ℕ) :
    IsFullWait (5 + ∑ i, t i) (lift (residueBase 3 3) t) ↔
      0 < t 0 ∨ 0 < t 3 := by
  rw [full_lift_iff_canonical _ (by rw [residueBase_size]; norm_num) t]
  norm_num [Fin.forall_fin_succ, Fin.exists_fin_succ,
    virtuallyMeldable_six, canonicalTriplet_six, scanTriplets, scanStates, residueBase,
    Pi.add_apply, Pi.sub_apply, single, pair, Matrix.vecHead, Matrix.vecTail]
  all_goals omega

/-- Full-sidedness for defects at ranks 3 and 4, with arbitrary triplet tails. -/
theorem full_deficit_34 (t : Rank 2 → ℕ) :
    IsFullWait (5 + ∑ i, t i) (lift (residueBase 3 4) t) ↔
      (0 < t 0 ∧ 0 < t 1) ∨ (0 < t 1 ∧ 0 < t 3) ∨ (0 < t 0 ∧ 0 < t 4) ∨ (0 < t 3 ∧ 0 < t 4) := by
  rw [full_lift_iff_canonical _ (by rw [residueBase_size]; norm_num) t]
  norm_num [Fin.forall_fin_succ, Fin.exists_fin_succ,
    virtuallyMeldable_six, canonicalTriplet_six, scanTriplets, scanStates, residueBase,
    Pi.add_apply, Pi.sub_apply, single, pair, Matrix.vecHead, Matrix.vecTail]
  all_goals omega

/-- Full-sidedness for defects at ranks 3 and 5, with arbitrary triplet tails. -/
theorem full_deficit_35 (t : Rank 2 → ℕ) :
    IsFullWait (5 + ∑ i, t i) (lift (residueBase 3 5) t) ↔
      0 < t 0 ∨ 0 < t 3 := by
  rw [full_lift_iff_canonical _ (by rw [residueBase_size]; norm_num) t]
  norm_num [Fin.forall_fin_succ, Fin.exists_fin_succ,
    virtuallyMeldable_six, canonicalTriplet_six, scanTriplets, scanStates, residueBase,
    Pi.add_apply, Pi.sub_apply, single, pair, Matrix.vecHead, Matrix.vecTail]
  all_goals omega

/-- Full-sidedness for defects at ranks 4 and 4, with arbitrary triplet tails. -/
theorem full_deficit_44 (t : Rank 2 → ℕ) :
    IsFullWait (5 + ∑ i, t i) (lift (residueBase 4 4) t) ↔
      (0 < t 0 ∧ 0 < t 4) ∨ (0 < t 3 ∧ 0 < t 4) := by
  rw [full_lift_iff_canonical _ (by rw [residueBase_size]; norm_num) t]
  norm_num [Fin.forall_fin_succ, Fin.exists_fin_succ,
    virtuallyMeldable_six, canonicalTriplet_six, scanTriplets, scanStates, residueBase,
    Pi.add_apply, Pi.sub_apply, single, pair, Matrix.vecHead, Matrix.vecTail]
  all_goals omega

/-- Full-sidedness for defects at ranks 4 and 5, with arbitrary triplet tails. -/
theorem full_deficit_45 (t : Rank 2 → ℕ) :
    IsFullWait (5 + ∑ i, t i) (lift (residueBase 4 5) t) ↔
      True := by
  rw [full_lift_iff_canonical _ (by rw [residueBase_size]; norm_num) t]
  norm_num [Fin.forall_fin_succ, Fin.exists_fin_succ,
    virtuallyMeldable_six, canonicalTriplet_six, scanTriplets, scanStates, residueBase,
    Pi.add_apply, Pi.sub_apply, single, pair, Matrix.vecHead, Matrix.vecTail]
  all_goals omega

/-- Full-sidedness for defects at ranks 5 and 5, with arbitrary triplet tails. -/
theorem full_deficit_55 (t : Rank 2 → ℕ) :
    IsFullWait (5 + ∑ i, t i) (lift (residueBase 5 5) t) ↔
      (0 < t 0 ∧ 0 < t 1 ∧ 0 < t 5) ∨ (0 < t 1 ∧ 0 < t 3 ∧ 0 < t 5) ∨
      (0 < t 0 ∧ 0 < t 4 ∧ 0 < t 5) ∨ (0 < t 3 ∧ 0 < t 4 ∧ 0 < t 5) := by
  rw [full_lift_iff_canonical _ (by rw [residueBase_size]; norm_num) t]
  norm_num [Fin.forall_fin_succ, Fin.exists_fin_succ,
    virtuallyMeldable_six, canonicalTriplet_six, scanTriplets, scanStates, residueBase,
    Pi.add_apply, Pi.sub_apply, single, pair, Matrix.vecHead, Matrix.vecTail]
  all_goals omega

end Mahjong.VirtualHand.TripletCore.SixRankTop
