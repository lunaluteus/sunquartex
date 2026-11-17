/-
Copyright (c) 2026 Luna Luteus. Released under Apache 2.0.
Authors: Luna Luteus
-/
import TripletCounting

/-!
# Full-dimensional cores and the exact leading coefficient

Proposition 6.2 of arXiv:2611.06944v1 makes every hand above the local
abundance profile and of size congruent to one modulo three a full wait.
Fully active cores lie in the three-tile band above that profile. They
correspond to residue vectors of sum one, so there are `3^(3*n-1)` of
them for positive `n`. Only these cells contribute to the top coefficient.
-/

open Mahjong Mahjong.VirtualHand

namespace Mahjong.VirtualHand.TripletCore

/-- Cores with a free triplet tail at every rank. -/
abbrev DenseCores (n : ℕ) := {a : Cores n // ∀ i, abundanceThreshold i ≤ a.val i}

/-- One affine residue condition on a full rank vector. -/
abbrev Residues (n : ℕ) := {v : Rank n → ZMod 3 // ∑ i, v i = 1}

private def sumFiberEquiv (N : ℕ) (s : ZMod 3) :
    (Fin N → ZMod 3) ≃ {v : Fin (N + 1) → ZMod 3 // ∑ i, v i = s} where
  toFun v := ⟨Fin.cons (s - ∑ i, v i) v, by simp [Fin.sum_univ_succ]⟩
  invFun v := Fin.tail v.val
  left_inv v := rfl
  right_inv v := by
    apply Subtype.ext
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · have total := v.property
      rw [Fin.sum_univ_succ] at total
      change s - ∑ j : Fin N, v.val j.succ = v.val 0
      exact sub_eq_iff_eq_add.mpr total.symm
    · rfl

private lemma residues_card {n : ℕ} (positive : 0 < n) : Nat.card (Residues n) = 3 ^ (3 * n - 1) :=
    by
  have count (N : ℕ) : Nat.card {v : Fin (N + 1) → ZMod 3 // ∑ i, v i = 1} = 3 ^ N := by
    rw [← Nat.card_congr (sumFiberEquiv N 1)]
    simp
  have result := count (3 * n - 1)
  rw [show 3 * n - 1 + 1 = 3 * n by omega] at result
  exact result

private def residueHand {n : ℕ} (v : Residues n) : VirtualHand n :=
  fun i ↦ abundanceThreshold i + (v.val i - (abundanceThreshold i : ZMod 3)).val

private lemma residueHand_cast {n : ℕ} (v : Residues n) (i : Rank n) :
    (residueHand v i : ZMod 3) = v.val i := by
  simp [residueHand]

private lemma residueHand_bounds {n : ℕ} (v : Residues n) (i : Rank n) :
    abundanceThreshold i ≤ residueHand v i ∧
      residueHand v i ≤ abundanceThreshold i + 2 := by
  have bound := (v.val i - (abundanceThreshold i : ZMod 3)).val_lt
  dsimp [residueHand]
  omega

private lemma residueHand_full {n : ℕ} (positive : 0 < n) (v : Residues n) :
    IsFullWait (grade (residueHand v)) (residueHand v) := by
  have nonnegative : Nonnegative (residueHand v) := fun i ↦ by
    have lower := (residueHand_bounds v i).1
    have threshold := (abundanceThreshold_bounds i).1
    change 0 ≤ residueHand v i
    omega
  have residue : (size (residueHand v) : ZMod 3) = 1 := by
    simpa [size, Int.cast_sum, residueHand_cast] using v.property
  have remainder : size (residueHand v) % 3 = 1 := by
    have same := (ZMod.intCast_eq_intCast_iff' (size (residueHand v)) 1 3).mp residue
    norm_num at same
    exact same
  have lower := nonnegative.size_nonnegative
  apply isFullWait_of_abundant positive
  · intro i
    exact (residueHand_bounds v i).1
  · unfold grade
    omega

/-- Dense full cores correspond exactly to residue vectors with sum one. -/
def denseCoreEquiv {n : ℕ} (positive : 0 < n) : DenseCores n ≃ Residues n where
  toFun a := ⟨fun i ↦ (a.val.val i : ZMod 3), by
    have residue := (full_grade a.val.property.2).size_cast
    simpa [size, Int.cast_sum] using residue⟩
  invFun v := ⟨⟨residueHand v, ⟨fun i ↦ by
       have lower := (residueHand_bounds v i).1
       have threshold := (abundanceThreshold_bounds i).1
       change 0 ≤ residueHand v i
       omega,
     fun i ↦ (residueHand_bounds v i).2⟩,
    grade (residueHand v), residueHand_full positive v⟩,
    fun i ↦ (residueHand_bounds v i).1⟩
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    have lower := a.property i
    have upper := a.val.property.1.2 i
    have residue := ZMod.val_intCast (n := 3) (a.val.val i - abundanceThreshold i)
    simp only [Int.cast_sub] at residue
    change abundanceThreshold i +
      (((a.val.val i : ZMod 3) - (abundanceThreshold i : ZMod 3)).val : ℤ) = a.val.val i
    omega
  right_inv v := by
    apply Subtype.ext
    funext i
    exact residueHand_cast v i

/-- There are exactly `3^(3*n-1)` full-dimensional core cells. -/
theorem dense_core_card {n : ℕ} (positive : 0 < n) :
    Nat.card (DenseCores n) = 3 ^ (3 * n - 1) := by
  rw [Nat.card_congr (denseCoreEquiv positive)]
  exact residues_card positive


private lemma active_card_eq_iff {n : ℕ} (a : Cores n) :
    Nat.card (Active a) = 3 * n ↔ ∀ i, abundanceThreshold i ≤ a.val i := by
  classical
  constructor
  · intro same
    by_contra missing
    obtain ⟨i, small⟩ := not_forall.mp missing
    have strict : Nat.card (Active a) < 3 * n := by
      simpa [Nat.card_eq_fintype_card, Rank] using
        Fintype.card_subtype_lt (p := fun j : Rank n ↦ abundanceThreshold j ≤ a.val j) small
    omega
  · intro dense
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv dense)]
    simp [Rank]

private lemma row_topCoeff {n : ℕ} (positive : 0 < n) (a : Cores n) :
    (rowPolynomial a).coeff (3 * n - 1) =
      if (∀ i, abundanceThreshold i ≤ a.val i) then ((3 * n - 1).factorial : ℚ)⁻¹ else 0 := by
  classical
  by_cases dense : ∀ i, abundanceThreshold i ≤ a.val i
  · rw [ite_eq_left dense, rowPolynomial, (active_card_eq_iff a).mpr dense,
      ite_eq_right (by omega)]
    exact Polynomial.coeff_preHilbertPoly_self ℚ _ _
  · rw [ite_eq_right dense]
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    unfold rowPolynomial
    split_ifs with empty
    · simp only [Polynomial.natDegree_zero]
      omega
    · rw [Polynomial.natDegree_preHilbertPoly]
      have bound := Nat.card_le_card_of_injective
        (fun i : Active a ↦ i.val) Subtype.val_injective
      have ranks : Nat.card (Rank n) = 3 * n := by simp [Rank]
      rw [ranks] at bound
      have strict := mt (active_card_eq_iff a).mp dense
      omega

/-- The top coefficient is determined by the fully active residue cells. -/
theorem eventualPolynomial_topCoeff {n : ℕ} (positive : 0 < n) :
    (eventualPolynomial n).coeff (3 * n - 1) =
      (3 : ℚ) ^ (3 * n - 1) / (3 * n - 1).factorial := by
  classical
  rw [eventualPolynomial, Polynomial.finsetSum_coeff]
  simp_rw [row_topCoeff positive]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have count : (Finset.univ.filter (fun a : Cores n ↦ ∀ i, abundanceThreshold i ≤ a.val i)).card =
      3 ^ (3 * n - 1) := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact dense_core_card positive
  rw [count]
  simp [div_eq_mul_inv]

/-- The eventual counting polynomial has the exact maximal degree. -/
theorem eventualPolynomial_natDegree {n : ℕ} (positive : 0 < n) :
    (eventualPolynomial n).natDegree = 3 * n - 1 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (eventualPolynomial_degree n)
  rw [eventualPolynomial_topCoeff positive]
  positivity

/-- Its leading coefficient is independent of the lower-dimensional core table. -/
theorem eventualPolynomial_leadingCoeff {n : ℕ} (positive : 0 < n) :
    (eventualPolynomial n).leadingCoeff =
      (3 : ℚ) ^ (3 * n - 1) / (3 * n - 1).factorial := by
  rw [← Polynomial.coeff_natDegree, eventualPolynomial_natDegree positive]
  exact eventualPolynomial_topCoeff positive

/-- The common denominator has no cancellation at one. -/
theorem numerator_eval_one {n : ℕ} (positive : 0 < n) :
    (numerator n).eval 1 = (3 : ℚ) ^ (3 * n - 1) := by
  classical
  rw [numerator, Polynomial.eval_finsetSum]
  trans ∑ a : Cores n, if (∀ i, abundanceThreshold i ≤ a.val i) then (1 : ℚ) else 0
  · apply Finset.sum_congr rfl
    intro a _
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_sub, Polynomial.eval_one, one_pow, sub_self, one_mul]
    by_cases dense : ∀ i, abundanceThreshold i ≤ a.val i
    · rw [ite_eq_left dense, (active_card_eq_iff a).mpr dense]
      simp
    · have bound := Nat.card_le_card_of_injective
        (fun i : Active a ↦ i.val) Subtype.val_injective
      have ranks : Nat.card (Rank n) = 3 * n := by simp [Rank]
      rw [ranks] at bound
      have strict := mt (active_card_eq_iff a).mp dense
      have nonzero : 3 * n - Nat.card (Active a) ≠ 0 := by omega
      rw [ite_eq_right dense, zero_pow nonzero]
  · rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have count :
        (Finset.univ.filter (fun a : Cores n ↦ ∀ i, abundanceThreshold i ≤ a.val i)).card =
        3 ^ (3 * n - 1) := by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      exact dense_core_card positive
    rw [count]
    simp

end Mahjong.VirtualHand.TripletCore
