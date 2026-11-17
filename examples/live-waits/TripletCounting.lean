/-
Copyright (c) 2026 Luna Luteus. Released under Apache 2.0.
Authors: Luna Luteus
-/
import TripletCore
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.NatCard
import Mathlib.RingTheory.Polynomial.HilbertPoly

/-!
# Counting unrestricted full waits from bounded cores

The core decomposition gives an exact finite sum of multichoose numbers, a
rational generating series with denominator `(1-X)^(3*n)`, and an explicit
rational-coefficient counting polynomial valid at every meld count at least
`polynomialBound n` (two at order one, `5*n-4` at higher orders).
Its degree is at most `3*n-1`; this cutoff is sufficient, not asserted
optimal. Mathlib supplies stars and bars through `Sym.equivNatSumOfFintype`
and the polynomial evaluation through `Polynomial.preHilbertPoly`.
-/

open Mahjong Mahjong.VirtualHand

namespace Mahjong.VirtualHand.TripletCore

noncomputable instance cores_fintype (n : ℕ) : Fintype (Cores n) := Fintype.ofFinite _

/-- Tails contributing to a fixed total meld count. -/
abbrev Row {n : ℕ} (a : Cores n) (m : ℕ) :=
  {t : Active a → ℕ // grade a.val + ∑ i, t i = m}

instance row_finite {n : ℕ} (a : Cores n) (m : ℕ) : Finite (Row a m) := by
  let encode : Row a m → (Active a → Fin (m + 1)) := fun t i ↦ ⟨t.val i, by
    have bound := Finset.single_le_sum (fun j _ ↦ Nat.zero_le (t.val j)) (Finset.mem_univ i)
    have total := t.property
    omega⟩
  have injective : Function.Injective encode := by
    intro t u same
    apply Subtype.ext
    funext i
    exact congrArg (fun f : Active a → Fin (m + 1) ↦ (f i).val) same
  exact Finite.of_injective encode injective

/-- Each core contributes one weak-composition count, subject to its grade. -/
theorem row_card {n : ℕ} (a : Cores n) (m : ℕ) :
    Nat.card (Row a m) = if grade a.val ≤ m then
      Nat.multichoose (Nat.card (Active a)) (m - grade a.val) else 0 := by
  classical
  by_cases permitted : grade a.val ≤ m
  · let e : Row a m ≃ {t : Active a → ℕ // ∑ i, t i = m - grade a.val} :=
      Equiv.subtypeEquivRight (fun _ ↦ by omega)
    rw [ite_eq_left permitted, Nat.card_congr e,
      ← Nat.card_congr (Sym.equivNatSumOfFintype (Active a) (m - grade a.val)),
      Sym.natCard_sym_eq_multichoose]
  · let : IsEmpty (Row a m) := ⟨fun t ↦ by have total := t.property; omega⟩
    simp [permitted]

/-- The exact count is a finite sum indexed by full cores with coordinates at most eight. -/
theorem full_card_formula (n m : ℕ) :
    Nat.card {c : VirtualHand n // IsFullWait m c} =
      ∑ a : Cores n, if grade a.val ≤ m then
        Nat.multichoose (Nat.card (Active a)) (m - grade a.val) else 0 := by
  rw [Nat.card_congr (fixedEquiv n m), Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro a _
  exact row_card a m

/-- Uniform starting bound supplied by the local threshold profile. -/
def polynomialBound (n : ℕ) : ℕ := if n = 1 then 2 else 5 * n - 4

/-- The profile improves the previous five-times-order sufficient bound. -/
theorem polynomialBound_le_five (n : ℕ) : polynomialBound n ≤ 5 * n := by
  unfold polynomialBound
  split_ifs with one
  · subst n
    norm_num
  · omega

/-- Weighting active ranks by the local profile sharpens each core's grade bound. -/
theorem core_grade_active_bound {n : ℕ} (a : Cores n) :
    grade a.val + 1 ≤ polynomialBound n + Nat.card (Active a) := by
  classical
  have active_sum : (∑ i : Rank n, if abundanceThreshold i ≤ a.val i then (3 : ℤ) else 0) =
      (Nat.card (Active a) : ℤ) * 3 := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
      ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  have upper : size a.val ≤
      size (abundanceThreshold : VirtualHand n) - ((3 * n : ℕ) : ℤ) +
      (Nat.card (Active a) : ℤ) * 3 := by
    calc
      _ ≤ ∑ i : Rank n,
          (abundanceThreshold i - 1 +
            if abundanceThreshold i ≤ a.val i then (3 : ℤ) else 0) := by
        change (∑ i, a.val i) ≤ _
        apply Finset.sum_le_sum
        intro i _
        split_ifs with active
        · have bound := a.property.1.2 i
          omega
        · omega
      _ = _ := by
        rw [Finset.sum_add_distrib, active_sum, Finset.sum_sub_distrib]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, mul_one]
        rfl
  have count := (full_grade a.property.2).2.1
  have positive : 0 < n := by
    by_contra empty
    have zero : n = 0 := by omega
    subst n
    simp [size, Rank] at count
    omega
  rw [count, abundanceThreshold_size positive] at upper
  unfold polynomialBound
  split_ifs with one
  · subst n
    norm_num at upper
    rw [Nat.card_eq_fintype_card]
    omega
  · omega

/-- Polynomial contribution of one core to the eventual count. -/
noncomputable def rowPolynomial {n : ℕ} (a : Cores n) : Polynomial ℚ :=
  if Nat.card (Active a) = 0 then 0 else
    Polynomial.preHilbertPoly ℚ (Nat.card (Active a) - 1) (grade a.val)

/-- An explicit finite sum giving the eventual counting polynomial. -/
noncomputable def eventualPolynomial (n : ℕ) : Polynomial ℚ :=
  ∑ a : Cores n, rowPolynomial a

private lemma rowPolynomial_eval {n : ℕ} (a : Cores n) (m : ℕ)
    (large : polynomialBound n ≤ m) :
    (rowPolynomial a).eval (m : ℚ) =
      ((if grade a.val ≤ m then
        Nat.multichoose (Nat.card (Active a)) (m - grade a.val) else 0 : ℕ) : ℚ) := by
  have bound := core_grade_active_bound a
  unfold rowPolynomial
  by_cases empty : Nat.card (Active a) = 0
  · have permitted : grade a.val ≤ m := by omega
    rw [ite_eq_left permitted, ite_eq_left empty]
    obtain ⟨j, equal⟩ := Nat.exists_eq_succ_of_ne_zero
      (show m - grade a.val ≠ 0 by omega)
    rw [empty, equal]
    simp
  · rw [ite_eq_right empty,
      Polynomial.preHilbertPoly_eq_choose_add_sub ℚ (Nat.card (Active a) - 1) (by omega)]
    by_cases permitted : grade a.val ≤ m
    · rw [ite_eq_left permitted, Nat.multichoose_eq]
      have shape : m + (Nat.card (Active a) - 1) - grade a.val =
          Nat.card (Active a) + (m - grade a.val) - 1 := by omega
      rw [shape]
      exact_mod_cast (Nat.choose_symm_of_eq_add
        (by omega : Nat.card (Active a) + (m - grade a.val) - 1 =
          (Nat.card (Active a) - 1) + (m - grade a.val)))
    · rw [ite_eq_right permitted, Nat.choose_eq_zero_of_lt (by omega)]

/-- The count is polynomial from the starting bound supplied by the local profile. -/
theorem eventualPolynomial_eval (n m : ℕ) (large : polynomialBound n ≤ m) :
    (eventualPolynomial n).eval (m : ℚ) =
      (Nat.card {c : VirtualHand n // IsFullWait m c} : ℚ) := by
  rw [eventualPolynomial, Polynomial.eval_finsetSum, full_card_formula]
  simp only [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact rowPolynomial_eval a m large

/-- The eventual polynomial has degree at most the number of free coordinates minus one. -/
theorem eventualPolynomial_degree (n : ℕ) :
    (eventualPolynomial n).natDegree ≤ 3 * n - 1 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro a _
  unfold rowPolynomial
  split_ifs with empty
  · simp
  · rw [Polynomial.natDegree_preHilbertPoly]
    have bound := Nat.card_le_card_of_injective
      (fun i : Active a ↦ i.val) Subtype.val_injective
    have ranks : Nat.card (Rank n) = 3 * n := by simp [Rank]
    rw [ranks] at bound
    omega

/-- The ordinary generating series, expressed as a finite sum of geometric cells. -/
noncomputable def generatingSeries (n : ℕ) : PowerSeries ℚ :=
  ∑ a : Cores n, PowerSeries.X ^ grade a.val *
    (PowerSeries.invOneSubPow ℚ (Nat.card (Active a))).val

private lemma coeff_invOneSubPow (r k : ℕ) :
    PowerSeries.coeff k (PowerSeries.invOneSubPow ℚ r).val = (Nat.multichoose r k : ℚ) := by
  cases r with
  | zero =>
    cases k <;> simp [PowerSeries.invOneSubPow_zero]
  | succ r =>
    rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose, PowerSeries.coeff_mk,
      Nat.multichoose_eq, show r + 1 + k - 1 = r + k by omega]
    exact_mod_cast (Nat.choose_symm_add (a := r) (b := k))

/-- Each coefficient of the series is the exact unrestricted full-wait count. -/
theorem generatingSeries_coeff (n m : ℕ) :
    PowerSeries.coeff m (generatingSeries n) =
      (Nat.card {c : VirtualHand n // IsFullWait m c} : ℚ) := by
  rw [generatingSeries, map_sum, full_card_formula]
  simp only [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [PowerSeries.coeff_X_pow_mul', coeff_invOneSubPow]
  split_ifs <;> simp

/-- Clearing a common denominator leaves a finite polynomial. -/
noncomputable def numerator (n : ℕ) : Polynomial ℚ :=
  ∑ a : Cores n, Polynomial.X ^ grade a.val *
    (1 - Polynomial.X) ^ (3 * n - Nat.card (Active a))

/-- The active-rank correction also bounds the rational numerator's degree. -/
theorem numerator_degree (n : ℕ) : (numerator n).natDegree ≤ polynomialBound n + 3 * n - 1 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro a _
  have bound := core_grade_active_bound a
  have ranks_bound := Nat.card_le_card_of_injective
    (fun i : Active a ↦ i.val) Subtype.val_injective
  have ranks : Nat.card (Rank n) = 3 * n := by simp [Rank]
  rw [ranks] at ranks_bound
  have linear : (1 - Polynomial.X : Polynomial ℚ).natDegree ≤ 1 := by
    simpa using Polynomial.natDegree_sub_le (1 : Polynomial ℚ) Polynomial.X
  have power := Polynomial.natDegree_pow_le_of_le (3 * n - Nat.card (Active a)) linear
  simp only [mul_one] at power
  have product := Polynomial.natDegree_mul_le
    (p := (Polynomial.X ^ grade a.val : Polynomial ℚ))
    (q := (1 - Polynomial.X) ^ (3 * n - Nat.card (Active a)))
  rw [Polynomial.natDegree_X_pow] at product
  omega

/-- The exact generating series has common denominator `(1-X)^(3*n)`. -/
theorem generatingSeries_rational (n : ℕ) :
    (1 - PowerSeries.X) ^ (3 * n) * generatingSeries n =
      ((numerator n : Polynomial ℚ) : PowerSeries ℚ) := by
  have mapped := map_sum (Polynomial.coeToPowerSeries.ringHom (R := ℚ))
    (fun a : Cores n ↦ Polynomial.X ^ grade a.val *
      (1 - Polynomial.X) ^ (3 * n - Nat.card (Active a))) Finset.univ
  rw [generatingSeries, Finset.mul_sum, numerator]
  trans ∑ a : Cores n, ((Polynomial.X ^ grade a.val *
    (1 - Polynomial.X) ^ (3 * n - Nat.card (Active a)) : Polynomial ℚ) : PowerSeries ℚ)
  · apply Finset.sum_congr rfl
    intro a _
    have bound := Nat.card_le_card_of_injective
      (fun i : Active a ↦ i.val) Subtype.val_injective
    have ranks : Nat.card (Rank n) = 3 * n := by simp [Rank]
    rw [ranks] at bound
    have cancel := PowerSeries.one_sub_pow_add_mul_invOneSubPow_val_eq_one_sub_pow
      ℚ (3 * n - Nat.card (Active a)) (Nat.card (Active a))
    rw [Nat.sub_add_cancel bound] at cancel
    simp only [Polynomial.coe_mul,
      Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_sub, Polynomial.coe_one]
    calc
      _ = PowerSeries.X ^ grade a.val * ((1 - PowerSeries.X) ^ (3 * n) *
          (PowerSeries.invOneSubPow ℚ (Nat.card (Active a))).val) := by ring
      _ = _ := by rw [cancel]
  · exact mapped.symm

end Mahjong.VirtualHand.TripletCore
