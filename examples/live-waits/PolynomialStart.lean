/-
Copyright (c) 2026 Luna Luteus. Released under Apache 2.0.
Authors: Luna Luteus
-/
import TripletCounting
import Mathlib.Algebra.Polynomial.Roots

/-!
# The exact start of the counting polynomial

For positive order, the degree of the actual generating-function numerator
controls the first index from which the eventual counting polynomial agrees
with every subsequent coefficient. The finite numerator need not be computed
in order to prove this criterion.
-/

open Mahjong Mahjong.VirtualHand

namespace Mahjong.VirtualHand.TripletCore

/-- Reconstruct a counting polynomial directly from its rational numerator. -/
noncomputable def numeratorCountingPolynomial (n : ℕ) : Polynomial ℚ :=
  ∑ j ∈ (numerator n).support, Polynomial.C ((numerator n).coeff j) *
    Polynomial.preHilbertPoly ℚ (3 * n - 1) j

/-- The first uniform polynomial index, expressed through the actual numerator. -/
noncomputable def polynomialStart (n : ℕ) : ℕ := (numerator n).natDegree + 1 - 3 * n

private lemma series_from_numerator (n : ℕ) :
    generatingSeries n = ((numerator n : Polynomial ℚ) : PowerSeries ℚ) *
      (PowerSeries.invOneSubPow ℚ (3 * n)).val := by
  have cancel : (1 - PowerSeries.X) ^ (3 * n) *
      (PowerSeries.invOneSubPow ℚ (3 * n)).val = 1 := by
    simpa using PowerSeries.one_sub_pow_add_mul_invOneSubPow_val_eq_one_sub_pow ℚ 0 (3 * n)
  calc
    _ = generatingSeries n * ((1 - PowerSeries.X) ^ (3 * n) *
        (PowerSeries.invOneSubPow ℚ (3 * n)).val) := by rw [cancel, mul_one]
    _ = ((1 - PowerSeries.X) ^ (3 * n) * generatingSeries n) *
        (PowerSeries.invOneSubPow ℚ (3 * n)).val := by ring
    _ = _ := by rw [generatingSeries_rational]

private lemma series_numerator_sum (n : ℕ) :
    generatingSeries n = ∑ j ∈ (numerator n).support,
      PowerSeries.C ((numerator n).coeff j) * (PowerSeries.X ^ j *
        (PowerSeries.invOneSubPow ℚ (3 * n)).val) := by
  rw [series_from_numerator]
  have expansion : ((numerator n : Polynomial ℚ) : PowerSeries ℚ) =
      ∑ j ∈ (numerator n).support,
        ((Polynomial.C ((numerator n).coeff j) * Polynomial.X ^ j : Polynomial ℚ) :
          PowerSeries ℚ) := by
    calc
      _ = ((∑ j ∈ (numerator n).support,
          Polynomial.C ((numerator n).coeff j) * Polynomial.X ^ j : Polynomial ℚ) :
          PowerSeries ℚ) := congrArg (fun p : Polynomial ℚ ↦ (p : PowerSeries ℚ))
            (numerator n).as_sum_support_C_mul_X_pow
      _ = _ := map_sum (Polynomial.coeToPowerSeries.ringHom (R := ℚ)) _ _
  rw [expansion, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X]
  ring

private lemma basis_eval_coeff {n : ℕ} (positive : 0 < n) (m j : ℕ)
    (small : j ≤ m + (3 * n - 1)) :
    (Polynomial.preHilbertPoly ℚ (3 * n - 1) j).eval (m : ℚ) =
      PowerSeries.coeff m (PowerSeries.X ^ j *
        (PowerSeries.invOneSubPow ℚ (3 * n)).val) := by
  rw [Polynomial.preHilbertPoly_eq_choose_add_sub ℚ (3 * n - 1) small,
    PowerSeries.coeff_X_pow_mul']
  by_cases allowed : j ≤ m
  · rw [ite_eq_left allowed, show 3 * n = (3 * n - 1) + 1 by omega,
      PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose, PowerSeries.coeff_mk]
    congr 2
    omega
  · rw [ite_eq_right allowed, Nat.choose_eq_zero_of_lt (by omega)]
    rfl

/-- The numerator polynomial gives the count once every basis term has entered its zero range. -/
theorem numeratorCountingPolynomial_eval {n : ℕ} (positive : 0 < n) (m : ℕ)
    (large : (numerator n).natDegree ≤ m + (3 * n - 1)) :
    (numeratorCountingPolynomial n).eval (m : ℚ) =
      (Nat.card {c : VirtualHand n // IsFullWait m c} : ℚ) := by
  rw [numeratorCountingPolynomial, Polynomial.eval_finsetSum,
    ← generatingSeries_coeff, series_numerator_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j member
  rw [Polynomial.eval_mul, Polynomial.eval_C, PowerSeries.coeff_C_mul,
    basis_eval_coeff positive m j ((Polynomial.le_natDegree_of_mem_supp j member).trans large)]

/-- Any polynomial agreeing with all counts on a tail is the eventual counting polynomial. -/
theorem countingPolynomial_unique {n : ℕ} (p : Polynomial ℚ) (s : ℕ)
    (counts : ∀ m : ℕ, s ≤ m → p.eval (m : ℚ) =
      (Nat.card {c : VirtualHand n // IsFullWait m c} : ℚ)) :
    p = eventualPolynomial n := by
  apply Polynomial.eq_of_infinite_eval_eq
  have injective :
      Function.Injective (fun k : ℕ ↦ ((k + s + polynomialBound n : ℕ) : ℚ)) := by
    intro i j same
    change ((i + s + polynomialBound n : ℕ) : ℚ) =
      ((j + s + polynomialBound n : ℕ) : ℚ) at same
    have natural : i + s + polynomialBound n = j + s + polynomialBound n := by
      exact_mod_cast same
    omega
  apply (Set.infinite_range_of_injective injective).mono
  rintro x ⟨k, rfl⟩
  change p.eval ((k + s + polynomialBound n : ℕ) : ℚ) =
    (eventualPolynomial n).eval ((k + s + polynomialBound n : ℕ) : ℚ)
  rw [counts (k + s + polynomialBound n) (by omega),
    eventualPolynomial_eval n (k + s + polynomialBound n) (by omega)]

/-- Reconstruction from the numerator agrees with the original core-cell polynomial. -/
theorem numeratorCountingPolynomial_eq {n : ℕ} (positive : 0 < n) :
    numeratorCountingPolynomial n = eventualPolynomial n := by
  apply countingPolynomial_unique _ (polynomialBound n)
  intro m large
  apply numeratorCountingPolynomial_eval positive m
  have bound := numerator_degree n
  omega

/-- The true numerator yields a sharper range than an a priori degree estimate. -/
theorem eventualPolynomial_eval_from_start {n : ℕ} (positive : 0 < n) (m : ℕ)
    (large : polynomialStart n ≤ m) :
    (eventualPolynomial n).eval (m : ℚ) =
      (Nat.card {c : VirtualHand n // IsFullWait m c} : ℚ) := by
  rw [← numeratorCountingPolynomial_eq positive]
  apply numeratorCountingPolynomial_eval positive m
  unfold polynomialStart at large
  omega

/-- The exact-numerator start is bounded by the local-profile estimate. -/
theorem polynomialStart_le {n : ℕ} (positive : 0 < n) : polynomialStart n ≤ polynomialBound n := by
  have bound := numerator_degree n
  unfold polynomialStart
  omega

private lemma basis_boundary (d m : ℕ) :
    (Polynomial.preHilbertPoly ℚ d (m + d + 1)).eval (m : ℚ) = (-1 : ℚ) ^ d := by
  rw [Polynomial.preHilbertPoly, Polynomial.eval_smul, Polynomial.eval_comp]
  have point : (Polynomial.X - Polynomial.C ((m + d + 1 : ℕ) : ℚ) + 1).eval (m : ℚ) =
      -(d : ℚ) := by simp; ring
  rw [point, ascPochhammer_eval_neg_eq_descPochhammer,
    descPochhammer_eval_eq_descFactorial, Nat.descFactorial_self]
  have nonzero : (d.factorial : ℚ) ≠ 0 := by positivity
  simp only [smul_eq_mul]
  field_simp

private lemma evaluation_error {n : ℕ} (positive : 0 < n) (m : ℕ) :
    (eventualPolynomial n).eval (m : ℚ) -
      (Nat.card {c : VirtualHand n // IsFullWait m c} : ℚ) =
      ∑ j ∈ (numerator n).support, (numerator n).coeff j *
        ((Polynomial.preHilbertPoly ℚ (3 * n - 1) j).eval (m : ℚ) -
          PowerSeries.coeff m (PowerSeries.X ^ j *
            (PowerSeries.invOneSubPow ℚ (3 * n)).val)) := by
  rw [← numeratorCountingPolynomial_eq positive, numeratorCountingPolynomial,
    Polynomial.eval_finsetSum, ← generatingSeries_coeff, series_numerator_sum,
    map_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.eval_mul, Polynomial.eval_C, PowerSeries.coeff_C_mul]
  ring

/-- At the last exceptional index, only the top numerator coefficient contributes an error. -/
theorem polynomial_boundary_error {n : ℕ} (positive : 0 < n)
    (large : 3 * n ≤ (numerator n).natDegree) :
    (eventualPolynomial n).eval (((numerator n).natDegree - 3 * n : ℕ) : ℚ) -
      (Nat.card {c : VirtualHand n //
        IsFullWait ((numerator n).natDegree - 3 * n) c} : ℚ) =
      (numerator n).leadingCoeff * (-1 : ℚ) ^ (3 * n - 1) := by
  set R := (numerator n).natDegree with degree_eq
  set m := R - 3 * n with index_eq
  rw [evaluation_error positive, Finset.sum_eq_single R]
  · have shape : R = m + (3 * n - 1) + 1 := by omega
    have value := basis_boundary (3 * n - 1) m
    rw [← shape] at value
    rw [value, PowerSeries.coeff_X_pow_mul', ite_eq_right (by omega), sub_zero,
      degree_eq, Polynomial.coeff_natDegree]
  · intro j member different
    have bound := Polynomial.le_natDegree_of_mem_supp j member
    rw [← degree_eq] at bound
    rw [basis_eval_coeff positive m j (by omega), sub_self, mul_zero]
  · intro missing
    have zero : (numerator n).coeff R = 0 := by
      simpa only [Polynomial.mem_support_iff, not_not] using missing
    rw [zero, zero_mul]

/-- The immediately preceding index really is exceptional when the start is positive. -/
theorem eventualPolynomial_ne_before_start {n : ℕ} (positive : 0 < n)
    (nonzero : 0 < polynomialStart n) :
    (eventualPolynomial n).eval ((polynomialStart n - 1 : ℕ) : ℚ) ≠
      (Nat.card {c : VirtualHand n // IsFullWait (polynomialStart n - 1) c} : ℚ) := by
  have large : 3 * n ≤ (numerator n).natDegree := by
    unfold polynomialStart at nonzero
    omega
  have error := polynomial_boundary_error positive large
  have index : (numerator n).natDegree - 3 * n = polynomialStart n - 1 := by
    unfold polynomialStart
    omega
  rw [index] at error
  have lead_ne : (numerator n).leadingCoeff ≠ 0 := by
    apply Polynomial.leadingCoeff_ne_zero.mpr
    intro zero
    rw [zero, Polynomial.natDegree_zero] at large
    omega
  intro same
  rw [same, sub_self] at error
  exact (mul_ne_zero lead_ne (pow_ne_zero _ (by norm_num))) error.symm

/-- A uniform range for the eventual polynomial starts exactly at the numerator index or later. -/
theorem polynomialStart_optimal {n : ℕ} (positive : 0 < n) (s : ℕ) :
    (∀ m : ℕ, s ≤ m → (eventualPolynomial n).eval (m : ℚ) =
      (Nat.card {c : VirtualHand n // IsFullWait m c} : ℚ)) ↔ polynomialStart n ≤ s := by
  constructor
  · intro all
    by_contra too_small
    have failure := eventualPolynomial_ne_before_start positive
      (show 0 < polynomialStart n by omega)
    exact failure (all (polynomialStart n - 1) (by omega))
  · intro starts m large
    exact eventualPolynomial_eval_from_start positive m (starts.trans large)

/-- No other polynomial can give the count on an earlier tail. -/
theorem exists_countingPolynomial_iff {n : ℕ} (positive : 0 < n) (s : ℕ) :
    (∃ p : Polynomial ℚ, ∀ m : ℕ, s ≤ m → p.eval (m : ℚ) =
      (Nat.card {c : VirtualHand n // IsFullWait m c} : ℚ)) ↔ polynomialStart n ≤ s := by
  constructor
  · rintro ⟨p, counts⟩
    rw [countingPolynomial_unique p s counts] at counts
    exact (polynomialStart_optimal positive s).mp counts
  · intro large
    exact ⟨eventualPolynomial n, (polynomialStart_optimal positive s).mpr large⟩

end Mahjong.VirtualHand.TripletCore
