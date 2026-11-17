/-
Copyright (c) 2026 Luna Luteus. Released under Apache 2.0.
Authors: Luna Luteus
-/
import TripletLeading
import Mathlib.Analysis.Polynomial.Basic

/-!
# Full waits have density one among uncapped hands

The sample space is the uniform set of nonnegative multiplicity vectors of
size `3*m+1` on `3*n` labelled ranks. This is different from drawing labelled
tiles independently. Stars and bars gives its polynomial count, with the
same exact degree and leading coefficient as the full-wait count.
-/

open Mahjong Mahjong.VirtualHand Filter
open scoped Topology

namespace Mahjong.VirtualHand.TripletCore

/-- All nonnegative hands of the requisite size, without a copy cap. -/
abbrev AllHands (n m : ℕ) :=
  {c : VirtualHand n // Nonnegative c ∧ size c = 3 * (m : ℤ) + 1}

/-- Convert integer multiplicities to a weak composition. -/
def allHandsEquiv (n m : ℕ) :
    AllHands n m ≃ {v : Rank n → ℕ // ∑ i, v i = 3 * m + 1} where
  toFun c := ⟨fun i ↦ (c.val i).toNat, by
    have same : (∑ i, ((c.val i).toNat : ℤ)) = 3 * (m : ℤ) + 1 := by
      calc
        _ = size c.val := by
          apply Finset.sum_congr rfl
          intro i _
          exact Int.toNat_of_nonneg (c.property.1 i)
        _ = _ := c.property.2
    exact_mod_cast same⟩
  invFun v := ⟨fun i ↦ (v.val i : ℤ), ⟨fun i ↦ Int.natCast_nonneg _, by
    dsimp [size]
    exact_mod_cast v.property⟩⟩
  left_inv c := by
    apply Subtype.ext
    funext i
    exact Int.toNat_of_nonneg (c.property.1 i)
  right_inv v := by
    apply Subtype.ext
    funext i
    exact Int.toNat_natCast _

instance allHands_finite (n m : ℕ) : Finite (AllHands n m) :=
  Finite.of_equiv (Sym (Rank n) (3 * m + 1))
    ((Sym.equivNatSumOfFintype (Rank n) (3 * m + 1)).trans (allHandsEquiv n m).symm)

/-- The denominator of the uniform-hand probability is a stars-and-bars count. -/
theorem allHands_card (n m : ℕ) :
    Nat.card (AllHands n m) = Nat.multichoose (3 * n) (3 * m + 1) := by
  rw [Nat.card_congr (allHandsEquiv n m),
    ← Nat.card_congr (Sym.equivNatSumOfFintype (Rank n) (3 * m + 1)),
    Sym.natCard_sym_eq_multichoose]
  simp [Rank]

/-- The ambient count in its usual binomial form. -/
theorem allHands_card_choose {n : ℕ} (positive : 0 < n) (m : ℕ) :
    Nat.card (AllHands n m) = (3 * m + 3 * n).choose (3 * n - 1) := by
  rw [allHands_card, Nat.multichoose_eq,
    show 3 * n + (3 * m + 1) - 1 = 3 * m + 3 * n by omega]
  exact Nat.choose_symm_of_eq_add (by omega)

/-- The uniform sample space is nonempty at every positive order. -/
theorem allHands_card_pos {n : ℕ} (positive : 0 < n) (m : ℕ) :
    0 < Nat.card (AllHands n m) := by
  rw [allHands_card, Nat.multichoose_eq]
  exact Nat.choose_pos (by omega)

/-- Full waits form a subset of the uniform sample space. -/
theorem fullWait_card_le_all (n m : ℕ) :
    Nat.card {c : VirtualHand n // IsFullWait m c} ≤ Nat.card (AllHands n m) := by
  let embed : {c : VirtualHand n // IsFullWait m c} → AllHands n m :=
    fun c ↦ ⟨c.val, c.property.1, c.property.2.1⟩
  apply Nat.card_le_card_of_injective embed
  intro c d same
  apply Subtype.ext
  exact congrArg (fun a : AllHands n m ↦ a.val) same

/-- The polynomial counting the ambient uniform sample space. -/
noncomputable def allPolynomial (n : ℕ) : Polynomial ℚ :=
  (Polynomial.preHilbertPoly ℚ (3 * n - 1) 0).comp
    (Polynomial.C 3 * Polynomial.X + Polynomial.C 1)

/-- The ambient count is polynomial at every meld count for positive order. -/
theorem allPolynomial_eval {n : ℕ} (positive : 0 < n) (m : ℕ) :
    (allPolynomial n).eval (m : ℚ) = (Nat.card (AllHands n m) : ℚ) := by
  rw [allPolynomial, Polynomial.eval_comp]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  rw [show (3 : ℚ) * m + 1 = ((3 * m + 1 : ℕ) : ℚ) by push_cast; rfl,
    Polynomial.preHilbertPoly_eq_choose_add_sub ℚ (3 * n - 1) (by omega),
    allHands_card_choose positive]
  simp only [Nat.sub_zero]
  rw [show 3 * m + 1 + (3 * n - 1) = 3 * m + 3 * n by omega]

/-- The ambient sample space has the same polynomial degree as full waits. -/
theorem allPolynomial_natDegree (n : ℕ) :
    (allPolynomial n).natDegree = 3 * n - 1 := by
  rw [allPolynomial, Polynomial.natDegree_comp, Polynomial.natDegree_preHilbertPoly,
    Polynomial.natDegree_linear (by norm_num : (3 : ℚ) ≠ 0), mul_one]

/-- Full waits and all hands have identical leading counting coefficients. -/
theorem allPolynomial_leadingCoeff (n : ℕ) :
    (allPolynomial n).leadingCoeff =
      (3 : ℚ) ^ (3 * n - 1) / (3 * n - 1).factorial := by
  rw [allPolynomial, Polynomial.leadingCoeff_comp
      (by rw [Polynomial.natDegree_linear (by norm_num : (3 : ℚ) ≠ 0)]; decide +kernel),
    Polynomial.leadingCoeff_preHilbertPoly,
    Polynomial.leadingCoeff_linear (by norm_num : (3 : ℚ) ≠ 0),
    Polynomial.natDegree_preHilbertPoly]
  ring

/-- Uniformly sampled uncapped multiplicity vectors are asymptotically full waits. -/
theorem fullWait_density_one {n : ℕ} (positive : 0 < n) :
    Tendsto (fun m : ℕ ↦
      (Nat.card {c : VirtualHand n // IsFullWait m c} : ℝ) /
        (Nat.card (AllHands n m) : ℝ)) atTop (𝓝 1) := by
  let cast : ℚ →+* ℝ := Rat.castHom ℝ
  let P := (eventualPolynomial n).map cast
  let Q := (allPolynomial n).map cast
  have full_nonzero : eventualPolynomial n ≠ 0 := by
    intro zero
    have nonzero : (eventualPolynomial n).leadingCoeff ≠ 0 := by
      rw [eventualPolynomial_leadingCoeff positive]
      positivity
    exact nonzero (by rw [zero, Polynomial.leadingCoeff_zero])
  have all_nonzero : allPolynomial n ≠ 0 := by
    intro zero
    have nonzero : (allPolynomial n).leadingCoeff ≠ 0 := by
      rw [allPolynomial_leadingCoeff]
      positivity
    exact nonzero (by rw [zero, Polynomial.leadingCoeff_zero])
  have degrees : P.degree = Q.degree := by
    dsimp [P, Q]
    rw [Polynomial.degree_map, Polynomial.degree_map,
      Polynomial.degree_eq_natDegree full_nonzero, Polynomial.degree_eq_natDegree all_nonzero,
      eventualPolynomial_natDegree positive, allPolynomial_natDegree]
  have coefficient : P.leadingCoeff = Q.leadingCoeff := by
    simp only [P, Q, Polynomial.leadingCoeff_map,
      eventualPolynomial_leadingCoeff positive, allPolynomial_leadingCoeff]
  have q_nonzero : Q.leadingCoeff ≠ 0 := by
    dsimp [Q]
    rw [Polynomial.leadingCoeff_map]
    intro zero
    have original : (allPolynomial n).leadingCoeff = 0 :=
      cast.injective (zero.trans (map_zero cast).symm)
    rw [allPolynomial_leadingCoeff] at original
    have nonzero : (3 : ℚ) ^ (3 * n - 1) / (3 * n - 1).factorial ≠ 0 := by positivity
    exact nonzero original
  have limit := Polynomial.div_tendsto_atTop_leadingCoeff_div_of_degree_eq P Q degrees
  rw [coefficient, div_self q_nonzero] at limit
  have sampled := limit.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  apply sampled.congr'
  filter_upwards [eventually_ge_atTop (8 * n)] with m large
  dsimp [P, Q]
  rw [show (m : ℝ) = cast (m : ℚ) by simp [cast], Polynomial.eval_map_apply,
    Polynomial.eval_map_apply, eventualPolynomial_eval n m large,
    allPolynomial_eval positive m]
  simp [cast]

end Mahjong.VirtualHand.TripletCore
