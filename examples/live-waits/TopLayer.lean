/-
Copyright (c) 2026 Luna Luteus. Released under Apache 2.0.
Authors: Luna Luteus
-/
import PolynomialStart

/-!
# The highest numerator layer

The local weighted core bound has very little slack at its highest degree.
At orders at least two, a cell can reach degree `8*n-5` precisely when the
sum of its coordinate deficits from the active/inactive upper endpoints is two.
-/

open Mahjong Mahjong.VirtualHand

namespace Mahjong.VirtualHand.TripletCore

/-- The upper endpoint of the active or inactive band containing a coordinate. -/
def bandTop {n : ℕ} (a : Cores n) (i : Rank n) : ℤ :=
  abundanceThreshold i - 1 + if abundanceThreshold i ≤ a.val i then 3 else 0

/-- A coordinate's nonnegative distance from its band's upper endpoint. -/
def bandDefect {n : ℕ} (a : Cores n) (i : Rank n) : ℕ :=
  (bandTop a i - a.val i).toNat

/-- The total distance from all band endpoints. -/
def totalDefect {n : ℕ} (a : Cores n) : ℕ := ∑ i, bandDefect a i

/-- Core caps make the upper endpoint an actual coordinate bound. -/
theorem bandTop_le {n : ℕ} (a : Cores n) (i : Rank n) : a.val i ≤ bandTop a i := by
  unfold bandTop
  split_ifs with active
  · have upper := a.property.1.2 i
    omega
  · omega

/-- Defects exactly measure the gap in the weighted coordinate sum. -/
theorem totalDefect_add_size {n : ℕ} (a : Cores n) :
    (totalDefect a : ℤ) + size a.val =
      size (abundanceThreshold : VirtualHand n) - (3 * n : ℕ) +
        3 * (Nat.card (Active a) : ℤ) := by
  classical
  have active_sum : (∑ i : Rank n, if abundanceThreshold i ≤ a.val i then (3 : ℤ) else 0) =
      (Nat.card (Active a) : ℤ) * 3 := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
      ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  have each (i : Rank n) : (bandDefect a i : ℤ) = bandTop a i - a.val i := by
    exact Int.toNat_of_nonneg (sub_nonneg.mpr (bandTop_le a i))
  simp only [totalDefect, Nat.cast_sum, each]
  change (∑ i, (bandTop a i - a.val i)) + (∑ i, a.val i) = _
  rw [Finset.sum_sub_distrib, sub_add_cancel]
  simp only [bandTop]
  rw [Finset.sum_add_distrib,
    Finset.sum_sub_distrib, active_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  change size abundanceThreshold - _ + _ = _
  ring

/-- At higher orders, the deficit is two modulo three with an explicit grade identity. -/
theorem totalDefect_grade {n : ℕ} (a : Cores n) (order : 2 ≤ n) :
    (totalDefect a : ℤ) + 3 * (grade a.val : ℤ) =
      15 * (n : ℤ) - 13 + 3 * (Nat.card (Active a) : ℤ) := by
  have h := totalDefect_add_size a
  have count := (full_grade a.property.2).2.1
  rw [count, abundanceThreshold_size (by omega), ite_eq_right (by omega : n ≠ 1)] at h
  push_cast at h
  omega

/-- Reaching the allowed top cell degree is equivalent to total deficit two. -/
theorem top_cell_iff_defect_two {n : ℕ} (a : Cores n) (order : 2 ≤ n) :
    grade a.val + (3 * n - Nat.card (Active a)) = 8 * n - 5 ↔ totalDefect a = 2 := by
  have ranks := Nat.card_le_card_of_injective
    (fun i : Active a ↦ i.val) Subtype.val_injective
  have rank_count : Nat.card (Rank n) = 3 * n := by simp [Rank]
  rw [rank_count] at ranks
  have gap := totalDefect_grade a order
  omega

/-- Only deficit-two cells contribute to the highest allowed numerator coefficient. -/
theorem cell_top_coeff {n : ℕ} (a : Cores n) (order : 2 ≤ n) :
    (Polynomial.X ^ grade a.val *
      (1 - Polynomial.X : Polynomial ℚ) ^ (3 * n - Nat.card (Active a))).coeff
        (8 * n - 5) =
      if totalDefect a = 2 then (-1 : ℚ) ^ (3 * n - Nat.card (Active a)) else 0 := by
  have linear : (1 - Polynomial.X : Polynomial ℚ).natDegree ≤ 1 := by
    simpa using Polynomial.natDegree_sub_le (1 : Polynomial ℚ) Polynomial.X
  by_cases top : totalDefect a = 2
  · rw [ite_eq_left top]
    have index := (top_cell_iff_defect_two a order).mpr top
    rw [← index, Nat.add_comm (grade a.val), Polynomial.coeff_X_pow_mul]
    have h := Polynomial.coeff_pow_of_natDegree_le
      (m := 3 * n - Nat.card (Active a)) linear
    simpa [Polynomial.coeff_one] using h
  · rw [ite_eq_right top]
    have bound := core_grade_active_bound a
    have ranks := Nat.card_le_card_of_injective
      (fun i : Active a ↦ i.val) Subtype.val_injective
    have rank_count : Nat.card (Rank n) = 3 * n := by simp [Rank]
    rw [rank_count] at ranks
    have not_top := (top_cell_iff_defect_two a order).not.mpr top
    unfold polynomialBound at bound
    rw [ite_eq_right (by omega : n ≠ 1)] at bound
    have smaller : grade a.val + (3 * n - Nat.card (Active a)) < 8 * n - 5 := by omega
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have product := Polynomial.natDegree_mul_le
      (p := (Polynomial.X ^ grade a.val : Polynomial ℚ))
      (q := (1 - Polynomial.X) ^ (3 * n - Nat.card (Active a)))
    have power := Polynomial.natDegree_pow_le_of_le (3 * n - Nat.card (Active a)) linear
    simp only [Polynomial.natDegree_X_pow, mul_one] at product power
    omega

/-- The highest numerator coefficient is a signed count of deficit-two cores. -/
theorem numerator_top_coeff {n : ℕ} (order : 2 ≤ n) :
    (numerator n).coeff (8 * n - 5) =
      ∑ a : Cores n, if totalDefect a = 2 then
        (-1 : ℚ) ^ (3 * n - Nat.card (Active a)) else 0 := by
  classical
  rw [numerator, Polynomial.finsetSum_coeff]
  exact Finset.sum_congr rfl (fun a _ ↦ cell_top_coeff a order)

/-- Cancellation in the thin top layer is exactly a one-degree improvement. -/
theorem numerator_degree_improves_iff {n : ℕ} (order : 2 ≤ n) :
    (numerator n).natDegree ≤ 8 * n - 6 ↔
      (∑ a : Cores n, if totalDefect a = 2 then
        (-1 : ℚ) ^ (3 * n - Nat.card (Active a)) else 0) = 0 := by
  rw [← numerator_top_coeff order]
  constructor
  · intro smaller
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    omega
  · intro zero
    have bound := numerator_degree n
    unfold polynomialBound at bound
    rw [ite_eq_right (by omega : n ≠ 1)] at bound
    have upper : (numerator n).natDegree ≤ 8 * n - 5 := by omega
    have improved := Polynomial.natDegree_le_pred upper zero
    omega

/-- A top-layer cancellation extends the proved polynomial range by one index. -/
theorem eventualPolynomial_eval_of_top_cancel {n : ℕ} (order : 2 ≤ n)
    (cancel : (∑ a : Cores n, if totalDefect a = 2 then
      (-1 : ℚ) ^ (3 * n - Nat.card (Active a)) else 0) = 0)
    (m : ℕ) (large : 5 * n - 5 ≤ m) :
    (eventualPolynomial n).eval (m : ℚ) =
      (Nat.card {c : VirtualHand n // IsFullWait m c} : ℚ) := by
  apply eventualPolynomial_eval_from_start (by omega) m
  have degree := (numerator_degree_improves_iff order).mpr cancel
  unfold polynomialStart
  omega

/-- There are only weak-composition-many deficit-two patterns to consider. -/
theorem defect_pattern_card (n : ℕ) :
    Nat.card {d : Rank n → ℕ // ∑ i, d i = 2} = Nat.multichoose (3 * n) 2 := by
  rw [← Nat.card_congr (Sym.equivNatSumOfFintype (Rank n) 2),
    Sym.natCard_sym_eq_multichoose]
  simp [Rank]

/-- Six ranks have twenty-one deficit-two patterns, independent of any winning test. -/
theorem six_rank_defect_pattern_card :
    Nat.card {d : Rank 2 → ℕ // ∑ i, d i = 2} = 21 := by
  rw [defect_pattern_card]
  norm_num [Nat.multichoose]

/-- A top-layer core is reconstructed from an activity mask and a deficit-two pattern. -/
theorem top_core_reconstruct {n : ℕ} (a : Cores n) (top : totalDefect a = 2) :
    ∃ d : Rank n → Fin 3, (∑ i, (d i).val) = 2 ∧
      ∀ i, a.val i = abundanceThreshold i - 1 +
        (if abundanceThreshold i ≤ a.val i then 3 else 0) - (d i).val := by
  have bound (i : Rank n) : bandDefect a i < 3 := by
    have upper := Finset.single_le_sum (fun j _ ↦ Nat.zero_le (bandDefect a j))
      (Finset.mem_univ i)
    change bandDefect a i ≤ totalDefect a at upper
    omega
  refine ⟨fun i ↦ ⟨bandDefect a i, bound i⟩, top, ?_⟩
  intro i
  have gap : (bandDefect a i : ℤ) = bandTop a i - a.val i :=
    Int.toNat_of_nonneg (sub_nonneg.mpr (bandTop_le a i))
  change a.val i = abundanceThreshold i - 1 + _ - (bandDefect a i : ℤ)
  rw [gap, bandTop]
  ring

/-- The thin top layer is encoded by its defect pattern and activity mask. -/
def topEncode {n : ℕ} (a : {a : Cores n // totalDefect a = 2}) :
    {d : Rank n → ℕ // ∑ i, d i = 2} × (Rank n → Bool) :=
  (⟨bandDefect a.val, a.property⟩,
    fun i ↦ decide (abundanceThreshold i ≤ a.val.val i))

/-- No two top-layer cores share a pattern and activity mask. -/
theorem topEncode_injective (n : ℕ) : Function.Injective (@topEncode n) := by
  intro a b same
  apply Subtype.ext
  apply Subtype.ext
  funext i
  have defects := congrArg (fun p ↦ p.1.val i) same
  have masks := congrArg (fun p ↦ p.2 i) same
  change bandDefect a.val i = bandDefect b.val i at defects
  change decide (abundanceThreshold i ≤ a.val.val i) =
    decide (abundanceThreshold i ≤ b.val.val i) at masks
  have active := decide_eq_decide.mp masks
  have ga : (bandDefect a.val i : ℤ) = bandTop a.val i - a.val.val i :=
    Int.toNat_of_nonneg (sub_nonneg.mpr (bandTop_le a.val i))
  have gb : (bandDefect b.val i : ℤ) = bandTop b.val i - b.val.val i :=
    Int.toNat_of_nonneg (sub_nonneg.mpr (bandTop_le b.val i))
  have same_top : bandTop a.val i = bandTop b.val i := by simp only [bandTop, active]
  rw [defects, same_top] at ga
  omega

/-- At most 1344 six-rank cores can affect the coefficient of degree eleven. -/
theorem six_rank_top_card_le :
    Nat.card {a : Cores 2 // totalDefect a = 2} ≤ 1344 := by
  let : Finite {d : Rank 2 → ℕ // ∑ i, d i = 2} :=
    Nat.finite_of_card_ne_zero (by rw [six_rank_defect_pattern_card]; norm_num)
  have bound := Nat.card_le_card_of_injective (@topEncode 2) (topEncode_injective 2)
  rw [Nat.card_prod, six_rank_defect_pattern_card, Nat.card_fun] at bound
  norm_num [Rank] at bound ⊢
  exact bound

end Mahjong.VirtualHand.TripletCore
