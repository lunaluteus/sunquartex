/-
Copyright (c) 2026 Luna Luteus. Released under Apache 2.0.
Authors: Luna Luteus
-/
import TopLayer

/-! The next numerator coefficient has contributions only from deficits two and five. -/

open Mahjong Mahjong.VirtualHand

namespace Mahjong.VirtualHand.TripletCore

private lemma coeff_one_sub_X_pred (q : ℕ) (positive : 0 < q) :
    ((1 - Polynomial.X : Polynomial ℚ) ^ q).coeff (q - 1) =
      (q : ℚ) * (-1 : ℚ) ^ (q - 1) := by
  have shape : (1 - Polynomial.X : Polynomial ℚ) ^ q =
      Polynomial.C ((-1 : ℚ) ^ q) * (Polynomial.X + Polynomial.C (-1)) ^ q := by
    calc
      (1 - Polynomial.X : Polynomial ℚ) ^ q =
          (Polynomial.C (-1) * (Polynomial.X + Polynomial.C (-1))) ^ q := by
        congr 1
        simp [sub_eq_add_neg, add_comm]
      _ = _ := by rw [mul_pow, ← map_pow]
  rw [shape, Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  simp [pow_succ, Nat.choose_succ_self_right]
  ring

/-- Only the first two defect layers affect the next numerator coefficient. -/
theorem cell_next_coeff {n : ℕ} (a : Cores n) (order : 2 ≤ n) :
    (Polynomial.X ^ grade a.val *
      (1 - Polynomial.X : Polynomial ℚ) ^ (3 * n - Nat.card (Active a))).coeff
        (8 * n - 6) =
      if totalDefect a = 2 then
        ((3 * n - Nat.card (Active a) : ℕ) : ℚ) *
          (-1 : ℚ) ^ (3 * n - Nat.card (Active a) - 1)
      else if totalDefect a = 5 then (-1 : ℚ) ^ (3 * n - Nat.card (Active a)) else 0 := by
  have ranks := Nat.card_le_card_of_injective
    (fun i : Active a ↦ i.val) Subtype.val_injective
  have rank_count : Nat.card (Rank n) = 3 * n := by simp [Rank]
  rw [rank_count] at ranks
  have gap := totalDefect_grade a order
  have linear : (1 - Polynomial.X : Polynomial ℚ).natDegree ≤ 1 := by
    simpa using Polynomial.natDegree_sub_le (1 : Polynomial ℚ) Polynomial.X
  by_cases two : totalDefect a = 2
  · rw [ite_eq_left two]
    by_cases empty : 3 * n - Nat.card (Active a) = 0
    · rw [empty]
      simp only [pow_zero, mul_one, Nat.cast_zero, zero_mul]
      rw [Polynomial.coeff_X_pow, ite_eq_right (by omega)]
    · have index : 8 * n - 6 =
          (3 * n - Nat.card (Active a) - 1) + grade a.val := by omega
      rw [index, Polynomial.coeff_X_pow_mul]
      exact coeff_one_sub_X_pred _ (by omega)
  · rw [ite_eq_right two]
    by_cases five : totalDefect a = 5
    · rw [ite_eq_left five]
      have index : 8 * n - 6 = (3 * n - Nat.card (Active a)) + grade a.val := by omega
      rw [index, Polynomial.coeff_X_pow_mul]
      have h := Polynomial.coeff_pow_of_natDegree_le
        (m := 3 * n - Nat.card (Active a)) linear
      simpa [Polynomial.coeff_one] using h
    · rw [ite_eq_right five]
      have smaller : grade a.val + (3 * n - Nat.card (Active a)) < 8 * n - 6 := by omega
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have product := Polynomial.natDegree_mul_le
        (p := (Polynomial.X ^ grade a.val : Polynomial ℚ))
        (q := (1 - Polynomial.X) ^ (3 * n - Nat.card (Active a)))
      have power := Polynomial.natDegree_pow_le_of_le (3 * n - Nat.card (Active a)) linear
      simp only [Polynomial.natDegree_X_pow, mul_one] at product power
      omega

/-- The next coefficient separates into a weighted top layer and a signed next layer. -/
theorem numerator_next_coeff {n : ℕ} (order : 2 ≤ n) :
    (numerator n).coeff (8 * n - 6) =
      (∑ a : Cores n, if totalDefect a = 2 then
        ((3 * n - Nat.card (Active a) : ℕ) : ℚ) *
          (-1 : ℚ) ^ (3 * n - Nat.card (Active a) - 1) else 0) +
      ∑ a : Cores n, if totalDefect a = 5 then
        (-1 : ℚ) ^ (3 * n - Nat.card (Active a)) else 0 := by
  classical
  rw [numerator, Polynomial.finsetSum_coeff, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [cell_next_coeff a order]
  by_cases two : totalDefect a = 2
  · simp [two]
  · simp [two]

end Mahjong.VirtualHand.TripletCore
