/-
Copyright (c) 2026 Luna Luteus. Released under Apache 2.0.
Authors: Luna Luteus
-/
import MaskCancellation

/-! Two irrelevant bits cancel the weighted contribution to the next coefficient. -/

namespace Mahjong.VirtualHand.TripletCore

/-- The next coefficient of a cell: its sign times minus the number of inactive ranks. -/
def maskNextSign {α : Type*} [Fintype α] (b : α → Bool) : ℚ :=
  -(∑ i, if b i then 0 else maskSign b)

/-- The weighted mask sign is the sign multiplied by minus its inactive cardinality. -/
theorem maskNextSign_eq {α : Type*} [Fintype α] (b : α → Bool) :
    maskNextSign b = -(Nat.card {i : α // b i = false} : ℚ) * maskSign b := by
  classical
  have count : (∑ i, if b i then (0 : ℚ) else maskSign b) =
      (Nat.card {i : α // b i = false} : ℚ) * maskSign b := by
    calc
      _ = ∑ i, if b i = false then maskSign b else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        cases b i <;> rfl
      _ = _ := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
          ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  rw [maskNextSign, count]
  ring

/-- Two distinct free bits cancel the weighted signed mask sum as well. -/
theorem weighted_signed_sum_eq_zero {α : Type*} [Fintype α] [DecidableEq α]
    (P : (α → Bool) → Prop) [DecidablePred P] (i j : α) (different : i ≠ j)
    (free_i : ∀ b, P (flipMask b i) ↔ P b)
    (free_j : ∀ b, P (flipMask b j) ↔ P b) :
    (∑ b : α → Bool, if P b then maskNextSign b else 0) = 0 := by
  classical
  have expand (b : α → Bool) : (if P b then maskNextSign b else 0) =
      -(∑ k, if P b ∧ b k = false then maskSign b else 0) := by
    by_cases full : P b
    · simp only [full, ite_true, true_and, maskNextSign]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      cases b k <;> rfl
    · simp [full]
  simp_rw [expand]
  rw [Finset.sum_neg_distrib, Finset.sum_comm]
  apply neg_eq_zero.mpr
  apply Finset.sum_eq_zero
  intro k _
  by_cases same : k = i
  · apply signed_mask_sum_eq_zero _ j
    intro b
    rw [free_j b]
    have distinct : k ≠ j := by simpa only [same] using different
    simp [flipMask, distinct]
  · apply signed_mask_sum_eq_zero _ i
    intro b
    rw [free_i b]
    simp [flipMask, same]

end Mahjong.VirtualHand.TripletCore
