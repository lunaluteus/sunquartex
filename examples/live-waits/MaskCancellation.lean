/-
Copyright (c) 2026 Luna Luteus. Released under Apache 2.0.
Authors: Luna Luteus
-/
import TopLayer

/-! Sign-reversing Boolean-mask cancellation at any irrelevant coordinate. -/

namespace Mahjong.VirtualHand.TripletCore

/-- Each inactive coordinate contributes a minus sign. -/
def maskSign {α : Type*} [Fintype α] (b : α → Bool) : ℚ :=
  ∏ i, if b i then 1 else -1

/-- Toggle one coordinate of a Boolean mask. -/
def flipMask {α : Type*} [DecidableEq α] (b : α → Bool) (i : α) : α → Bool :=
  Function.update b i (!(b i))

/-- Toggling twice returns the original mask. -/
theorem flipMask_involutive {α : Type*} [DecidableEq α] (b : α → Bool) (i : α) :
    flipMask (flipMask b i) i = b := by
  funext j
  by_cases same : j = i
  · subst j
    simp [flipMask]
  · simp [flipMask, same]

/-- A toggle has no fixed mask. -/
theorem flipMask_ne {α : Type*} [DecidableEq α] (b : α → Bool) (i : α) :
    flipMask b i ≠ b := by
  intro equal
  have at_i := congrFun equal i
  cases flag : b i <;> simp [flipMask, flag] at at_i

/-- A toggle reverses the sign of a mask. -/
theorem maskSign_flip {α : Type*} [Fintype α] [DecidableEq α] (b : α → Bool) (i : α) :
    maskSign (flipMask b i) = -maskSign b := by
  have original := Finset.mul_prod_erase Finset.univ
    (fun j ↦ if b j then (1 : ℚ) else -1) (Finset.mem_univ i)
  have flipped := Finset.mul_prod_erase Finset.univ
    (fun j ↦ if flipMask b i j then (1 : ℚ) else -1) (Finset.mem_univ i)
  have rest : (∏ j ∈ Finset.univ.erase i, if flipMask b i j then (1 : ℚ) else -1) =
      ∏ j ∈ Finset.univ.erase i, if b j then (1 : ℚ) else -1 := by
    apply Finset.prod_congr rfl
    intro j member
    have different := (Finset.mem_erase.mp member).1
    simp [flipMask, different]
  unfold maskSign
  rw [← original, ← flipped, rest]
  cases flag : b i <;> simp [flipMask, flag]

/-- If a predicate ignores one bit, its signed mask sum vanishes. -/
theorem signed_mask_sum_eq_zero {α : Type*} [Fintype α] [DecidableEq α]
    (P : (α → Bool) → Prop) [DecidablePred P] (i : α)
    (invariant : ∀ b, P (flipMask b i) ↔ P b) :
    (∑ b : α → Bool, if P b then maskSign b else 0) = 0 := by
  apply Finset.sum_ninvolution (fun b ↦ flipMask b i)
  · intro b
    by_cases full : P b <;> simp [invariant b, full, maskSign_flip]
  · intro b _
    exact flipMask_ne b i
  · intro b
    exact Finset.mem_univ _
  · intro b
    exact flipMask_involutive b i

end Mahjong.VirtualHand.TripletCore
