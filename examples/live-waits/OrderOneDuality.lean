/-
Copyright (c) 2026 Luna Luteus. Released under Apache 2.0.
Authors: Luna Luteus
-/
import Ninegates

/-! A complement involution for three-rank live full-sided waits. -/

open Mahjong Mahjong.VirtualHand

namespace Mahjong.VirtualHand.OrderOne

/-- Reflect each coordinate between its full-wait threshold and `cap - 1`.
The subtraction in the constant hand is in the integers. -/
def dual (cap : ℕ) (c : VirtualHand 1) : VirtualHand 1 :=
  (fun _ ↦ (cap : ℤ) - 1) - c + pairThreshold (fixedClass c)

lemma dual_apply (cap : ℕ) (c : VirtualHand 1) (i : Rank 1) :
    dual cap c i = (cap : ℤ) - 1 - c i + pairThreshold (fixedClass c) i := rfl

lemma fixedClass_dual (cap : ℕ) (c : VirtualHand 1) :
    fixedClass (dual cap c) = fixedClass c := by
  simp only [dual, fixedClass, map_add, map_sub, Int.cast_add, Int.cast_sub,
    rankSum_const_cast, rankSum_pairThreshold]
  have three : (3 : ZMod 3) * (rankSum c : ZMod 3) = 0 := by
    rw [show (3 : ZMod 3) = 0 from ZMod.natCast_self 3, zero_mul]
  linear_combination -three

lemma dual_involutive (cap : ℕ) : Function.Involutive (dual cap) := by
  intro c
  ext i
  simp only [dual_apply, fixedClass_dual]
  ring

lemma size_dual (cap : ℕ) (c : VirtualHand 1) :
    size (dual cap c) = 3 * (cap : ℤ) - size c + 2 := by
  rw [dual, map_add, map_sub, size_const, size_pairThreshold]
  ring

lemma live_meldCount_le_cap {cap m : ℕ} {c : VirtualHand 1}
    (live : IsLiveFullWait cap m c) : m ≤ cap := by
  have upper := (isLiveFullWait_iff.mp live).2
  have bound : size c ≤ size (fun _ : Rank 1 ↦ (cap : ℤ) - 1) := by
    simp only [size, LinearMap.coe_mk, AddHom.coe_mk]
    apply Finset.sum_le_sum
    intro i _
    have := upper i
    omega
  rw [size_const, live.1.2.1] at bound
  norm_num at bound
  omega

lemma dual_live {cap m : ℕ} {c : VirtualHand 1}
    (live : IsLiveFullWait cap m c) : IsLiveFullWait cap (cap - m) (dual cap c) := by
  have count := live_meldCount_le_cap live
  obtain ⟨full, upper⟩ := isLiveFullWait_iff.mp live
  obtain ⟨size_c, lower⟩ := (full_iff c).mp full
  apply isLiveFullWait_iff.mpr
  constructor
  · apply (full_iff _).mpr
    constructor
    · rw [size_dual, size_c]
      omega
    · intro i
      rw [fixedClass_dual, dual_apply]
      have := upper i
      linarith
  · intro i
    rw [dual_apply]
    have := lower i
    linarith

/-- A concrete bijection exchanging meld counts `m` and `cap - m`. -/
def liveDualEquiv (cap m : ℕ) (bound : m ≤ cap) :
    {c : VirtualHand 1 // IsLiveFullWait cap m c} ≃
      {c : VirtualHand 1 // IsLiveFullWait cap (cap - m) c} where
  toFun c := ⟨dual cap c, dual_live c.property⟩
  invFun c := ⟨dual cap c, by
    have live := dual_live c.property
    simpa only [Nat.sub_sub_self bound] using live⟩
  left_inv c := Subtype.ext (dual_involutive cap c)
  right_inv c := Subtype.ext (dual_involutive cap c)

theorem live_card_symmetry (cap m : ℕ) (bound : m ≤ cap) :
    Nat.card {c : VirtualHand 1 // IsLiveFullWait cap m c} =
      Nat.card {c : VirtualHand 1 // IsLiveFullWait cap (cap - m) c} :=
  Nat.card_congr (liveDualEquiv cap m bound)

end Mahjong.VirtualHand.OrderOne
