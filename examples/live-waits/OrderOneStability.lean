/-
Copyright (c) 2026 Luna Luteus. Released under Apache 2.0.
Authors: Luna Luteus
-/
import OrderOneDuality

/-! The sharp copy cap at which every three-rank full wait becomes live. -/

open Mahjong Mahjong.VirtualHand

namespace Mahjong.VirtualHand.OrderOne.Stability

private lemma coordinate_bound {m : ℕ} {c : VirtualHand 1} (s : ZMod 3)
    (count : size c = 3 * (m : ℤ) + 1) (fixed : fixedClass c = s)
    (lower : pairThreshold s ≤ c) (i : Rank 1) : c i ≤ 3 * (m : ℤ) - 3 := by
  have table (t : ZMod 3) : pairThreshold t = ![![2, 2, 1], ![1, 2, 2], ![2, 1, 2]] t := by
    ext j
    fin_cases t <;> fin_cases j <;> decide +kernel
  rw [table] at lower
  have lo0 := lower 0
  have lo1 := lower 1
  have lo2 := lower 2
  have total : c 0 + c 1 + c 2 = 3 * (m : ℤ) + 1 := by
    simpa [size, Fin.sum_univ_succ, add_assoc] using count
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_iff 3 (rankSum c) s).mp fixed
  have weighted : c 0 + 2 * c 1 + 3 * c 2 = s.val + 3 * k := by
    simpa [rankSum, rank, Fin.sum_univ_succ, add_assoc] using hk
  fin_cases s <;> fin_cases i <;> dsimp at lo0 lo1 lo2 <;>
    norm_num [ZMod.val] at lo0 lo1 lo2 weighted ⊢ <;> omega

lemma full_coordinate_bound {m : ℕ} {c : VirtualHand 1} (full : IsFullWait m c)
    (i : Rank 1) : c i ≤ 3 * (m : ℤ) - 3 :=
  coordinate_bound (fixedClass c) full.2.1 rfl ((full_iff c).mp full).2 i

theorem live_iff_full {cap m : ℕ} (bound : 3 * m - 2 ≤ cap) (c : VirtualHand 1) :
    IsLiveFullWait cap m c ↔ IsFullWait m c := by
  refine ⟨fun live ↦ live.1, fun full ↦ isLiveFullWait_iff.mpr ⟨full, fun i ↦ ?_⟩⟩
  have at_i := full_coordinate_bound full i
  have positive := full.meldCount_gt_order
  omega

theorem live_card_stable {cap m : ℕ} (bound : 3 * m - 2 ≤ cap) :
    Nat.card {c : VirtualHand 1 // IsLiveFullWait cap m c} = (3 * m - 2).choose 2 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (live_iff_full bound))]
  exact orderOne_fullWait_card m

/-- A full wait attaining the largest possible coordinate. -/
def extremal (m : ℕ) : VirtualHand 1 := ![3 * (m : ℤ) - 3, 1, 3]

lemma extremal_full {m : ℕ} (order : 2 ≤ m) : IsFullWait m (extremal m) := by
  have weighted : rankSum (extremal m) = 3 * (m : ℤ) + 8 := by
    simp [rankSum, rank, extremal, Fin.sum_univ_succ]
    ring
  have fixed : fixedClass (extremal m) = 2 := by
    rw [fixedClass, weighted, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_ofNat]
    rw [show (3 : ZMod 3) = 0 from ZMod.natCast_self 3, zero_mul, zero_add]
    decide +kernel
  apply (full_iff _).mpr
  constructor
  · simp [size, extremal, Fin.sum_univ_succ]
    ring
  · rw [fixed]
    have threshold : pairThreshold (2 : ZMod 3) = ![2, 1, 2] := by
      ext i
      fin_cases i <;> decide +kernel
    rw [threshold]
    intro i
    fin_cases i <;> dsimp [extremal] <;> omega

theorem all_full_live_iff {cap m : ℕ} (order : 2 ≤ m) :
    (∀ c : VirtualHand 1, IsFullWait m c → IsLiveFullWait cap m c) ↔ 3 * m - 2 ≤ cap := by
  constructor
  · intro all_live
    have live := all_live (extremal m) (extremal_full order)
    have upper := (isLiveFullWait_iff.mp live).2 (0 : Rank 1)
    change 3 * (m : ℤ) - 3 + 1 ≤ cap at upper
    omega
  · intro bound c full
    exact (live_iff_full bound c).mpr full

theorem live_card_lt {cap m : ℕ} (order : 2 ≤ m) (small : cap < 3 * m - 2) :
    Nat.card {c : VirtualHand 1 // IsLiveFullWait cap m c} < (3 * m - 2).choose 2 := by
  let Full := {c : VirtualHand 1 // IsFullWait m c}
  let Live := {c : VirtualHand 1 // IsLiveFullWait cap m c}
  let inclusion : Live → Full := fun c ↦ ⟨c.val, c.property.1⟩
  have injective : Function.Injective inclusion := by
    intro c d same
    exact Subtype.ext (congrArg (fun x : Full ↦ x.val) same)
  have finite_full : Finite Full := Nat.finite_of_card_ne_zero (by
    change Nat.card {c : VirtualHand 1 // IsFullWait m c} ≠ 0
    rw [orderOne_fullWait_card]
    exact ne_of_gt (Nat.choose_pos (by omega)))
  have finite_live : Finite Live := Finite.of_injective inclusion injective
  let := Fintype.ofFinite Full
  let := Fintype.ofFinite Live
  have not_surjective : ¬Function.Surjective inclusion := by
    intro onto
    obtain ⟨c, equal⟩ := onto ⟨extremal m, extremal_full order⟩
    have value : c.val = extremal m := congrArg Subtype.val equal
    have upper := (isLiveFullWait_iff.mp c.property).2 (0 : Rank 1)
    rw [value] at upper
    change 3 * (m : ℤ) - 3 + 1 ≤ cap at upper
    omega
  have strict := Fintype.card_lt_of_injective_not_surjective inclusion injective not_surjective
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at strict
  change Nat.card {c : VirtualHand 1 // IsLiveFullWait cap m c} <
    Nat.card {c : VirtualHand 1 // IsFullWait m c} at strict
  rwa [orderOne_fullWait_card] at strict

theorem live_card_stable_iff {cap m : ℕ} (order : 2 ≤ m) :
    Nat.card {c : VirtualHand 1 // IsLiveFullWait cap m c} = (3 * m - 2).choose 2 ↔
      3 * m - 2 ≤ cap := by
  constructor
  · intro equal
    by_contra small
    have strict := live_card_lt order (Nat.lt_of_not_ge small)
    omega
  · exact live_card_stable

theorem live_card_top {cap : ℕ} (large : 4 ≤ cap) :
    Nat.card {c : VirtualHand 1 // IsLiveFullWait cap (cap - 2) c} = 6 := by
  rw [← live_card_symmetry cap 2 (by omega), live_card_stable (by omega)]
  decide +kernel

end Mahjong.VirtualHand.OrderOne.Stability
