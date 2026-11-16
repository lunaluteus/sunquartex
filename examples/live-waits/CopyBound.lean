/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
import Ninegates

/-! A full-sided wait needs three copies of at least one rank. Consequently,
any live full-sided wait needs a physical copy bound of at least four.
The proof compares class sizes in two winning draws; it does not enumerate hands. -/

open Mahjong Mahjong.VirtualHand

namespace Mahjong.VirtualHand

private lemma DrawPair.classSize_le_of_not_draw {n : ℕ} {c : VirtualHand n}
    {i j : Rank n} (edge : DrawPair c i j) (upper : ∀ k, c k ≤ 2)
    {r s : ZMod 3} (outside : r ≠ rankClass i) :
    classSize r (c + single i - pair j) ≤ classSize s (c + single i - pair j) := by
  by_contra bad
  have gap : classSize s (c + single i - pair j) <
      classSize r (c + single i - pair j) := by omega
  obtain ⟨k, class_k, three, _⟩ := Meldable.exists_triplet_of_classSize_lt edge r s gap
  have different : k ≠ i := by
    intro same
    exact outside (class_k.symm.trans (congrArg rankClass same))
  have bound := upper k
  have pair_nonnegative : 0 ≤ pair j k := nonnegative_pair j k
  change 3 ≤ c k + single i k - pair j k at three
  rw [single_of_ne different] at three
  omega

lemma IsFullWait.exists_three_copies {n m : ℕ} {c : VirtualHand n}
    (full : IsFullWait m c) : ∃ i : Rank n, 3 ≤ c i := by
  by_contra absent
  push Not at absent
  have upper (i : Rank n) : c i ≤ 2 := by have bound := absent i; omega
  have positive : 0 < n := by
    by_contra not_positive
    have zero : n = 0 := by omega
    subst n
    exact not_isFullWait_order_zero m c full
  obtain ⟨i, fixed_i⟩ := exists_rankClass positive (fixedClass c)
  obtain ⟨j, fixed_edge⟩ := (isFullWait_iff.mp full).2.2 i
  have fixed_j := fixed_edge.fixed_class_iff.mp fixed_i
  obtain ⟨a, class_a⟩ := exists_rankClass positive (fixedClass c + 1)
  have nonfixed_a : rankClass a ≠ fixedClass c := by
    rw [class_a]
    intro same
    have zero : (1 : ZMod 3) = 0 := by linear_combination same
    norm_num at zero
  obtain ⟨b, other_edge⟩ := (isFullWait_iff.mp full).2.2 a
  have nonfixed_b : rankClass b ≠ fixedClass c := by
    intro same
    exact nonfixed_a (other_edge.fixed_class_iff.mpr same)
  have smaller := fixed_edge.classSize_le_of_not_draw upper
    (r := rankClass b) (s := fixedClass c) (by rwa [fixed_i])
  have larger := other_edge.classSize_le_of_not_draw upper
    (r := fixedClass c) (s := rankClass b) nonfixed_a.symm
  simp only [map_sub, map_add, classSize_pair, classSize_single, fixed_i, fixed_j,
    ite_eq_right nonfixed_b.symm, ite_true, mul_zero, mul_one, add_zero, sub_zero] at smaller
  simp only [map_sub, map_add, classSize_pair, classSize_single,
    ite_eq_right nonfixed_a, ite_eq_right nonfixed_b,
    ite_eq_right (other_edge.nonfixed_classes nonfixed_a), ite_true,
    mul_zero, mul_one, add_zero, sub_zero] at larger
  omega

lemma IsLiveFullWait.four_le_cap {n cap m : ℕ} {c : VirtualHand n}
    (live : IsLiveFullWait cap m c) : 4 ≤ cap := by
  obtain ⟨i, three⟩ := live.1.exists_three_copies
  have upper := (isLiveFullWait_iff.mp live).2 i
  omega

lemma exists_live_some_meldCount_iff {n cap : ℕ} (positive : 0 < n) :
    (∃ m, ∃ c : VirtualHand n, IsLiveFullWait cap m c) ↔ 4 ≤ cap := by
  constructor
  · rintro ⟨m, c, live⟩
    exact live.four_le_cap
  · intro bound
    refine ⟨n + 1, Standard.A n, isLiveFullWait_iff.mpr
      ⟨Standard.A_full_positive positive, fun i ↦ ?_⟩⟩
    rw [Standard.A_apply]
    split_ifs <;> omega

end Mahjong.VirtualHand
