/-
Copyright (c) 2026 Luna Luteus. Released under Apache 2.0.
Authors: Luna Luteus
-/
import LiveMaximum
import CopyBound

/-! The exact existence spectrum for live full-sided waits at arbitrary copy cap.
Adding one complete layer of disjoint sequences raises the cap by one and the
meld count by the order. This fills every interval beyond the cap-four case. -/

open Mahjong Mahjong.VirtualHand

namespace Mahjong.VirtualHand.LiveSpectrum

/-- One copy of every rank, partitioned into `n` disjoint sequences. -/
def layer (n : ℕ) : VirtualHand n := segment 0 (3 * n)

lemma layer_apply (n : ℕ) (i : Rank n) : layer n i = 1 := by
  simp [layer, segment_apply, i.isLt]

lemma layer_sequential (n : ℕ) : Sequential (layer n) :=
  sequential_segment (by omega) le_rfl (by omega)

lemma layer_size (n : ℕ) : size (layer n) = 3 * (n : ℤ) := by
  simpa [layer] using (size_segment (n := n) (a := 0) (b := 3 * n) le_rfl)

lemma mono_cap {n cap larger m : ℕ} {c : VirtualHand n}
    (live : IsLiveFullWait cap m c) (bound : cap ≤ larger) :
    IsLiveFullWait larger m c := by
  apply isLiveFullWait_iff.mpr
  refine ⟨live.1, fun i ↦ ?_⟩
  have at_i := (isLiveFullWait_iff.mp live).2 i
  have cast : (cap : ℤ) ≤ larger := by exact_mod_cast bound
  exact at_i.trans cast

lemma add_layer {n cap m : ℕ} {c : VirtualHand n}
    (live : IsLiveFullWait cap m c) :
    IsLiveFullWait (cap + 1) (m + n) (c + layer n) := by
  apply isLiveFullWait_iff.mpr
  refine ⟨live.1.add_meldable (layer_sequential n).meldable (layer_size n), fun i ↦ ?_⟩
  have at_i := (isLiveFullWait_iff.mp live).2 i
  simp only [Pi.add_apply, layer_apply]
  push_cast
  omega

private lemma exists_with_offset (k n m : ℕ) (lower : n < m)
    (upper : m < n * (k + 3)) :
    ∃ c : VirtualHand n, IsLiveFullWait (k + 4) m c := by
  induction k generalizing m with
  | zero =>
    exact (LiveMaximum.exists_live_iff n m).mpr
      ⟨lower, by simpa only [Nat.zero_add, Nat.mul_comm] using upper⟩
  | succ k ih =>
    change m < n * ((k + 1) + 3) at upper
    by_cases base : m < 3 * n
    · obtain ⟨c, live⟩ := (LiveMaximum.exists_live_iff n m).mpr ⟨lower, base⟩
      exact ⟨c, mono_cap live (by omega)⟩
    · have positive : 0 < n := by
        by_contra absent
        have zero : n = 0 := by omega
        simp [zero] at upper
      have shift : (k + 1) + 3 = (k + 3) + 1 := by omega
      have upper_sum : m < n * (k + 3) + n := by
        simpa only [shift, Nat.mul_add, Nat.mul_one] using upper
      have lower_reduced : n < m - n := by omega
      have upper_reduced : m - n < n * (k + 3) := by omega
      obtain ⟨c, live⟩ := ih (m - n) lower_reduced upper_reduced
      refine ⟨c + layer n, ?_⟩
      have count : m - n + n = m := Nat.sub_add_cancel (Nat.le_of_lt lower)
      have cap : (k + 4) + 1 = (k + 1) + 4 := by omega
      simpa only [count, cap] using add_layer live

theorem exists_live_iff (n cap m : ℕ) :
    (∃ c : VirtualHand n, IsLiveFullWait cap m c) ↔
      4 ≤ cap ∧ n < m ∧ m < n * (cap - 1) := by
  constructor
  · rintro ⟨c, live⟩
    exact ⟨live.four_le_cap, live.1.meldCount_gt_order, live.meldCount_lt_copyCapacity⟩
  · rintro ⟨cap_lower, lower, upper⟩
    have shifted : cap - 4 + 4 = cap := by omega
    have predecessor : cap - 4 + 3 = cap - 1 := by omega
    obtain ⟨c, live⟩ := exists_with_offset (cap - 4) n m lower
      (by simpa only [predecessor] using upper)
    exact ⟨c, by simpa only [shifted] using live⟩

theorem maximum {n cap : ℕ} (positive : 0 < n) (cap_lower : 4 ≤ cap) :
    (∃ c : VirtualHand n, IsLiveFullWait cap (n * (cap - 1) - 1) c) ∧
      ∀ m, (∃ c : VirtualHand n, IsLiveFullWait cap m c) →
        m ≤ n * (cap - 1) - 1 := by
  have capacity : 3 * n ≤ n * (cap - 1) := by
    calc
      3 * n = n * 3 := Nat.mul_comm _ _
      _ ≤ n * (cap - 1) := Nat.mul_le_mul_left _ (by omega)
  refine ⟨(exists_live_iff n cap _).mpr ⟨cap_lower, by omega, by omega⟩, ?_⟩
  rintro m ⟨c, live⟩
  have upper := live.meldCount_lt_copyCapacity
  omega

/-- The cap-four extremal hand with `cap - 4` complete layers added. -/
def extremal (n cap : ℕ) : VirtualHand n :=
  LiveMaximum.hand n + ((cap - 4 : ℕ) : ℤ) • layer n

lemma extremal_apply {n cap : ℕ} (positive : 0 < n) (cap_lower : 4 ≤ cap)
    (i : Rank n) :
    extremal n cap i = if i.val = 3 * n - 2 then (cap : ℤ) - 3 else cap - 1 := by
  simp only [extremal, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    layer_apply, mul_one, LiveMaximum.hand_apply positive]
  split_ifs <;> omega

lemma extremal_live {n cap : ℕ} (positive : 0 < n) (cap_lower : 4 ≤ cap) :
    IsLiveFullWait cap (n * (cap - 1) - 1) (extremal n cap) := by
  apply isLiveFullWait_iff.mpr
  constructor
  · have sequential := (layer_sequential n).smul
      (show (0 : ℤ) ≤ ((cap - 4 : ℕ) : ℤ) by exact_mod_cast Nat.zero_le (cap - 4))
    have count : size (((cap - 4 : ℕ) : ℤ) • layer n) =
        3 * (((cap - 4) * n : ℕ) : ℤ) := by
      rw [map_smul, layer_size]
      simp only [smul_eq_mul, Nat.cast_mul]
      ring
    have full := (LiveMaximum.hand_full positive).add_meldable sequential.meldable count
    have predecessor : cap - 1 = (cap - 4) + 3 := by omega
    have total : n * (cap - 1) = 3 * n + (cap - 4) * n := by
      rw [predecessor]
      ring
    have index : 3 * n - 1 + (cap - 4) * n = n * (cap - 1) - 1 := by
      rw [total]
      omega
    simpa only [index, extremal] using full
  · intro i
    rw [extremal_apply positive cap_lower]
    split_ifs <;> omega

end Mahjong.VirtualHand.LiveSpectrum
