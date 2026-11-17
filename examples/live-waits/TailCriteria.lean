/-
Copyright (c) 2026 Luna Luteus. Released under Apache 2.0.
Authors: Luna Luteus
-/
import TripletCore

/-!
# Full waits above an arbitrary residue representative

Triplet multiplicities affect neither virtual meldability nor canonical sequence
coefficients. Full-sidedness is therefore a finite formula of linear inequalities
in those multiplicities, even when the residue representative has negative entries.
-/

open Mahjong Mahjong.VirtualHand

namespace Mahjong.VirtualHand.TripletCore

/-- A fixed residue representative gives a linear criterion for each draw-pair edge. -/
theorem drawPair_lift_iff {n : ℕ} (base : VirtualHand n) (t : Rank n → ℕ)
    (draw pairRank : Rank n) :
    DrawPair (lift base t) draw pairRank ↔
      VirtuallyMeldable (base + single draw - pair pairRank) ∧
        ∀ i, 0 ≤ canonicalTriplet (base + single draw - pair pairRank) i + (t i : ℤ) := by
  have shape : lift base t + single draw - pair pairRank =
      (base + single draw - pair pairRank) + (3 : ℤ) • (fun i ↦ (t i : ℤ)) := by
    unfold lift
    abel
  rw [DrawPair, shape, meldable_iff_scan]
  simp only [virtuallyMeldable_add_triplets_iff, canonicalTriplet_add_triplets]

/-- Size is affine in the triplet multiplicities, without assuming a positive base. -/
theorem size_lift {n : ℕ} (base : VirtualHand n) (t : Rank n → ℕ) :
    size (lift base t) = size base + 3 * (∑ i, t i : ℕ) := by
  rw [lift, map_add, map_smul]
  simp [size, Nat.cast_sum, Finset.mul_sum]

/-- Full-sidedness becomes a finite formula in the nonnegative tail variables. -/
theorem full_lift_iff_canonical {n k : ℕ} (base : VirtualHand n)
    (count : size base = 3 * (k : ℤ) + 1) (t : Rank n → ℕ) :
    IsFullWait (k + ∑ i, t i) (lift base t) ↔
      (∀ i, 0 ≤ base i + 3 * (t i : ℤ)) ∧
        ∀ draw, ∃ pairRank,
          VirtuallyMeldable (base + single draw - pair pairRank) ∧
            ∀ i, 0 ≤ canonicalTriplet (base + single draw - pair pairRank) i + (t i : ℤ) := by
  have total : size (lift base t) = 3 * ((k + ∑ i, t i : ℕ) : ℤ) + 1 := by
    rw [size_lift, count]
    push_cast
    ring
  rw [isFullWait_iff, total]
  simp only [true_and, drawPair_lift_iff]
  rfl

end Mahjong.VirtualHand.TripletCore
