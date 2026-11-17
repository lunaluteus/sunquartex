/-
Copyright (c) 2026 Luna Luteus. Released under Apache 2.0.
Authors: Luna Luteus
-/
import TailCriteria

/-! Closed canonical scan formulas on six ranks, reusable across residue representatives. -/

open Mahjong Mahjong.VirtualHand

namespace Mahjong.VirtualHand.TripletCore.SixRankTop

/-- The seven prefix residues, including the initial zero and both final tests. -/
def scanStates (c : VirtualHand 2) : Fin 7 → ℤ :=
  ![0, c 0 % 3, (c 1 - c 0) % 3, (c 2 - c 1) % 3,
    (c 3 - c 2 + c 0) % 3, (c 4 - c 3 + c 1 - c 0) % 3,
    (c 5 - c 4 + c 2 - c 1) % 3]

/-- Six ranks need only these explicit linear prefix expressions modulo three. -/
theorem canonicalSequence_six (c : VirtualHand 2) (k : Fin 7) :
    canonicalSequence c k.val = scanStates c k := by
  fin_cases k <;>
    norm_num [canonicalSequence, sequenceScan, SequenceScan.run, coefficient, scanStates,
      Matrix.vecHead, Matrix.vecTail]
  all_goals (congr 1; ring)

/-- A natural-index form of the closed scan, for the triplet quotient formula. -/
theorem canonicalSequence_six_of_le (c : VirtualHand 2) (k : ℕ) (bound : k ≤ 6) :
    canonicalSequence c k = scanStates c ⟨k, by omega⟩ := canonicalSequence_six c ⟨k, by omega⟩

/-- All six canonical triplet quotients in a compact coordinate formula. -/
def scanTriplets (c : VirtualHand 2) : Rank 2 → ℤ :=
  ![c 0 / 3, (c 1 - scanStates c 1) / 3,
    (c 2 - scanStates c 2 - scanStates c 1) / 3,
    (c 3 - scanStates c 3 - scanStates c 2) / 3,
    (c 4 - scanStates c 4 - scanStates c 3) / 3,
    (c 5 - scanStates c 5 - scanStates c 4) / 3]

/-- The explicit quotient vector agrees with the library's canonical decomposition. -/
theorem canonicalTriplet_six (c : VirtualHand 2) (i : Rank 2) :
    canonicalTriplet c i = scanTriplets c i := by
  rw [canonicalTriplet_eq,
    canonicalSequence_six_of_le c i.val (by have h := i.isLt; omega),
    canonicalSequence_six_of_le c (i.val - 1) (by have h := i.isLt; omega)]
  fin_cases i <;> norm_num [scanTriplets, scanStates]

/-- The two final prefix residues decide virtual meldability. -/
theorem virtuallyMeldable_six (c : VirtualHand 2) :
    VirtuallyMeldable c ↔ scanStates c 6 = 0 ∧ scanStates c 5 = 0 := by
  rw [virtuallyMeldable_iff_canonicalSequence,
    canonicalSequence_six_of_le c 6 (by omega),
    canonicalSequence_six_of_le c 5 (by omega)]
  rfl

end Mahjong.VirtualHand.TripletCore.SixRankTop
