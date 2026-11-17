/-
Copyright (c) 2026 Luna Luteus. Released under Apache 2.0.
Authors: Luna Luteus
-/
import SixRankTop

/-! A full parametrization of the six-rank deficit-two layer by patterns and masks. -/

open Mahjong Mahjong.VirtualHand

namespace Mahjong.VirtualHand.TripletCore.SixRankTop

/-- Natural deficit patterns of total two. -/
abbrev Pattern := {d : Rank 2 → ℕ // ∑ i, d i = 2}

noncomputable instance pattern_fintype : Fintype Pattern := by
  let : Finite Pattern := Nat.finite_of_card_ne_zero (by
    change Nat.card {d : Rank 2 → ℕ // ∑ i, d i = 2} ≠ 0
    rw [six_rank_defect_pattern_card]
    norm_num)
  exact Fintype.ofFinite _

/-- The zero-or-one triplet multiplicity of a Boolean activity mask. -/
def maskTail (b : Rank 2 → Bool) (i : Rank 2) : ℕ := (b i).toNat

/-- Reconstruct a hand from its deficit pattern and activity mask. -/
def maskHand (d : Pattern) (b : Rank 2 → Bool) : VirtualHand 2 :=
  lift (defectBase d.val) (maskTail b)

/-- Codes whose reconstructed hand really is full-sided. -/
abbrev FullCode := {p : Pattern × (Rank 2 → Bool) //
  IsFullWait (5 + ∑ i, maskTail p.2 i) (maskHand p.1 p.2)}

/-- No coordinate of a deficit-two pattern exceeds two. -/
theorem pattern_le_two (d : Pattern) (i : Rank 2) : d.val i ≤ 2 := by
  have h := Finset.single_le_sum (fun j _ ↦ Nat.zero_le (d.val j)) (Finset.mem_univ i)
  rw [d.property] at h
  exact h

/-- Each reconstructed coordinate has the prescribed band endpoint and deficit. -/
theorem maskHand_apply (d : Pattern) (b : Rank 2 → Bool) (i : Rank 2) :
    maskHand d b i = abundanceThreshold i - 1 - (d.val i : ℤ) + 3 * (maskTail b i : ℤ) := rfl

/-- The activity mask is recovered exactly, even when an inactive coordinate is negative. -/
theorem maskHand_active (d : Pattern) (b : Rank 2 → Bool) (i : Rank 2) :
    abundanceThreshold i ≤ maskHand d b i ↔ b i = true := by
  have bound := pattern_le_two d i
  rw [maskHand_apply]
  cases flag : b i <;> simp [maskTail, flag] <;> omega

/-- Every residue representative in this layer has size sixteen. -/
theorem defectBase_size (d : Pattern) : size (defectBase d.val) = 16 := by
  obtain ⟨first, second, pattern⟩ := sum_two_representation d.val d.property
  rw [defectBase_eq_residueBase d.val first second pattern, residueBase_size]

/-- The grade of a mask hand is five plus its number of active coordinates. -/
theorem maskHand_size (d : Pattern) (b : Rank 2 → Bool) :
    size (maskHand d b) = 3 * ((5 + ∑ i, maskTail b i : ℕ) : ℤ) + 1 := by
  rw [maskHand, size_lift, defectBase_size]
  push_cast
  ring

/-- A full code reconstructs a bounded core. -/
def decode (p : FullCode) : Cores 2 :=
  ⟨maskHand p.val.1 p.val.2, ⟨p.property.1, by
    intro i
    rw [maskHand_apply]
    have positive : 0 ≤ (p.val.1.val i : ℤ) := by positivity
    cases flag : p.val.2 i <;> simp [maskTail, flag] <;> omega⟩,
    ⟨5 + ∑ i, maskTail p.val.2 i, p.property⟩⟩

/-- The defect pattern is recovered exactly from a decoded full code. -/
theorem decode_bandDefect (p : FullCode) (i : Rank 2) :
    bandDefect (decode p) i = p.val.1.val i := by
  have activity := maskHand_active p.val.1 p.val.2 i
  change abundanceThreshold i ≤ (decode p).val i ↔ p.val.2 i = true at activity
  unfold bandDefect bandTop
  simp only [activity]
  change ((abundanceThreshold i - 1 + (if p.val.2 i = true then 3 else 0) -
    maskHand p.val.1 p.val.2 i)).toNat = _
  rw [maskHand_apply]
  cases flag : p.val.2 i <;> simp [maskTail, flag]

/-- Decoding lands in the defect-two layer. -/
def decodeTop (p : FullCode) : {a : Cores 2 // totalDefect a = 2} :=
  ⟨decode p, by simpa only [totalDefect, decode_bandDefect] using p.val.1.property⟩

/-- Encoding after decoding recovers the original pattern and mask. -/
theorem topEncode_decode (p : FullCode) : topEncode (decodeTop p) = p.val := by
  apply Prod.ext
  · apply Subtype.ext
    funext i
    exact decode_bandDefect p i
  · funext i
    change decide (abundanceThreshold i ≤ maskHand p.val.1 p.val.2 i) = p.val.2 i
    simp [maskHand_active]

/-- Reconstructing the encoded pattern and mask returns the original full core. -/
theorem maskHand_topEncode (a : {a : Cores 2 // totalDefect a = 2}) :
    maskHand (topEncode a).1 (topEncode a).2 = a.val.val := by
  ext i
  have gap : (bandDefect a.val i : ℤ) = bandTop a.val i - a.val.val i :=
    Int.toNat_of_nonneg (sub_nonneg.mpr (bandTop_le a.val i))
  rw [maskHand_apply]
  change abundanceThreshold i - 1 - (bandDefect a.val i : ℤ) +
    3 * (maskTail (fun j ↦ decide (abundanceThreshold j ≤ a.val.val j)) i : ℤ) = _
  rw [gap]
  by_cases active : abundanceThreshold i ≤ a.val.val i
  · simp [maskTail, bandTop, active]
    ring
  · simp [maskTail, bandTop, active]

/-- Encode a top-layer full core as a full pattern-mask code. -/
def encodeTop (a : {a : Cores 2 // totalDefect a = 2}) : FullCode :=
  ⟨topEncode a, by
    have full := full_grade a.val.property.2
    have count := maskHand_size (topEncode a).1 (topEncode a).2
    rw [maskHand_topEncode, full.2.1] at count
    have grade_eq : grade a.val.val = 5 + ∑ i, maskTail (topEncode a).2 i := by omega
    change IsFullWait (5 + ∑ i, maskTail (topEncode a).2 i)
      (maskHand (topEncode a).1 (topEncode a).2)
    rw [maskHand_topEncode, ← grade_eq]
    exact full⟩

/-- Full deficit-two cores are exactly the full pattern-mask codes. -/
def codeEquiv : {a : Cores 2 // totalDefect a = 2} ≃ FullCode where
  toFun := encodeTop
  invFun := decodeTop
  left_inv a := by
    apply topEncode_injective 2
    exact topEncode_decode (encodeTop a)
  right_inv p := Subtype.ext (topEncode_decode p)

end Mahjong.VirtualHand.TripletCore.SixRankTop
