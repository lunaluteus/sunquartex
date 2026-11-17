/-
Copyright (c) 2026 Luna Luteus. Released under Apache 2.0.
Authors: Luna Luteus
-/
import SixRankEncoding
import MaskCancellation

/-! The degree-eleven numerator coefficient cancels by a free Boolean coordinate. -/

open Mahjong Mahjong.VirtualHand

namespace Mahjong.VirtualHand.TripletCore.SixRankTop

noncomputable instance fullCode_fintype : Fintype FullCode := Fintype.ofFinite _

/-- The coordinate-product sign agrees with the original core-cell sign. -/
theorem maskSign_topEncode (a : {a : Cores 2 // totalDefect a = 2}) :
    maskSign (topEncode a).2 = (-1 : ℚ) ^ (6 - Nat.card (Active a.val)) := by
  classical
  unfold maskSign
  simp only [topEncode, decide_eq_true_eq]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
  have card := Fintype.card_subtype_compl (fun i : Rank 2 ↦ abundanceThreshold i ≤ a.val.val i)
  rw [Fintype.card_subtype] at card
  have inactive : (Finset.univ.filter (fun i : Rank 2 ↦ ¬abundanceThreshold i ≤ a.val.val i)).card =
      6 - Nat.card (Active a.val) := by
    simpa [Rank, Nat.card_eq_fintype_card] using card
  rw [inactive]

/-- Toggling a mask is the corresponding update of its natural triplet tail. -/
theorem maskTail_flip (b : Rank 2 → Bool) (i : Rank 2) :
    maskTail (flipMask b i) = Function.update (maskTail b) i (!(b i)).toNat := by
  funext j
  by_cases same : j = i
  · subst j
    simp [maskTail, flipMask]
  · simp [maskTail, flipMask, same]

open Classical in
/-- The signed full-mask count is zero separately at every deficit pattern. -/
theorem pattern_signed_sum (d : Pattern) :
    (∑ b : Rank 2 → Bool, if IsFullWait (5 + ∑ i, maskTail b i) (maskHand d b)
      then maskSign b else 0) = 0 := by
  classical
  obtain ⟨i, free⟩ := exists_free_coordinate_of_defect d.val d.property
  apply signed_mask_sum_eq_zero _ i
  intro b
  have h := (free (maskTail b) (!(b i)).toNat).trans
    (free (maskTail b) (b i).toNat).symm
  have same : Function.update (maskTail b) i (b i).toNat = maskTail b := by
    change Function.update (maskTail b) i (maskTail b i) = maskTail b
    exact Function.update_eq_self i (maskTail b)
  rw [same] at h
  simpa only [maskHand, maskTail_flip] using h

/-- The entire defect-two core sum cancels, without evaluating core cardinalities. -/
theorem top_signed_sum :
    (∑ a : Cores 2, if totalDefect a = 2 then
      (-1 : ℚ) ^ (6 - Nat.card (Active a)) else 0) = 0 := by
  classical
  have restrict : (∑ a : Cores 2, if totalDefect a = 2 then
      (-1 : ℚ) ^ (6 - Nat.card (Active a)) else 0) =
      ∑ a : {a : Cores 2 // totalDefect a = 2},
        (-1 : ℚ) ^ (6 - Nat.card (Active a.val)) := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (fun a ↦ by simp) _
  rw [restrict]
  have reindex := Fintype.sum_equiv codeEquiv
    (fun a ↦ (-1 : ℚ) ^ (6 - Nat.card (Active a.val)))
    (fun p : FullCode ↦ maskSign p.val.2) (fun a ↦ (maskSign_topEncode a).symm)
  rw [reindex]
  have expand : (∑ p : FullCode, maskSign p.val.2) =
      ∑ p : Pattern × (Rank 2 → Bool),
        if IsFullWait (5 + ∑ i, maskTail p.2 i) (maskHand p.1 p.2)
        then maskSign p.2 else 0 := by
    symm
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (fun p ↦ by simp) _
  rw [expand, Fintype.sum_prod_type]
  exact Finset.sum_eq_zero (fun d _ ↦ pattern_signed_sum d)

/-- The only possibly nonzero coefficient above degree ten vanishes. -/
theorem numerator_coeff_eleven : (numerator 2).coeff 11 = 0 := by
  exact (numerator_top_coeff (show 2 ≤ 2 by omega)).trans top_signed_sum

/-- The six-rank numerator has degree at most ten. -/
theorem numerator_degree_ten : (numerator 2).natDegree ≤ 10 := by
  have h := (numerator_degree_improves_iff (show 2 ≤ 2 by omega)).mpr top_signed_sum
  norm_num at h
  exact h

/-- The exact-numerator starting index is at most five for six ranks. -/
theorem polynomialStart_le_five : polynomialStart 2 ≤ 5 := by
  have degree := numerator_degree_ten
  unfold polynomialStart
  omega

/-- The six-rank counting polynomial is valid from five melds onward. -/
theorem counting_from_five (m : ℕ) (large : 5 ≤ m) :
    (eventualPolynomial 2).eval (m : ℚ) =
      (Nat.card {c : VirtualHand 2 // IsFullWait m c} : ℚ) := by
  exact eventualPolynomial_eval_of_top_cancel (show 2 ≤ 2 by omega) top_signed_sum m large

end Mahjong.VirtualHand.TripletCore.SixRankTop
