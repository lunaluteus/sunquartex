/-
Copyright (c) 2026 Luna Luteus. Released under Apache 2.0.
Authors: Luna Luteus
-/
import OrderOneBoxes
import OrderOneDuality
import Mathlib.Algebra.Polynomial.BigOperators

/-! The three-rank generating polynomial, with coefficients counting live waits. -/

open Mahjong Mahjong.VirtualHand Polynomial
open Mahjong.VirtualHand.OrderOne.Boxes

namespace Mahjong.VirtualHand.OrderOne.Generating

instance boxFintype (cap : ℕ) (r : Fin 3) : Fintype (Box cap r) := by
  unfold Box
  infer_instance

abbrev Coordinates (cap : ℕ) := Fin 3 × (r : Fin 3) × Box cap r
abbrev LiveHands (cap : ℕ) := {c : VirtualHand 1 // AllLive cap c}

@[instance_reducible]
noncomputable def liveFintype {cap : ℕ} (large : 4 ≤ cap) : Fintype (LiveHands cap) :=
  Fintype.ofEquiv (Coordinates cap) (liveBoxEquiv large)

/-- The meld count is recovered from the size of an actual waiting hand. -/
def meldCount (c : VirtualHand 1) : ℕ := (size c - 1).toNat / 3

lemma meldCount_of_live {cap m : ℕ} {c : VirtualHand 1} (live : IsLiveFullWait cap m c) :
    meldCount c = m := by
  unfold meldCount
  rw [live.1.2.1]
  omega

lemma live_iff_meldCount {cap m : ℕ} {c : VirtualHand 1} (live : AllLive cap c) :
    IsLiveFullWait cap m c ↔ meldCount c = m := by
  obtain ⟨k, hk⟩ := live
  constructor
  · exact meldCount_of_live
  · intro equal
    have same : k = m := (meldCount_of_live hk).symm.trans equal
    simpa only [same] using hk

/-- Every hand contributes one monomial at its uniquely determined meld count. -/
noncomputable def livePolynomial {cap : ℕ} (large : 4 ≤ cap) : ℕ[X] :=
  letI := liveFintype large
  ∑ c : LiveHands cap, X ^ meldCount c.val

noncomputable def geom (length : ℕ) : ℕ[X] := ∑ i : Fin length, X ^ i.val

lemma box_sum (cap : ℕ) (r : Fin 3) :
    (∑ x : Box cap r,
      (X : ℕ[X]) ^ (x.1.val + x.2.1.val + x.2.2.val + if r = 1 then 3 else 2)) =
      geom (width cap r) ^ 2 * geom (depth cap r) * X ^ (if r = 1 then 3 else 2) := by
  classical
  simp only [Box, Fintype.sum_prod_type, pow_add]
  simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
  simp only [geom, pow_two]
  ring

theorem livePolynomial_formula {cap : ℕ} (large : 4 ≤ cap) :
    livePolynomial large = 3 * X ^ 2 *
      (geom ((cap - 1) / 3) ^ 2 * geom ((cap + 1) / 3) +
        X * geom ((cap - 2) / 3) ^ 2 * geom (cap / 3) +
        geom (cap / 3) ^ 2 * geom ((cap - 1) / 3)) := by
  classical
  let := liveFintype large
  change (∑ c : LiveHands cap, (X : ℕ[X]) ^ meldCount c.val) = _
  rw [← (liveBoxEquiv large).sum_comp]
  have count (x : Coordinates cap) : meldCount ((liveBoxEquiv large) x).val =
      x.2.2.1.val + x.2.2.2.1.val + x.2.2.2.2.val + if x.2.1 = 1 then 3 else 2 :=
    meldCount_of_live (encode_live large x)
  simp_rw [count]
  simp only [Fintype.sum_prod_type, Fintype.sum_sigma]
  simp only [box_sum]
  simp [Fin.sum_univ_succ, width, depth, offset]
  ring

def waitFiberEquiv {cap m : ℕ} :
    {c : LiveHands cap // meldCount c.val = m} ≃
      {c : VirtualHand 1 // IsLiveFullWait cap m c} where
  toFun c := ⟨c.val.val, (live_iff_meldCount c.val.property).mpr c.property⟩
  invFun c := ⟨⟨c.val, ⟨m, c.property⟩⟩, meldCount_of_live c.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem livePolynomial_coeff {cap : ℕ} (large : 4 ≤ cap) (m : ℕ) :
    (livePolynomial large).coeff m =
      Nat.card {c : VirtualHand 1 // IsLiveFullWait cap m c} := by
  classical
  let := liveFintype large
  rw [← Nat.card_congr (waitFiberEquiv (cap := cap) (m := m))]
  simp [livePolynomial, Fintype.card_subtype, Nat.card_eq_fintype_card, eq_comm]

theorem livePolynomial_eval_one {cap : ℕ} (large : 4 ≤ cap) :
    (livePolynomial large).eval 1 = Nat.card (LiveHands cap) := by
  classical
  let := liveFintype large
  simp [livePolynomial, eval_finsetSum, Nat.card_eq_fintype_card]

theorem livePolynomial_seven :
    livePolynomial (cap := 7) (by omega) =
      6 * X ^ 2 + 21 * X ^ 3 + 21 * X ^ 4 + 6 * X ^ 5 := by
  rw [livePolynomial_formula]
  norm_num [geom, Fin.sum_univ_succ]
  ring

theorem livePolynomial_coeff_symmetry {cap : ℕ} (large : 4 ≤ cap) (m : ℕ)
    (bound : m ≤ cap) :
    (livePolynomial large).coeff m = (livePolynomial large).coeff (cap - m) := by
  rw [livePolynomial_coeff, livePolynomial_coeff]
  exact live_card_symmetry cap m bound

end Mahjong.VirtualHand.OrderOne.Generating
