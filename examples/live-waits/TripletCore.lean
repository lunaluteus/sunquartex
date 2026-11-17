/-
Copyright (c) 2026 Luna Luteus. Released under Apache 2.0.
Authors: Luna Luteus
-/
import BoundaryTriplets

/-!
# Unique bounded cores and free triplet tails

A full wait has a unique representation by a full hand in the abundance-profile
box, together with nonnegative triplet counts at its active coordinates.
The graded equivalence records the original meld count exactly.

The removable-triplet threshold comes from Xue and Zhong, *Beyond Nine Gates*,
arXiv:2611.06944v1, proof of Proposition 6.8, refined here by the canonical
sequence bound in ninegates-lean4 at
7b379afe7f54f34c59c8abdfc8e6fa5f0bee952a.
The truncated core need not be minimal under meld removal.
-/

open Mahjong Mahjong.VirtualHand

namespace Mahjong.VirtualHand.TripletCore

/-- The finite core box follows the paper's abundance profile at each rank. -/
def CoreBounded {n : ℕ} (c : VirtualHand n) : Prop :=
  Nonnegative c ∧ ∀ i, c i ≤ abundanceThreshold i + 2

/-- Every rank-dependent core cap is at most eight. -/
theorem CoreBounded.bounded_eight {n : ℕ} {c : VirtualHand n} (bounded : CoreBounded c) :
    Bounded 8 c := by
  refine ⟨bounded.1, ?_⟩
  intro i
  have local_bound := bounded.2 i
  have threshold := (abundanceThreshold_bounds i).2
  omega

/-- Keep small coordinates; otherwise retain the residue in the local three-tile band. -/
def coreCoord (b z : ℤ) : ℤ := if z < b then z else b + (z - b) % 3

/-- The number of triplets removed relative to a coordinate's threshold. -/
def tailCoord (b z : ℤ) : ℕ := if z < b then 0 else ((z - b) / 3).toNat

private lemma coord_bounds {b z : ℤ} (base : 0 ≤ b) (positive : 0 ≤ z) :
    0 ≤ coreCoord b z ∧ coreCoord b z ≤ b + 2 := by
  unfold coreCoord
  split_ifs <;> omega

private lemma coord_fixed {b z : ℤ} (small : z ≤ b + 2) : coreCoord b z = z := by
  unfold coreCoord
  split_ifs <;> omega

private lemma coord_reconstruct (b z : ℤ) : z = coreCoord b z + 3 * (tailCoord b z : ℤ) := by
  unfold coreCoord tailCoord
  split_ifs <;> omega

private lemma coord_sub_three {b z : ℤ} (large : b + 3 ≤ z) :
    coreCoord b (z - 3) = coreCoord b z := by
  unfold coreCoord
  split_ifs <;> omega

private lemma coord_low_tail (b z : ℤ) : coreCoord b z < b → tailCoord b z = 0 := by
  unfold coreCoord tailCoord
  split_ifs <;> omega

private lemma coord_lift {b a : ℤ} (small : a ≤ b + 2) (t : ℕ) (inactive : a < b → t = 0) :
    coreCoord b (a + 3 * (t : ℤ)) = a ∧ tailCoord b (a + 3 * (t : ℤ)) = t := by
  unfold coreCoord tailCoord
  by_cases low : a < b
  · have zero := inactive low
    subst t
    simp [low]
  · split_ifs <;> omega

/-- The bounded representative of a hand under removal of large triplets. -/
def core {n : ℕ} (c : VirtualHand n) : VirtualHand n :=
  fun i ↦ coreCoord (abundanceThreshold i) (c i)

/-- The triplet multiplicities removed from a hand. -/
def tail {n : ℕ} (c : VirtualHand n) : Rank n → ℕ := fun i ↦ tailCoord (abundanceThreshold i) (c i)

/-- Add the indicated triplet at every rank. -/
def lift {n : ℕ} (a : VirtualHand n) (t : Rank n → ℕ) : VirtualHand n :=
  a + (3 : ℤ) • (fun i ↦ (t i : ℤ))

/-- A hand is exactly its core plus its removed triplets. -/
theorem reconstruct {n : ℕ} (c : VirtualHand n) : lift (core c) (tail c) = c := by
  ext i
  exact (coord_reconstruct (abundanceThreshold i) (c i)).symm

/-- Truncation lands in the rank-dependent finite core box. -/
theorem core_bounded {n : ℕ} {c : VirtualHand n} (positive : Nonnegative c) :
    CoreBounded (core c) := by
  have base (i : Rank n) : 0 ≤ abundanceThreshold i := by
    have lower := (abundanceThreshold_bounds i).1
    omega
  exact ⟨fun i ↦ (coord_bounds (base i) (positive i)).1,
    fun i ↦ (coord_bounds (base i) (positive i)).2⟩

private lemma core_sub_triplet {n : ℕ} {c : VirtualHand n} (i : Rank n)
    (large : abundanceThreshold i + 3 ≤ c i) : core (c - triplet i) = core c := by
  ext j
  by_cases same : j = i
  · subst j
    simpa [core, triplet_apply, single_self] using coord_sub_three large
  · simp [core, triplet_apply, single_of_ne same]

/-- Every full wait truncates to another full wait, at a possibly smaller meld count. -/
theorem full_core {n m : ℕ} {c : VirtualHand n} (full : IsFullWait m c) :
    ∃ k, IsFullWait k (core c) := by
  classical
  induction m using Nat.strong_induction_on generalizing c with
  | h m ih =>
    by_cases small : ∀ i, c i ≤ abundanceThreshold i + 2
    · have same : core c = c := by ext i; exact coord_fixed (small i)
      exact ⟨m, same.symm ▸ full⟩
    · push Not at small
      obtain ⟨i, large⟩ := small
      have lower := full.meldCount_gt_order
      obtain ⟨k, smaller⟩ := ih (m - 1) (by omega) (full.sub_triplet_of_threshold i (by omega))
      rw [core_sub_triplet i (by omega)] at smaller
      exact ⟨k, smaller⟩

/-- Adding any nonnegative vector of triplets preserves full-sidedness and its size. -/
theorem full_lift {n m : ℕ} {a : VirtualHand n} (full : IsFullWait m a)
    (t : Rank n → ℕ) : IsFullWait (m + ∑ i, t i) (lift a t) := by
  have melds : Meldable ((3 : ℤ) • (fun i ↦ (t i : ℤ))) := by
    refine ⟨⟨0, fun i ↦ (t i : ℤ)⟩, ⟨le_refl _, fun i ↦ by positivity⟩, ?_⟩
    simp [Placement.toHand_eq]
  apply full.add_meldable melds
  simp [size, Finset.mul_sum, Nat.cast_sum]

/-- The split records the exact number of removed melds. -/
theorem meldCount_split {n m : ℕ} {c : VirtualHand n} (full : IsFullWait m c) :
    ∃ k, IsFullWait k (core c) ∧ m = k + ∑ i, tail c i := by
  obtain ⟨k, base⟩ := full_core full
  have lifted := full_lift base (tail c)
  rw [reconstruct] at lifted
  have first := full.2.1
  have second := lifted.2.1
  refine ⟨k, base, ?_⟩
  simp only [Nat.cast_add] at second
  omega

/-- Truncation recovers the core and active tails of every permitted parameter pair. -/
theorem core_tail_lift {n : ℕ} {a : VirtualHand n} (bounded : CoreBounded a)
    (t : Rank n → ℕ) (inactive : ∀ i, a i < abundanceThreshold i → t i = 0) :
    core (lift a t) = a ∧ tail (lift a t) = t := by
  constructor
  · ext i
    exact (coord_lift (bounded.2 i) (t i) (inactive i)).1
  · funext i
    exact (coord_lift (bounded.2 i) (t i) (inactive i)).2

/-- Full waits without fixing their uniquely determined meld count. -/
def FullHand (n : ℕ) := {c : VirtualHand n // ∃ m, IsFullWait m c}

/-- Bounded full cores with tails supported at or above the local profile. -/
def Parameters (n : ℕ) :=
  {p : VirtualHand n × (Rank n → ℕ) //
    CoreBounded p.1 ∧ (∃ m, IsFullWait m p.1) ∧ ∀ i, p.1 i < abundanceThreshold i → p.2 i = 0}

/-- Truncation and triplet addition are mutually inverse parametrizations. -/
def coreEquiv (n : ℕ) : FullHand n ≃ Parameters n where
  toFun c := ⟨(core c.val, tail c.val), core_bounded c.property.choose_spec.1,
    full_core c.property.choose_spec, fun i ↦ coord_low_tail (abundanceThreshold i) (c.val i)⟩
  invFun p := ⟨lift p.val.1 p.val.2, by
    obtain ⟨m, full⟩ := p.property.2.1
    exact ⟨m + ∑ i, p.val.2 i, full_lift full p.val.2⟩⟩
  left_inv c := Subtype.ext (reconstruct c.val)
  right_inv p := by
    apply Subtype.ext
    exact Prod.ext (core_tail_lift p.property.1 p.val.2 p.property.2.2).1
      (core_tail_lift p.property.1 p.val.2 p.property.2.2).2

/-- The core's meld count is uniformly bounded, independently of the source hand. -/
theorem core_meldCount_bound {n k : ℕ} {a : VirtualHand n}
    (bounded : CoreBounded a) (full : IsFullWait k a) : k < 8 * n := by
  have upper := bounded.bounded_eight.size_le
  rw [full.2.1] at upper
  omega

/-- The meld count determined by the size of a full hand. -/
def grade {n : ℕ} (c : VirtualHand n) : ℕ := ((size c - 1) / 3).toNat

/-- The size-based grade agrees with every witnessed meld count. -/
theorem grade_eq {n m : ℕ} {c : VirtualHand n} (full : IsFullWait m c) : grade c = m := by
  unfold grade
  rw [full.2.1]
  omega

/-- The same full-hand witness can be stated at its computable size-based grade. -/
theorem full_grade {n : ℕ} {c : VirtualHand n} (full : ∃ m, IsFullWait m c) :
    IsFullWait (grade c) c := by
  obtain ⟨m, hm⟩ := full
  rw [grade_eq hm]
  exact hm

/-- Finite indexing data for all full waits at a fixed order. -/
def Cores (n : ℕ) := {a : VirtualHand n // CoreBounded a ∧ ∃ m, IsFullWait m a}

instance cores_finite (n : ℕ) : Finite (Cores n) := by
  let encode : Cores n → (Rank n → Fin 9) := fun a i ↦
    ⟨(a.val i).toNat, by
      have lo := a.property.1.1 i
      have hi := a.property.1.bounded_eight.2 i
      omega⟩
  have injective : Function.Injective encode := by
    intro a b same
    apply Subtype.ext
    funext i
    have equal := congrArg (fun x : Rank n → Fin 9 ↦ (x i).val) same
    change (a.val i).toNat = (b.val i).toNat at equal
    simpa only [Int.toNat_of_nonneg (a.property.1.1 i),
      Int.toNat_of_nonneg (b.property.1.1 i)] using congrArg (fun k : ℕ ↦ (k : ℤ)) equal
  exact Finite.of_injective encode injective

/-- Only these coordinates can carry an arbitrary tail without changing the core. -/
abbrev Active {n : ℕ} (a : Cores n) := {i : Rank n // abundanceThreshold i ≤ a.val i}

/-- Extend the active coordinates by zero to a complete vector of triplets. -/
def extend {n : ℕ} (a : Cores n) (t : Active a → ℕ) (i : Rank n) : ℕ :=
  if h : abundanceThreshold i ≤ a.val i then t ⟨i, h⟩ else 0

private lemma sum_extend {n : ℕ} (a : Cores n) (t : Active a → ℕ) :
    ∑ i, extend a t i = ∑ i, t i := by
  classical
  have partition := Fintype.sum_subtype_add_sum_subtype
    (fun i ↦ abundanceThreshold i ≤ a.val i) (extend a t)
  have positive : (∑ i : Active a, extend a t i.val) = ∑ i, t i := by
    apply Finset.sum_congr rfl
    intro i _
    exact dite_eq_left i.property
  have negative :
      (∑ i : {i : Rank n // ¬abundanceThreshold i ≤ a.val i}, extend a t i.val) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact dite_eq_right i.property
  rw [positive, negative, add_zero] at partition
  exact partition.symm

/-- Split the flat parameter representation into a core and its active tails. -/
def parametersEquiv (n : ℕ) : Parameters n ≃ (a : Cores n) × (Active a → ℕ) where
  toFun p := ⟨⟨p.val.1, p.property.1, p.property.2.1⟩, fun i ↦ p.val.2 i.val⟩
  invFun p := ⟨(p.1.val, extend p.1 p.2), p.1.property.1, p.1.property.2, by
    intro i small
    change p.1.val i < abundanceThreshold i at small
    simp [extend, show ¬abundanceThreshold i ≤ p.1.val i by omega]⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    funext i
    change (if h : abundanceThreshold i ≤ p.val.1 i then p.val.2 i else 0) = p.val.2 i
    split_ifs with high
    · rfl
    · exact (p.property.2.2 i (by omega)).symm
  right_inv p := by
    refine Sigma.ext rfl ?_
    apply heq_of_eq
    funext i
    exact dite_eq_left i.property

private lemma forget_injective (n m : ℕ) : Function.Injective
    (fun p : (a : Cores n) × {t : Active a → ℕ // grade a.val + ∑ i, t i = m} ↦
      (⟨p.1, p.2.val⟩ : (a : Cores n) × (Active a → ℕ))) := by
  rintro ⟨a, t, ht⟩ ⟨b, u, hu⟩ same
  cases same
  rfl

/-- Full waits of a fixed meld count are weak compositions over finitely many cores. -/
def fixedEquiv (n m : ℕ) : {c : VirtualHand n // IsFullWait m c} ≃
    (a : Cores n) × {t : Active a → ℕ // grade a.val + ∑ i, t i = m} where
  toFun c := by
    let p := (parametersEquiv n) ((coreEquiv n) ⟨c.val, m, c.property⟩)
    refine ⟨p.1, p.2, ?_⟩
    obtain ⟨k, base, count⟩ := meldCount_split c.property
    have sum_equal := sum_extend p.1 p.2
    have shape : extend p.1 p.2 = tail c.val := by
      funext i
      change (if h : abundanceThreshold i ≤ core c.val i then tail c.val i else 0) = tail c.val i
      split_ifs with high
      · rfl
      · exact (coord_low_tail (abundanceThreshold i) (c.val i) (by simpa [core] using high)).symm
    rw [shape] at sum_equal
    change grade (core c.val) + ∑ i, p.2 i = m
    rw [grade_eq base, ← sum_equal]
    omega
  invFun p := ⟨lift p.1.val (extend p.1 p.2.val), by
    have full := full_lift (full_grade p.1.property.2) (extend p.1 p.2.val)
    rw [sum_extend, p.2.property] at full
    exact full⟩
  left_inv c := by
    apply Subtype.ext
    have same := (parametersEquiv n).left_inv ((coreEquiv n) ⟨c.val, m, c.property⟩)
    have lifted := congrArg (fun p : Parameters n ↦ lift p.val.1 p.val.2) same
    exact lifted.trans (reconstruct c.val)
  right_inv p := by
    apply forget_injective n m
    exact ((coreEquiv n).trans (parametersEquiv n)).right_inv ⟨p.1, p.2.val⟩

end Mahjong.VirtualHand.TripletCore
