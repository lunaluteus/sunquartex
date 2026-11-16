/-
Copyright (c) 2026 Luna Luteus. Released under Apache 2.0.
Authors: Luna Luteus
-/
import Ninegates

/-! Three-rank live waits as a disjoint union of integer boxes. -/

open Mahjong Mahjong.VirtualHand

namespace Mahjong.VirtualHand.OrderOne.Boxes

def AllLive (cap : ℕ) (c : VirtualHand 1) : Prop := ∃ m, IsLiveFullWait cap m c

def spin (r : Fin 3) (c : VirtualHand 1) : VirtualHand 1 := fun i ↦ c (i - r)

lemma spin_zero (c : VirtualHand 1) : spin 0 c = c := by ext i; simp [spin]

lemma spin_add (r t : Fin 3) (c : VirtualHand 1) :
    spin (r + t) c = spin r (spin t c) := by
  ext i
  simp only [spin]
  congr 1
  abel

lemma size_spin (r : Fin 3) (c : VirtualHand 1) : size (spin r c) = size c := by
  fin_cases r <;> norm_num [size, spin, Fin.sum_univ_succ] <;>
    simp only [show (-1 : Fin 3) = 2 from rfl, show (-2 : Fin 3) = 1 from rfl] <;> ring

lemma fixedClass_spin (r : Fin 3) (c : VirtualHand 1) :
    fixedClass (spin r c) = fixedClass c + (r.val : ZMod 3) * (size c : ZMod 3) := by
  have zero (z : ℤ) : (3 : ZMod 3) * (z : ZMod 3) = 0 := by
    rw [show (3 : ZMod 3) = 0 from ZMod.natCast_self 3, zero_mul]
  fin_cases r <;>
    simp only [fixedClass, rankSum, size, LinearMap.coe_mk, AddHom.coe_mk,
      Fin.sum_univ_succ, spin] <;>
    norm_num [rank, show (-1 : Fin 3) = 2 from rfl, show (-2 : Fin 3) = 1 from rfl] <;>
    simp only [show (-1 : Fin 3) = 2 from rfl, show (-2 : Fin 3) = 1 from rfl]
  · linear_combination -zero (c 2)
  · linear_combination -zero (c 1) - zero (c 2)

lemma spin_threshold (r : Fin 3) (s : ZMod 3) :
    spin r (pairThreshold s) = pairThreshold (s + (r.val : ZMod 3)) := by
  ext i
  fin_cases r <;> fin_cases s <;> fin_cases i <;> decide +kernel

lemma spin_live {cap m : ℕ} {c : VirtualHand 1} (live : IsLiveFullWait cap m c)
    (r : Fin 3) : IsLiveFullWait cap m (spin r c) := by
  obtain ⟨full, upper⟩ := isLiveFullWait_iff.mp live
  obtain ⟨count, lower⟩ := (full_iff c).mp full
  apply isLiveFullWait_iff.mpr
  refine ⟨(full_iff _).mpr ⟨(size_spin r c).trans count, ?_⟩, fun i ↦ upper (i - r)⟩
  rw [fixedClass_spin, size_cast_of_wait_size count, mul_one, ← spin_threshold]
  exact fun i ↦ lower (i - r)

/-- The minimum first and second coordinates in each common residue class. -/
def offset (r : Fin 3) : ℕ := if r = 0 then 3 else if r = 1 then 4 else 2

def width (cap : ℕ) (r : Fin 3) : ℕ := (cap + 2 - offset r) / 3
def depth (cap : ℕ) (r : Fin 3) : ℕ := (cap + 1 - r.val) / 3
def Box (cap : ℕ) (r : Fin 3) := Fin (width cap r) × Fin (width cap r) × Fin (depth cap r)

def shape (r : Fin 3) (a b d : ℕ) : VirtualHand 1 :=
  ![3 * (a : ℤ) + offset r, 3 * (b : ℤ) + offset r, 3 * (d : ℤ) + r.val + 1]

lemma fixedClass_shape (r : Fin 3) (a b d : ℕ) : fixedClass (shape r a b d) = 0 := by
  have multiple : rankSum (shape r a b d) =
      3 * ((a : ℤ) + 2 * b + 3 * d + offset r + r.val + 1) := by
    simp [shape, rankSum, rank, Fin.sum_univ_succ]
    ring
  rw [fixedClass, multiple, Int.cast_mul, Int.cast_ofNat]
  rw [show (3 : ZMod 3) = 0 from ZMod.natCast_self 3, zero_mul]

lemma size_shape (r : Fin 3) (a b d : ℕ) :
    size (shape r a b d) = 3 * ((a + b + d + if r = 1 then 3 else 2 : ℕ) : ℤ) + 1 := by
  fin_cases r <;> norm_num [shape, offset, size, Fin.sum_univ_succ] <;> ring

lemma shape_live {cap : ℕ} (large : 4 ≤ cap) (r : Fin 3) (x : Box cap r) :
    IsLiveFullWait cap (x.1.val + x.2.1.val + x.2.2.val + if r = 1 then 3 else 2)
      (shape r x.1.val x.2.1.val x.2.2.val) := by
  have ha := x.1.isLt
  have hb := x.2.1.isLt
  have hd := x.2.2.isLt
  change x.1.val < (cap + 2 - offset r) / 3 at ha
  change x.2.1.val < (cap + 2 - offset r) / 3 at hb
  change x.2.2.val < (cap + 1 - r.val) / 3 at hd
  apply isLiveFullWait_iff.mpr
  refine ⟨(full_iff _).mpr ⟨size_shape _ _ _ _, ?_⟩, ?_⟩
  · rw [fixedClass_shape]
    have threshold : pairThreshold (0 : ZMod 3) = ![2, 2, 1] := by
      ext i
      fin_cases i <;> decide +kernel
    rw [threshold]
    have small : 2 ≤ offset r := by unfold offset; split_ifs <;> omega
    intro i
    fin_cases i
    · change 2 ≤ 3 * (x.1.val : ℤ) + offset r
      omega
    · change 2 ≤ 3 * (x.2.1.val : ℤ) + offset r
      omega
    · change 1 ≤ 3 * (x.2.2.val : ℤ) + r.val + 1
      omega
  · have digit_bound {o a : ℕ} (small : o ≤ 4) (digit : a < (cap + 2 - o) / 3) :
        3 * (a : ℤ) + o + 1 ≤ cap := by omega
    have small : offset r ≤ 4 := by unfold offset; split_ifs <;> omega
    have first := digit_bound small ha
    have second := digit_bound small hb
    have third : 3 * (x.2.2.val : ℤ) + r.val + 1 + 1 ≤ cap := by
      have hr := r.isLt
      omega
    intro i
    fin_cases i
    · exact first
    · exact second
    · exact third

lemma shape_residue (r : Fin 3) (a b d : ℕ) : shape r a b d 0 % 3 = r.val := by
  fin_cases r <;> norm_num [shape, offset, Int.add_emod, Int.mul_emod]

lemma shape_injective : Function.Injective
    (fun x : Fin 3 × (ℕ × ℕ × ℕ) ↦ shape x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  rintro ⟨r, a, b, d⟩ ⟨s, e, f, g⟩ same
  have h0 := congrFun same 0
  have h1 := congrFun same 1
  have h2 := congrFun same 2
  have residues := congrArg (fun c : VirtualHand 1 ↦ c 0 % 3) same
  rw [shape_residue, shape_residue] at residues
  have equal : r = s := Fin.ext (by exact_mod_cast residues)
  subst s
  change 3 * (a : ℤ) + offset r = 3 * (e : ℤ) + offset r at h0
  change 3 * (b : ℤ) + offset r = 3 * (f : ℤ) + offset r at h1
  change 3 * (d : ℤ) + r.val + 1 = 3 * (g : ℤ) + r.val + 1 at h2
  have : a = e ∧ b = f ∧ d = g := by omega
  rcases this with ⟨rfl, rfl, rfl⟩
  rfl

private lemma digit_surj {cap base o : ℕ} {z : ℤ}
    (start : base ≤ o) (stop : o < base + 3) (lower : (base : ℤ) ≤ z)
    (residue : z % 3 = (o : ℤ) % 3) (upper : z + 1 ≤ cap) :
    ∃ a : Fin ((cap + 2 - o) / 3), z = 3 * (a.val : ℤ) + o := by
  let a := ((z - o) / 3).toNat
  have positive : 0 ≤ (z - o) / 3 := by omega
  have cast_a : (a : ℤ) = (z - o) / 3 := Int.toNat_of_nonneg positive
  refine ⟨⟨a, by omega⟩, ?_⟩
  change z = 3 * (a : ℤ) + o
  omega

lemma canonical_shape {cap : ℕ} {c : VirtualHand 1} (live : AllLive cap c)
    (fixed : fixedClass c = 0) :
    ∃ r, ∃ x : Box cap r, shape r x.1.val x.2.1.val x.2.2.val = c := by
  obtain ⟨m, live⟩ := live
  obtain ⟨full, upper⟩ := isLiveFullWait_iff.mp live
  have lower := ((full_iff c).mp full).2
  rw [fixed] at lower
  have threshold : pairThreshold (0 : ZMod 3) = ![2, 2, 1] := by
    ext i
    fin_cases i <;> decide +kernel
  rw [threshold] at lower
  have lo0 : 2 ≤ c 0 := lower 0
  have lo1 : 2 ≤ c 1 := lower 1
  have lo2 : 1 ≤ c 2 := lower 2
  have up0 := upper 0
  have up1 := upper 1
  have up2 := upper 2
  have total : c 0 + c 1 + c 2 = 3 * (m : ℤ) + 1 := by
    have := full.2.1
    simpa [size, Fin.sum_univ_succ, add_assoc] using this
  have weight : (c 0 + 2 * c 1 + 3 * c 2) % 3 = 0 := by
    have weighted : rankSum c = c 0 + 2 * c 1 + 3 * c 2 := by
      simp [rankSum, rank, Fin.sum_univ_succ]
      ring
    rw [fixedClass, weighted] at fixed
    exact (ZMod.intCast_eq_intCast_iff' _ 0 3).mp fixed
  let r : Fin 3 := ⟨(c 0 % 3).toNat, by omega⟩
  have residue : c 0 % 3 = (r.val : ℤ) := by
    dsimp [r]
    omega
  have small : 2 ≤ offset r ∧ offset r < 2 + 3 := by
    unfold offset
    split_ifs <;> omega
  have offset_mod : (offset r : ℤ) % 3 = r.val := by
    have every (s : Fin 3) : (offset s : ℤ) % 3 = s.val := by
      fin_cases s <;> decide +kernel
    exact every r
  obtain ⟨a, ha⟩ := digit_surj small.1 small.2 lo0 (residue.trans offset_mod.symm) up0
  obtain ⟨b, hb⟩ := digit_surj small.1 small.2 lo1
    (show c 1 % 3 = (offset r : ℤ) % 3 by omega) up1
  have third_mod : c 2 % 3 = ((r.val + 1 : ℕ) : ℤ) % 3 := by omega
  obtain ⟨d, hd⟩ := digit_surj (base := 1) (o := r.val + 1)
    (by omega) (by have := r.isLt; omega) lo2 third_mod up2
  have depth_eq : (cap + 2 - (r.val + 1)) / 3 = depth cap r := by
    unfold depth
    congr 1
    omega
  refine ⟨r, ⟨a, b, ⟨d.val, by rw [← depth_eq]; exact d.isLt⟩⟩, ?_⟩
  ext i
  fin_cases i
  · exact ha.symm
  · exact hb.symm
  · simpa [shape, add_assoc] using hd.symm

def encode {cap : ℕ} (large : 4 ≤ cap) (x : Fin 3 × (r : Fin 3) × Box cap r) :
    {c : VirtualHand 1 // AllLive cap c} :=
  ⟨spin x.1 (shape x.2.1 x.2.2.1.val x.2.2.2.1.val x.2.2.2.2.val),
    ⟨_, spin_live (shape_live large x.2.1 x.2.2) x.1⟩⟩

lemma encode_live {cap : ℕ} (large : 4 ≤ cap) (x : Fin 3 × (r : Fin 3) × Box cap r) :
    IsLiveFullWait cap
      (x.2.2.1.val + x.2.2.2.1.val + x.2.2.2.2.val + if x.2.1 = 1 then 3 else 2)
      (encode large x).val :=
  spin_live (shape_live large x.2.1 x.2.2) x.1

lemma fixedClass_encode {cap : ℕ} (large : 4 ≤ cap)
    (x : Fin 3 × (r : Fin 3) × Box cap r) : fixedClass (encode large x).val = x.1.val := by
  rw [encode, fixedClass_spin, fixedClass_shape,
    size_cast_of_wait_size (shape_live large x.2.1 x.2.2).1.2.1, mul_one, zero_add]

lemma encode_injective {cap : ℕ} (large : 4 ≤ cap) : Function.Injective (encode large) := by
  rintro ⟨s, r, a, b, d⟩ ⟨t, u, e, f, g⟩ same
  have values := congrArg Subtype.val same
  have classes := congrArg (fun c ↦ fixedClass c.val) same
  rw [fixedClass_encode, fixedClass_encode] at classes
  have residues := (ZMod.natCast_eq_natCast_iff' _ _ 3).mp classes
  have st : s = t := Fin.ext (by have := s.isLt; have := t.isLt; dsimp at residues; omega)
  subst t
  have original := congrArg (spin (-s)) values
  change spin (-s) (spin s (shape r a.val b.val d.val)) =
    spin (-s) (spin s (shape u e.val f.val g.val)) at original
  rw [← spin_add, ← spin_add, neg_add_cancel, spin_zero, spin_zero] at original
  have parameters := @shape_injective ⟨r, a.val, b.val, d.val⟩ ⟨u, e.val, f.val, g.val⟩ original
  have ru : r = u := congrArg Prod.fst parameters
  subst u
  have ae : a = e := Fin.ext (congrArg (fun x ↦ x.2.1) parameters)
  have bf : b = f := Fin.ext (congrArg (fun x ↦ x.2.2.1) parameters)
  have dg : d = g := Fin.ext (congrArg (fun x ↦ x.2.2.2) parameters)
  subst e; subst f; subst g
  rfl

lemma encode_surjective {cap : ℕ} (large : 4 ≤ cap) : Function.Surjective (encode large) := by
  rintro ⟨c, m, live⟩
  let s : Fin 3 := fixedClass c
  have hs : (s.val : ZMod 3) = fixedClass c :=
    ZMod.natCast_zmod_val (n := 3) (fixedClass c)
  have cast_neg : ((-s).val : ZMod 3) = -(s.val : ZMod 3) := by
    have every (t : Fin 3) : ((-t).val : ZMod 3) = -(t.val : ZMod 3) := by
      fin_cases t <;> decide +kernel
    exact every s
  have fixed : fixedClass (spin (-s) c) = 0 := by
    rw [fixedClass_spin, size_cast_of_wait_size live.1.2.1, mul_one, cast_neg, hs, add_neg_cancel]
  obtain ⟨r, x, shape_eq⟩ := canonical_shape ⟨m, spin_live live (-s)⟩ fixed
  refine ⟨⟨s, r, x⟩, Subtype.ext ?_⟩
  change spin s (shape r x.1.val x.2.1.val x.2.2.val) = c
  rw [shape_eq, ← spin_add, add_neg_cancel, spin_zero]

/-- A live hand has one unique cyclic position and one unique box coordinate. -/
noncomputable def liveBoxEquiv {cap : ℕ} (large : 4 ≤ cap) :
    (Fin 3 × (r : Fin 3) × Box cap r) ≃ {c : VirtualHand 1 // AllLive cap c} :=
  Equiv.ofBijective (encode large) ⟨encode_injective large, encode_surjective large⟩

theorem total_live_card {cap : ℕ} (large : 4 ≤ cap) :
    Nat.card {c : VirtualHand 1 // AllLive cap c} =
      3 * (((cap - 1) / 3) ^ 2 * ((cap + 1) / 3) +
        ((cap - 2) / 3) ^ 2 * (cap / 3) + (cap / 3) ^ 2 * ((cap - 1) / 3)) := by
  have finite_box (r : Fin 3) : Finite (Box cap r) := by unfold Box; infer_instance
  rw [Nat.card_congr (liveBoxEquiv large).symm, Nat.card_prod, Nat.card_fin, Nat.card_sigma]
  simp only [Box, Nat.card_prod, Nat.card_fin]
  simp [Fin.sum_univ_succ, width, depth, offset, pow_two]
  ring

theorem total_live_card_mod_zero (k : ℕ) (large : 2 ≤ k) :
    Nat.card {c : VirtualHand 1 // AllLive (3 * k) c} =
      3 * k * (k - 1) * (3 * k - 2) := by
  rw [total_live_card (by omega)]
  have a : (3 * k - 1) / 3 = k - 1 := by omega
  have b : (3 * k + 1) / 3 = k := by omega
  have d : (3 * k - 2) / 3 = k - 1 := by omega
  have e : 3 * k / 3 = k := by omega
  have f : 3 * k - 2 = k + 2 * (k - 1) := by omega
  rw [a, b, d, e, f]
  ring

theorem total_live_card_mod_one (k : ℕ) (positive : 1 ≤ k) :
    Nat.card {c : VirtualHand 1 // AllLive (3 * k + 1) c} =
      3 * k * (2 * k ^ 2 + (k - 1) ^ 2) := by
  rw [total_live_card (by omega)]
  have a : (3 * k + 1 - 1) / 3 = k := by omega
  have b : (3 * k + 1 + 1) / 3 = k := by omega
  have d : (3 * k + 1 - 2) / 3 = k - 1 := by omega
  have e : (3 * k + 1) / 3 = k := by omega
  rw [a, b, d, e]
  ring

theorem total_live_card_mod_two (k : ℕ) (positive : 1 ≤ k) :
    Nat.card {c : VirtualHand 1 // AllLive (3 * k + 2) c} =
      3 * k ^ 2 * (3 * k + 1) := by
  rw [total_live_card (by omega)]
  have a : (3 * k + 2 - 1) / 3 = k := by omega
  have b : (3 * k + 2 + 1) / 3 = k + 1 := by omega
  have d : (3 * k + 2 - 2) / 3 = k := by omega
  have e : (3 * k + 2) / 3 = k := by omega
  rw [a, b, d, e]
  ring

end Mahjong.VirtualHand.OrderOne.Boxes
