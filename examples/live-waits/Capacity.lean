-- Copyright (c) 2026 Luna Luteus. Released under Apache 2.0.
import Ninegates

open Mahjong Mahjong.VirtualHand

namespace SunQuarTeX.Examples

/-
### A Lean checkpoint {#sec-lean-checkpoint}

This is the complete proof of the capacity bound, imported from a Lean source
file with `lean-include`. The copy cap is independent of the order and meld count.
-/

theorem live_capacity {n cap m : ℕ} {c : VirtualHand n}
    (live : IsLiveFullWait cap m c) : m < n * (cap - 1) := by
  have bounded : Bounded (cap - 1) c := by
    refine ⟨live.1.1, fun i ↦ ?_⟩
    have upper := (isLiveFullWait_iff.mp live).2 i
    have lower := live.1.1 i
    omega
  have upper := bounded.size_le
  have shape : 3 * (n : ℤ) * ((cap - 1 : ℕ) : ℤ) =
      3 * ((n * (cap - 1) : ℕ) : ℤ) := by push_cast; ring
  rw [shape, live.1.2.1] at upper
  have strict : (m : ℤ) < ((n * (cap - 1) : ℕ) : ℤ) := by omega
  exact_mod_cast strict

end SunQuarTeX.Examples
