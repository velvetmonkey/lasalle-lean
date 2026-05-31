/-
Copyright (c) 2025. All rights reserved.
Released under the MIT license.

# LaSalle's Invariance Principle — Definitions

This file defines the core structures for LaSalle's invariance principle:
a continuous semiflow on a topological space, Lyapunov functions, and
the largest positively invariant subset.
-/
import Mathlib

open Set Filter Topology NNReal omegaLimit

noncomputable section

/-! ### Auxiliary lemmas for ℝ≥0 and Filter.atTop -/

/-- Adding a constant to ℝ≥0 sends atTop to atTop. -/
lemma NNReal.tendsto_atTop_add (t : ℝ≥0) :
    Tendsto (t + ·) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  exact ⟨b, fun c hc => le_add_left hc⟩

/-! ### Core definitions -/

variable {E : Type*} [TopologicalSpace E]

/-- The omega-limit set of a single point `x` under a flow `φ`,
defined as `ω⁺ φ {x}` using Mathlib's `omegaLimit`. -/
def omegaLimitPt (φ : ℝ≥0 → E → E) (x : E) : Set E :=
  ω atTop φ {x}

/-- The largest positively invariant subset of `S` under `φ`:
the set of points in `S` whose entire forward orbit stays in `S`. -/
def largestInvSubset (φ : ℝ≥0 → E → E) (S : Set E) : Set E :=
  {x ∈ S | ∀ t : ℝ≥0, φ t x ∈ S}

/-- `largestInvSubset φ S` is a subset of `S`. -/
@[simp]
theorem largestInvSubset_subset (φ : ℝ≥0 → E → E) (S : Set E) :
    largestInvSubset φ S ⊆ S :=
  fun _ hx => hx.1

/-- A LaSalle setup bundles a continuous semiflow on `E`, a compact positively
invariant set `M`, a continuous Lyapunov function `V`, and its orbital
derivative `Vdot`, together with the hypotheses needed for LaSalle's
invariance principle. -/
structure LaSalleSetup (E : Type*) [TopologicalSpace E] where
  /-- The continuous semiflow (a `Flow` by the additive monoid `ℝ≥0`). -/
  φ : Flow ℝ≥0 E
  /-- The compact positively invariant set. -/
  M : Set E
  /-- The Lyapunov function. -/
  V : E → ℝ
  /-- The orbital derivative of `V`. -/
  Vdot : E → ℝ
  /-- `M` is compact. -/
  hM_compact : IsCompact M
  /-- `M` is nonempty. -/
  hM_nonempty : M.Nonempty
  /-- `M` is positively invariant under `φ`. -/
  hM_inv : IsInvariant φ M
  /-- `V` is continuous. -/
  hV_cont : Continuous V
  /-- `Vdot` is continuous. -/
  hVdot_cont : Continuous Vdot
  /-- `Vdot` is non-positive on `M`. -/
  hVdot_nonpos : ∀ x ∈ M, Vdot x ≤ 0
  /-- `V` is non-increasing along trajectories in `M`. -/
  hV_mono : ∀ x ∈ M, ∀ s t : ℝ≥0, s ≤ t → V (φ t x) ≤ V (φ s x)
  /-- If `V` is constant along the full forward trajectory of `x ∈ M`,
      then `Vdot x = 0`. -/
  hVdot_zero_of_const : ∀ x ∈ M, (∀ t : ℝ≥0, V (φ t x) = V x) → Vdot x = 0

namespace LaSalleSetup

variable {E : Type*} [TopologicalSpace E] (L : LaSalleSetup E)

/-- The zero set of the orbital derivative within `M`. -/
def zeroSet : Set E :=
  {x ∈ L.M | L.Vdot x = 0}

/-- The largest positively invariant subset of the zero set. -/
def targetSet : Set E :=
  largestInvSubset L.φ L.zeroSet

/-- `targetSet` is a subset of `M`. -/
theorem targetSet_subset_M : L.targetSet ⊆ L.M :=
  fun _ hx => hx.1.1

/-- `zeroSet` is a subset of `M`. -/
theorem zeroSet_subset_M : L.zeroSet ⊆ L.M :=
  fun _ hx => hx.1

end LaSalleSetup

end
