/-
Copyright (c) 2025. All rights reserved.
Released under the MIT license.

# LaSalle's Invariance Principle — Omega-Limit Properties

This file proves key properties of omega-limit sets in the context
of a LaSalle setup:
- `omega_limit_nonempty`: the ω-limit set of any point in `M` is nonempty
- `omega_limit_isCompact`: the ω-limit set is compact
- `omega_limit_invariant`: the ω-limit set is positively invariant
-/
import LasalleLean.Defs

open Set Filter Topology NNReal omegaLimit

noncomputable section

namespace LaSalleSetup

variable {E : Type*} [TopologicalSpace E]

/-! ### Positive invariance (no T2Space needed) -/

/-- The omega-limit set of any point is positively invariant
under the flow `φ`. This holds for any topological space. -/
theorem omega_limit_invariant (L : LaSalleSetup E) {x : E} :
    IsInvariant L.φ (omegaLimitPt L.φ x) :=
  Flow.isInvariant_omegaLimit atTop L.φ {x} NNReal.tendsto_atTop_add

/-! ### Properties requiring T2Space -/

variable [T2Space E] (L : LaSalleSetup E)

/-- The closure of all forward images of `{x}` lies in `M` when `x ∈ M`. -/
private theorem closure_image2_subset_M {x : E} (hx : x ∈ L.M) (u : Set ℝ≥0) :
    closure (image2 (↑L.φ) u {x}) ⊆ L.M := by
  apply L.hM_compact.isClosed.closure_subset_iff.mpr
  intro z hz
  obtain ⟨t, _, x', hx', rfl⟩ := hz
  rw [mem_singleton_iff] at hx'
  subst hx'
  exact L.hM_inv t hx

/-- The omega-limit set of any point `x ∈ M` is contained in `M`. -/
theorem omegaLimitPt_subset_M {x : E} (hx : x ∈ L.M) :
    omegaLimitPt L.φ x ⊆ L.M := by
  intro y hy
  rw [omegaLimitPt, omegaLimit_def] at hy
  simp only [mem_iInter] at hy
  exact L.closure_image2_subset_M hx univ (hy univ univ_mem)

/-- The omega-limit set of any point `x ∈ M` is nonempty. -/
theorem omega_limit_nonempty {x : E} (hx : x ∈ L.M) :
    (omegaLimitPt L.φ x).Nonempty :=
  nonempty_omegaLimit_of_isCompact_absorbing atTop L.φ {x} L.hM_compact
    ⟨univ, univ_mem, L.closure_image2_subset_M hx univ⟩
    (singleton_nonempty x)

/-- The omega-limit set of any point `x ∈ M` is compact. -/
theorem omega_limit_isCompact {x : E} (hx : x ∈ L.M) :
    IsCompact (omegaLimitPt L.φ x) :=
  L.hM_compact.of_isClosed_subset (isClosed_omegaLimit _ _ _) (L.omegaLimitPt_subset_M hx)

end LaSalleSetup

end
