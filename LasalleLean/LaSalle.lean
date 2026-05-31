/-
Copyright (c) 2025. All rights reserved.
Released under the MIT license.

# LaSalle's Invariance Principle

This file proves the two main results of LaSalle's invariance principle:
- `lyapunov_constant_on_omega_limit`: the Lyapunov function `V` is constant
  on the ω-limit set of any point in `M`
- `lasalle_convergence`: the ω-limit set of any point in `M` is contained
  in the largest positively invariant subset of `{x ∈ M | Vdot x = 0}`
-/
import LasalleLean.OmegaLimit

open Set Filter Topology NNReal omegaLimit

noncomputable section

namespace LaSalleSetup

variable {E : Type*} [TopologicalSpace E]

/-! ### Monotonicity and convergence of V (no T2Space needed) -/

/-- `V(φ(t, x))` is antitone in `t` for `x ∈ M`. -/
theorem V_antitone_of_mem (L : LaSalleSetup E) {x : E} (hx : x ∈ L.M) :
    Antitone (fun t : ℝ≥0 => L.V (L.φ t x)) :=
  fun _ _ hst => L.hV_mono x hx _ _ hst

/-- The range of `t ↦ V(φ(t, x))` is bounded below for `x ∈ M`. -/
theorem V_bddBelow_of_mem (L : LaSalleSetup E) {x : E} (hx : x ∈ L.M) :
    BddBelow (range (fun t : ℝ≥0 => L.V (L.φ t x))) := by
  obtain ⟨m, hm⟩ := (L.hM_compact.image L.hV_cont).bddBelow
  exact ⟨m, fun v ⟨t, ht⟩ => ht ▸ hm (mem_image_of_mem L.V (L.hM_inv t hx))⟩

/-- `V(φ(t, x))` converges as `t → ∞` for `x ∈ M`. -/
theorem V_tendsto_of_mem (L : LaSalleSetup E) {x : E} (hx : x ∈ L.M) :
    ∃ c : ℝ, Tendsto (fun t : ℝ≥0 => L.V (L.φ t x)) atTop (𝓝 c) :=
  ⟨_, tendsto_atTop_ciInf (L.V_antitone_of_mem hx) (L.V_bddBelow_of_mem hx)⟩

/-! ### Results requiring T2Space -/

variable [T2Space E] (L : LaSalleSetup E)

/-! ### V is constant on the omega-limit set -/

/-- `V` is constant on the ω-limit set of any point `x ∈ M`.

**Proof**: Since `V(φ(t,x))` is antitone and bounded below (by
compactness of `M`), it converges to some `c` as `t → ∞`. For any
`y ∈ ω(x)`, `y` is a cluster point of `t ↦ φ(t,x)`, so by
continuity of `V` and uniqueness of limits in T₂ spaces, `V(y) = c`. -/
theorem lyapunov_constant_on_omega_limit {x : E} (hx : x ∈ L.M) :
    ∃ c : ℝ, ∀ y ∈ omegaLimitPt L.φ x, L.V y = c := by
  obtain ⟨c, hc⟩ := V_tendsto_of_mem L hx
  use c
  intro y hy
  have hy_cluster : MapClusterPt y atTop (fun t => L.φ.toFun t x) := by
    rwa [omegaLimitPt, mem_omegaLimit_singleton_iff_map_cluster_point] at hy
  have hV_y : MapClusterPt (L.V y) atTop (fun t => L.V (L.φ.toFun t x)) := by
    rw [mapClusterPt_iff_frequently] at *
    intro s hs
    exact hy_cluster (L.V ⁻¹' s) (L.hV_cont.continuousAt.preimage_mem_nhds hs)
  unfold MapClusterPt at hV_y
  simp_all +decide [ClusterPt, Filter.Tendsto]
  contrapose! hV_y
  simp +decide [Filter.inf_eq_bot_iff]
  exact ⟨{z | |z - L.V y| < |L.V y - c| / 2},
    Metric.ball_mem_nhds _ (half_pos (abs_pos.mpr (sub_ne_zero.mpr hV_y))),
    {z | |z - c| < |L.V y - c| / 2},
    Filter.eventually_atTop.mp
      (hc (Metric.ball_mem_nhds _ (half_pos (abs_pos.mpr (sub_ne_zero.mpr hV_y))))),
    Set.eq_empty_of_forall_notMem fun z hz => by
      cases abs_cases (z - L.V y) <;> cases abs_cases (z - c) <;>
        cases abs_cases (L.V y - c) <;> linarith [hz.1.out, hz.2.out]⟩

/-! ### The omega-limit set lies in the zero set of Vdot -/

/-- For any `y` in the ω-limit of `x ∈ M`, `V` is constant along the
entire forward trajectory of `y`. -/
theorem V_const_along_omega_limit_trajectory {x : E} (hx : x ∈ L.M)
    {y : E} (hy : y ∈ omegaLimitPt L.φ x) :
    ∀ t : ℝ≥0, L.V (L.φ t y) = L.V y := by
  obtain ⟨c, hc⟩ := L.lyapunov_constant_on_omega_limit hx
  intro t
  rw [hc y hy, hc (L.φ t y) (L.omega_limit_invariant t hy)]

/-- The ω-limit of `x ∈ M` lies in the zero set `{z ∈ M | Vdot z = 0}`. -/
theorem omega_limit_subset_zeroSet {x : E} (hx : x ∈ L.M) :
    omegaLimitPt L.φ x ⊆ L.zeroSet := by
  intro y hy
  exact ⟨L.omegaLimitPt_subset_M hx hy,
    L.hVdot_zero_of_const y (L.omegaLimitPt_subset_M hx hy)
      (L.V_const_along_omega_limit_trajectory hx hy)⟩

/-! ### LaSalle convergence theorem -/

/-- **LaSalle's Invariance Principle**: The ω-limit set of any point
`x ∈ M` is contained in the largest positively invariant subset of
`{z ∈ M | Vdot z = 0}`.

Combined with `omega_limit_nonempty` and `omega_limit_isCompact`, this
shows that every trajectory starting in `M` asymptotically approaches
the target set. -/
theorem lasalle_convergence {x : E} (hx : x ∈ L.M) :
    omegaLimitPt L.φ x ⊆ L.targetSet := by
  intro y hy
  exact ⟨L.omega_limit_subset_zeroSet hx hy, fun t =>
    L.omega_limit_subset_zeroSet hx (L.omega_limit_invariant t hy)⟩

end LaSalleSetup

end
