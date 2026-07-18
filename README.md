# lasalle-lean

[![thread](https://img.shields.io/badge/%F0%9F%A7%B5-how%20it%20works-1DA1F2)](https://x.com/thevelvetmonke)
[![Lean 4](https://img.shields.io/badge/Lean-4.28.0-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-purple)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)
[![Proofs](https://img.shields.io/badge/proofs-proven%20%2F%200%20sorry-brightgreen)](LasalleLean)
[![Zenodo](https://img.shields.io/badge/Zenodo-10.5281%2Fzenodo.20476034-blue)](https://zenodo.org/records/20476034)

**lasalle-lean: Formal Proofs of LaSalle's Invariance Principle in Lean 4**

Lean 4 formal proofs of LaSalle's invariance principle for continuous semiflows: ω-limit sets are nonempty, compact, and invariant; a Lyapunov function is constant on them; and trajectories converge into the largest invariant subset of the set where V̇ = 0.

**Zero sorry statements.** Standard axioms only (`propext`, `Classical.choice`, `Quot.sound`).

## What this is, and why it matters

This library formalizes LaSalle's invariance principle for continuous semiflows. Its headline theorem, `LaSalleSetup.lasalle_convergence`, proves that the omega-limit set of a trajectory starting in a compact invariant set lies inside the largest positively invariant subset of the set where the orbital derivative is zero.

The result handles the case where a Lyapunov function is nonincreasing but not strictly decreasing. Compactness and monotonicity give a limiting Lyapunov value, continuity makes that value constant on omega-limit points, and invariance carries the constancy along their future trajectories. The setup's derivative link then places those trajectories in the zero set.

The theorem assumes the continuous semiflow, compact invariant region, Lyapunov monotonicity, and the implication from orbitwise constancy to zero orbital derivative. It does not construct solutions from an ODE or prove these conditions for a specific system. Its conclusion is containment of the omega-limit set, not necessarily convergence to one equilibrium or a rate of approach.

## Background and motivation

Lyapunov's direct method proves stability when V̇ < 0 strictly. But for many real systems V̇ is only *non-positive* — V̇ ≤ 0, with equality on a whole set — and Lyapunov's theorem alone cannot conclude convergence. LaSalle's invariance principle is what closes that gap: trajectories must converge to the **largest invariant set contained in {V̇ = 0}**, not merely to where V̇ = 0 pointwise. This is the workhorse result behind convergence proofs for oscillator networks, adaptive control, and gradient-like flows. This library machine-checks it for continuous semiflows over a general space.

## Setting

A continuous semiflow `Flow ℝ≥0 E` (Mathlib's `Flow`, with non-negative time modelling forward evolution), a compact positively invariant set M, and a continuous Lyapunov function V with orbital derivative V̇ ≤ 0 on M and V non-increasing along trajectories. The development builds directly on Mathlib's `Dynamics.OmegaLimit` and `Dynamics.Flow`.

## Key definitions

- `omegaLimitPt φ x` — the ω-limit set of a point, via Mathlib's `omegaLimit` with `Filter.atTop`.
- `largestInvSubset φ S` — the largest positively invariant subset of S.
- `LaSalleSetup E` — bundles the semiflow, compact invariant M, continuous V, its orbital derivative `Vdot` with `Vdot ≤ 0` on M, monotonicity of V along trajectories, and the link between `Vdot = 0` and constancy of V.
- `zeroSet` = {x ∈ M | V̇(x) = 0}; `targetSet` = `largestInvSubset` of `zeroSet`.

## Theorem inventory

| # | Name | Statement |
|---|------|-----------|
| 1 | `omega_limit_invariant` | ω(x) is positively invariant (via `Flow.isInvariant_omegaLimit`) |
| 2 | `omega_limit_nonempty` | ω(x) is nonempty for x ∈ M (compact-absorbing) |
| 3 | `omega_limit_isCompact` | ω(x) is compact (closed ∩ compact M) |
| 4 | `omegaLimitPt_subset_M` | ω(x) ⊆ M |
| 5 | `V_tendsto_of_mem` | V(φ(t,x)) converges as t → ∞ (antitone + bounded below) |
| 6 | `lyapunov_constant_on_omega_limit` | V is constant on ω(x) (cluster-point + continuity) |
| 7 | `V_const_along_omega_limit_trajectory` | V(φ(t,y)) = V(y) for y ∈ ω(x) |
| 8 | `omega_limit_subset_zeroSet` | ω(x) ⊆ {V̇ = 0} ∩ M |
| 9 | `lasalle_convergence` | ω(x) ⊆ targetSet — the LaSalle convergence theorem |

## Design note

The library leans heavily on Mathlib's `Dynamics.OmegaLimit` and `Dynamics.Flow`. A `Flow ℝ≥0 E` models the continuous semiflow, so the classical ω-limit machinery (`Flow.isInvariant_omegaLimit`, `nonempty_omegaLimit_of_isCompact_absorbing`, `isClosed_omegaLimit`) is reused rather than rebuilt. Convergence of V along trajectories is obtained from antitonicity plus boundedness below (compactness of M), and constancy of V on ω(x) from a cluster-point argument: V∘φ(·,x) → c, and every y ∈ ω(x) is a cluster point, so continuity forces V(y) = c.

## Significance

This library closes the documented `sorry` gap in [kuramoto-lean](https://github.com/velvetmonkey/kuramoto-lean) — the LaSalle step that its Lyapunov-descent argument assumed — and supplies the trajectory-convergence infrastructure that [lyapunov-odes-lean](https://github.com/velvetmonkey/lyapunov-odes-lean) factored out as a hypothesis (`hVlim`). Together they give a full chain from V̇ ≤ 0 to convergence into the invariant target set.

## Project structure

```
LasalleLean/
├── Defs.lean       — omegaLimitPt, largestInvSubset, LaSalleSetup, zeroSet, targetSet
├── OmegaLimit.lean — omega_limit_invariant, omega_limit_nonempty,
│                     omega_limit_isCompact, omegaLimitPt_subset_M
└── LaSalle.lean    — V_tendsto_of_mem, lyapunov_constant_on_omega_limit,
                      V_const_along_omega_limit_trajectory, omega_limit_subset_zeroSet,
                      lasalle_convergence
LasalleLean.lean    — Root module
```

## Dependencies

- Lean 4.28.0
- Mathlib v4.28.0

## Paper

**lasalle-lean: Formal Proofs of LaSalle's Invariance Principle in Lean 4**
Ben Cassie (2026). Companion paper: [paper.md](paper.md).

DOI: https://doi.org/10.5281/zenodo.20476034

## Related work

- [kuramoto-lean](https://github.com/velvetmonkey/kuramoto-lean) — Lean 4 Kuramoto synchronisation and Lyapunov descent
- [lyapunov-odes-lean](https://github.com/velvetmonkey/lyapunov-odes-lean) — Lean 4 Lyapunov stability theorems for autonomous ODEs
- [contraction-lean](https://github.com/velvetmonkey/contraction-lean) — Lean 4 contraction theory and exponential convergence
- [barbalat-lean](https://github.com/velvetmonkey/barbalat-lean) — Lean 4 Barbalat's lemma

## Acknowledgements

Proofs in this library were generated using [Aristotle](https://aristotle.harmonic.fun), an AI proof assistant for Lean 4 and Mathlib. The proof discipline — zero sorry, standard axioms only — was specified by the author and enforced by the Lean type checker.

## Author

Ben Cassie · [@thevelvetmonke](https://x.com/thevelvetmonke)
## Part of the Lean proof corpus

One of a family of small, machine-checked Lean 4 developments. Index: [velvetmonkey/lean](https://github.com/velvetmonkey/lean) ([live index](https://velvetmonkey.github.io/lean)).
