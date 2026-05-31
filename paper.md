# lasalle-lean: Formal Proofs of LaSalle's Invariance Principle in Lean 4

Ben Cassie  
2026

## Abstract

`lasalle-lean` is a Lean 4 / Mathlib library formalising LaSalle's invariance principle for continuous semiflows. The library works with Mathlib's `Flow` over non-negative time, defines omega-limit points, the largest invariant subset of a set, a `LaSalleSetup` packaging a compact positively invariant set and Lyapunov data, proves omega-limit nonemptiness, compactness, and invariance, proves constancy of the Lyapunov function on omega-limit sets, and proves convergence into the largest invariant subset of the zero-derivative set. The development contains zero `sorry`, zero `admit`, and uses standard Lean/Mathlib axioms only. It supplies the continuous-time invariant-set component needed by Lyapunov and synchronisation libraries.

## 1. Introduction

Lyapunov stability theorems often require a strict decrease condition: `Vdot < 0` away from the target. Many important systems only satisfy `Vdot <= 0`. In that case a trajectory may approach a whole invariant set on which `Vdot = 0`, rather than a single equilibrium. LaSalle's invariance principle is the classical theorem that describes this behaviour.

The library studies a continuous semiflow

```text
Flow R>=0 E
```

on a topological or normed space `E`. A `LaSalleSetup` packages the flow, a compact positively invariant set `M`, a continuous Lyapunov function `V`, an orbital derivative `Vdot` satisfying `Vdot <= 0` on `M`, monotonicity of `V` along trajectories, and a linking condition between `Vdot = 0` and constancy of `V`.

The zero set is

```text
zeroSet = {x in M | Vdot(x) = 0}.
```

The target set is the largest positively invariant subset of `zeroSet`. The main theorem says that the omega-limit set of any point in `M` is contained in that target set.

This is stronger than basic Lyapunov stability. It proves convergence toward the invariant part of the zero-derivative set, not merely boundedness or non-increase of an energy function.

## 2. Library Overview

The project is organised into three implementation modules plus a root import file:

- `LasalleLean/Defs.lean` defines `omegaLimitPt`, `largestInvSubset`, `LaSalleSetup`, `zeroSet`, and `targetSet`.
- `LasalleLean/OmegaLimit.lean` proves omega-limit invariance, nonemptiness, compactness, and containment in `M`.
- `LasalleLean/LaSalle.lean` proves convergence of Lyapunov values, constancy on omega-limit sets, membership in the zero set, and the main LaSalle convergence theorem.
- `LasalleLean.lean` is the root module importing the library.

The project depends on Lean `v4.28.0` and Mathlib `v4.28.0`.

The development builds directly on Mathlib's `Dynamics.OmegaLimit` and `Dynamics.Flow` infrastructure. This avoids rebuilding the general theory of omega-limit sets and keeps the library focused on the LaSalle argument.

## 3. Theorem Inventory

The source contains nine headline results, organised into three layers.

### Layer 1 - Omega-Limit Set

1. `omega_limit_invariant` — The omega-limit set is positively invariant, using Mathlib's `Flow.isInvariant_omegaLimit`.

2. `omega_limit_nonempty` — For `x in M`, the omega-limit set `omega(x)` is nonempty. Compactness and positive invariance provide the recurrence/cluster-point infrastructure.

3. `omega_limit_isCompact` — The omega-limit set is compact, using closedness of omega-limits and containment in compact `M`.

4. `omegaLimitPt_subset_M` — The omega-limit set is contained in the compact positively invariant set `M`.

### Layer 2 - Lyapunov Constancy

5. `V_tendsto_of_mem` — The scalar function `V(phi(t,x))` converges as `t -> infinity`. The proof uses antitonicity from Lyapunov monotonicity and boundedness below from compactness.

6. `lyapunov_constant_on_omega_limit` — `V` is constant on `omega(x)`. Every point of the omega-limit set is a cluster point of the trajectory, and continuity forces the same limiting value.

7. `V_const_along_omega_limit_trajectory` — If `y in omega(x)`, then

```text
V(phi(t,y)) = V(y)
```

for all forward times `t`.

### Layer 3 - LaSalle Convergence

8. `omega_limit_subset_zeroSet` — The omega-limit set is contained in `{Vdot = 0} ∩ M`.

9. `lasalle_convergence` — The main theorem:

```text
omega(x) subset targetSet.
```

Thus trajectories converge, in the omega-limit sense, into the largest invariant subset of the zero-derivative set.

## 4. Key Technical Highlights

### Stronger Than Basic Lyapunov

Basic Lyapunov arguments often prove stability from non-increase of `V`, or asymptotic stability from strict decrease away from an equilibrium. LaSalle handles the more subtle case `Vdot <= 0`, where equality may hold on a nontrivial set.

The conclusion is correspondingly set-valued. The trajectory approaches the largest invariant subset of `{Vdot = 0}`, not necessarily a single point.

### The Omega-Limit Argument

Compactness of `M` ensures that forward trajectories have omega-limit points. Positive invariance keeps those limit points inside `M`. Invariance of omega-limit sets then lets the proof follow entire forward trajectories starting from omega-limit points.

The Lyapunov function is monotone along the original trajectory and bounded below, so it converges. Any omega-limit point is reached along a time subsequence, so continuity forces `V` to take the limiting value there. Invariance then shows `V` remains constant along omega-limit trajectories.

### Mathlib Infrastructure

The library sits directly on Mathlib's `Dynamics.OmegaLimit` and `Dynamics.Flow`. This is important engineering: the difficult topological facts about omega-limit sets are imported from the shared library, and `lasalle-lean` focuses on assembling them into the invariance-principle proof.

### Kuramoto Connection

The library closes the documented LaSalle gap in the Kuramoto formalisation. Kuramoto synchronisation proofs often show that a Lyapunov function decreases and then invoke LaSalle or Barbalat-type reasoning to conclude convergence to synchrony. `lasalle-lean` supplies the invariant-set theorem needed for that final step.

## 5. Relation to Sibling Libraries

`kuramoto-lean` has DOI `10.5281/zenodo.20468619`. Its Lyapunov descent arguments are a natural application site for LaSalle invariance.

`lyapunov-odes-lean` factors out the LaSalle step through a hypothesis that `V` tends to zero. `lasalle-lean` supplies omega-limit infrastructure that can prove such convergence hypotheses under compactness and invariance assumptions.

`contraction-lean` has DOI `10.5281/zenodo.20474762`. Contraction gives exponential convergence through metric decay. LaSalle gives asymptotic convergence to invariant sets under weaker non-increase hypotheses.

`hopfield-lean` has DOI `10.5281/zenodo.20474169` and proves a discrete Lyapunov convergence theorem. `lasalle-lean` is a continuous-time analogue built around omega-limit sets.

## 6. AI Safety Significance

Many safety-relevant dynamical arguments use energy functions that are non-increasing but not strictly decreasing. In such systems, knowing that an objective never increases is not enough to identify where trajectories go. LaSalle's principle supplies the missing invariant-set conclusion.

Formalising the theorem makes the assumptions explicit: compactness, positive invariance, continuity, monotonicity of `V`, and the link between zero derivative and constancy. These are exactly the side conditions that are often left implicit in informal safety arguments about convergence.

The library does not certify deployed systems. It provides a checked mathematical component for reasoning about simplified continuous-time learning dynamics, synchronisation models, control systems, and invariant-set convergence.

## 7. Conclusion

`lasalle-lean` formalises LaSalle's invariance principle in Lean 4. It defines omega-limit and invariant-set notions, proves the needed omega-limit properties, proves constancy of Lyapunov functions on omega-limit sets, and derives convergence into the largest invariant subset of the zero-derivative set. It is a reusable continuous-time convergence component for the Lean formalisation ecosystem.

## References

LaSalle, J. P. (1960). *Some extensions of Liapunov's second method*. IRE Transactions on Circuit Theory, 7(4), 520-527.

Khalil, H. K. (2002). *Nonlinear Systems* (3rd ed.). Prentice Hall.

The Mathlib Community. (2024). *The Lean Mathematical Library*. GitHub repository. <https://github.com/leanprover-community/mathlib4>

Cassie, B. (2026). *kuramoto-lean: A Sorry-Free Lean 4 Library for Finite-N Kuramoto Synchronisation Dynamics*. Zenodo. <https://doi.org/10.5281/zenodo.20468619>

Cassie, B. (2026). *contraction-lean*. Zenodo. <https://doi.org/10.5281/zenodo.20474762>

Cassie, B. (2026). *hopfield-lean: Lean 4 Formal Proofs of Hopfield Network Energy Descent and Attractor Convergence*. Zenodo. <https://doi.org/10.5281/zenodo.20474169>
