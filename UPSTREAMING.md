# Upstreaming to Mathlib

This file maps the contents of lc-manifolds against Mathlib, so that Mathlib maintainers and
reviewers can see what might belong in Mathlib, what it depends on, and where it overlaps with
existing Mathlib code. Nothing has been proposed to Mathlib yet. Inclusion is decided by the
Mathlib community, piece by piece, after discussion.

Checked against Mathlib `v4.36.0-rc2` (commit `9d581dfff2e4`), on 2026-11-12. The overlap search
was by name and topic in the Mathlib sources; it may have missed results stated under other names.

The companion file for the analytic foundations is
[lc-analysis/UPSTREAMING.md](https://github.com/glaroton/lc-analysis/blob/main/UPSTREAMING.md).
The rules for proposing pieces are the same, and are stated there: scope first on Zulip for new
theories, small PRs, disclosure of AI use with the `LLM-generated` label, and an author who
understands and defends every line.

## Classes

| Class | Meaning |
|---|---|
| **E** | Extends a theory Mathlib already has. |
| **N** | A new theory, independent of the Michal–Bastiani calculus. Needs a scope discussion on Zulip. |
| **F** | Built on the Michal–Bastiani calculus of lc-analysis. Can only be proposed after that framework is accepted. |
| **X** | A counterexample, for Mathlib's `Counterexamples/` project. |

## The main point

Mathlib's manifolds (`ChartedSpace`, `ModelWithCorners`, `IsManifold`) are modeled on normed
spaces, with Fréchet calculus. The manifolds of lc-analysis are modeled on locally convex spaces,
with the Michal–Bastiani calculus: this is what manifolds of mappings and groups of
diffeomorphisms need. lc-manifolds reuses Mathlib's `ChartedSpace` and `StructureGroupoid`, with
the groupoid of Michal–Bastiani smooth maps in place of `contDiffGroupoid`. So almost all of
lc-manifolds is class F: it can only go to Mathlib if the calculus of lc-analysis does, and then
it would have to be reconciled with Mathlib's normed manifolds rather than run in parallel.

Two parts are independent of the calculus:

* `MetricGeometry/`: length metrics, interior metric spaces, midpoints, short curves and the
  metric Hopf–Rinow theorem, for symmetric and asymmetric distances. It builds on Mathlib's
  `eVariationOn` and `variationOnFromTo`. Mathlib has no Hopf–Rinow theorem and no length spaces.
* `Examples/McAlpin.lean`: McAlpin's complete Riemannian manifold without shortest curves, an
  ellipsoid in `ℓ²`, stated with the norm of `ℓ²` and no manifold structure.

## Overlaps with Mathlib

| Here | In Mathlib | Relation |
|---|---|---|
| `Manifold/`, `Tangent/` | `IsManifold`, `TangentBundle`, `mfderiv` | Same objects, normed models and Fréchet calculus in Mathlib; locally convex models here. |
| `VectorField/Basic.lean` | `VectorField.mlieBracket` (`Geometry/Manifold/VectorField/LieBracket.lean`) | The Lie bracket of vector fields. |
| `Flow/` | `IsMIntegralCurve`, existence and uniqueness (`Geometry/Manifold/IntegralCurve/`) | Mathlib has integral curves on manifolds modeled on Banach spaces; flows, their smooth dependence and maximal flows are not there. |
| `Bundle/`, `Connection/`, `Metric/LeviCivita.lean` | `VectorBundle`, `CovariantDerivative`, Levi-Civita and torsion (`Geometry/Manifold/VectorBundle/CovariantDerivative/`) | Same notions in the normed setting. The weak metrics and the projector connections here have no Mathlib counterpart. |
| `Metric/Finsler*.lean` | `pathELength`, `riemannianEDist` (`Geometry/Manifold/Riemannian/PathELength.lean`) | Mathlib's distance is already defined for Finsler-type norms on tangent spaces, as its docstring notes. |
| `DifferentialForm/` | `extDeriv` (`Analysis/Calculus/DifferentialForm/Basic.lean`) | Local exterior derivative on normed spaces in Mathlib; forms on manifolds, wedge product, Cartan's formula and de Rham cohomology are not there. |
| `Submanifold/`, `RoughBoundary/` | `IsImmersion`, `IsSmoothEmbedding`, `ModelWithCorners.interior`, `boundary` | Normed counterparts. Manifolds with rough boundary (locally convex subsets with dense interior) are more general than manifolds with corners. |

No Mathlib counterpart was found for sprays and the exponential map (`Geodesic/`), local additions
(`LocalAddition/`), manifolds of mappings (`MappingSpace/`), symplectic manifolds and Darboux's
theorem (`Symplectic/`), almost complex structures and the Nijenhuis tensor (`Complex/`), or real
analytic manifolds in Milnor's sense (`Analytic/`).

## Inventory by folder

| Folder | Contents | Class | Status |
|---|---|---|---|
| `Manifold/` | Manifolds modeled on locally convex spaces, `C^k` maps, products, `C^{k,ℓ}` maps, local diffeomorphisms, atlases with varying models | F | – |
| `Tangent/` | Tangent bundle, tangent map, double and iterated tangent bundles | F | – |
| `VectorField/` | Vector fields, Lie bracket, derivations, the Frobenius theorem on Banach manifolds | F | – |
| `Flow/` | Local and maximal flows on Banach manifolds, completeness, analytic flows, Lie derivative | F | – |
| `DifferentialForm/` | Forms, exterior derivative, wedge product, Lie derivative and Cartan's formula, Poincaré lemma, de Rham cohomology | F | – |
| `Bundle/` | Vector bundles, Hom and dual bundles, sections, connections, pullback connections, bundle metrics | F | – |
| `Connection/` | Connections, covariant derivatives along curves, connection forms, projector connections | F | – |
| `Geodesic/` | Sprays, geodesics, exponential map, normal neighbourhoods | F | – |
| `Metric/` | Weak pseudo-Riemannian metrics (Krein type included), Levi-Civita, Finsler structures, Finsler distance, Hopf–Rinow for Finsler manifolds | F | – |
| `MetricGeometry/` | Length metrics, interior spaces, midpoints, metric Hopf–Rinow, asymmetric distances | N (E where it extends `eVariationOn`) | – |
| `Submanifold/` | Notions of submanifolds and immersions, embedded submanifolds, local additions on submanifolds | F | – |
| `LocalAddition/` | Local additions and their normalization | F | – |
| `MappingSpace/` | Manifolds of continuous and `C^ℓ` maps on compact manifolds, their topologies, tangent spaces, exponential law | F | – |
| `RoughBoundary/` | Manifolds with rough boundary, graphs, subspaces, tangent bundle | F | – |
| `Analytic/` | Real and complex analytic manifolds, analytic forms, analytic submanifolds | F | – |
| `Complex/` | Nijenhuis operators, almost complex structures, Newlander–Nirenberg | F | – |
| `Symplectic/` | Symplectic manifolds, cotangent bundle, Darboux (smooth and real analytic) | F | – |
| `Examples/` | Spheres, unitary groups, `Diff⁺(S¹)`, subspaces and graphs; counterexamples | F; counterexamples X | – |

### Counterexamples

| File | Contents | Depends on the calculus |
|---|---|---|
| `Examples/McAlpin.lean` | A complete Riemannian manifold without shortest curves | no |
| `Examples/Lemniscate.lean` | The figure eight is an injective immersion that is not initial | yes |
| `Examples/Phillips.lean` | `c₀ ⊆ ℓ^∞` is embedded but not split (Phillips' lemma) | yes |
| `Examples/Counterexamples.lean` | Weak immersions that are not immersions | yes |
| `Examples/FinslerCusp.lean` | A Finsler length structure that is not a Finsler metric | yes |
| `Examples/IncompleteFinsler.lean` | A Finsler lemma fails without completeness of the model | yes |
| `Examples/NoLeviCivita.lean` | A weak Riemannian metric without Levi-Civita connection | yes |

## Suggested order

1. `MetricGeometry/`, after a scope discussion on Zulip: it extends Mathlib's lengths of curves
   and needs nothing from lc-analysis.
2. McAlpin's example, for `Counterexamples/`.
3. Everything else only after the design discussion on the Michal–Bastiani calculus (see
   lc-analysis/UPSTREAMING.md), and then as a generalization of Mathlib's normed manifolds rather
   than as a second theory.
