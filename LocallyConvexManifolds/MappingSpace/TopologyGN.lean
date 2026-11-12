/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.MappingSpace.Topology

/-!
# The chart topology of `C^ℓ(M, N)` and the compact-open `C^ℓ` topology

We prove that the chart topology `CkMap.chartTopology` of `C^ℓ(M, N)` (local representatives on open
subsets of compact sets in charts) is, for a locally compact model of `M`, the compact-open `C^ℓ`
topology of [GN26, Definition 4.1.2]: the initial topology with respect to the iterated tangent maps
`f ↦ T^j f ∈ C(T^j M, T^j N)`, `j ≤ ℓ` (`MBMfld.gnTopology`), and for `ℓ = ∞` with respect to all of
them (`MBMfld.gnTopologySm`, the projective limit of [GN26, Remark 4.1.3(b)]).

The topology of `C^ℓ(M, N)` is the jet topology, not the chart topology; [GN26, Theorem 4.2.2(b)]
for it, for every Hausdorff `M` and every model, is `MBMfld.jetTopology_eq_gnTopology`
(`MappingSpace/TopologyJet.lean`), and `CkMap.topology_eq_gnTopology`,
`SmoothMap.topology_eq_gnTopologySm` for `N` in any universe (`MappingSpace/TopologyULift.lean`).
For a locally compact model the two topologies agree (`CkMap.chartTopology_eq_jetTopology`), so the
theorems here give a second proof of (b) in that case, which does not use `CompactLocalizable`.

## Main results

* `chartTopology_eq_gnTopology`, `chartTopologySm_eq_gnTopologySm`: for a locally compact model of
  `M`, by induction on `ℓ` from the recursion of [GN26, Lemma 4.1.6] for both topologies
  (`chartTopology_succ`, `MBMfld.gnTopology_succ`).

## Implementation notes

* Glöckner–Neeb obtain (b) "by construction", their charts being homeomorphisms for the topology
  of [GN26, Definition 4.1.2] by the results of their Section 4.1. Here the two topologies are
  compared by induction, through [GN26, Lemma 4.1.6]. We do not claim this argument is new.
* Universes: the induction runs over the bundled manifolds `MBMfld.{u, v}`, whose carriers live
  in `Type (max u v)`, `u` the universe of `M` and of the models: the iteration `T^j` needs `N` and
  `TN` to be carriers of one bundled type. For `N` in any universe, [GN26, Definition 4.1.2] is
  `CkMap.gnTopology` (through `ULift N`, which is `MBMfld.gnTopology` when `N` is a carrier), and
  the chart topology is that topology for a locally compact model:
  `CkMap.chartTopology_eq_gnTopology`, `SmoothMap.chartTopologySm_eq_gnTopologySm`
  (`MappingSpace/TopologyULift.lean`).

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Function TopologicalSpace
open scoped Topology

noncomputable section

universe u v

namespace LocallyConvex.Manifolds

/-- **The chart topology is the compact-open `C^ℓ` topology** ([GN26, Definition 4.1.2]),
for a locally compact model of `X`. -/
theorem chartTopology_eq_gnTopology (ℓ : ℕ) :
    ∀ (X : MBMfld.{u, u}) (Y : MBMfld.{u, v}) [LocallyCompactSpace X.Model],
      CkMap.chartTopology X.Model Y.Model ℓ X.Carrier Y.Carrier = MBMfld.gnTopology ℓ X Y := by
  induction ℓ with
  | zero =>
    intro X Y _
    rw [chartTopology_zero, MBMfld.gnTopology]
    have e : ∀ j : Fin (0 + 1), TopologicalSpace.induced (MBMfld.iterMapC (X := X) (Y := Y)
        (ℓ := 0) (Nat.lt_succ_iff.1 j.2)) inferInstance =
        TopologicalSpace.induced CkMap.toC inferInstance := fun j ↦ by
      obtain rfl : j = 0 := Fin.fin_one_eq_zero j
      congr 1
    exact le_antisymm (le_iInf fun j ↦ (e j).ge) ((iInf_le _ 0).trans (e 0).le)
  | succ ℓ ih =>
    intro X Y _
    calc CkMap.chartTopology X.Model Y.Model (ℓ + 1) X.Carrier Y.Carrier
        = TopologicalSpace.induced CkMap.toC inferInstance ⊓
            TopologicalSpace.induced MBMfld.tangentCk (CkMap.chartTopology (MBMfld.tangent X).Model
              (MBMfld.tangent Y).Model ℓ (MBMfld.tangent X).Carrier (MBMfld.tangent Y).Carrier) :=
          chartTopology_succ
      _ = TopologicalSpace.induced CkMap.toC inferInstance ⊓
            TopologicalSpace.induced MBMfld.tangentCk
              (MBMfld.gnTopology ℓ (MBMfld.tangent X) (MBMfld.tangent Y)) := by
          rw [← ih (MBMfld.tangent X) (MBMfld.tangent Y)]
      _ = MBMfld.gnTopology (ℓ + 1) X Y := (MBMfld.gnTopology_succ ℓ X Y).symm

/-- **The chart topology of `C^∞` is the compact-open `C^∞` topology** ([GN26,
Definition 4.1.2] and Remark 4.1.3(b)), for a locally compact model of `X`. -/
theorem chartTopologySm_eq_gnTopologySm (X : MBMfld.{u, u}) (Y : MBMfld.{u, v})
    [LocallyCompactSpace X.Model] :
    SmoothMap.chartTopologySm X.Model Y.Model X.Carrier Y.Carrier = MBMfld.gnTopologySm X Y := by
  rw [MBMfld.gnTopologySm_eq]
  exact iInf_congr fun ℓ ↦ by rw [chartTopology_eq_gnTopology ℓ X Y]

end LocallyConvex.Manifolds
