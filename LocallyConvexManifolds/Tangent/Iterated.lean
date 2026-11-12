/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.Tangent.Map
public import LocallyConvexManifolds.MappingSpace.Ck

/-!
# Iterated tangent bundles and the compact-open `C^ℓ` topology

Glöckner and Neeb [GN26, Definition 4.1.2] give `C^ℓ(M, N)` the initial topology with respect to the
iterated tangent maps `f ↦ T^j f ∈ C(T^j M, T^j N)`, `j ≤ ℓ`, each space of continuous maps with the
compact-open topology. This file sets up the iterated tangent bundles and the iterated tangent maps
of the library's manifolds (modeled on Hausdorff locally convex spaces) and defines that topology.

## Main definitions

* `MBMfld`: a bundled manifold (model space and carrier, with all their instances).
  `MBMfld.tangent`: its tangent bundle, modeled on `E × E`; `MBMfld.iter j X = T^j X`.
* `MBMfld.iterMap j f = T^j f`, by `T^(j+1) f = T^j (T f)`; `MBMfld.contMDiffMB_iterMap`: it is
  `C^k` if `f` is `C^(k+j)`; `MBMfld.iterMapC`, `MBMfld.iterMapSm`: as continuous maps.
* `MBMfld.gnTopology ℓ X Y`: the topology of [GN26, Definition 4.1.2] on `C^ℓ(X, Y)`;
  `MBMfld.gnTopologySm X Y`: the case `ℓ = ∞`.

## Main results

* `MBMfld.gnTopology_succ`: the topology of `C^(ℓ+1)(X, Y)` is initial with respect to `f ↦ f`
  and `f ↦ Tf ∈ C^ℓ(TX, TY)` (the statement used in the proof of [GN26, Lemma 4.1.6]).
* `MBMfld.gnTopologySm_eq`: the `C^∞` topology is the projective limit of the `C^ℓ` topologies
  [GN26, Remark 4.1.3(b)].

## Implementation notes

* The tangent bundle construction changes both the model space and the carrier, so the iteration
  runs over the bundled structure `MBMfld.{u, v}`: the model lives in `Type u` and the carrier in
  `Type (max u v)`, the universe of its tangent bundle, so that `T` maps `MBMfld.{u, v}` to
  itself. The manifolds of mappings `C^ℓ(X, Y)` take `X : MBMfld.{u, u}` (the library's `C^ℓ` maps
  have source and model in one universe) and `Y : MBMfld.{u, v}`: the target lives in a universe
  `max u v`. A target `N` in any universe is handled through `ULift N` (`CkMap.gnTopology`,
  `MappingSpace/TopologyULift.lean`).

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Function TopologicalSpace
open scoped Topology
open LocallyConvex.Analysis

noncomputable section

universe u v w

namespace LocallyConvex.Manifolds

set_option linter.checkUnivs false in
/-- **A bundled manifold**: a carrier in `Type (max u v)` with a manifold structure modeled on a
Hausdorff locally convex space in `Type u`. Bundling makes it possible to iterate the tangent
bundle construction, which changes both the model and the carrier; the universe `max u v` of the
carrier is stable under it. -/
structure MBMfld where
  /-- The model space. -/
  Model : Type u
  [addCommGroup : AddCommGroup Model]
  [module : Module ℝ Model]
  [topologicalSpace : TopologicalSpace Model]
  [isTopologicalAddGroup : IsTopologicalAddGroup Model]
  [continuousSMul : ContinuousSMul ℝ Model]
  [locallyConvexSpace : LocallyConvexSpace ℝ Model]
  [t2Space : T2Space Model]
  /-- The manifold. -/
  Carrier : Type (max u v)
  [topologicalSpaceCarrier : TopologicalSpace Carrier]
  [chartedSpace : ChartedSpace Model Carrier]
  [mbManifold : MBManifold Model Carrier]

attribute [instance] MBMfld.addCommGroup MBMfld.module MBMfld.topologicalSpace
  MBMfld.isTopologicalAddGroup MBMfld.continuousSMul MBMfld.locallyConvexSpace MBMfld.t2Space
  MBMfld.topologicalSpaceCarrier MBMfld.chartedSpace MBMfld.mbManifold

namespace MBMfld

/-- The bundled manifold `M` modeled on `E`. -/
abbrev of (E : Type u) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
    (M : Type (max u v)) [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M] :
    MBMfld.{u, v} :=
  ⟨E, M⟩

/-- **The tangent bundle** of a bundled manifold, modeled on `E × E`. -/
abbrev tangent (X : MBMfld.{u, v}) : MBMfld.{u, v} :=
  ⟨X.Model × X.Model, TangentBundle X.Model X.Carrier⟩

/-- The model of the tangent bundle is `E × E`. -/
theorem tangent_model (X : MBMfld.{u, v}) : (tangent X).Model = (X.Model × X.Model) :=
  rfl

/-- **The iterated tangent bundles** `T^j X`. -/
def iter (j : ℕ) (X : MBMfld.{u, v}) : MBMfld.{u, v} := tangent^[j] X

/-- `T^(j+1) X = T^j (T X)`. -/
theorem iter_succ (j : ℕ) (X : MBMfld.{u, v}) : iter (j + 1) X = iter j (tangent X) :=
  rfl

/-- The model of an iterated tangent bundle is locally compact if the original model is. -/
instance locallyCompactSpace_tangent (X : MBMfld.{u, v}) [LocallyCompactSpace X.Model] :
    LocallyCompactSpace (tangent X).Model :=
  inferInstanceAs (LocallyCompactSpace (X.Model × X.Model))

/-- The model of `T^j X` is locally compact if that of `X` is. -/
theorem locallyCompactSpace_iter (j : ℕ) :
    ∀ (X : MBMfld.{u, v}) [LocallyCompactSpace X.Model], LocallyCompactSpace (iter j X).Model := by
  induction j with
  | zero => intro X _; exact ‹_›
  | succ j ih => intro X _; exact ih (tangent X)

/-- **The iterated tangent maps** `T^j f : T^j X → T^j Y`. -/
def iterMap : (j : ℕ) → {X : MBMfld.{u, v}} → {Y : MBMfld.{u, w}} → (X.Carrier → Y.Carrier) →
    (iter j X).Carrier → (iter j Y).Carrier
  | 0, _, _, f => f
  | j + 1, X, Y, f => iterMap j (X := tangent X) (Y := tangent Y) (tangentMap X.Model Y.Model f)

/-- `T^0 f = f`. -/
theorem iterMap_zero {X : MBMfld.{u, v}} {Y : MBMfld.{u, w}} (f : X.Carrier → Y.Carrier) :
    iterMap 0 f = f :=
  rfl

/-- `T^(j+1) f = T^j (T f)`. -/
theorem iterMap_succ (j : ℕ) {X : MBMfld.{u, v}} {Y : MBMfld.{u, w}} (f : X.Carrier → Y.Carrier) :
    iterMap (j + 1) f = iterMap j (X := tangent X) (Y := tangent Y)
      (tangentMap X.Model Y.Model f) :=
  rfl

/-- **Iterated tangent maps of `C^(k+j)` maps are `C^k`.** -/
theorem contMDiffMB_iterMap (k : ℕ) :
    ∀ (j : ℕ) {X : MBMfld.{u, v}} {Y : MBMfld.{u, w}} {f : X.Carrier → Y.Carrier},
      ContMDiffMB X.Model Y.Model (k + j) f →
        ContMDiffMB (iter j X).Model (iter j Y).Model k (iterMap j f) := by
  intro j
  induction j with
  | zero => intro X Y f hf; exact hf
  | succ j ih =>
    intro X Y f hf
    exact ih (X := tangent X) (Y := tangent Y)
      (ContMDiffMB.tangentMap (k := k + j) (by rwa [← Nat.add_assoc] at hf))

/-- Iterated tangent maps `T^j f`, `j ≤ ℓ`, of `C^ℓ` maps are continuous. -/
theorem continuous_iterMap {ℓ j : ℕ} (hj : j ≤ ℓ) {X : MBMfld.{u, u}} {Y : MBMfld.{u, v}}
    (f : CkMap X.Model Y.Model ℓ X.Carrier Y.Carrier) : Continuous (iterMap j f) :=
  continuousOn_univ.1 (contMDiffMB_iterMap (ℓ - j) j
    (by rw [Nat.sub_add_cancel hj]; exact f.contMDiffMB)).1

/-- `T^j f` as a continuous map, for `f ∈ C^ℓ(X, Y)` and `j ≤ ℓ`. -/
def iterMapC {ℓ j : ℕ} (hj : j ≤ ℓ) {X : MBMfld.{u, u}} {Y : MBMfld.{u, v}}
    (f : CkMap X.Model Y.Model ℓ X.Carrier Y.Carrier) : C((iter j X).Carrier, (iter j Y).Carrier) :=
  ⟨iterMap j f, continuous_iterMap hj f⟩

/-- The tangent map `T : C^(ℓ+1)(X, Y) → C^ℓ(TX, TY)`. -/
def tangentCk {ℓ : ℕ} {X : MBMfld.{u, u}} {Y : MBMfld.{u, v}}
    (f : CkMap X.Model Y.Model (ℓ + 1) X.Carrier Y.Carrier) :
    CkMap (tangent X).Model (tangent Y).Model ℓ (tangent X).Carrier (tangent Y).Carrier :=
  ⟨tangentMap X.Model Y.Model f, ContMDiffMB.tangentMap f.2⟩

/-- **The compact-open `C^ℓ` topology of [GN26, Definition 4.1.2]**: the initial topology on
`C^ℓ(X, Y)` with respect to the maps `f ↦ T^j f ∈ C(T^j X, T^j Y)`, `j ≤ ℓ`, each space of
continuous maps carrying the compact-open topology. -/
@[instance_reducible]
def gnTopology (ℓ : ℕ) (X : MBMfld.{u, u}) (Y : MBMfld.{u, v}) :
    TopologicalSpace (CkMap X.Model Y.Model ℓ X.Carrier Y.Carrier) :=
  ⨅ j : Fin (ℓ + 1), TopologicalSpace.induced (iterMapC (Nat.lt_succ_iff.1 j.2)) inferInstance

/-- `T^j f` as a continuous map, for `f ∈ C^∞(X, Y)`. -/
def iterMapSm (j : ℕ) {X : MBMfld.{u, u}} {Y : MBMfld.{u, v}}
    (f : SmoothMap X.Model Y.Model X.Carrier Y.Carrier) :
    C((iter j X).Carrier, (iter j Y).Carrier) :=
  iterMapC le_rfl (SmoothMap.toCk j f)

/-- **The compact-open `C^∞` topology of [GN26, Definition 4.1.2]**, `ℓ = ∞`: the initial
topology with respect to all the maps `f ↦ T^j f ∈ C(T^j X, T^j Y)`, `j ∈ ℕ`. -/
@[instance_reducible]
def gnTopologySm (X : MBMfld.{u, u}) (Y : MBMfld.{u, v}) :
    TopologicalSpace (SmoothMap X.Model Y.Model X.Carrier Y.Carrier) :=
  ⨅ j : ℕ, TopologicalSpace.induced (iterMapSm j) inferInstance

/-- The compact-open `C^∞` topology is the projective limit of the compact-open `C^ℓ` topologies
[GN26, Remark 4.1.3(b)]: it is initial with respect to the inclusions into the
`C^ℓ(X, Y)`. -/
theorem gnTopologySm_eq (X : MBMfld.{u, u}) (Y : MBMfld.{u, v}) :
    gnTopologySm X Y = ⨅ ℓ : ℕ, TopologicalSpace.induced (SmoothMap.toCk ℓ) (gnTopology ℓ X Y) := by
  refine le_antisymm (le_iInf fun ℓ ↦ ?_) (le_iInf fun j ↦ ?_)
  · simp only [gnTopology, induced_iInf, induced_compose]
    exact le_iInf fun j ↦ iInf_le_of_le (j : ℕ) (le_of_eq rfl)
  · refine iInf_le_of_le j ?_
    simp only [gnTopology, induced_iInf, induced_compose]
    exact iInf_le_of_le (Fin.last j) (le_of_eq rfl)

/-- **[GN26, Lemma 4.1.6]** (in the form used in its proof): the compact-open `C^(ℓ+1)`
topology is initial with respect to `f ↦ f ∈ C(X, Y)` and `f ↦ Tf ∈ C^ℓ(TX, TY)`, the latter with
the compact-open `C^ℓ` topology. This is a rearrangement of the infimum defining it. -/
theorem gnTopology_succ (ℓ : ℕ) (X : MBMfld.{u, u}) (Y : MBMfld.{u, v}) :
    gnTopology (ℓ + 1) X Y = TopologicalSpace.induced CkMap.toC inferInstance ⊓
      TopologicalSpace.induced tangentCk (gnTopology ℓ (tangent X) (tangent Y)) := by
  have hT : ∀ j : Fin (ℓ + 1), TopologicalSpace.induced (tangentCk (X := X) (Y := Y))
      (TopologicalSpace.induced (iterMapC (Nat.lt_succ_iff.1 j.2)) inferInstance) =
      TopologicalSpace.induced (iterMapC (X := X) (Y := Y) (ℓ := ℓ + 1)
        (Nat.lt_succ_iff.1 j.succ.2)) inferInstance := fun j ↦ by
    rw [induced_compose]
    rfl
  refine le_antisymm (le_inf ?_ ?_) (le_iInf fun j ↦ ?_)
  · exact iInf_le_of_le 0 le_rfl
  · simp only [gnTopology, induced_iInf]
    exact le_iInf fun j ↦ (iInf_le _ j.succ).trans (hT j).ge
  · refine Fin.cases ?_ (fun j ↦ ?_) j
    · exact inf_le_left
    · refine inf_le_right.trans ?_
      simp only [gnTopology, induced_iInf]
      exact (iInf_le _ j).trans (hT j).le

end MBMfld

end LocallyConvex.Manifolds
