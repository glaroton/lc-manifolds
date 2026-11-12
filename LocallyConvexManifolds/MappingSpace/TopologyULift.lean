/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.MappingSpace.TopologyJet

/-!
# The compact-open `C^ℓ` topology for targets in any universe

The iterated tangent bundles `T^j N` behind H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie
Groups* (arXiv:2602.12362), Definition 4.1.2, run over the bundled manifolds `MBMfld.{u, v}`, whose
carriers live in `Type (max u v)`, `u` the universe of the models: the tangent bundle of `N` lives
in the universe of `N` and of its model, so only there is the iteration `T^j` closed. A target `N`
in a universe below `u` is not the carrier of a bundled manifold. This file removes that
restriction by a transport along `ULift`: `ULift N` is a manifold over the same model, with the
charts of `N` (`chartedSpaceULift`), and `f ↦ ULift.up ∘ f` is a homeomorphism
`C^ℓ(M, N) ≃ₜ C^ℓ(M, ULift N)` for the topology of `C^ℓ(M, N)` (`CkMap.uliftHomeomorph`).

## Main definitions

* `chartedSpaceULift`, `mbManifoldULift`: the manifold `ULift N`, with the charts of `N`.
* `CkMap.uliftHomeomorph`, `SmoothMap.uliftHomeomorph`: `C^ℓ(M, N) ≃ₜ C^ℓ(M, ULift N)`,
  `ℓ ∈ ℕ ∪ {∞}`.
* `CkMap.gnTopology H E ℓ M N`, `SmoothMap.gnTopologySm H E M N`: the compact-open `C^ℓ` topology
  of Definition 4.1.2 for `N` in any universe, through `ULift N`. For `N` in the universe of the
  bundled manifolds it is `MBMfld.gnTopology` (`CkMap.gnTopology_eq`, `SmoothMap.gnTopologySm_eq`).

## Main results

* `MBMfld.gnTopology_eq_induced`, `MBMfld.gnTopologySm_eq_induced`: Definition 4.1.2 is natural in
  the target: a diffeomorphism `φ : Y → Y'` induces a homeomorphism `f ↦ φ ∘ f` between the
  topologies of Definition 4.1.2. The proof uses the chain rule for the iterated tangent maps,
  `MBMfld.iterMap_comp`.
* For every universe of `N`: `CkMap.jetTopology_eq_gnTopology`, `CkMap.topology_eq_gnTopology`,
  `SmoothMap.jetTopologySm_eq_gnTopologySm`, `SmoothMap.topology_eq_gnTopologySm`: **the
  topology of `C^ℓ(M, N)` is the compact-open `C^ℓ` topology of Definition 4.1.2** (Glöckner–Neeb,
  Theorem 4.2.2(b)), for every Hausdorff `M`, `ℓ ∈ ℕ ∪ {∞}`; the same for a locally compact model
  (`..._of_locallyCompactSpace`); `CkMap.chartTopology_eq_gnTopology`,
  `SmoothMap.chartTopologySm_eq_gnTopologySm`: the chart topology is that topology for a locally
  compact model.

## Implementation notes

* Only `M` and the models are required to live in one universe `u` (as for `CkMap`); `N` lives in
  any universe `w`, and `ULift.{u} N` in `Type (max u w)`, the carrier universe of
  `MBMfld.{u, w}`. The comparison theorems for bundled manifolds (`MBMfld.jetTopology_eq_gnTopology`
  and the others in `MappingSpace/TopologyJet.lean`, `MappingSpace/TopologyGN.lean`) are transported
  along `CkMap.uliftHomeomorph`; the jets of `C^ℓ(M, ULift N)` are, chart by chart, those of
  `C^ℓ(M, N)`, since the charts of `ULift N` are those of `N` precomposed with `ULift.down`.
* Mathematically `ULift N` is `N`; the transport is a formal device of type theory. The
  naturality of Definition 4.1.2 (`MBMfld.gnTopology_eq_induced`) shows that `CkMap.gnTopology`
  does not depend on it: for `N` in the carrier universe of a bundled manifold it is
  `MBMfld.gnTopology`. We do not claim this argument is new.
-/

@[expose] public section

open Set Function TopologicalSpace
open scoped Topology

noncomputable section

universe u v w w'

namespace LocallyConvex.Manifolds

/-! ### Naturality of Definition 4.1.2 in the target -/

namespace MBMfld

/-- `T^j id = id`. -/
theorem iterMap_id (j : ℕ) : ∀ {X : MBMfld.{u, v}}, iterMap j (X := X) (Y := X) id = id := by
  induction j with
  | zero => intro X; rfl
  | succ j ih =>
    intro X
    have hT : tangentMap X.Model X.Model (id : X.Carrier → X.Carrier) = id :=
      funext tangentMap_id
    rw [iterMap_succ, hT]
    exact ih

/-- **The chain rule for iterated tangent maps**: `T^j (g ∘ f) = T^j g ∘ T^j f`, for `g` smooth
and `f` of class `C^j`. -/
theorem iterMap_comp (j : ℕ) :
    ∀ {X : MBMfld.{u, v}} {Y : MBMfld.{u, w}} {Z : MBMfld.{u, w'}} {f : X.Carrier → Y.Carrier}
      {g : Y.Carrier → Z.Carrier}, SmoothMBM Y.Model Z.Model g → ContMDiffMB X.Model Y.Model j f →
      iterMap j (g ∘ f) = iterMap j g ∘ iterMap j f := by
  induction j with
  | zero => intros; rfl
  | succ j ih =>
    intro X Y Z f g hg hf
    have hT : tangentMap X.Model Z.Model (g ∘ f) =
        tangentMap Y.Model Z.Model g ∘ tangentMap X.Model Y.Model f :=
      funext fun p ↦ (tangentMap_comp (hg 1)
        ⟨hf.1, fun x hx ↦ (hf.2 x hx).of_le (by omega)⟩ p).symm
    rw [iterMap_succ, iterMap_succ, iterMap_succ, hT]
    exact ih (X := tangent X) (Y := tangent Y) (Z := tangent Z)
      (fun k ↦ ContMDiffMB.tangentMap (hg (k + 1))) (ContMDiffMB.tangentMap hf)

/-- `T^j φ` as a continuous map, for a smooth map `φ`. -/
def iterMapSmC (j : ℕ) {Y : MBMfld.{u, v}} {Y' : MBMfld.{u, w}} {φ : Y.Carrier → Y'.Carrier}
    (hφ : SmoothMBM Y.Model Y'.Model φ) : C((iter j Y).Carrier, (iter j Y').Carrier) :=
  ⟨iterMap j φ, continuousOn_univ.1 (contMDiffMB_iterMap 0 j (hφ _)).1⟩

/-- Postcomposition with a homeomorphism `B ≃ B'` (given as continuous maps inverse to each other)
is an embedding `C(A, B) → C(A, B')` for the compact-open topologies. -/
theorem induced_postcomp_eq {A B B' : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace B'] (Φ : C(B, B')) (Ψ : C(B', B)) (h : ∀ b, Ψ (Φ b) = b) :
    TopologicalSpace.induced (fun f : C(A, B) ↦ Φ.comp f)
        (inferInstance : TopologicalSpace C(A, B')) =
      (inferInstance : TopologicalSpace C(A, B)) := by
  have hid : (fun f : C(A, B') ↦ Ψ.comp f) ∘ (fun f : C(A, B) ↦ Φ.comp f) = id := by
    funext f
    ext a
    exact h (f a)
  have hi : Topology.IsInducing (fun f : C(A, B) ↦ Φ.comp f) :=
    Topology.IsInducing.of_comp (ContinuousMap.continuous_postcomp Φ)
      (ContinuousMap.continuous_postcomp Ψ) (hid ▸ Topology.IsInducing.id)
  exact hi.eq_induced.symm

/-- **Definition 4.1.2 is natural in the target**: if `φ : Y → Y'` is a diffeomorphism (smooth,
with a smooth left inverse `ψ`), then `f ↦ φ ∘ f` is an embedding `C^ℓ(X, Y) → C^ℓ(X, Y')` for the
compact-open `C^ℓ` topologies of Glöckner–Neeb, Definition 4.1.2. The map is given as any `e` with
`e f = φ ∘ f`. -/
theorem gnTopology_eq_induced (ℓ : ℕ) (X : MBMfld.{u, u}) {Y : MBMfld.{u, v}}
    {Y' : MBMfld.{u, w}} {φ : Y.Carrier → Y'.Carrier} {ψ : Y'.Carrier → Y.Carrier}
    (hφ : SmoothMBM Y.Model Y'.Model φ) (hψ : SmoothMBM Y'.Model Y.Model ψ)
    (hψφ : LeftInverse ψ φ)
    (e : CkMap X.Model Y.Model ℓ X.Carrier Y.Carrier →
      CkMap X.Model Y'.Model ℓ X.Carrier Y'.Carrier) (he : ∀ f, ⇑(e f) = φ ∘ f) :
    gnTopology ℓ X Y = TopologicalSpace.induced e (gnTopology ℓ X Y') := by
  simp only [gnTopology, induced_iInf, induced_compose]
  refine iInf_congr fun j ↦ ?_
  have hj : (j : ℕ) ≤ ℓ := Nat.lt_succ_iff.1 j.2
  have hcomp : iterMapC hj ∘ e = (iterMapSmC j hφ).comp ∘ iterMapC hj := by
    funext f
    ext p
    change iterMap j (⇑(e f)) p = iterMap j φ (iterMap j f p)
    rw [he, iterMap_comp j hφ ⟨f.contMDiffMB.1, fun x hx ↦ (f.contMDiffMB.2 x hx).of_le hj⟩]
    rfl
  rw [hcomp, ← induced_compose, induced_postcomp_eq _ (iterMapSmC j hψ)]
  intro p
  change iterMap j ψ (iterMap j φ p) = p
  rw [← comp_apply (f := iterMap j ψ), ← iterMap_comp j hψ (hφ j), hψφ.comp_eq_id, iterMap_id]
  rfl

/-- **Definition 4.1.2 for `ℓ = ∞` is natural in the target**: a diffeomorphism `φ : Y → Y'`
induces an embedding `f ↦ φ ∘ f` of `C^∞(X, Y)` into `C^∞(X, Y')`. -/
theorem gnTopologySm_eq_induced (X : MBMfld.{u, u}) {Y : MBMfld.{u, v}}
    {Y' : MBMfld.{u, w}} {φ : Y.Carrier → Y'.Carrier} {ψ : Y'.Carrier → Y.Carrier}
    (hφ : SmoothMBM Y.Model Y'.Model φ) (hψ : SmoothMBM Y'.Model Y.Model ψ)
    (hψφ : LeftInverse ψ φ)
    (e : SmoothMap X.Model Y.Model X.Carrier Y.Carrier →
      SmoothMap X.Model Y'.Model X.Carrier Y'.Carrier) (he : ∀ f, ⇑(e f) = φ ∘ f) :
    gnTopologySm X Y = TopologicalSpace.induced e (gnTopologySm X Y') := by
  simp only [gnTopologySm_eq, induced_iInf, induced_compose]
  refine iInf_congr fun ℓ ↦ ?_
  let eℓ : CkMap X.Model Y.Model ℓ X.Carrier Y.Carrier →
      CkMap X.Model Y'.Model ℓ X.Carrier Y'.Carrier :=
    fun f ↦ ⟨φ ∘ f, (hφ ℓ).comp isOpen_univ isOpen_univ f.contMDiffMB (mapsTo_univ _ _)⟩
  have hcomp : SmoothMap.toCk ℓ ∘ e = eℓ ∘ SmoothMap.toCk ℓ := by
    funext f
    exact CkMap.ext fun x ↦ congrFun (he f) x
  rw [hcomp, ← induced_compose, ← gnTopology_eq_induced ℓ X hφ hψ hψφ eℓ fun _ ↦ rfl]

end MBMfld

/-! ### The manifold `ULift N` -/

section ULiftManifold

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {N : Type w} [TopologicalSpace N] [ChartedSpace E N]

/-- **The charts of `ULift N`** are those of `N`, precomposed with `ULift.down`. -/
instance chartedSpaceULift : ChartedSpace E (ULift.{v} N) where
  atlas := Homeomorph.ulift.transOpenPartialHomeomorph '' atlas E N
  chartAt y := Homeomorph.ulift.transOpenPartialHomeomorph (chartAt E y.down)
  mem_chart_source y := mem_chart_source E y.down
  chart_mem_atlas y := mem_image_of_mem _ (chart_mem_atlas E y.down)

/-- `ULift N` is a manifold: its coordinate changes are those of `N`. -/
instance mbManifoldULift [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    [T2Space E] [MBManifold E N] : MBManifold E (ULift.{v} N) where
  compatible := by
    rintro _ _ ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
    exact (HasGroupoid.compatible (G := mbGroupoid E) (M := N) hc hc' :)

variable {G : Type u} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
  {P : Type*} [TopologicalSpace P] [ChartedSpace G P]

/-- A map into `ULift N` is `C^k` if and only if its composition with `ULift.down` is. -/
theorem contMDiffMB_down_comp_iff {k : ℕ} {g : P → ULift.{v} N} :
    ContMDiffMB G E k (ULift.down ∘ g) ↔ ContMDiffMB G E k g :=
  ⟨fun h ↦ ⟨Homeomorph.ulift.symm.continuous.comp_continuousOn h.1, h.2⟩,
    fun h ↦ ⟨Homeomorph.ulift.continuous.comp_continuousOn h.1, h.2⟩⟩

/-- A map into `N` is `C^k` if and only if its composition with `ULift.up` is. -/
theorem contMDiffMB_up_comp_iff {k : ℕ} {f : P → N} :
    ContMDiffMB G E k (ULift.up.{v} ∘ f) ↔ ContMDiffMB G E k f :=
  (contMDiffMB_down_comp_iff (g := ULift.up.{v} ∘ f)).symm

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]

/-- `ULift.up : N → ULift N` is smooth. -/
theorem smoothMBM_up : SmoothMBM E E (ULift.up.{v} : N → ULift.{v} N) := fun k ↦
  contMDiffMB_up_comp_iff.2 (smoothMBMOn_id isOpen_univ k)

/-- `ULift.down : ULift N → N` is smooth. -/
theorem smoothMBM_down : SmoothMBM E E (ULift.down : ULift.{v} N → N) := fun k ↦
  contMDiffMB_down_comp_iff.2 (smoothMBMOn_id isOpen_univ k)

end ULiftManifold

/-! ### `C^ℓ(M, N) ≃ₜ C^ℓ(M, ULift N)` -/

section ULiftMaps

variable {H : Type u} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {N : Type w} [TopologicalSpace N] [ChartedSpace E N] {ℓ : ℕ}

/-- The bijection `C^ℓ(M, N) ≃ C^ℓ(M, ULift N)`, `f ↦ ULift.up ∘ f`. -/
def CkMap.uliftEquiv : CkMap H E ℓ M N ≃ CkMap H E ℓ M (ULift.{v} N) where
  toFun f := ⟨ULift.up ∘ f, contMDiffMB_up_comp_iff.2 f.contMDiffMB⟩
  invFun g := ⟨ULift.down ∘ g, contMDiffMB_down_comp_iff.2 g.contMDiffMB⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `CkMap.uliftEquiv f` is `ULift.up ∘ f`. -/
@[simp]
theorem CkMap.coe_uliftEquiv (f : CkMap H E ℓ M N) :
    ⇑(CkMap.uliftEquiv f : CkMap H E ℓ M (ULift.{v} N)) = ULift.up ∘ f :=
  rfl

/-- The bijection `C^∞(M, N) ≃ C^∞(M, ULift N)`, `f ↦ ULift.up ∘ f`. -/
def SmoothMap.uliftEquiv : SmoothMap H E M N ≃ SmoothMap H E M (ULift.{v} N) where
  toFun f := ⟨ULift.up ∘ f, fun k ↦ contMDiffMB_up_comp_iff.2 (f.2 k)⟩
  invFun g := ⟨ULift.down ∘ g, fun k ↦ contMDiffMB_down_comp_iff.2 (g.2 k)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `SmoothMap.uliftEquiv f` is `ULift.up ∘ f`. -/
@[simp]
theorem SmoothMap.coe_uliftEquiv (f : SmoothMap H E M N) :
    ⇑(SmoothMap.uliftEquiv f : SmoothMap H E M (ULift.{v} N)) = ULift.up ∘ f :=
  rfl

/-- `f ↦ ULift.up ∘ f` is continuous `C^ℓ(M, N) → C^ℓ(M, ULift N)`: the jets of `ULift.up ∘ f` in
the charts of `ULift N` are those of `f` in the charts of `N`. -/
theorem CkMap.continuous_uliftEquiv :
    Continuous (CkMap.uliftEquiv : CkMap H E ℓ M N → CkMap H E ℓ M (ULift.{v} N)) := by
  refine continuous_jetTopology_iff.2 ⟨?_, fun a m hm ↦ ?_⟩
  · exact (ContinuousMap.continuous_postcomp
      ⟨ULift.up.{v}, Homeomorph.ulift.symm.continuous⟩).comp continuous_toC
  · obtain ⟨j, ⟨_, c, hc, rfl⟩, K, hK, hKj⟩ := a
    exact (CompactIdx.continuousOn_jet (ℓ := ℓ) ⟨j, ⟨c, hc⟩, K, hK, hKj⟩ hm :)

/-- `g ↦ ULift.down ∘ g` is continuous `C^ℓ(M, ULift N) → C^ℓ(M, N)`. -/
theorem CkMap.continuous_uliftEquiv_symm :
    Continuous (CkMap.uliftEquiv.symm :
      CkMap H E ℓ M (ULift.{v} N) → CkMap H E ℓ M N) := by
  refine continuous_jetTopology_iff.2 ⟨?_, fun a m hm ↦ ?_⟩
  · exact (ContinuousMap.continuous_postcomp
      ⟨ULift.down, Homeomorph.ulift.continuous⟩).comp continuous_toC
  · obtain ⟨j, ⟨c, hc⟩, K, hK, hKj⟩ := a
    exact (CompactIdx.continuousOn_jet (ℓ := ℓ) (N := ULift.{v} N)
      ⟨j, ⟨Homeomorph.ulift.transOpenPartialHomeomorph c, mem_image_of_mem _ hc⟩, K, hK, hKj⟩ hm :)

/-- **`C^ℓ(M, N) ≃ₜ C^ℓ(M, ULift N)`**, `f ↦ ULift.up ∘ f`, for the topology of `C^ℓ(M, N)` (the
jet topology). -/
def CkMap.uliftHomeomorph : CkMap H E ℓ M N ≃ₜ CkMap H E ℓ M (ULift.{v} N) where
  toEquiv := CkMap.uliftEquiv
  continuous_toFun := CkMap.continuous_uliftEquiv
  continuous_invFun := CkMap.continuous_uliftEquiv_symm

/-- **`C^∞(M, N) ≃ₜ C^∞(M, ULift N)`**, `f ↦ ULift.up ∘ f`. -/
def SmoothMap.uliftHomeomorph : SmoothMap H E M N ≃ₜ SmoothMap H E M (ULift.{v} N) where
  toEquiv := SmoothMap.uliftEquiv
  continuous_toFun := continuous_iInf_rng.2 fun ℓ ↦ continuous_induced_rng.2 <| by
    have h : Continuous ((CkMap.uliftEquiv : CkMap H E ℓ M N ≃ CkMap H E ℓ M (ULift.{v} N)) ∘
        SmoothMap.toCk ℓ) :=
      CkMap.continuous_uliftEquiv.comp (SmoothMap.continuous_toCk ℓ)
    exact h
  continuous_invFun := continuous_iInf_rng.2 fun ℓ ↦ continuous_induced_rng.2 <| by
    have h : Continuous ((CkMap.uliftEquiv : CkMap H E ℓ M N ≃ CkMap H E ℓ M (ULift.{v} N)).symm ∘
        SmoothMap.toCk ℓ) :=
      CkMap.continuous_uliftEquiv_symm.comp (SmoothMap.continuous_toCk ℓ)
    exact h

end ULiftMaps

/-! ### Definition 4.1.2 for targets in any universe -/

section AnyUniverse

variable {H : Type u} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [IsTopologicalAddGroup H]
  [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [MBManifold H M]
  {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {N : Type w} [TopologicalSpace N] [ChartedSpace E N] [MBManifold E N]

variable (H E) in
/-- **The compact-open `C^ℓ` topology of Glöckner–Neeb, Definition 4.1.2, for `N` in any
universe**: the initial topology with respect to `f ↦ T^j (ULift.up ∘ f) ∈ C(T^j M, T^j N)`,
`j ≤ ℓ`, where `ULift N`, with the charts of `N`, is the carrier of a bundled manifold
`MBMfld.{u, w}`. For `N` in the carrier universe of a bundled manifold it is
`MBMfld.gnTopology` (`CkMap.gnTopology_eq`). -/
@[instance_reducible]
def CkMap.gnTopology (ℓ : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace H M] [MBManifold H M]
    (N : Type w) [TopologicalSpace N] [ChartedSpace E N] [MBManifold E N] :
    TopologicalSpace (CkMap H E ℓ M N) :=
  TopologicalSpace.induced (CkMap.uliftEquiv : CkMap H E ℓ M N ≃ CkMap H E ℓ M (ULift.{u} N))
    (MBMfld.gnTopology ℓ (MBMfld.of H M) (MBMfld.of.{u, w} E (ULift.{u} N)))

variable (H E) in
/-- **The compact-open `C^∞` topology of Glöckner–Neeb, Definition 4.1.2, for `N` in any
universe**, through `ULift N` as for `CkMap.gnTopology`. For `N` in the carrier universe of a
bundled manifold it is `MBMfld.gnTopologySm` (`SmoothMap.gnTopologySm_eq`). -/
@[instance_reducible]
def SmoothMap.gnTopologySm (M : Type u) [TopologicalSpace M] [ChartedSpace H M] [MBManifold H M]
    (N : Type w) [TopologicalSpace N] [ChartedSpace E N] [MBManifold E N] :
    TopologicalSpace (SmoothMap H E M N) :=
  TopologicalSpace.induced
    (SmoothMap.uliftEquiv : SmoothMap H E M N ≃ SmoothMap H E M (ULift.{u} N))
    (MBMfld.gnTopologySm (MBMfld.of H M) (MBMfld.of.{u, w} E (ULift.{u} N)))

/-- For `N` in the carrier universe of a bundled manifold, `CkMap.gnTopology` is
`MBMfld.gnTopology`: Definition 4.1.2 does not depend on the transport along `ULift`. -/
theorem CkMap.gnTopology_eq {N : Type (max u v)} [TopologicalSpace N] [ChartedSpace E N]
    [MBManifold E N] (ℓ : ℕ) :
    CkMap.gnTopology H E ℓ M N = MBMfld.gnTopology ℓ (MBMfld.of H M) (MBMfld.of.{u, v} E N) :=
  (MBMfld.gnTopology_eq_induced ℓ (MBMfld.of H M) (Y := MBMfld.of.{u, v} E N)
    (Y' := MBMfld.of.{u, max u v} E (ULift.{u} N)) smoothMBM_up smoothMBM_down
    (fun _ ↦ rfl) CkMap.uliftEquiv fun _ ↦ rfl).symm

/-- For `N` in the carrier universe of a bundled manifold, `SmoothMap.gnTopologySm` is
`MBMfld.gnTopologySm`. -/
theorem SmoothMap.gnTopologySm_eq {N : Type (max u v)} [TopologicalSpace N] [ChartedSpace E N]
    [MBManifold E N] :
    SmoothMap.gnTopologySm H E M N =
      MBMfld.gnTopologySm (MBMfld.of H M) (MBMfld.of.{u, v} E N) :=
  (MBMfld.gnTopologySm_eq_induced (MBMfld.of H M) (Y := MBMfld.of.{u, v} E N)
    (Y' := MBMfld.of.{u, max u v} E (ULift.{u} N)) smoothMBM_up smoothMBM_down
    (fun _ ↦ rfl) SmoothMap.uliftEquiv fun _ ↦ rfl).symm

/-- **The jet topology of `C^ℓ(M, N)` is the compact-open `C^ℓ` topology of Glöckner–Neeb,
Definition 4.1.2**, for every Hausdorff manifold `M` (compact or not) modeled on any Hausdorff
locally convex space `H` (locally compact or not), and `N` in any universe. -/
theorem CkMap.jetTopology_eq_gnTopology [T2Space M] (ℓ : ℕ) :
    CkMap.jetTopology H E ℓ M N = CkMap.gnTopology H E ℓ M N := by
  rw [CkMap.gnTopology, ← MBMfld.jetTopology_eq_gnTopology]
  exact (CkMap.uliftHomeomorph : CkMap H E ℓ M N ≃ₜ CkMap H E ℓ M (ULift.{u} N)).induced_eq.symm

/-- The jet topology of `C^ℓ(M, N)` is the compact-open `C^ℓ` topology of Glöckner–Neeb,
Definition 4.1.2, for a locally compact model `H` (no Hausdorff hypothesis on `M`) and `N` in any
universe. -/
theorem CkMap.jetTopology_eq_gnTopology_of_locallyCompactSpace [LocallyCompactSpace H] (ℓ : ℕ) :
    CkMap.jetTopology H E ℓ M N = CkMap.gnTopology H E ℓ M N := by
  rw [CkMap.gnTopology, ← MBMfld.jetTopology_eq_gnTopology_of_locallyCompactSpace]
  exact (CkMap.uliftHomeomorph : CkMap H E ℓ M N ≃ₜ CkMap H E ℓ M (ULift.{u} N)).induced_eq.symm

/-- **Glöckner–Neeb, Theorem 4.2.2(b)**, finite `ℓ`, and more: the topology of `C^ℓ(M, N)` (the
jet topology; for `M` compact, the topology underlying the atlas `LocalAddition.mappingAtlasCk`)
is the compact-open `C^ℓ` topology of Definition 4.1.2, for every Hausdorff manifold `M` (compact
or not) modeled on any Hausdorff locally convex space, and `N` in any universe. -/
theorem CkMap.topology_eq_gnTopology [T2Space M] (ℓ : ℕ) :
    (inferInstance : TopologicalSpace (CkMap H E ℓ M N)) = CkMap.gnTopology H E ℓ M N :=
  CkMap.jetTopology_eq_gnTopology ℓ

/-- **The chart topology is the compact-open `C^ℓ` topology** of Glöckner–Neeb, Definition 4.1.2,
for a locally compact model of `M` and `N` in any universe. -/
theorem CkMap.chartTopology_eq_gnTopology [LocallyCompactSpace H] (ℓ : ℕ) :
    CkMap.chartTopology H E ℓ M N = CkMap.gnTopology H E ℓ M N :=
  CkMap.chartTopology_eq_jetTopology.trans
    (CkMap.jetTopology_eq_gnTopology_of_locallyCompactSpace ℓ)

/-- **The jet topology of `C^∞(M, N)` is the compact-open `C^∞` topology of Glöckner–Neeb,
Definition 4.1.2**, for every Hausdorff manifold `M` and `N` in any universe. -/
theorem SmoothMap.jetTopologySm_eq_gnTopologySm [T2Space M] :
    SmoothMap.jetTopologySm H E M N = SmoothMap.gnTopologySm H E M N := by
  rw [SmoothMap.gnTopologySm, ← MBMfld.jetTopologySm_eq_gnTopologySm]
  exact (SmoothMap.uliftHomeomorph :
    SmoothMap H E M N ≃ₜ SmoothMap H E M (ULift.{u} N)).induced_eq.symm

/-- The jet topology of `C^∞(M, N)` is the compact-open `C^∞` topology of Glöckner–Neeb,
Definition 4.1.2, for a locally compact model `H` and `N` in any universe. -/
theorem SmoothMap.jetTopologySm_eq_gnTopologySm_of_locallyCompactSpace [LocallyCompactSpace H] :
    SmoothMap.jetTopologySm H E M N = SmoothMap.gnTopologySm H E M N := by
  rw [SmoothMap.gnTopologySm, ← MBMfld.jetTopologySm_eq_gnTopologySm_of_locallyCompactSpace]
  exact (SmoothMap.uliftHomeomorph :
    SmoothMap H E M N ≃ₜ SmoothMap H E M (ULift.{u} N)).induced_eq.symm

/-- **Glöckner–Neeb, Theorem 4.2.2(b)**, `ℓ = ∞`, and more: the topology of `C^∞(M, N)` is the
compact-open `C^∞` topology of Definition 4.1.2, for every Hausdorff manifold `M` and `N` in any
universe. -/
theorem SmoothMap.topology_eq_gnTopologySm [T2Space M] :
    (inferInstance : TopologicalSpace (SmoothMap H E M N)) = SmoothMap.gnTopologySm H E M N :=
  SmoothMap.jetTopologySm_eq_gnTopologySm

/-- **The chart topology of `C^∞(M, N)` is the compact-open `C^∞` topology** of Glöckner–Neeb,
Definition 4.1.2 and Remark 4.1.3(b), for a locally compact model of `M` and `N` in any universe. -/
theorem SmoothMap.chartTopologySm_eq_gnTopologySm [LocallyCompactSpace H] :
    SmoothMap.chartTopologySm H E M N = SmoothMap.gnTopologySm H E M N :=
  SmoothMap.chartTopologySm_eq_jetTopologySm.trans
    SmoothMap.jetTopologySm_eq_gnTopologySm_of_locallyCompactSpace

end AnyUniverse

end LocallyConvex.Manifolds
