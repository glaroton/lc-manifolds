/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.Manifold.CkSuperposition

/-!
# Manifolds of `C^ℓ` maps on compact manifolds

Let `M` be a compact manifold modeled on a Hausdorff locally convex space `H` (necessarily
finite-dimensional if `M ≠ ∅`), `N` a manifold modeled on a Hausdorff locally convex space `E`
with a local addition `Σ : TN ⊇ Ω → N`, `θ = (π, Σ)` (`LocalAddition`), and `ℓ ∈ ℕ ∪ {∞}`. Following
H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups* (arXiv:2602.12362), proof of
Theorem 4.2.2, the space `C^ℓ(M, N)` of `C^ℓ` maps is a smooth manifold with charts

  `φ_f : O'_f → O_f ⊆ Γ_f`,  `g ↦ θ⁻¹ ∘ (f, g)`,

where `O'_f = {g : (f, g)(M) ⊆ θ(Ω)}`, `Γ_f` is the space of `C^ℓ` sections of `TN` along `f` and
`O_f = Γ_f ∩ C^ℓ(M, Ω)`; the inverse of `φ_f` is `τ ↦ Σ ∘ τ`. The case `ℓ = 0` (with `M` replaced
by a compact Hausdorff space) is `LocallyConvexManifolds.MappingSpace.Basic`.

## Main definitions

* `CkMap H E ℓ M N`: the space `C^ℓ(M, N)`, `ℓ ∈ ℕ`, with the **compact-open `C^ℓ` topology**
  `CkMap.jetTopology` (the instance): the coarsest topology finer than the compact-open topology
  for which the jets `g ↦ d^(m)(i ∘ g ∘ j⁻¹)|_{K × H^m} ∈ C(K × H^m, E)`, `m ≤ ℓ`, are continuous on
  the open sets `{g : g(j⁻¹ K) ⊆ i.source}` (`j`, `i` charts of `M` and `N`, `K` compact; no
  interior required). This is Hirsch's weak `C^ℓ` topology in locally convex form; it is the
  topology of Glöckner–Neeb, Definition 4.1.2, for every Hausdorff `M` and every model
  (`CkMap.topology_eq_gnTopology`, `MappingSpace/TopologyULift.lean`).
* `CkMap.chartTopology`: the **chart topology**, defined in the same way by the local
  representatives `g ↦ i ∘ g ∘ j⁻¹ ∈ C^ℓ(V, E)` on open sets `V ⊆ L`, `L` compact. It is always
  coarser than the jet topology (`CkMap.jetTopology_le_chartTopology`) and equal to it for a locally
  compact model of `M` (`CkMap.chartTopology_eq_jetTopology`), in particular for `M` compact
  (`CkMap.topology_eq_chartTopology_of_compactSpace`). It is not the instance.
* `SecCk H E ℓ f`: the space `Γ_f` of `C^ℓ` sections along `f` (Glöckner–Neeb, 4.1.30, 4.2.1),
  in fiber coordinates, with the initial topology with respect to the local representatives
  `D_{j,i}(f) → E` in the charts `j` of `M` and `i` of `N`.
* `LocalAddition.chartCk f`: the chart `φ_f` of `C^ℓ(M, N)` at `f`.
* `SmoothMap H E M N`, `SecSm H E f`, `LocalAddition.chartSm f`: the same for `ℓ = ∞`, with the
  initial topologies with respect to the inclusions into the `C^ℓ` spaces (Glöckner–Neeb,
  Remark 4.1.3(b)): `SmoothMap.jetTopologySm` (the instance), `SmoothMap.chartTopologySm`.

## Main results

* `SecCk.instLocallyConvexSpaceReal`, `SecCk.instT2Space`: `Γ_f` is a Hausdorff locally convex
  space (Glöckner–Neeb, Lemma 4.1.31); `SecCk.isClosed_range_toPi`: the local representatives embed
  it as a closed subspace of `∏ C^ℓ(D_{j,i}(f), E)` (compare Proposition 4.1.26 and the proof of
  Proposition 4.1.34); `SecCk.toSec`: `Γ_f` embeds continuously in the space of continuous sections.
* `LocalAddition.chartCk`: `φ_f` is a partial homeomorphism of `C^ℓ(M, N)` onto the open set `O_f`
  of `Γ_f`, for the compact-open `C^ℓ` topology.
* `LocalAddition.smoothMBOn_transitionCk`: the transition maps `φ_g ∘ φ_f⁻¹` are smooth.
* `LocalAddition.mappingAtlasCk`: **Glöckner–Neeb, Theorem 4.2.2(a), (b) for finite `ℓ`**: the
  charts form an atlas of `C^ℓ(M, N)` with varying models `Γ_f` (`VaryingAtlas`), whose topology
  is the compact-open `C^ℓ` topology. `LocalAddition.mappingAtlasSm`: the same for `ℓ = ∞`.
* `LocalAddition.smoothMBMOn_eval_chartCk_symm`, `LocalAddition.smoothMBMOn_eval_chartSm_symm`:
  **Theorem 4.2.2(c)**, point evaluations are smooth in the charts.

## Implementation notes

* **The manifolds `M`.** The library has smooth manifolds only, so `M` is a smooth manifold (not
  a `C^ℓ` manifold, as Glöckner–Neeb allow), compact Hausdorff, without boundary. `M`, `H` and
  `E` live in one universe.
* **Finite dimension of `M`.** If `M` is nonempty and compact, its model `H` is locally compact
  (`locallyCompactSpace_of_compactSpace`), hence finite-dimensional by Riesz's theorem
  (`finiteDimensional_of_compactSpace`): `M` is modeled on some `ℝⁿ`, and only the target `N` may be
  infinite-dimensional. The proofs use only the local compactness of `H` (for uncurrying,
  Theorem 1.7.30(a), and for superposition operators); it is derived inside the proofs, after
  disposing of the trivial case `M = ∅` (where `C^ℓ(M, N)` and `Γ_f` are points), so that the public
  statements carry only Glöckner–Neeb's hypotheses on `M` (compact, Hausdorff).
* **The topologies.** Glöckner–Neeb define the compact-open `C^ℓ` topology through the iterated
  tangent maps `T^j g` (Definition 4.1.2), give `Γ_f` the topology induced by `C^ℓ(M, TN)` (4.1.30)
  and identify it with spaces of local representatives in charts (Proposition 4.1.26, proof of
  Proposition 4.1.34; for vector-valued maps Definition 4.1.16 and Lemma 4.1.17 use the chart
  description from the start). Here `C^ℓ(M, N)` carries the jet topology, defined by jets of local
  representatives on compact sets in charts, and `Γ_f` the topology of its local representatives
  on the open sets `D_{j,i}(f)`; the agreement of the jet topology with Definition 4.1.2 for every
  Hausdorff `M` is proved in `MappingSpace/TopologyJet.lean` (Theorem 4.2.2(b)).
* **The jet topology and the chart topology.** The chart topology uses local representatives on
  open sets `V` inside compact sets `L` of the model. If the model of `M` is not locally compact
  (for instance infinite-dimensional), compact sets have empty interior, every such `V` is empty,
  and the chart topology collapses to the compact-open `C^0` topology; this is why the instance is
  the jet topology, which uses jets on the compact sets themselves and is correct for every model
  and every `M`. For a locally compact model the two agree (`CkMap.chartTopology_eq_jetTopology`,
  proved directly: a compact set in a chart domain lies in the interior of a compact set there).
  The continuity of the charts `φ_f` and of their inverses for compact `M` is proved in the chart
  topology, after rewriting the instance by `CkMap.topology_eq_chartTopology` (the model of a
  nonempty compact `M` is locally compact).
* **The charts are continuous.** The map `g ↦ θ⁻¹ ∘ (f, g)` is continuous at `g₀` because, near
  each point, `g₀` lies in a chart `i'` of `N` over a compact neighborhood `L` in a chart of `M`;
  for `g` with `g(L) ⊆ i'.source` (an open condition) the local representative of `φ_f(g)` is a
  superposition operator applied to `(i' ∘ g, i ∘ f)` on a smaller neighborhood, and
  `ContDiffMBMap.tendsto_of_tendsto_restrictCLM` glues these local statements.
* **Smoothness of the transition maps.** Glöckner–Neeb deduce it from the exponential law for
  sections (Proposition 4.1.34) and the smoothness of the evaluation map (Proposition 4.1.32). Here,
  over the open sets where `f` and `g` lie in charts `i` and `j` of `N`, the local representative of
  `φ_g ∘ φ_f⁻¹` is the superposition operator of the smooth map
  `(y, z, v) ↦ θ⁻¹(j⁻¹ z, Σ(i⁻¹ y, v))` (`LocalAddition.transMap`, from the case `ℓ = 0`) applied to
  `(i ∘ f, j ∘ g, τ)`, which depends affinely on `τ`; it is smooth by
  `ContDiffMBMap.contDiffMBOn_compLeftOn`, and these local statements glue by
  `ContDiffMBMap.contDiffMBOn_of_restrictCLM`. For `ℓ = ∞` the spaces are projective limits of the
  finite-order ones and everything follows from the finite orders. We do not claim these
  arguments are new.
* The rest of Theorem 4.2.2 is in `MappingSpace/ExponentialLaw.lean` (the exponential law and
  uniqueness in (a), and (c)), `MappingSpace/Tangent.lean` ((d)) and `MappingSpace/TopologyJet.lean`
  ((b) in the form of Definition 4.1.2).
-/

@[expose] public section

open Set Filter Function TopologicalSpace
open scoped Topology
open LocallyConvex.Analysis

noncomputable section

universe u v

namespace LocallyConvex.Manifolds

/-! ### The space `Γ_f` of `C^ℓ` sections along `f` -/

section SectionsCk

variable {H : Type u} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [IsTopologicalAddGroup H]
  [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [MBManifold E N]

/-- The domain `D_{j,i}(f) = j(j.source ∩ f⁻¹(i.source))` of the local representatives of `f` in
the charts `j` of `M` and `i` of `N`, as an open subset of `H`. -/
def chartDomOpens (f : C(M, N)) (j : atlas H M) (i : atlas E N) : Opens H :=
  ⟨chartDomain f univ j.1 i.1, isOpen_chartDomain isOpen_univ f.continuous.continuousOn _ _⟩

omit [AddCommGroup H] [Module ℝ H] [IsTopologicalAddGroup H] [ContinuousSMul ℝ H]
  [LocallyConvexSpace ℝ H] [T2Space H] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E N] in
/-- Points of `D_{j,i}(f)` are sent by `j⁻¹` into `f⁻¹(i.source)`. -/
theorem mem_chartDomOpens {f : C(M, N)} {j : atlas H M} {i : atlas E N} {x : H} :
    x ∈ chartDomOpens f j i ↔ x ∈ j.1.target ∧ f (j.1.symm x) ∈ i.1.source := by
  change x ∈ chartDomain f univ j.1 i.1 ↔ _
  simp [chartDomain]

omit [AddCommGroup H] [Module ℝ H] [IsTopologicalAddGroup H] [ContinuousSMul ℝ H]
  [LocallyConvexSpace ℝ H] [T2Space H] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E N] in
/-- The preferred charts give a point of `D_{j,i}(f)`. -/
theorem chartAt_mem_chartDomOpens (f : C(M, N)) (p : M) :
    chartAt H p p ∈ chartDomOpens f ⟨chartAt H p, chart_mem_atlas H p⟩
      ⟨chartAt E (f p), chart_mem_atlas E (f p)⟩ := by
  rw [mem_chartDomOpens]
  refine ⟨(chartAt H p).map_source (mem_chart_source H p), ?_⟩
  rw [(chartAt H p).left_inv (mem_chart_source H p)]
  exact mem_chart_source E (f p)

/-- The local representative `x ↦ (u(j⁻¹ x) in the fiber coordinates of the chart i)` of a
section `u` along `f`. -/
def localCoord (f : C(M, N)) (j : atlas H M) (i : atlas E N) (u : M → E) (x : H) : E :=
  coordAt i (⟨f (j.1.symm x), u (j.1.symm x)⟩ : TangentBundle E N)

omit [AddCommGroup H] [Module ℝ H] [IsTopologicalAddGroup H] [ContinuousSMul ℝ H]
  [LocallyConvexSpace ℝ H] [T2Space H] in
/-- The local representatives are linear in the section. -/
theorem localCoord_linearCombination (f : C(M, N)) (j : atlas H M) (i : atlas E N)
    (u w : M → E) (a b : ℝ) {x : H} (hx : x ∈ chartDomOpens f j i) :
    localCoord f j i (a • u + b • w) x = a • localCoord f j i u x + b • localCoord f j i w x := by
  have hs := (mem_chartDomOpens.1 hx).2
  simp only [localCoord, Pi.add_apply, Pi.smul_apply]
  rw [coordAt_add i hs, coordAt_smul i hs, coordAt_smul i hs]

variable (H E) in
/-- The `C^ℓ` sections along `f`, written in fiber coordinates: the maps `u : M → E` whose local
representatives in all charts are `C^ℓ`. -/
def sectionSubmoduleCk (ℓ : ℕ) (f : C(M, N)) : Submodule ℝ (M → E) where
  carrier := {u | ∀ (j : atlas H M) (i : atlas E N),
    ContDiffMBOn ℓ (localCoord f j i u) (chartDomOpens f j i)}
  add_mem' {u w} hu hw j i := by
    refine ContDiffMBOn.congr_of_isOpen (chartDomOpens f j i).isOpen (fun x hx ↦ ?_)
      ((hu j i).add (chartDomOpens f j i).isOpen (hw j i))
    have h := localCoord_linearCombination f j i u w 1 1 hx
    simp only [one_smul] at h
    exact h.symm
  zero_mem' j i := by
    refine ContDiffMBOn.congr_of_isOpen (chartDomOpens f j i).isOpen (fun x hx ↦ ?_)
      (contDiffMBOn_const ℓ (0 : E) _)
    have h := localCoord_linearCombination f j i 0 0 0 0 hx
    simp only [zero_smul, add_zero] at h
    exact h.symm
  smul_mem' c u hu j i := by
    refine ContDiffMBOn.congr_of_isOpen (chartDomOpens f j i).isOpen (fun x hx ↦ ?_)
      ((hu j i).const_smul (chartDomOpens f j i).isOpen c)
    have h := localCoord_linearCombination f j i u u c 0 hx
    simp only [zero_smul, add_zero] at h
    exact h.symm

variable (H E) in
/-- **The space `Γ_f` of `C^ℓ` sections of `TN` along `f`** (Glöckner–Neeb, 4.1.30 and 4.2.1),
written in the fiber coordinates of `TN`: the maps `u : M → E` such that `x ↦ ⟨f x, u x⟩ ∈ TN`
has `C^ℓ` local representatives. Its topology, defined below, is the initial topology with
respect to the local representatives `D_{j,i}(f) → E` in the charts `j` of `M` and `i` of `N`,
each in its compact-open `C^ℓ` topology. -/
def SecCk (ℓ : ℕ) (f : C(M, N)) : Type u := sectionSubmoduleCk H E ℓ f

namespace SecCk

variable {ℓ : ℕ} {f : C(M, N)}

/-- The vector space operations of `Γ_f` are pointwise. -/
instance : AddCommGroup (SecCk H E ℓ f) :=
  inferInstanceAs (AddCommGroup (sectionSubmoduleCk H E ℓ f))

/-- The vector space operations of `Γ_f` are pointwise. -/
instance : Module ℝ (SecCk H E ℓ f) := inferInstanceAs (Module ℝ (sectionSubmoduleCk H E ℓ f))

/-- A section is given by its fiber coordinates `M → E`. -/
instance : FunLike (SecCk H E ℓ f) M E where
  coe u := Subtype.val (u : sectionSubmoduleCk H E ℓ f)
  coe_injective := Subtype.val_injective

/-- Sections are equal if their coordinates agree. -/
@[ext]
theorem ext {u w : SecCk H E ℓ f} (h : ∀ x, u x = w x) : u = w :=
  DFunLike.ext _ _ h

/-- Over an empty manifold there is only one section. -/
instance [IsEmpty M] : Subsingleton (SecCk H E ℓ f) :=
  ⟨fun _ _ ↦ ext fun x ↦ isEmptyElim x⟩

/-- The section with fiber coordinates `u`. -/
def mk (u : M → E) (hu : ∀ (j : atlas H M) (i : atlas E N),
    ContDiffMBOn ℓ (localCoord f j i u) (chartDomOpens f j i)) :
    SecCk H E ℓ f :=
  ⟨u, hu⟩

/-- The coordinates of `SecCk.mk u hu` are `u`. -/
@[simp]
theorem coe_mk (u : M → E) (hu : ∀ (j : atlas H M) (i : atlas E N),
    ContDiffMBOn ℓ (localCoord f j i u) (chartDomOpens f j i)) :
    ⇑(mk u hu) = u :=
  rfl

/-- Addition is pointwise. -/
@[simp]
theorem coe_add (u w : SecCk H E ℓ f) : ⇑(u + w) = u + w :=
  rfl

/-- Scalar multiplication is pointwise. -/
@[simp]
theorem coe_smul (c : ℝ) (u : SecCk H E ℓ f) : ⇑(c • u) = c • ⇑u :=
  rfl

/-- The zero section. -/
@[simp]
theorem coe_zero : ⇑(0 : SecCk H E ℓ f) = 0 :=
  rfl

/-- The local representatives of a section are `C^ℓ`. -/
theorem contDiffMBOn_localCoord (u : SecCk H E ℓ f) (j : atlas H M) (i : atlas E N) :
    ContDiffMBOn ℓ (localCoord f j i u) (chartDomOpens f j i) :=
  (u : sectionSubmoduleCk H E ℓ f).2 j i

/-- The local representative of a section in the charts `a = (j, i)`, as an element of
`C^ℓ(D_{j,i}(f), E)`. -/
def coordFun (a : atlas H M × atlas E N) (u : SecCk H E ℓ f) :
    ContDiffMBMap E ℓ (chartDomOpens f a.1 a.2) :=
  ContDiffMBMap.mk ((chartDomOpens f a.1 a.2 : Set H).indicator (localCoord f a.1 a.2 u))
    (ContDiffMBOn.congr_of_isOpen (chartDomOpens f a.1 a.2).isOpen
      (fun _ hx ↦ (indicator_of_mem hx _).symm) (contDiffMBOn_localCoord u a.1 a.2))
    fun _ hx ↦ indicator_of_notMem hx _

/-- On `D_{j,i}(f)`, `coordFun` is the local representative. -/
theorem coordFun_apply (a : atlas H M × atlas E N) (u : SecCk H E ℓ f) {x : H}
    (hx : x ∈ chartDomOpens f a.1 a.2) : coordFun a u x = localCoord f a.1 a.2 u x :=
  indicator_of_mem (show x ∈ (chartDomOpens f a.1 a.2 : Set H) from hx) _

/-- The local representatives, as a linear map. -/
def coordL (a : atlas H M × atlas E N) :
    SecCk H E ℓ f →ₗ[ℝ] ContDiffMBMap E ℓ (chartDomOpens f a.1 a.2) where
  toFun := coordFun a
  map_add' u w := by
    ext x
    by_cases hx : x ∈ chartDomOpens f a.1 a.2
    · have h := localCoord_linearCombination f a.1 a.2 u w 1 1 hx
      simp only [one_smul] at h
      simp only [ContDiffMBMap.coe_add, Pi.add_apply, coordFun_apply _ _ hx]
      exact h
    · simp [ContDiffMBMap.apply_of_notMem _ hx]
  map_smul' c u := by
    ext x
    by_cases hx : x ∈ chartDomOpens f a.1 a.2
    · have h := localCoord_linearCombination f a.1 a.2 u u c 0 hx
      simp only [zero_smul, add_zero] at h
      simp only [ContDiffMBMap.coe_smul, Pi.smul_apply, coordFun_apply _ _ hx, RingHom.id_apply]
      exact h
    · simp [ContDiffMBMap.apply_of_notMem _ hx]

/-- All the local representatives. -/
def toPi : SecCk H E ℓ f →ₗ[ℝ] ∀ a : atlas H M × atlas E N,
    ContDiffMBMap E ℓ (chartDomOpens f a.1 a.2) :=
  LinearMap.pi coordL

/-- The value of a section at `p` is its local representative in the preferred charts. -/
theorem coordFun_chartAt (u : SecCk H E ℓ f) (p : M) :
    coordFun (⟨chartAt H p, chart_mem_atlas H p⟩, ⟨chartAt E (f p), chart_mem_atlas E (f p)⟩) u
      (chartAt H p p) = u p := by
  rw [coordFun_apply _ _ (chartAt_mem_chartDomOpens f p)]
  simp only [localCoord]
  rw [(chartAt H p).left_inv (mem_chart_source H p)]
  exact coordAt_chartAt (f p) (u p)

/-- The local representatives separate the sections. -/
theorem toPi_injective : Function.Injective (toPi (E := E) (ℓ := ℓ) (f := f) (H := H)) := by
  intro u w h
  ext p
  have h1 := congrArg (fun φ ↦ φ (⟨chartAt H p, chart_mem_atlas H p⟩,
    ⟨chartAt E (f p), chart_mem_atlas E (f p)⟩) (chartAt H p p)) h
  change coordFun _ u _ = coordFun _ w _ at h1
  rwa [coordFun_chartAt, coordFun_chartAt] at h1

/-- **The topology of `Γ_f`**: the initial topology with respect to the local representatives,
each in the compact-open `C^ℓ` topology. -/
instance : TopologicalSpace (SecCk H E ℓ f) := .induced toPi inferInstance

/-- `Γ_f` embeds in the product of the spaces of local representatives. -/
theorem isEmbedding_toPi : Topology.IsEmbedding (toPi (E := E) (ℓ := ℓ) (f := f) (H := H)) :=
  ⟨⟨rfl⟩, toPi_injective⟩

/-- `Γ_f` is a topological vector space (Glöckner–Neeb, Lemma 4.1.31). -/
instance : IsTopologicalAddGroup (SecCk H E ℓ f) := isTopologicalAddGroup_induced toPi

/-- `Γ_f` is a topological vector space (Glöckner–Neeb, Lemma 4.1.31). -/
instance : ContinuousSMul ℝ (SecCk H E ℓ f) := continuousSMul_induced toPi

/-- `Γ_f` is locally convex (Glöckner–Neeb, Lemma 4.1.31). -/
instance : LocallyConvexSpace ℝ (SecCk H E ℓ f) := LocallyConvexSpace.induced toPi

/-- `Γ_f` is Hausdorff. -/
instance : T2Space (SecCk H E ℓ f) := isEmbedding_toPi.t2Space

/-- The local representatives are continuous linear. -/
def coordCLM (a : atlas H M × atlas E N) :
    SecCk H E ℓ f →L[ℝ] ContDiffMBMap E ℓ (chartDomOpens f a.1 a.2) :=
  ⟨coordL a, (continuous_apply a).comp (continuous_induced_dom : Continuous (toPi (f := f)))⟩

/-- All the local representatives, as a continuous linear map. -/
def toPiCLM : SecCk H E ℓ f →L[ℝ] ∀ a : atlas H M × atlas E N,
    ContDiffMBMap E ℓ (chartDomOpens f a.1 a.2) :=
  ⟨toPi, continuous_induced_dom⟩

/-- **The local representatives of `Γ_f` have closed range**: the families of `C^ℓ` maps that are
compatible under the coordinate changes are the local representatives of sections. -/
theorem isClosed_range_toPi : IsClosed (range (toPi (E := E) (ℓ := ℓ) (f := f) (H := H))) := by
  let S : Set (∀ a : atlas H M × atlas E N, ContDiffMBMap E ℓ (chartDomOpens f a.1 a.2)) :=
    {φ | ∀ (a b : atlas H M × atlas E N) (x y : H) (hx : x ∈ chartDomOpens f a.1 a.2)
      (hy : y ∈ chartDomOpens f b.1 b.2) (_ : a.1.1.symm x = b.1.1.symm y),
      tangentCoordChange a.2 b.2 (f (a.1.1.symm x)) (φ a x) = φ b y}
  have hev : ∀ (a : atlas H M × atlas E N) (x : H) (hx : x ∈ chartDomOpens f a.1 a.2),
      Continuous fun φ : (∀ a : atlas H M × atlas E N,
        ContDiffMBMap E ℓ (chartDomOpens f a.1 a.2)) ↦ φ a x := fun a x hx ↦
    ((continuous_eval_const ((⟨x, hx⟩, Fin.elim0) : chartDomOpens f a.1 a.2 × (Fin 0 → H))).comp
      (ContDiffMBMap.continuous_iteratedD 0 (Nat.zero_le ℓ))).comp (continuous_apply a)
  have hS : IsClosed S := by
    simp only [S, ofPred_forall]
    refine isClosed_iInter fun a ↦ isClosed_iInter fun b ↦ isClosed_iInter fun x ↦
      isClosed_iInter fun y ↦ isClosed_iInter fun hx ↦ isClosed_iInter fun hy ↦
      isClosed_iInter fun hxy ↦ isClosed_eq ?_ (hev b y hy)
    exact (continuous_tangentCoordChange a.2 b.2 ⟨(mem_chartDomOpens.1 hx).2,
      hxy ▸ (mem_chartDomOpens.1 hy).2⟩).comp (hev a x hx)
  convert hS using 1
  ext φ
  constructor
  · rintro ⟨u, rfl⟩ a b x y hx hy hxy
    change tangentCoordChange a.2 b.2 (f (a.1.1.symm x)) (coordFun a u x) = coordFun b u y
    rw [coordFun_apply _ _ hx, coordFun_apply _ _ hy]
    simp only [localCoord, coordAt, ← hxy]
    exact tangentCoordChange_comp _ _ _ ⟨⟨mem_chart_source E _, (mem_chartDomOpens.1 hx).2⟩,
      hxy ▸ (mem_chartDomOpens.1 hy).2⟩ _
  · intro hφ
    let c : M → atlas H M × atlas E N := fun p ↦
      (⟨chartAt H p, chart_mem_atlas H p⟩, ⟨chartAt E (f p), chart_mem_atlas E (f p)⟩)
    let u : M → E := fun p ↦ φ (c p) (chartAt H p p)
    have key : ∀ (b : atlas H M × atlas E N) (y : H) (hy : y ∈ chartDomOpens f b.1 b.2),
        localCoord f b.1 b.2 u y = φ b y := fun b y hy ↦ by
      set p := b.1.1.symm y
      have hp : (c p).1.1.symm (chartAt H p p) = p :=
        (chartAt H p).left_inv (mem_chart_source H p)
      have h := hφ (c p) b (chartAt H p p) y (chartAt_mem_chartDomOpens f p) hy hp
      rw [hp] at h
      exact h
    have hu : ∀ j i, ContDiffMBOn ℓ (localCoord f j i u) (chartDomOpens f j i) := fun j i ↦
      ContDiffMBOn.congr_of_isOpen (chartDomOpens f j i).isOpen
        (fun y hy ↦ (key (j, i) y hy).symm) (φ (j, i)).contDiffMBOn
    refine ⟨mk u hu, funext fun a ↦ ?_⟩
    ext x
    change coordFun a (mk u hu) x = φ a x
    by_cases hx : x ∈ chartDomOpens f a.1 a.2
    · rw [coordFun_apply _ _ hx, coe_mk, key a x hx]
    · rw [ContDiffMBMap.apply_of_notMem _ hx, ContDiffMBMap.apply_of_notMem _ hx]

/-- **`C^k` maps into `Γ_f`**: a map into `Γ_f` is `C^k` if all its local representatives are. -/
theorem contDiffMBOn_of_coordFun {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [T2Space X] {k : ℕ}
    {ψ : X → SecCk H E ℓ f} {W : Set X} (hW : IsOpen W)
    (h : ∀ a, ContDiffMBOn k (fun w ↦ coordFun a (ψ w)) W) : ContDiffMBOn k ψ W :=
  contDiffMBOn_of_isClosedEmbedding toPiCLM isEmbedding_toPi isClosed_range_toPi hW
    (contDiffMBOn_pi hW h)

/-- A map into `Γ_f` is continuous if and only if all its local representatives are. -/
theorem continuous_iff {P : Type*} [tP : TopologicalSpace P] {ψ : P → SecCk H E ℓ f} :
    Continuous ψ ↔ ∀ a, Continuous fun p ↦ coordFun a (ψ p) :=
  ⟨fun h a ↦ (coordCLM a).continuous.comp h, fun h ↦ continuous_induced_rng.2
    (continuous_pi fun a ↦ h a)⟩

/-- A `C^ℓ` section is a continuous section. -/
theorem continuous_section (u : SecCk H E ℓ f) :
    Continuous fun x ↦ (⟨f x, u x⟩ : TangentBundle E N) := by
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  let j : atlas H M := ⟨chartAt H p, chart_mem_atlas H p⟩
  let i : atlas E N := ⟨chartAt E (f p), chart_mem_atlas E (f p)⟩
  refine (continuousAt_iff_coordAt (s := fun x ↦ (⟨f x, u x⟩ : TangentBundle E N)) i
    (mem_chart_source E (f p))).2 ⟨f.continuous.continuousAt, ?_⟩
  have hc : ContinuousAt (localCoord f j i u) (chartAt H p p) :=
    (contDiffMBOn_localCoord u j i).continuousOn.continuousAt
      ((chartDomOpens f j i).isOpen.mem_nhds (chartAt_mem_chartDomOpens f p))
  refine (hc.comp ((chartAt H p).continuousAt (mem_chart_source H p))).congr ?_
  filter_upwards [(chartAt H p).open_source.mem_nhds (mem_chart_source H p)] with x hx
  simp only [Function.comp_apply, localCoord, j]
  rw [(chartAt H p).left_inv hx]

variable [T2Space M]

/-- A `C^ℓ` section is a continuous section: the inclusion `Γ_f^ℓ → Γ_f^0` is continuous linear. -/
def toSec : SecCk H E ℓ f →L[ℝ] Sec E f where
  toFun u := Sec.mk u (continuous_section u)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by
    refine Sec.continuous_iff.2 fun b ↦ ?_
    obtain ⟨t, ht⟩ := b.2.1.elim_finite_subcover (fun p : M ↦ (chartAt H p).source)
      (fun p ↦ (chartAt H p).open_source) fun x _ ↦ mem_iUnion.2 ⟨x, mem_chart_source H x⟩
    obtain ⟨Kb, hKb, hKbs, hLeq⟩ := b.2.1.finite_compact_cover t _
      (fun p _ ↦ (chartAt H p).open_source) ht
    have hsub : ∀ q : t, Kb q.1 ⊆ b.1.2 := fun q ↦ by
      rw [hLeq]
      exact subset_biUnion_of_mem (u := Kb) q.2
    have hcov : b.1.2 ⊆ ⋃ q : t, Kb q.1 := by
      rw [hLeq]
      intro y hy
      obtain ⟨a, ha, hya⟩ := mem_iUnion₂.1 hy
      exact mem_iUnion.2 ⟨⟨a, ha⟩, hya⟩
    refine continuous_of_continuous_restrict_pieces (G := E) hsub (fun q ↦ hKb q.1) hcov
      fun q ↦ ?_
    let j : atlas H M := ⟨chartAt H q.1, chart_mem_atlas H q.1⟩
    have hmem : ∀ y : Kb q.1, chartAt H q.1 y ∈ chartDomOpens f j b.1.1 := fun y ↦ by
      rw [mem_chartDomOpens]
      refine ⟨(chartAt H q.1).map_source (hKbs q.1 y.2), ?_⟩
      rw [(chartAt H q.1).left_inv (hKbs q.1 y.2)]
      exact b.2.2 y (hsub q y.2)
    let σ : C(Kb q.1, chartDomOpens f j b.1.1 × (Fin 0 → H)) :=
      ⟨fun y ↦ (⟨chartAt H q.1 y, hmem y⟩, Fin.elim0), by
        refine Continuous.prodMk (Continuous.subtype_mk ?_ _) continuous_const
        exact (chartAt H q.1).continuousOn.comp_continuous continuous_subtype_val
          fun y ↦ hKbs q.1 y.2⟩
    refine ((ContinuousMap.continuous_precomp σ).comp
      ((ContDiffMBMap.continuous_iteratedD 0 (Nat.zero_le ℓ)).comp
        (coordCLM (j, b.1.1)).continuous)).congr fun u ↦ ?_
    ext y
    change coordFun (j, b.1.1) u (chartAt H q.1 y) = coordAt b.1.1 (⟨f y, u y⟩ : TangentBundle E N)
    rw [coordFun_apply _ _ (hmem y)]
    simp only [localCoord, j]
    rw [(chartAt H q.1).left_inv (hKbs q.1 y.2)]

/-- `toSec u` has the same fiber coordinates as `u`. -/
@[simp]
theorem toSec_apply (u : SecCk H E ℓ f) (x : M) : toSec u x = u x :=
  rfl

end SecCk

end SectionsCk
/-! ### Jets on subsets of a locally convex space -/

section Jets

variable {H : Type u} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H]
  {E : Type v} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

open scoped Classical in
/-- **The `m`-jet of `f` on a set `S`**: the restriction `d^(m) f|_{S × H^m}` of the `m`-th
differential, as a continuous map (and `0` if this restriction is not continuous). For `f` of
class `C^k` on an open set containing `S` and `m ≤ k` it is the honest restriction
(`jetOn_apply`). The set `S` is arbitrary: no interior is required. -/
def jetOn (m : ℕ) (f : H → E) (S : Set H) : C(S × (Fin m → H), E) :=
  if h : Continuous fun p : S × (Fin m → H) ↦ iteratedDMB m f ((p.1 : H), p.2) then ⟨_, h⟩
  else 0

/-- The restricted differentials of a `C^k` map are continuous. -/
theorem continuous_iteratedDMB_restrict {k m : ℕ} {f : H → E} {U S : Set H}
    (hf : ContDiffMBOn k f U) (hSU : S ⊆ U) (hm : m ≤ k) :
    Continuous fun p : S × (Fin m → H) ↦ iteratedDMB m f ((p.1 : H), p.2) :=
  (hf.hasContIterDerivOn.2 m hm).comp_continuous (continuous_subtype_val.prodMap continuous_id)
    fun p ↦ ⟨hSU p.1.2, mem_univ _⟩

/-- On a set where `f` is `C^k`, the `m`-jet (`m ≤ k`) is the restricted differential. -/
theorem jetOn_apply {k m : ℕ} {f : H → E} {U S : Set H} (hf : ContDiffMBOn k f U) (hSU : S ⊆ U)
    (hm : m ≤ k) (p : S × (Fin m → H)) : jetOn m f S p = iteratedDMB m f ((p.1 : H), p.2) := by
  rw [jetOn]
  split_ifs with h
  · rfl
  · exact absurd (continuous_iteratedDMB_restrict hf hSU hm) h

/-- The inclusion `S × H^m → S' × H^m` for `S ⊆ S'`. -/
def jetIncl {S S' : Set H} (h : S ⊆ S') (m : ℕ) : C(S × (Fin m → H), S' × (Fin m → H)) :=
  ⟨fun p ↦ (Set.inclusion h p.1, p.2),
    ((continuous_inclusion h).comp continuous_fst).prodMk continuous_snd⟩

/-- Jets on a smaller set are restrictions of jets on a larger one. -/
theorem jetOn_mono {k m : ℕ} {f : H → E} {U S S' : Set H} (hf : ContDiffMBOn k f U)
    (hS'U : S' ⊆ U) (h : S ⊆ S') (hm : m ≤ k) :
    jetOn m f S = (jetOn m f S').comp (jetIncl h m) := by
  ext p
  rw [ContinuousMap.comp_apply, jetOn_apply hf (h.trans hS'U) hm, jetOn_apply hf hS'U hm]
  rfl

/-- **Jets are determined by compact sets**: a family of jets on `S` depends continuously on a
parameter if its restrictions to the compact subsets of `S` do (compact-open topologies). -/
theorem continuousOn_jetOn_of_isCompact {P : Type*} [TopologicalSpace P] {ψ : P → H → E}
    {Q : Set P} {S : Set H} {k m : ℕ} (hm : m ≤ k)
    (hreg : ∀ p ∈ Q, ∃ U, S ⊆ U ∧ ContDiffMBOn k (ψ p) U)
    (h : ∀ K ⊆ S, IsCompact K → ContinuousOn (fun p ↦ jetOn m (ψ p) K) Q) :
    ContinuousOn (fun p ↦ jetOn m (ψ p) S) Q := by
  intro p hp
  change Tendsto _ _ _
  rw [ContinuousMap.tendsto_compactOpen_iff_forall]
  intro C hC
  set K : Set H := Subtype.val '' (Prod.fst '' C)
  have hKc : IsCompact K := (hC.image continuous_fst).image continuous_subtype_val
  have hKS : K ⊆ S := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  let ρ : C(C, K × (Fin m → H)) :=
    ⟨fun c ↦ (⟨c.1.1, mem_image_of_mem _ (mem_image_of_mem _ c.2)⟩, c.1.2), by fun_prop⟩
  have heq : ∀ q ∈ Q, (jetOn m (ψ q) S).restrict C = (jetOn m (ψ q) K).comp ρ := by
    intro q hq
    obtain ⟨U, hSU, hq⟩ := hreg q hq
    ext c
    rw [ContinuousMap.restrict_apply, ContinuousMap.comp_apply, jetOn_apply hq hSU hm,
      jetOn_apply hq (hKS.trans hSU) hm]
    rfl
  rw [heq p hp]
  refine Tendsto.congr' (eventually_nhdsWithin_of_forall fun q hq ↦ (heq q hq).symm) ?_
  exact ((ContinuousMap.continuous_precomp ρ).tendsto _).comp (h K hKS hKc p hp)

end Jets

/-! ### The space `C^ℓ(M, N)` and its compact-open `C^ℓ` topology -/

/-- On a type with at most one element, all topologies agree. -/
theorem topologicalSpace_eq_of_subsingleton {α : Type*} [Subsingleton α]
    (t₁ t₂ : TopologicalSpace α) : t₁ = t₂ := by
  ext s
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨fun _ ↦ @isOpen_empty _ t₂, fun _ ↦ @isOpen_empty _ t₁⟩
  · rw [hs.eq_univ]
    exact ⟨fun _ ↦ @isOpen_univ _ t₂, fun _ ↦ @isOpen_univ _ t₁⟩

section CkMaps

variable (H : Type u) [AddCommGroup H] [Module ℝ H] [TopologicalSpace H]
  (E : Type u) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  (ℓ : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
  (N : Type*) [TopologicalSpace N] [ChartedSpace E N]

/-- **The `C^ℓ` maps** `M → N`. -/
def CkMap : Type _ := {f : M → N // ContMDiffMB H E ℓ f}

/-- An index for the jets that define the topology of `C^ℓ(M, N)`: charts `j` of `M` and `i` of
`N` and a compact set `K` in the target of `j`. No interior is required of `K`: in a model that is
not locally compact (for instance an infinite-dimensional one), compact sets have empty interior. -/
structure CkMap.CompactIdx where
  /-- The chart of `M`. -/
  j : atlas H M
  /-- The chart of `N`. -/
  i : atlas E N
  /-- A compact set in the target of `j`. -/
  K : Set H
  /-- `K` is compact. -/
  isCompact_K : IsCompact K
  /-- `K` lies in the target of `j`. -/
  K_subset : K ⊆ j.1.target

/-- An index for the local representatives that define the chart topology of `C^ℓ(M, N)`:
charts `j` of `M` and `i` of `N`, a compact set `L` in the target of `j` and an open set `V ⊆ L`. -/
structure CkMap.ChartIdx where
  /-- The chart of `M`. -/
  j : atlas H M
  /-- The chart of `N`. -/
  i : atlas E N
  /-- A compact set in the target of `j`. -/
  L : Set H
  /-- `L` is compact. -/
  isCompact_L : IsCompact L
  /-- `L` lies in the target of `j`. -/
  L_subset : L ⊆ j.1.target
  /-- An open set inside `L`, the domain of the local representative. -/
  V : Opens H
  /-- `V` lies in `L`. -/
  V_subset : (V : Set H) ⊆ L

namespace CkMap

variable {H E ℓ M N}

/-- A `C^ℓ` map is a map. -/
instance : FunLike (CkMap H E ℓ M N) M N where
  coe f := f.1
  coe_injective := Subtype.val_injective

/-- `C^ℓ` maps are equal if they agree as maps. -/
@[ext]
theorem ext {f g : CkMap H E ℓ M N} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

/-- On an empty manifold there is only one map. -/
instance [IsEmpty M] : Subsingleton (CkMap H E ℓ M N) :=
  ⟨fun _ _ ↦ ext fun x ↦ isEmptyElim x⟩

/-- A `C^ℓ` map is `C^ℓ`. -/
theorem contMDiffMB (f : CkMap H E ℓ M N) : ContMDiffMB H E ℓ f :=
  f.2

/-- A `C^ℓ` map as a continuous map. -/
def toC (f : CkMap H E ℓ M N) : C(M, N) :=
  ⟨f, continuousOn_univ.1 f.2.1⟩

/-- `toC f` is `f`. -/
@[simp]
theorem coe_toC (f : CkMap H E ℓ M N) : ⇑(toC f) = f :=
  rfl

/-- The continuous maps sending `j⁻¹(K)` into the source of `i`. -/
def CompactIdx.domC (a : CompactIdx H E M N) : Set C(M, N) :=
  {g | MapsTo g (a.j.1.symm '' a.K) a.i.1.source}

/-- The `C^ℓ` maps sending `j⁻¹(K)` into the source of `i`. -/
def CompactIdx.dom (a : CompactIdx H E M N) : Set (CkMap H E ℓ M N) :=
  toC ⁻¹' a.domC

omit [AddCommGroup H] [Module ℝ H] [AddCommGroup E] [Module ℝ E] in
/-- `j⁻¹(K)` is compact. -/
theorem CompactIdx.isCompact_symm_image (a : CompactIdx H E M N) :
    IsCompact (a.j.1.symm '' a.K) :=
  a.isCompact_K.image_of_continuousOn (a.j.1.continuousOn_symm.mono a.K_subset)

omit [AddCommGroup H] [Module ℝ H] [AddCommGroup E] [Module ℝ E] in
/-- The sets `g(j⁻¹(K)) ⊆ i.source` are open in `C(M, N)`. -/
theorem CompactIdx.isOpen_domC (a : CompactIdx H E M N) : IsOpen a.domC :=
  ContinuousMap.isOpen_setOfPred_mapsTo a.isCompact_symm_image a.i.1.open_source

/-- If `g` sends `j⁻¹(K)` into the source of `i`, then `K` lies in the domain of the local
representative `i ∘ g ∘ j⁻¹`. -/
theorem CompactIdx.subset_chartDomain (a : CompactIdx H E M N) {g : CkMap H E ℓ M N}
    (hg : g ∈ a.dom) : a.K ⊆ chartDomain g univ a.j.1 a.i.1 := fun _ hx ↦
  ⟨a.K_subset hx, mem_univ _, hg (mem_image_of_mem _ hx)⟩

/-- The continuous maps sending `j⁻¹(L)` into the source of `i`. -/
def ChartIdx.domC (a : ChartIdx H E M N) : Set C(M, N) :=
  {g | MapsTo g (a.j.1.symm '' a.L) a.i.1.source}

/-- The `C^ℓ` maps sending `j⁻¹(L)` into the source of `i`. -/
def ChartIdx.dom (a : ChartIdx H E M N) : Set (CkMap H E ℓ M N) :=
  toC ⁻¹' a.domC

omit [AddCommGroup H] [Module ℝ H] [AddCommGroup E] [Module ℝ E] in
/-- The sets `g(j⁻¹(L)) ⊆ i.source` are open in `C(M, N)`. -/
theorem ChartIdx.isOpen_domC (a : ChartIdx H E M N) : IsOpen a.domC := by
  have hK : IsCompact (a.j.1.symm '' a.L) :=
    a.isCompact_L.image_of_continuousOn (a.j.1.continuousOn_symm.mono a.L_subset)
  exact ContinuousMap.isOpen_setOfPred_mapsTo hK a.i.1.open_source

/-- If `g` sends `j⁻¹(L)` into the source of `i`, the open set `V ⊆ L` lies in the domain of the
local representative of `g` in the charts `j`, `i`. -/
theorem ChartIdx.subset_chartDomain (a : ChartIdx H E M N) {g : CkMap H E ℓ M N}
    (hg : g ∈ a.dom) : (a.V : Set H) ⊆ chartDomain g univ a.j.1 a.i.1 := fun _ hx ↦
  ⟨a.L_subset (a.V_subset hx), mem_univ _, hg (mem_image_of_mem _ (a.V_subset hx))⟩

/-- The jet index of a compact subset `K` of the open set `V` of a chart index. -/
def ChartIdx.compactIdx (b : ChartIdx H E M N) (K : Set H) (hK : IsCompact K)
    (hKV : K ⊆ b.V) : CompactIdx H E M N :=
  ⟨b.j, b.i, K, hK, fun _ hx ↦ b.L_subset (b.V_subset (hKV hx))⟩

/-- Maps sending `j⁻¹(L)` into the source of `i` send `j⁻¹(K)` there, for `K ⊆ V`. -/
theorem ChartIdx.dom_subset_compactIdx_dom (b : ChartIdx H E M N) {K : Set H} (hK : IsCompact K)
    (hKV : K ⊆ b.V) : (b.dom : Set (CkMap H E ℓ M N)) ⊆ (b.compactIdx K hK hKV).dom :=
  fun _ hg ↦ MapsTo.mono_left hg (image_mono (hKV.trans b.V_subset))

variable [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold H M] [MBManifold E N]

/-- The `m`-jet of the local representative `i ∘ g ∘ j⁻¹` on `K`:
`d^(m)(i ∘ g ∘ j⁻¹)|_{K × H^m}`. -/
def CompactIdx.jet (a : CompactIdx H E M N) (m : ℕ) (g : CkMap H E ℓ M N) :
    C(a.K × (Fin m → H), E) :=
  jetOn m (a.i.1 ∘ g ∘ a.j.1.symm) a.K

/-- The local representatives are `C^ℓ` on their (open) domains. -/
theorem CompactIdx.contDiffMBOn_rep (a : CompactIdx H E M N) (g : CkMap H E ℓ M N) :
    ContDiffMBOn ℓ (a.i.1 ∘ g ∘ a.j.1.symm) (chartDomain g univ a.j.1 a.i.1) :=
  g.contMDiffMB.contDiffMBOn_chart isOpen_univ a.j.2 a.i.2

omit [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold H M] [MBManifold E N] in
/-- The domains of the local representatives are open. -/
theorem CompactIdx.isOpen_chartDomain (a : CompactIdx H E M N) (g : CkMap H E ℓ M N) :
    IsOpen (chartDomain g univ a.j.1 a.i.1) :=
  LocallyConvex.Manifolds.isOpen_chartDomain isOpen_univ (toC g).continuous.continuousOn _ _

/-- On `dom a`, the jets are the restricted differentials of the local representative. -/
theorem CompactIdx.jet_apply (a : CompactIdx H E M N) {g : CkMap H E ℓ M N} (hg : g ∈ a.dom)
    {m : ℕ} (hm : m ≤ ℓ) (p : a.K × (Fin m → H)) :
    a.jet m g p = iteratedDMB m (a.i.1 ∘ g ∘ a.j.1.symm) ((p.1 : H), p.2) :=
  jetOn_apply (a.contDiffMBOn_rep g) (a.subset_chartDomain hg) hm p

open scoped Classical in
/-- The local representative `i ∘ g ∘ j⁻¹ ∈ C^ℓ(V, E)` of `g ∈ C^ℓ(M, N)` (and `0` if `g` does not
send `j⁻¹(L)` into the source of `i`). -/
def ChartIdx.rep (a : ChartIdx H E M N) (g : CkMap H E ℓ M N) : ContDiffMBMap E ℓ a.V :=
  if hg : g ∈ a.dom then
    ContDiffMBMap.mk ((a.V : Set H).indicator (a.i.1 ∘ g ∘ a.j.1.symm))
      (ContDiffMBOn.congr_of_isOpen a.V.isOpen (fun _ hx ↦ (indicator_of_mem hx _).symm)
        ((g.contMDiffMB.contDiffMBOn_chart isOpen_univ a.j.2 a.i.2).mono
          (a.subset_chartDomain hg)))
      fun _ hx ↦ indicator_of_notMem hx _
  else 0

/-- On `V`, the local representative is `i ∘ g ∘ j⁻¹`. -/
theorem ChartIdx.rep_apply (a : ChartIdx H E M N) {g : CkMap H E ℓ M N} (hg : g ∈ a.dom) {x : H}
    (hx : x ∈ a.V) : a.rep g x = a.i.1 (g (a.j.1.symm x)) := by
  rw [ChartIdx.rep, dite_eq_left_of_eq_true (eq_true hg)]
  exact indicator_of_mem (show x ∈ (a.V : Set H) from hx) _

/-- On a compact set `K ⊆ V`, the jets of the local representative `a.rep g ∈ C^ℓ(V, E)` are the
jets of `g` on `K`. -/
theorem ChartIdx.jetOn_rep (b : ChartIdx H E M N) {K : Set H} (hK : IsCompact K)
    (hKV : K ⊆ b.V) {g : CkMap H E ℓ M N} (hg : g ∈ b.dom) {m : ℕ} (hm : m ≤ ℓ) :
    jetOn m (b.rep g) K = (b.compactIdx K hK hKV).jet m g := by
  ext p
  refine (jetOn_apply (b.rep g).contDiffMBOn hKV hm p).trans <|
    (iteratedDMB_congr_of_eventuallyEq m (Filter.eventually_of_mem
      (b.V.isOpen.mem_nhds (hKV p.1.2)) fun x hx ↦ b.rep_apply hg hx) _).trans
      ((b.compactIdx K hK hKV).jet_apply (b.dom_subset_compactIdx_dom hK hKV hg) hm p).symm

/-- The jets on `V` of `a.rep g ∈ C^ℓ(V, E)` are its differentials. -/
theorem ChartIdx.jetOn_rep_V (b : ChartIdx H E M N) (g : CkMap H E ℓ M N) {m : ℕ} (hm : m ≤ ℓ) :
    jetOn m (b.rep g) (b.V : Set H) = ContDiffMBMap.iteratedD m hm (b.rep g) := by
  ext p
  rw [jetOn_apply (b.rep g).contDiffMBOn subset_rfl hm]
  rfl

variable (H E ℓ M N) in
/-- **The chart topology on `C^ℓ(M, N)`**: the coarsest topology finer than the compact-open
topology of `C(M, N)` for which the local representatives `g ↦ i ∘ g ∘ j⁻¹ ∈ C^ℓ(V, E)` are
continuous on the (open) sets of maps `g` with `g(j⁻¹(L)) ⊆ i.source`, for charts `j`, `i`,
compact `L` in the target of `j` and open `V ⊆ L`. It is coarser than the jet topology
(`CkMap.jetTopology_le_chartTopology`) and equal to it if the model `H` is locally compact
(`CkMap.chartTopology_eq_jetTopology`); otherwise compact sets have empty interior, every such `V`
is empty, and it collapses to the compact-open `C^0` topology. It is not the instance. -/
@[instance_reducible]
def chartTopology : TopologicalSpace (CkMap H E ℓ M N) :=
  TopologicalSpace.induced toC inferInstance ⊓ TopologicalSpace.generateFrom
    {S | ∃ (a : ChartIdx H E M N) (O : Set (ContDiffMBMap E ℓ a.V)), IsOpen O ∧
      S = a.dom ∩ a.rep ⁻¹' O}

variable (H E ℓ M N) in
/-- **The compact-open `C^ℓ` topology on `C^ℓ(M, N)` through jets on compact sets in charts**: the
coarsest topology finer than the compact-open topology of `C(M, N)` for which, for all charts `j`
of `M`, `i` of `N`, every compact set `K` in the target of `j` and every `m ≤ ℓ`, the jet
`g ↦ d^(m)(i ∘ g ∘ j⁻¹)|_{K × H^m} ∈ C(K × H^m, E)` (compact-open topology) is continuous on the
open set of maps `g` with `g(j⁻¹(K)) ⊆ i.source`. A subbasis is given by the open sets of
`C(M, N)` and the sets `{g : g(j⁻¹(K)) ⊆ i.source, d^(m)(i ∘ g ∘ j⁻¹)|_{K × H^m} ∈ O}`. This is the
instance `CkMap.instTopologicalSpace`. -/
@[instance_reducible]
def jetTopology : TopologicalSpace (CkMap H E ℓ M N) :=
  TopologicalSpace.induced toC inferInstance ⊓ TopologicalSpace.generateFrom
    {S | ∃ (a : CompactIdx H E M N) (m : ℕ), m ≤ ℓ ∧
      ∃ O : Set C(a.K × (Fin m → H), E), IsOpen O ∧ S = a.dom ∩ a.jet m ⁻¹' O}

/-- **The compact-open `C^ℓ` topology on `C^ℓ(M, N)`** is the jet topology `CkMap.jetTopology`
(the weak `C^ℓ` topology of Hirsch in locally convex form). It is the topology of Glöckner–Neeb,
Definition 4.1.2, for every Hausdorff `M` modeled on any Hausdorff locally convex space
(`CkMap.topology_eq_gnTopology`, `MappingSpace/TopologyULift.lean`), and the chart topology
`CkMap.chartTopology` when the model of `M` is locally compact, in particular when `M` is compact
(`CkMap.topology_eq_chartTopology`, `CkMap.topology_eq_chartTopology_of_compactSpace`). -/
instance instTopologicalSpace : TopologicalSpace (CkMap H E ℓ M N) :=
  jetTopology H E ℓ M N

omit [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold H M] [MBManifold E N] in
/-- The topology of `C^ℓ(M, N)` is the jet topology (by definition). -/
theorem topology_eq_jetTopology :
    (inferInstance : TopologicalSpace (CkMap H E ℓ M N)) = jetTopology H E ℓ M N :=
  rfl

/-! #### The jet topology -/

omit [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold H M] [MBManifold E N] in
/-- `C^ℓ(M, N) → C(M, N)` is continuous. -/
theorem continuous_toC : Continuous (toC : CkMap H E ℓ M N → C(M, N)) :=
  continuous_iff_le_induced.2 inf_le_left

omit [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold H M] [MBManifold E N] in
/-- The sets `g(j⁻¹(K)) ⊆ i.source` are open. -/
theorem CompactIdx.isOpen_dom (a : CompactIdx H E M N) :
    IsOpen (a.dom : Set (CkMap H E ℓ M N)) :=
  a.isOpen_domC.preimage continuous_toC

omit [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold H M] [MBManifold E N] in
/-- The sets `g(j⁻¹(L)) ⊆ i.source` are open. -/
theorem ChartIdx.isOpen_dom (a : ChartIdx H E M N) : IsOpen (a.dom : Set (CkMap H E ℓ M N)) :=
  a.isOpen_domC.preimage continuous_toC

omit [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold H M] [MBManifold E N] in
/-- **Continuity into `C^ℓ(M, N)`**: a map is continuous if and only if it is continuous into
`C(M, N)` and all its jets are continuous where defined. -/
theorem continuous_jetTopology_iff {P : Type*} [TopologicalSpace P] {ψ : P → CkMap H E ℓ M N} :
    Continuous ψ ↔ Continuous (fun p ↦ toC (ψ p)) ∧
      ∀ a : CompactIdx H E M N, ∀ m ≤ ℓ, ContinuousOn (fun p ↦ a.jet m (ψ p)) (ψ ⁻¹' a.dom) := by
  constructor
  · intro h
    have h₀ : Continuous fun p ↦ toC (ψ p) := continuous_toC.comp h
    refine ⟨h₀, fun a m hm ↦ ?_⟩
    have hdom : IsOpen (ψ ⁻¹' a.dom) := a.isOpen_domC.preimage h₀
    refine (continuousOn_open_iff hdom).2 fun O hO ↦ ?_
    have hS : IsOpen ((a.dom : Set (CkMap H E ℓ M N)) ∩ a.jet m ⁻¹' O) := by
      apply TopologicalSpace.le_def.1
        (inf_le_right (a := TopologicalSpace.induced toC inferInstance))
      exact TopologicalSpace.GenerateOpen.basic _ ⟨a, m, hm, O, hO, rfl⟩
    exact hS.preimage h
  · rintro ⟨h₀, h⟩
    refine continuous_inf_rng.2 ⟨continuous_induced_rng.2 h₀, continuous_generateFrom_iff.2 ?_⟩
    rintro S ⟨a, m, hm, O, hO, rfl⟩
    exact (h a m hm).isOpen_inter_preimage (a.isOpen_domC.preimage h₀) hO

omit [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold H M] [MBManifold E N] in
/-- The jets are continuous where they are defined. -/
theorem CompactIdx.continuousOn_jet (a : CompactIdx H E M N) {m : ℕ} (hm : m ≤ ℓ) :
    ContinuousOn (a.jet m : CkMap H E ℓ M N → _) a.dom :=
  (continuous_jetTopology_iff.1 continuous_id).2 a m hm

/-- The `0`-jets are continuous for the compact-open topology of `C(M, N)`. -/
theorem CompactIdx.continuousOn_jet_zero {P : Type*} [TopologicalSpace P]
    {ψ : P → CkMap H E ℓ M N} (h₀ : Continuous fun p ↦ toC (ψ p))
    (a : CompactIdx H E M N) :
    ContinuousOn (fun p ↦ a.jet 0 (ψ p)) (ψ ⁻¹' a.dom) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let σ : C(a.K × (Fin 0 → H), M) :=
    ⟨fun z ↦ a.j.1.symm z.1, a.j.1.continuousOn_symm.comp_continuous
      (continuous_subtype_val.comp continuous_fst) fun z ↦ a.K_subset z.1.2⟩
  have hmem : ∀ s : ψ ⁻¹' a.dom, ∀ z, (toC (ψ s)).comp σ z ∈ a.i.1.source :=
    fun s z ↦ s.2 (mem_image_of_mem _ z.1.2)
  have hc : Continuous fun s : ψ ⁻¹' a.dom ↦
      (⟨(toC (ψ s)).comp σ, hmem s⟩ :
        {g : C(a.K × (Fin 0 → H), N) // ∀ z, g z ∈ a.i.1.source}) :=
    (((ContinuousMap.continuous_precomp σ).comp h₀).comp continuous_subtype_val).subtype_mk _
  refine ((continuous_compOn a.i.1 a.i.1.continuousOn).comp hc).congr fun s ↦ ?_
  ext z
  change a.i.1 (ψ s (a.j.1.symm z.1)) = a.jet 0 (ψ s) z
  rw [a.jet_apply s.2 (Nat.zero_le ℓ)]
  rfl

/-! #### The chart topology -/

/-- `C^ℓ(M, N) → C(M, N)` is continuous for the chart topology. -/
theorem continuous_toC_chartTopology :
    Continuous[chartTopology H E ℓ M N, _] (toC : CkMap H E ℓ M N → C(M, N)) :=
  continuous_iff_le_induced.2 inf_le_left

/-- The sets `g(j⁻¹(L)) ⊆ i.source` are open for the chart topology. -/
theorem ChartIdx.isOpen_dom_chartTopology (a : ChartIdx H E M N) :
    IsOpen[chartTopology H E ℓ M N] (a.dom : Set (CkMap H E ℓ M N)) := by
  let _ : TopologicalSpace (CkMap H E ℓ M N) := chartTopology H E ℓ M N
  exact a.isOpen_domC.preimage continuous_toC_chartTopology

/-- The local representatives are continuous for the chart topology where they are defined. -/
theorem ChartIdx.continuousOn_rep (a : ChartIdx H E M N) :
    @ContinuousOn _ _ (chartTopology H E ℓ M N) _ (a.rep : CkMap H E ℓ M N → _) a.dom := by
  let _ : TopologicalSpace (CkMap H E ℓ M N) := chartTopology H E ℓ M N
  refine (continuousOn_open_iff a.isOpen_dom_chartTopology).2 fun O hO ↦ ?_
  exact TopologicalSpace.le_def.1 inf_le_right _
    (TopologicalSpace.GenerateOpen.basic _ ⟨a, O, hO, rfl⟩)

/-- **A continuity criterion for maps into `C^ℓ(M, N)` with the chart topology**: `ψ` is
continuous if `ψ` is continuous as a map into `C(M, N)` and all the local representatives of `ψ`
are continuous where defined. -/
theorem continuous_of_rep {P : Type*} [TopologicalSpace P] {ψ : P → CkMap H E ℓ M N}
    (h₀ : Continuous fun p ↦ toC (ψ p))
    (h : ∀ a : ChartIdx H E M N, ContinuousOn (fun p ↦ a.rep (ψ p)) (ψ ⁻¹' a.dom)) :
    Continuous[_, chartTopology H E ℓ M N] ψ := by
  refine continuous_inf_rng.2 ⟨continuous_induced_rng.2 h₀, continuous_generateFrom_iff.2 ?_⟩
  rintro S ⟨a, O, hO, rfl⟩
  exact (h a).isOpen_inter_preimage (a.isOpen_domC.preimage h₀) hO

/-- **A continuity criterion on open sets** for maps into `C^ℓ(M, N)` with the chart topology. -/
theorem continuousOn_of_rep {P : Type*} [TopologicalSpace P] {ψ : P → CkMap H E ℓ M N}
    {S : Set P} (h₀ : ContinuousOn (fun p ↦ toC (ψ p)) S)
    (h : ∀ a : ChartIdx H E M N, ContinuousOn (fun p ↦ a.rep (ψ p)) (S ∩ ψ ⁻¹' a.dom)) :
    @ContinuousOn _ _ _ (chartTopology H E ℓ M N) ψ S := by
  let _ : TopologicalSpace (CkMap H E ℓ M N) := chartTopology H E ℓ M N
  rw [continuousOn_iff_continuous_domRestrict]
  refine continuous_of_rep (continuousOn_iff_continuous_domRestrict.1 h₀) fun a ↦ ?_
  exact (h a).comp continuous_subtype_val.continuousOn fun s hs ↦ ⟨s.2, hs⟩

/-! #### Comparison of the jet topology and the chart topology -/

/-- **The jet topology is finer than the chart topology**, for every model: the local
representatives on `V ⊆ L` are determined by the jets on the compact subsets of `V`. -/
theorem jetTopology_le_chartTopology : jetTopology H E ℓ M N ≤ chartTopology H E ℓ M N := by
  refine continuous_id_iff_le.1 (continuous_of_rep (P := CkMap H E ℓ M N) continuous_toC
    fun b ↦ ?_)
  change ContinuousOn b.rep b.dom
  have h : ∀ m (hm : m ≤ ℓ),
      ContinuousOn (fun g ↦ ContDiffMBMap.iteratedD m hm (b.rep g)) b.dom := by
    intro m hm
    refine (continuousOn_jetOn_of_isCompact (ψ := fun g : CkMap H E ℓ M N ↦ ⇑(b.rep g))
      (S := (b.V : Set H)) hm (fun g _ ↦ ⟨b.V, subset_rfl, (b.rep g).contDiffMBOn⟩)
      fun K hKV hK ↦ ?_).congr fun g _ ↦ (b.jetOn_rep_V g hm).symm
    exact ((b.compactIdx K hK hKV).continuousOn_jet hm).mono
      (b.dom_subset_compactIdx_dom hK hKV) |>.congr fun g hg ↦ b.jetOn_rep hK hKV hg hm
  rw [continuousOn_iff_continuous_domRestrict]
  exact ContDiffMBMap.continuous_iff.2 fun m hm ↦
    continuousOn_iff_continuous_domRestrict.1 (h m hm)

/-- **For a locally compact model, the chart topology is finer than the jet topology**: a compact
set `K` in a chart domain lies in the interior `V` of a compact set `L` there. -/
theorem chartTopology_le_jetTopology [LocallyCompactSpace H] :
    chartTopology H E ℓ M N ≤ jetTopology H E ℓ M N := by
  let _ : TopologicalSpace (CkMap H E ℓ M N) := chartTopology H E ℓ M N
  refine continuous_id_iff_le.1 (continuous_jetTopology_iff.2
    ⟨continuous_toC_chartTopology, fun a m hm g₀ hg₀ ↦ ?_⟩)
  obtain ⟨L, hLc, hKL, hLD⟩ := exists_compact_between a.isCompact_K
    (a.isOpen_chartDomain g₀) (a.subset_chartDomain hg₀)
  let b : ChartIdx H E M N := ⟨a.j, a.i, L, hLc, fun x hx ↦ (hLD hx).1,
    ⟨interior L, isOpen_interior⟩, interior_subset⟩
  have hKV : a.K ⊆ b.V := hKL
  have hg₀b : g₀ ∈ b.dom := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hLD hx).2.2
  have hb : (b.dom : Set (CkMap H E ℓ M N)) ∈ 𝓝 g₀ := b.isOpen_dom_chartTopology.mem_nhds hg₀b
  have hc : ContinuousAt (fun g ↦ (jetOn m (b.rep g) (b.V : Set H)).comp (jetIncl hKV m)) g₀ := by
    simp only [b.jetOn_rep_V _ hm]
    exact (ContinuousMap.continuous_precomp _).continuousAt.comp
      ((ContDiffMBMap.continuous_iteratedD m hm).continuousAt.comp
        (b.continuousOn_rep.continuousAt hb))
  refine (hc.congr (Filter.eventually_of_mem hb fun g hg ↦ ?_)).continuousWithinAt
  change (jetOn m (b.rep g) (b.V : Set H)).comp (jetIncl hKV m) = a.jet m g
  rw [← jetOn_mono (b.rep g).contDiffMBOn subset_rfl hKV hm, b.jetOn_rep a.isCompact_K hKV hg hm]
  rfl

/-- **For a locally compact model, the chart topology is the jet topology.** -/
theorem chartTopology_eq_jetTopology [LocallyCompactSpace H] :
    chartTopology H E ℓ M N = jetTopology H E ℓ M N :=
  le_antisymm chartTopology_le_jetTopology jetTopology_le_chartTopology

/-- **For a locally compact model, the topology of `C^ℓ(M, N)` is the chart topology.** -/
theorem topology_eq_chartTopology [LocallyCompactSpace H] :
    (inferInstance : TopologicalSpace (CkMap H E ℓ M N)) = chartTopology H E ℓ M N :=
  chartTopology_eq_jetTopology.symm

/-- **For `M` compact, the topology of `C^ℓ(M, N)` is the chart topology**: a nonempty compact
manifold has a locally compact model (`locallyCompactSpace_of_compactSpace`). -/
theorem topology_eq_chartTopology_of_compactSpace [CompactSpace M] [T2Space M] :
    (inferInstance : TopologicalSpace (CkMap H E ℓ M N)) = chartTopology H E ℓ M N := by
  rcases isEmpty_or_nonempty M with hM | hM
  · exact topologicalSpace_eq_of_subsingleton _ _
  · have := locallyCompactSpace_of_compactSpace (H := H) M
    exact topology_eq_chartTopology

end CkMap

end CkMaps

/-! ### The charts and their inverses in local coordinates -/

section LocalFormulas

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [MBManifold E N]
  (A : LocalAddition E N)

/-- The fiber coordinate of a zero vector is zero. -/
theorem coordAt_zero (i : atlas E N) {q : N} (hq : q ∈ i.1.source) :
    coordAt i (⟨q, (0 : E)⟩ : TangentBundle E N) = 0 := by
  simpa using coordAt_smul i hq 0 0

/-- The chart `tangentChart i i` of `TN` is inverted by `(y, v) ↦ (i⁻¹ y, v)`. -/
theorem tangentChart_symm_coordAt (i : atlas E N) {v : TangentBundle E N}
    (hv : v.proj ∈ i.1.source) : (tangentChart i i.1).symm (i.1 v.proj, coordAt i v) = v := by
  have h := (tangentChart i i.1).left_inv ((mem_tangentChart_self_source i v).2 hv)
  rwa [tangentChart_self_apply] at h

namespace LocalAddition

/-- The local formula of the charts of `C^ℓ(M, N)`: `(y, z) ↦ θ⁻¹(i⁻¹ z, i'⁻¹ y)`, in the fiber
coordinates of the chart `i`. -/
def chartLocal (i' i : atlas E N) (q : E × E) : E :=
  A.transMap i' i (q.1, q.2, 0)

/-- The domain of `chartLocal`. -/
def chartLocalDom (i' i : atlas E N) : Set (E × E) :=
  (fun q : E × E ↦ (q.1, q.2, (0 : E))) ⁻¹' A.transDom i' i

/-- The domain of `chartLocal` is open. -/
theorem isOpen_chartLocalDom (i' i : atlas E N) : IsOpen (A.chartLocalDom i' i) :=
  (A.isOpen_transDom i' i).preimage (by fun_prop)

/-- `chartLocal` is smooth. -/
theorem smoothMBOn_chartLocal (i' i : atlas E N) :
    SmoothMBOn (A.chartLocal i' i) (A.chartLocalDom i' i) := fun k ↦ by
  let L : E × E →L[ℝ] E × E × E :=
    (ContinuousLinearMap.fst ℝ E E).prod ((ContinuousLinearMap.snd ℝ E E).prod 0)
  have h := ContDiffMBOn.comp (A.isOpen_chartLocalDom i' i) (A.isOpen_transDom i' i)
    (A.smoothMBOn_transMap i' i k) (L.contDiffMBOn k _) fun q hq ↦ hq
  exact h

/-- **The chart in local coordinates**: for `q ∈ i'.source`, `p ∈ i.source` and `(p, q)` in the
range of `θ`, `θ⁻¹(p, q)` has fiber coordinate `chartLocal (i' q, i p)` in the chart `i`. -/
theorem chartLocal_spec (i' i : atlas E N) {p q : N} (hq : q ∈ i'.1.source)
    (hp : p ∈ i.1.source) (hpq : (p, q) ∈ A.toOpenPartialHomeomorph.target) :
    ((i'.1 q, i.1 p) : E × E) ∈ A.chartLocalDom i' i ∧
      A.chartLocal i' i (i'.1 q, i.1 p) = coordAt i (A.toOpenPartialHomeomorph.symm (p, q)) := by
  have hvec : transVec i' (i'.1 q, i.1 p, 0) = (⟨q, 0⟩ : TangentBundle E N) := by
    have e : ((i'.1 q, (0 : E)) : E × E) =
        (i'.1 q, coordAt i' (⟨q, (0 : E)⟩ : TangentBundle E N)) := by
      rw [coordAt_zero i' hq]
    change (tangentChart i' i'.1).symm (i'.1 q, 0) = _
    rw [e]
    exact tangentChart_symm_coordAt i' (v := ⟨q, 0⟩) hq
  have hpair : A.transPair i' i (i'.1 q, i.1 p, 0) = (p, q) := by
    rw [transPair, hvec, LocalAddition.toFun_zero]
    exact Prod.ext (i.1.left_inv hp) rfl
  refine ⟨⟨⟨⟨i'.1.map_source hq, i.1.map_source hp⟩, ?_⟩, ?_⟩, ?_⟩
  · change transVec i' _ ∈ A.source
    rw [hvec]
    exact A.zero_mem q
  · change A.transPair i' i _ ∈ A.toOpenPartialHomeomorph.target
    rw [hpair]
    exact hpq
  · change coordAt i (A.toOpenPartialHomeomorph.symm (A.transPair i' i _)) = _
    rw [hpair]

/-- The local formula of the inverses of the charts: `(y, v) ↦ i''(Σ(i⁻¹ y, v))`. -/
def invLocal (i i'' : atlas E N) (q : E × E) : E :=
  i''.1 (A.toFun ((tangentChart i i.1).symm q))

/-- The domain of `invLocal`. -/
def invLocalDom (i i'' : atlas E N) : Set (E × E) :=
  ((tangentChart i i.1).target ∩ (tangentChart i i.1).symm ⁻¹' A.source) ∩
    (A.toFun ∘ (tangentChart i i.1).symm) ⁻¹' i''.1.source

/-- `(y, v) ↦ Σ(i⁻¹ y, v)` is smooth. -/
theorem smoothMBMOn_toFun_tangentChart_symm (i : atlas E N) :
    SmoothMBMOn (E × E) E (A.toFun ∘ (tangentChart i i.1).symm)
      ((tangentChart i i.1).target ∩ (tangentChart i i.1).symm ⁻¹' A.source) := fun k ↦ by
  have hs := smoothMBMOn_symm_of_mem_atlas (tangentChart_self_mem_atlas i)
  have hΩ : IsOpen ((tangentChart i i.1).target ∩ (tangentChart i i.1).symm ⁻¹' A.source) :=
    (hs 0).continuousOn.isOpen_inter_preimage (tangentChart i i.1).open_target A.isOpen_source
  exact (A.smoothMBMOn_toFun k).comp hΩ A.isOpen_source
    ((SmoothMBMOn.mono_of_isOpen (tangentChart i i.1).open_target hΩ hs inter_subset_left) k)
    fun q hq ↦ hq.2

/-- The domain of `invLocal` is open. -/
theorem isOpen_invLocalDom (i i'' : atlas E N) : IsOpen (A.invLocalDom i i'') := by
  have hs := smoothMBMOn_symm_of_mem_atlas (tangentChart_self_mem_atlas i)
  have hΩ : IsOpen ((tangentChart i i.1).target ∩ (tangentChart i i.1).symm ⁻¹' A.source) :=
    (hs 0).continuousOn.isOpen_inter_preimage (tangentChart i i.1).open_target A.isOpen_source
  exact ((A.smoothMBMOn_toFun_tangentChart_symm i) 0).continuousOn.isOpen_inter_preimage hΩ
    i''.1.open_source

/-- `invLocal` is smooth. -/
theorem smoothMBOn_invLocal (i i'' : atlas E N) :
    SmoothMBOn (A.invLocal i i'') (A.invLocalDom i i'') := fun k ↦ by
  have hs := smoothMBMOn_symm_of_mem_atlas (tangentChart_self_mem_atlas i)
  have hD := A.isOpen_invLocalDom i i''
  have h := ((smoothMBMOn_of_mem_atlas i''.2) k).comp hD i''.1.open_source
    ((SmoothMBMOn.mono_of_isOpen ((hs 0).continuousOn.isOpen_inter_preimage
      (tangentChart i i.1).open_target A.isOpen_source) hD
      (A.smoothMBMOn_toFun_tangentChart_symm i) inter_subset_left) k)
    fun q hq ↦ hq.2
  exact (contMDiffMBOn_iff_contDiffMBOn hD).1 h

/-- **The inverse chart in local coordinates**:
`i''(Σ v) = invLocal (i (π v), v in the chart i)`. -/
theorem invLocal_spec (i i'' : atlas E N) {v : TangentBundle E N} (hv : v.proj ∈ i.1.source)
    (hvA : v ∈ A.source) (hS : A.toFun v ∈ i''.1.source) :
    ((i.1 v.proj, coordAt i v) : E × E) ∈ A.invLocalDom i i'' ∧
      A.invLocal i i'' (i.1 v.proj, coordAt i v) = i''.1 (A.toFun v) := by
  have h := tangentChart_symm_coordAt i hv
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rw [← tangentChart_self_apply]
    exact (tangentChart i i.1).map_source ((mem_tangentChart_self_source i v).2 hv)
  · change (tangentChart i i.1).symm _ ∈ A.source
    rw [h]
    exact hvA
  · change A.toFun ((tangentChart i i.1).symm _) ∈ i''.1.source
    rw [h]
    exact hS
  · rw [invLocal, h]

/-- **The transition maps in local coordinates**: for `v ∈ Ω` over the source of `i` and `q` in
the source of `j` with `(q, Σ v)` in the range of `θ`, `θ⁻¹(q, Σ v)` has fiber coordinate
`transMap i j (i (π v), j q, v in the chart i)` in the chart `j`. -/
theorem transMap_spec (i j : atlas E N) {v : TangentBundle E N} {q : N}
    (hv : v.proj ∈ i.1.source) (hq : q ∈ j.1.source) (hvA : v ∈ A.source)
    (hqv : (q, A.toFun v) ∈ A.toOpenPartialHomeomorph.target) :
    ((i.1 v.proj, j.1 q, coordAt i v) : E × E × E) ∈ A.transDom i j ∧
      A.transMap i j (i.1 v.proj, j.1 q, coordAt i v) =
        coordAt j (A.toOpenPartialHomeomorph.symm (q, A.toFun v)) := by
  have hvec : transVec i (i.1 v.proj, j.1 q, coordAt i v) = v := tangentChart_symm_coordAt i hv
  have hpair : A.transPair i j (i.1 v.proj, j.1 q, coordAt i v) = (q, A.toFun v) := by
    rw [transPair, hvec]
    exact Prod.ext (j.1.left_inv hq) rfl
  refine ⟨⟨⟨⟨i.1.map_source hv, j.1.map_source hq⟩, ?_⟩, ?_⟩, ?_⟩
  · change transVec i _ ∈ A.source
    rw [hvec]
    exact hvA
  · change A.transPair i j _ ∈ A.toOpenPartialHomeomorph.target
    rw [hpair]
    exact hqv
  · change coordAt j (A.toOpenPartialHomeomorph.symm (A.transPair i j _)) = _
    rw [hpair]

end LocalAddition

end LocalFormulas

/-! ### The charts of `C^ℓ(M, N)` -/

section ChartsCk

variable {H : Type u} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [IsTopologicalAddGroup H]
  [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [MBManifold H M]
  {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [MBManifold E N]
  {ℓ : ℕ}

namespace CkMap

/-- The local representative `i ∘ f ∘ j⁻¹ ∈ C^ℓ(D_{j,i}(f), E)` of a `C^ℓ` map. -/
def localRep (f : CkMap H E ℓ M N) (j : atlas H M) (i : atlas E N) :
    ContDiffMBMap E ℓ (chartDomOpens (toC f) j i) :=
  ContDiffMBMap.mk ((chartDomOpens (toC f) j i : Set H).indicator (i.1 ∘ f ∘ j.1.symm))
    (ContDiffMBOn.congr_of_isOpen (chartDomOpens (toC f) j i).isOpen
      (fun _ hx ↦ (indicator_of_mem hx _).symm)
      (f.contMDiffMB.contDiffMBOn_chart isOpen_univ j.2 i.2))
    fun _ hx ↦ indicator_of_notMem hx _

/-- On `D_{j,i}(f)`, `localRep f j i` is `i ∘ f ∘ j⁻¹`. -/
theorem localRep_apply (f : CkMap H E ℓ M N) (j : atlas H M) (i : atlas E N) {x : H}
    (hx : x ∈ chartDomOpens (toC f) j i) : localRep f j i x = i.1 (f (j.1.symm x)) :=
  indicator_of_mem (show x ∈ (chartDomOpens (toC f) j i : Set H) from hx) _

end CkMap

variable (A : LocalAddition E N)

namespace LocalAddition

/-- `θ⁻¹(p, q)` lies over `p`. -/
theorem proj_symm {p q : N} (hpq : (p, q) ∈ A.toOpenPartialHomeomorph.target) :
    (A.toOpenPartialHomeomorph.symm (p, q)).proj = p := by
  have h := A.fst_eq _ (A.toOpenPartialHomeomorph.map_target hpq)
  rw [A.toOpenPartialHomeomorph.right_inv hpq] at h
  exact h.symm

/-- `θ⁻¹(p, q) = ⟨p, θ⁻¹(p, q).vec⟩`. -/
theorem mk_vec_symm {p q : N} (hpq : (p, q) ∈ A.toOpenPartialHomeomorph.target) :
    (⟨p, (A.toOpenPartialHomeomorph.symm (p, q)).vec⟩ : TangentBundle E N) =
      A.toOpenPartialHomeomorph.symm (p, q) :=
  TangentBundle.ext_vec (A.proj_symm hpq).symm rfl

/-- The domain `O'_f = {g : (f, g)(M) ⊆ θ(Ω)}` of the chart of `C^ℓ(M, N)` at `f`. -/
def chartSourceCk (f : CkMap H E ℓ M N) : Set (CkMap H E ℓ M N) :=
  CkMap.toC ⁻¹' A.chartSource (CkMap.toC f)

/-- The range `O_f = Γ_f ∩ C^ℓ(M, Ω)` of the chart of `C^ℓ(M, N)` at `f`. -/
def chartTargetCk [T2Space M] (f : CkMap H E ℓ M N) : Set (SecCk H E ℓ (CkMap.toC f)) :=
  SecCk.toSec ⁻¹' A.chartTarget (CkMap.toC f)

/-- `θ⁻¹ ∘ (f, g)`, for `g ∈ O'_f`, as a `C^ℓ` section along `f`. -/
def chartVec (f g : CkMap H E ℓ M N) (hg : g ∈ A.chartSourceCk f) : SecCk H E ℓ (CkMap.toC f) :=
  SecCk.mk (fun x ↦ (A.toOpenPartialHomeomorph.symm (f x, g x)).vec) fun j i ↦ by
    set D := chartDomOpens (CkMap.toC f) j i
    refine ContDiffMBOn.of_local D.isOpen fun x₀ hx₀ ↦ ?_
    let i' : atlas E N := ⟨chartAt E (g (j.1.symm x₀)), chart_mem_atlas E _⟩
    let W := chartDomOpens (CkMap.toC g) j i'
    have hx₀W : x₀ ∈ W :=
      mem_chartDomOpens.2 ⟨(mem_chartDomOpens.1 hx₀).1, _root_.mem_chart_source E _⟩
    refine ⟨W, W.isOpen, hx₀W, ?_⟩
    have hDW : IsOpen ((D : Set H) ∩ W) := D.isOpen.inter W.isOpen
    have hκ : ContDiffMBOn ℓ (fun x ↦ ((i'.1 (g (j.1.symm x)), i.1 (f (j.1.symm x))) : E × E))
        ((D : Set H) ∩ W) :=
      ContDiffMBOn.prodMk hDW
        ((g.contMDiffMB.contDiffMBOn_chart isOpen_univ j.2 i'.2).mono inter_subset_right)
        ((f.contMDiffMB.contDiffMBOn_chart isOpen_univ j.2 i.2).mono inter_subset_left)
    have hspec : ∀ x ∈ (D : Set H) ∩ W, ((i'.1 (g (j.1.symm x)), i.1 (f (j.1.symm x))) : E × E) ∈
        A.chartLocalDom i' i ∧ A.chartLocal i' i (i'.1 (g (j.1.symm x)), i.1 (f (j.1.symm x))) =
          coordAt i (A.toOpenPartialHomeomorph.symm (f (j.1.symm x), g (j.1.symm x))) :=
      fun x hx ↦ A.chartLocal_spec i' i (mem_chartDomOpens.1 hx.2).2 (mem_chartDomOpens.1 hx.1).2
        (hg (j.1.symm x))
    refine ContDiffMBOn.congr_of_isOpen hDW (fun x hx ↦ ?_)
      (ContDiffMBOn.comp hDW (A.isOpen_chartLocalDom i' i) (A.smoothMBOn_chartLocal i' i ℓ) hκ
        fun x hx ↦ (hspec x hx).1)
    simp only [Function.comp_apply, localCoord, (hspec x hx).2]
    exact congrArg (coordAt i) (A.mk_vec_symm (hg (j.1.symm x))).symm

/-- The fiber coordinates of `chartVec f g hg` describe `θ⁻¹ ∘ (f, g)`. -/
theorem mk_chartVec (f g : CkMap H E ℓ M N) (hg : g ∈ A.chartSourceCk f) (x : M) :
    (⟨f x, A.chartVec f g hg x⟩ : TangentBundle E N) =
      A.toOpenPartialHomeomorph.symm (f x, g x) :=
  A.mk_vec_symm (hg x)

variable [T2Space M]

/-- `Σ ∘ τ`, for `τ ∈ O_f`, as a `C^ℓ` map. -/
def chartInv (f : CkMap H E ℓ M N) (τ : SecCk H E ℓ (CkMap.toC f)) (hτ : τ ∈ A.chartTargetCk f) :
    CkMap H E ℓ M N :=
  ⟨fun x ↦ A.toFun ⟨f x, τ x⟩, by
    have hc : Continuous fun x ↦ A.toFun ⟨f x, τ x⟩ :=
      (A.smoothMBMOn_toFun 0).continuousOn.comp_continuous (SecCk.continuous_section τ) hτ
    refine contMDiffMB_of_chartAt hc fun p ↦ ?_
    let c : atlas H M := ⟨chartAt H p, chart_mem_atlas H p⟩
    let i : atlas E N := ⟨chartAt E (f p), chart_mem_atlas E (f p)⟩
    let i'' : atlas E N := ⟨chartAt E (A.toFun ⟨f p, τ p⟩), chart_mem_atlas E _⟩
    set O := chartDomain (fun x ↦ A.toFun ⟨f x, τ x⟩) univ c.1 i''.1 ∩
      chartDomOpens (CkMap.toC f) c i
    have hO : IsOpen O := (isOpen_chartDomain isOpen_univ hc.continuousOn _ _).inter
      (chartDomOpens (CkMap.toC f) c i).isOpen
    have hpO : chartAt H p p ∈ O := by
      refine ⟨⟨(chartAt H p).map_source (_root_.mem_chart_source H p), mem_univ _, ?_⟩,
        chartAt_mem_chartDomOpens (CkMap.toC f) p⟩
      change A.toFun ⟨f ((chartAt H p).symm _), τ ((chartAt H p).symm _)⟩ ∈ i''.1.source
      rw [(chartAt H p).left_inv (_root_.mem_chart_source H p)]
      exact _root_.mem_chart_source E _
    refine ⟨O, hO, hpO, inter_subset_left, ?_⟩
    have hκ : ContDiffMBOn ℓ (fun x ↦ ((i.1 (f (c.1.symm x)), localCoord (CkMap.toC f) c i τ x) :
        E × E)) O :=
      ContDiffMBOn.prodMk hO
        ((f.contMDiffMB.contDiffMBOn_chart isOpen_univ c.2 i.2).mono inter_subset_right)
        ((τ.contDiffMBOn_localCoord c i).mono inter_subset_right)
    have hspec : ∀ x ∈ O, ((i.1 (f (c.1.symm x)), localCoord (CkMap.toC f) c i τ x) : E × E) ∈
        A.invLocalDom i i'' ∧ A.invLocal i i'' (i.1 (f (c.1.symm x)),
          localCoord (CkMap.toC f) c i τ x) = i''.1 (A.toFun ⟨f (c.1.symm x), τ (c.1.symm x)⟩) :=
      fun x hx ↦ A.invLocal_spec i i'' (v := ⟨f (c.1.symm x), τ (c.1.symm x)⟩)
        (mem_chartDomOpens.1 hx.2).2 (hτ _) hx.1.2.2
    refine ContDiffMBOn.congr_of_isOpen hO (fun x hx ↦ ?_)
      (ContDiffMBOn.comp hO (A.isOpen_invLocalDom i i'') (A.smoothMBOn_invLocal i i'' ℓ) hκ
        fun x hx ↦ (hspec x hx).1)
    exact (hspec x hx).2⟩

/-- `chartInv f τ hτ x = Σ(τ(x))`. -/
theorem chartInv_apply (f : CkMap H E ℓ M N) (τ : SecCk H E ℓ (CkMap.toC f))
    (hτ : τ ∈ A.chartTargetCk f) (x : M) : A.chartInv f τ hτ x = A.toFun ⟨f x, τ x⟩ :=
  rfl

open scoped Classical in
/-- The chart of `C^ℓ(M, N)` at `f`, `g ↦ θ⁻¹ ∘ (f, g)` on `O'_f` (and `0` elsewhere). -/
def chartFunCk (f g : CkMap H E ℓ M N) : SecCk H E ℓ (CkMap.toC f) :=
  if hg : g ∈ A.chartSourceCk f then A.chartVec f g hg else 0

open scoped Classical in
/-- The inverse of the chart of `C^ℓ(M, N)` at `f`, `τ ↦ Σ ∘ τ` on `O_f` (and `f` elsewhere). -/
def chartInvFunCk (f : CkMap H E ℓ M N) (τ : SecCk H E ℓ (CkMap.toC f)) : CkMap H E ℓ M N :=
  if hτ : τ ∈ A.chartTargetCk f then A.chartInv f τ hτ else f

omit [T2Space M] in
/-- On `O'_f`, the fiber coordinates of the chart are those of `θ⁻¹ ∘ (f, g)`. -/
theorem mk_chartFunCk (f g : CkMap H E ℓ M N) (hg : g ∈ A.chartSourceCk f) (x : M) :
    (⟨f x, A.chartFunCk f g x⟩ : TangentBundle E N) =
      A.toOpenPartialHomeomorph.symm (f x, g x) := by
  rw [chartFunCk, dite_eq_left_of_eq_true (eq_true hg)]
  exact A.mk_chartVec f g hg x

/-- On `O_f`, the inverse of the chart is `τ ↦ Σ ∘ τ`. -/
theorem chartInvFunCk_apply (f : CkMap H E ℓ M N) {τ : SecCk H E ℓ (CkMap.toC f)}
    (hτ : τ ∈ A.chartTargetCk f) (x : M) : A.chartInvFunCk f τ x = A.toFun ⟨f x, τ x⟩ := by
  rw [chartInvFunCk, dite_eq_left_of_eq_true (eq_true hτ)]
  rfl

/-- **The charts are continuous** for the compact-open `C^ℓ` topologies. -/
theorem continuousOn_chartFunCk [CompactSpace M] (f : CkMap H E ℓ M N) :
    ContinuousOn (A.chartFunCk f) (A.chartSourceCk f) := by
  rcases isEmpty_or_nonempty M with hM | hM
  · exact (continuous_of_const fun _ _ ↦ Subsingleton.elim _ _).continuousOn
  have := locallyCompactSpace_of_compactSpace (H := H) M
  rw [show (CkMap.instTopologicalSpace : TopologicalSpace (CkMap H E ℓ M N)) =
    CkMap.chartTopology H E ℓ M N from CkMap.topology_eq_chartTopology]
  let _ : TopologicalSpace (CkMap H E ℓ M N) := CkMap.chartTopology H E ℓ M N
  rw [continuousOn_iff_continuous_domRestrict]
  refine SecCk.continuous_iff.2 fun a ↦ continuous_iff_continuousAt.2 fun g₀ ↦ ?_
  set D := chartDomOpens (CkMap.toC f) a.1 a.2
  have key : ∀ x₀ ∈ D, ∃ (V₁ : Opens H) (hV : V₁ ≤ D), x₀ ∈ V₁ ∧
      ContinuousAt (fun g : A.chartSourceCk f ↦ ContDiffMBMap.restrictCLM hV
        (SecCk.coordFun a (A.chartFunCk f g))) g₀ := by
    intro x₀ hx₀
    let i' : atlas E N := ⟨chartAt E (g₀.1 (a.1.1.symm x₀)), chart_mem_atlas E _⟩
    let Q : Opens H := D ⊓ chartDomOpens (CkMap.toC g₀.1) a.1 i'
    have hx₀Q : x₀ ∈ Q := ⟨hx₀, mem_chartDomOpens.2 ⟨(mem_chartDomOpens.1 hx₀).1,
      _root_.mem_chart_source E _⟩⟩
    obtain ⟨L₂, hL₂n, hL₂Q, hL₂c⟩ := local_compact_nhds (Q.isOpen.mem_nhds hx₀Q)
    let V₂ : Opens H := ⟨interior L₂, isOpen_interior⟩
    have hx₀V₂ : x₀ ∈ V₂ := mem_interior_iff_mem_nhds.2 hL₂n
    obtain ⟨L₁, hL₁n, hL₁V₂, hL₁c⟩ := local_compact_nhds (V₂.isOpen.mem_nhds hx₀V₂)
    let V₁ : Opens H := ⟨interior L₁, isOpen_interior⟩
    have hV₁₂ : V₁ ≤ V₂ := fun x hx ↦ hL₁V₂ (interior_subset hx)
    have hV₂D : V₂ ≤ D := fun x hx ↦ (hL₂Q (interior_subset hx)).1
    let b : CkMap.ChartIdx H E M N := ⟨a.1, i', L₂, hL₂c,
      fun x hx ↦ (mem_chartDomOpens.1 (hL₂Q hx).1).1, V₂, interior_subset⟩
    have hb : ∀ g : CkMap H E ℓ M N, g ∈ b.dom ↔ ∀ x ∈ L₂, g (a.1.1.symm x) ∈ i'.1.source :=
      fun g ↦ ⟨fun hg x hx ↦ hg (mem_image_of_mem _ hx), fun hg ↦ by
        rintro _ ⟨x, hx, rfl⟩; exact hg x hx⟩
    have hg₀b : g₀.1 ∈ b.dom := (hb _).2 fun x hx ↦ (mem_chartDomOpens.1 (hL₂Q hx).2).2
    let c_f : ContDiffMBMap E ℓ V₂ := ContDiffMBMap.restrictCLM hV₂D (CkMap.localRep f a.1 a.2)
    have hc_f : ∀ x ∈ V₂, c_f x = a.2.1 (f (a.1.1.symm x)) := fun x hx ↦ by
      simp only [c_f, ContDiffMBMap.restrictCLM_apply _ _ hx, CkMap.localRep_apply _ _ _ (hV₂D hx)]
    let L : ContDiffMBMap E ℓ V₂ →L[ℝ] ContDiffMBMap (E × E) ℓ V₁ :=
      (ContDiffMBMap.restrictCLM hV₁₂).comp
        (ContDiffMBMap.prodMkCLM.comp (ContinuousLinearMap.inl ℝ _ _))
    let c₀ : ContDiffMBMap (E × E) ℓ V₁ :=
      ContDiffMBMap.restrictCLM hV₁₂ (ContDiffMBMap.prodMkCLM (0, c_f))
    have hΛ : ∀ γ : ContDiffMBMap E ℓ V₂, ∀ x ∈ V₁, (c₀ + L γ) x = (γ x, c_f x) := fun γ x hx ↦ by
      have h1 := ContDiffMBMap.restrictCLM_apply hV₁₂
        (ContDiffMBMap.prodMkCLM ((0 : ContDiffMBMap E ℓ V₂), c_f)) hx
      have h2 := ContDiffMBMap.restrictCLM_apply hV₁₂
        (ContDiffMBMap.prodMkCLM (γ, (0 : ContDiffMBMap E ℓ V₂))) hx
      simp only [c₀, L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
        ContDiffMBMap.coe_add, Pi.add_apply, h1, h2]
      change ((0 : ContDiffMBMap E ℓ V₂) x, c_f x) + (γ x, (0 : ContDiffMBMap E ℓ V₂) x) = _
      simp
    let W : Set (ContDiffMBMap E ℓ V₂) :=
      {γ | ∀ x ∈ L₁, ((γ x, c_f x) : E × E) ∈ A.chartLocalDom i' a.2}
    have hW : IsOpen W := by
      have : CompactSpace L₁ := isCompact_iff_compactSpace.mp hL₁c
      let σ : L₁ → V₂ × (Fin 0 → H) := fun y ↦ (⟨y, hL₁V₂ y.2⟩, Fin.elim0)
      have hσ : Continuous σ := by fun_prop
      have h := (ContinuousMap.isOpen_setOfPred_mapsTo (isCompact_range hσ)
        (A.isOpen_chartLocalDom i' a.2)).preimage
        ((ContDiffMBMap.continuous_iteratedD 0 (Nat.zero_le ℓ)).comp
          (ContDiffMBMap.prodMkCLM.continuous.comp
            (continuous_id.prodMk (continuous_const (y := c_f)))))
      convert h using 1
      ext γ
      constructor
      · rintro hγ _ ⟨y, rfl⟩
        exact hγ y y.2
      · intro hγ x hx
        exact hγ ⟨⟨x, hx⟩, rfl⟩
    have hmaps : ∀ γ ∈ W, MapsTo (c₀ + L γ) V₁ (A.chartLocalDom i' a.2) := fun γ hγ x hx ↦ by
      rw [hΛ γ x hx]
      exact hγ x (interior_subset hx)
    have hΦ := (ContDiffMBMap.contDiffMBOn_compLeftOn ℓ (A.isOpen_chartLocalDom i' a.2)
      (A.smoothMBOn_chartLocal i' a.2) (k := 0) hW
      ((contDiffMBOn_const_add_clm c₀ L 0 W)) hmaps).continuousOn
    have hspec : ∀ g : A.chartSourceCk f, g.1 ∈ b.dom → ∀ x ∈ L₂,
        ((i'.1 (g.1 (a.1.1.symm x)), a.2.1 (f (a.1.1.symm x))) : E × E) ∈
          A.chartLocalDom i' a.2 ∧
        A.chartLocal i' a.2 (i'.1 (g.1 (a.1.1.symm x)), a.2.1 (f (a.1.1.symm x))) =
          coordAt a.2 (A.toOpenPartialHomeomorph.symm (f (a.1.1.symm x), g.1 (a.1.1.symm x))) :=
      fun g hg x hx ↦ A.chartLocal_spec i' a.2 ((hb _).1 hg x hx)
        (mem_chartDomOpens.1 (hL₂Q hx).1).2 (g.2 _)
    have hrepW : ∀ g : A.chartSourceCk f, g.1 ∈ b.dom → b.rep g.1 ∈ W := fun g hg x hx ↦ by
      have hx₂ : x ∈ V₂ := hL₁V₂ hx
      rw [b.rep_apply hg hx₂, hc_f x hx₂]
      exact (hspec g hg x (interior_subset hx₂)).1
    have hrep : ContinuousAt (fun g : A.chartSourceCk f ↦ b.rep g.1) g₀ :=
      (b.continuousOn_rep.continuousAt (b.isOpen_dom_chartTopology.mem_nhds hg₀b)).comp
        continuous_subtype_val.continuousAt
    have hG : ContinuousAt (fun g : A.chartSourceCk f ↦ ContDiffMBMap.compLeftOn
        (A.chartLocal i' a.2) (A.chartLocalDom i' a.2) (c₀ + L (b.rep g.1))) g₀ :=
      ContinuousAt.comp (f := fun g : A.chartSourceCk f ↦ b.rep g.1)
        (hΦ.continuousAt (hW.mem_nhds (hrepW g₀ hg₀b))) hrep
    refine ⟨V₁, fun x hx ↦ hV₂D (hV₁₂ hx), mem_interior_iff_mem_nhds.2 hL₁n, hG.congr ?_⟩
    filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
      (b.isOpen_dom_chartTopology.mem_nhds hg₀b)] with g hg
    ext x
    by_cases hx : x ∈ V₁
    · have hx₂ : x ∈ V₂ := hV₁₂ hx
      have hxD : x ∈ D := hV₂D hx₂
      rw [ContDiffMBMap.restrictCLM_apply _ _ hx, SecCk.coordFun_apply _ _ hxD,
        ContDiffMBMap.compLeftOn_apply (A.isOpen_chartLocalDom i' a.2)
          (A.smoothMBOn_chartLocal i' a.2 ℓ) (hmaps _ (hrepW g hg)) hx, hΛ _ x hx,
        b.rep_apply hg hx₂, hc_f x hx₂, (hspec g hg x (interior_subset hx₂)).2]
      change _ = coordAt a.2 (⟨f (a.1.1.symm x), A.chartFunCk f g.1 (a.1.1.symm x)⟩ :
        TangentBundle E N)
      rw [A.mk_chartFunCk f g.1 g.2]
    · rw [ContDiffMBMap.apply_of_notMem _ hx, ContDiffMBMap.apply_of_notMem _ hx]
  choose V₁ hV hxV hc using key
  exact ContDiffMBMap.tendsto_of_tendsto_restrictCLM (fun x : D ↦ V₁ x x.2) (fun x ↦ hV x x.2)
    (fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx⟩, hxV x hx⟩) fun x ↦ hc x x.2

variable [CompactSpace M]

omit [CompactSpace M] in
/-- Off `O_f`, the inverse of the chart is constant. -/
theorem chartInvFunCk_of_notMem (f : CkMap H E ℓ M N) {τ : SecCk H E ℓ (CkMap.toC f)}
    (hτ : τ ∉ A.chartTargetCk f) : A.chartInvFunCk f τ = f := by
  rw [chartInvFunCk, dite_eq_right_of_eq_false (eq_false hτ)]

omit [MBManifold H M] in
/-- `O_f` is open in `Γ_f`. -/
theorem isOpen_chartTargetCk (f : CkMap H E ℓ M N) : IsOpen (A.chartTargetCk f) :=
  (A.isOpen_chartTarget (CkMap.toC f)).preimage SecCk.toSec.continuous

omit [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  [MBManifold H M] in
/-- `O'_f` is open in `C^ℓ(M, N)`. -/
theorem isOpen_chartSourceCk (f : CkMap H E ℓ M N) :
    IsOpen (A.chartSourceCk f) :=
  (A.isOpen_chartSource (CkMap.toC f)).preimage CkMap.continuous_toC

/-- As a continuous map, `Σ ∘ τ` is the inverse of the chart of `C(M, N)` at `f`. -/
theorem toC_chartInvFunCk (f : CkMap H E ℓ M N) {τ : SecCk H E ℓ (CkMap.toC f)}
    (hτ : τ ∈ A.chartTargetCk f) :
    CkMap.toC (A.chartInvFunCk f τ) = (A.chart (CkMap.toC f)).symm (SecCk.toSec τ) :=
  ContinuousMap.ext fun x ↦ by
    rw [CkMap.coe_toC, A.chartInvFunCk_apply f hτ x, A.chart_symm_apply (CkMap.toC f) hτ x]
    rfl

/-- **The inverses of the charts are continuous** for the compact-open `C^ℓ` topologies. -/
theorem continuousOn_chartInvFunCk (f : CkMap H E ℓ M N) :
    ContinuousOn (A.chartInvFunCk f) (A.chartTargetCk f) := by
  rcases isEmpty_or_nonempty M with hM | hM
  · exact (continuous_of_const fun _ _ ↦ Subsingleton.elim _ _).continuousOn
  have := locallyCompactSpace_of_compactSpace (H := H) M
  rw [show (CkMap.instTopologicalSpace : TopologicalSpace (CkMap H E ℓ M N)) =
    CkMap.chartTopology H E ℓ M N from CkMap.topology_eq_chartTopology]
  let _ : TopologicalSpace (CkMap H E ℓ M N) := CkMap.chartTopology H E ℓ M N
  have h₀ : ContinuousOn (fun τ ↦ CkMap.toC (A.chartInvFunCk f τ)) (A.chartTargetCk f) :=
    ((A.chart (CkMap.toC f)).continuousOn_symm.comp SecCk.toSec.continuous.continuousOn
      fun τ hτ ↦ hτ).congr fun τ hτ ↦ A.toC_chartInvFunCk f hτ
  refine CkMap.continuousOn_of_rep h₀ fun a ↦ ?_
  have hW : IsOpen (A.chartTargetCk f ∩ A.chartInvFunCk f ⁻¹' a.dom) :=
    h₀.isOpen_inter_preimage (A.isOpen_chartTargetCk f) a.isOpen_domC
  let V : atlas E N → Opens H := fun i ↦ a.V ⊓ chartDomOpens (CkMap.toC f) a.j i
  have hVU : ∀ i, V i ≤ a.V := fun _ ↦ inf_le_left
  have hcov : (a.V : Set H) ⊆ ⋃ i, (V i : Set H) := fun x hx ↦
    mem_iUnion.2 ⟨⟨chartAt E (f (a.j.1.symm x)), chart_mem_atlas E _⟩, hx,
      mem_chartDomOpens.2 ⟨a.L_subset (a.V_subset hx), _root_.mem_chart_source E _⟩⟩
  refine ((ContDiffMBMap.isEmbedding_restrictCover V hVU hcov).continuousOn_iff).2
    (continuousOn_pi.2 fun i ↦ ?_)
  have hVD : V i ≤ chartDomOpens (CkMap.toC f) a.j i := inf_le_right
  let c_f : ContDiffMBMap E ℓ (V i) := ContDiffMBMap.restrictCLM hVD (CkMap.localRep f a.j i)
  let L : SecCk H E ℓ (CkMap.toC f) →L[ℝ] ContDiffMBMap (E × E) ℓ (V i) :=
    ContDiffMBMap.prodMkCLM.comp ((ContinuousLinearMap.inr ℝ _ _).comp
      ((ContDiffMBMap.restrictCLM hVD).comp (SecCk.coordCLM (a.j, i))))
  let c₀ : ContDiffMBMap (E × E) ℓ (V i) := ContDiffMBMap.prodMkCLM (c_f, 0)
  have hΛ : ∀ τ, ∀ x ∈ V i, (c₀ + L τ) x =
      (i.1 (f (a.j.1.symm x)), localCoord (CkMap.toC f) a.j i τ x) := fun τ x hx ↦ by
    have h1 : c_f x = i.1 (f (a.j.1.symm x)) := by
      simp only [c_f, ContDiffMBMap.restrictCLM_apply _ _ hx, CkMap.localRep_apply _ _ _ (hVD hx)]
    have h2 := ContDiffMBMap.restrictCLM_apply hVD (SecCk.coordFun (a.j, i) τ) hx
    simp only [c₀, L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      ContDiffMBMap.coe_add, Pi.add_apply]
    change (c_f x, (0 : ContDiffMBMap E ℓ (V i)) x) +
      ((0 : ContDiffMBMap E ℓ (V i)) x, ContDiffMBMap.restrictCLM hVD (SecCk.coordFun (a.j, i) τ) x)
        = _
    rw [h1, h2, SecCk.coordFun_apply _ _ (hVD hx)]
    simp
  have hspec : ∀ τ ∈ A.chartTargetCk f ∩ A.chartInvFunCk f ⁻¹' a.dom, ∀ x ∈ V i,
      ((i.1 (f (a.j.1.symm x)), localCoord (CkMap.toC f) a.j i τ x) : E × E) ∈
        A.invLocalDom i a.i ∧
      A.invLocal i a.i (i.1 (f (a.j.1.symm x)), localCoord (CkMap.toC f) a.j i τ x) =
        a.i.1 (A.toFun ⟨f (a.j.1.symm x), τ (a.j.1.symm x)⟩) := fun τ hτ x hx ↦ by
    have hS := hτ.2 (mem_image_of_mem _ (a.V_subset hx.1))
    rw [CkMap.coe_toC, A.chartInvFunCk_apply f hτ.1] at hS
    exact A.invLocal_spec i a.i (v := ⟨f (a.j.1.symm x), τ (a.j.1.symm x)⟩)
      (mem_chartDomOpens.1 hx.2).2 (hτ.1 _) hS
  have hmaps : ∀ τ ∈ A.chartTargetCk f ∩ A.chartInvFunCk f ⁻¹' a.dom,
      MapsTo (c₀ + L τ) (V i) (A.invLocalDom i a.i) := fun τ hτ x hx ↦ by
    rw [hΛ τ x hx]
    exact (hspec τ hτ x hx).1
  have hΦ := (ContDiffMBMap.contDiffMBOn_compLeftOn ℓ (A.isOpen_invLocalDom i a.i)
    (A.smoothMBOn_invLocal i a.i) (k := 0) hW (contDiffMBOn_const_add_clm c₀ L 0 _)
    hmaps).continuousOn
  refine hΦ.congr fun τ hτ ↦ ?_
  ext x
  change ContDiffMBMap.restrictCLM (hVU i) (a.rep (A.chartInvFunCk f τ)) x = _
  by_cases hx : x ∈ V i
  · rw [ContDiffMBMap.restrictCLM_apply _ _ hx, a.rep_apply hτ.2 hx.1,
      ContDiffMBMap.compLeftOn_apply (A.isOpen_invLocalDom i a.i) (A.smoothMBOn_invLocal i a.i ℓ)
        (hmaps τ hτ) hx, hΛ τ x hx, (hspec τ hτ x hx).2, A.chartInvFunCk_apply f hτ.1]
  · rw [ContDiffMBMap.apply_of_notMem _ hx, ContDiffMBMap.apply_of_notMem _ hx]

omit [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  [MBManifold H M] in
/-- `C^ℓ(M, N)` has a chart at `f` whose domain contains `f`. -/
theorem mem_chartSourceCk (f : CkMap H E ℓ M N) : f ∈ A.chartSourceCk f :=
  A.mem_chart_source (CkMap.toC f)


/-- **The chart of `C^ℓ(M, N)` at `f`** (Glöckner–Neeb, proof of Theorem 4.2.2):
`φ_f : O'_f → O_f ⊆ Γ_f`, `g ↦ θ⁻¹ ∘ (f, g)`, with inverse `τ ↦ Σ ∘ τ`, a partial homeomorphism
for the compact-open `C^ℓ` topologies. It is modeled on `Γ_f`. -/
def chartCk (f : CkMap H E ℓ M N) :
    OpenPartialHomeomorph (CkMap H E ℓ M N) (SecCk H E ℓ (CkMap.toC f)) where
  toFun := A.chartFunCk f
  invFun := A.chartInvFunCk f
  source := A.chartSourceCk f
  target := A.chartTargetCk f
  map_source' g hg x := by
    change (⟨f x, A.chartFunCk f g x⟩ : TangentBundle E N) ∈ A.toOpenPartialHomeomorph.source
    rw [A.mk_chartFunCk f g hg x]
    exact A.toOpenPartialHomeomorph.map_target (hg x)
  map_target' τ hτ x := by
    change (f x, A.chartInvFunCk f τ x) ∈ A.toOpenPartialHomeomorph.target
    rw [A.chartInvFunCk_apply f hτ x]
    have h := A.toOpenPartialHomeomorph.map_source (hτ x)
    rwa [A.toOpenPartialHomeomorph_apply (hτ x)] at h
  left_inv' g hg := by
    have hτ : A.chartFunCk f g ∈ A.chartTargetCk f := fun x ↦ by
      change (⟨f x, A.chartFunCk f g x⟩ : TangentBundle E N) ∈ A.toOpenPartialHomeomorph.source
      rw [A.mk_chartFunCk f g hg x]
      exact A.toOpenPartialHomeomorph.map_target (hg x)
    ext x
    rw [A.chartInvFunCk_apply f hτ x, A.mk_chartFunCk f g hg x]
    change (A.toOpenPartialHomeomorph (A.toOpenPartialHomeomorph.symm (f x, g x))).2 = g x
    rw [show ((f x, g x) : N × N) = (CkMap.toC f x, CkMap.toC g x) from rfl,
      A.toOpenPartialHomeomorph.right_inv (hg x)]
    rfl
  right_inv' τ hτ := by
    have hg : A.chartInvFunCk f τ ∈ A.chartSourceCk f := fun x ↦ by
      change (f x, A.chartInvFunCk f τ x) ∈ A.toOpenPartialHomeomorph.target
      rw [A.chartInvFunCk_apply f hτ x]
      have h := A.toOpenPartialHomeomorph.map_source (hτ x)
      rwa [A.toOpenPartialHomeomorph_apply (hτ x)] at h
    ext x
    have h := A.mk_chartFunCk f _ hg x
    rw [A.chartInvFunCk_apply f hτ x] at h
    have e : ((f x, A.toFun ⟨f x, τ x⟩) : N × N) = A.toOpenPartialHomeomorph ⟨f x, τ x⟩ :=
      (A.toOpenPartialHomeomorph_apply (hτ x)).symm
    have hl : A.toOpenPartialHomeomorph.symm (A.toOpenPartialHomeomorph ⟨f x, τ x⟩) =
        (⟨f x, τ x⟩ : TangentBundle E N) := A.toOpenPartialHomeomorph.left_inv (hτ x)
    rw [e, hl] at h
    exact congrArg TangentBundle.vec h
  open_source := A.isOpen_chartSourceCk f
  open_target := A.isOpen_chartTargetCk f
  continuousOn_toFun := A.continuousOn_chartFunCk f
  continuousOn_invFun := A.continuousOn_chartInvFunCk f

/-- The chart at `f` contains `f` in its domain. -/
theorem mem_chartCk_source (f : CkMap H E ℓ M N) : f ∈ (A.chartCk f).source :=
  A.mem_chartSourceCk f

/-- In the chart at `f`, `g` has fiber coordinates `x ↦ θ⁻¹(f x, g x)`. -/
theorem mk_chartCk (f g : CkMap H E ℓ M N) (hg : g ∈ (A.chartCk f).source) (x : M) :
    (⟨f x, A.chartCk f g x⟩ : TangentBundle E N) = A.toOpenPartialHomeomorph.symm (f x, g x) :=
  A.mk_chartFunCk f g hg x

/-- The inverse of the chart at `f` is `τ ↦ Σ ∘ τ`. -/
theorem chartCk_symm_apply (f : CkMap H E ℓ M N) {τ : SecCk H E ℓ (CkMap.toC f)}
    (hτ : τ ∈ (A.chartCk f).target) (x : M) : (A.chartCk f).symm τ x = A.toFun ⟨f x, τ x⟩ :=
  A.chartInvFunCk_apply f hτ x

end LocalAddition

end ChartsCk

/-! ### Smoothness of the transition maps -/

section TransitionCk

variable {H : Type u} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [IsTopologicalAddGroup H]
  [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [MBManifold H M] [CompactSpace M]
  [T2Space M]
  {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [MBManifold E N]
  {ℓ : ℕ} (A : LocalAddition E N)

namespace LocalAddition

/-- The domain of the transition map from the chart at `f` to the chart at `g`. -/
def transitionDomainCk (f g : CkMap H E ℓ M N) : Set (SecCk H E ℓ (CkMap.toC f)) :=
  (A.chartCk f).target ∩ (A.chartCk f).symm ⁻¹' (A.chartCk g).source

/-- The domain of the transition map is open. -/
theorem isOpen_transitionDomainCk (f g : CkMap H E ℓ M N) :
    IsOpen (A.transitionDomainCk f g) :=
  (A.chartCk f).isOpen_inter_preimage_symm (A.chartCk g).open_source

/-- **The transition maps of `C^ℓ(M, N)` are smooth** (Glöckner–Neeb, proof of Theorem 4.2.2):
`φ_g ∘ φ_f⁻¹` is smooth on its open domain in `Γ_f`. Over the open sets on which `f` and `g` lie
in charts `i` and `j` of `N`, the local representatives of the transition map are the
superposition operators `γ ↦ h ∘ γ` of the smooth map
`h(y, z, v) = θ⁻¹(j⁻¹ z, Σ(i⁻¹ y, v))` (in the fiber coordinates of `j`), applied to
`x ↦ (i(f x), j(g x), τ(x))`, which depends affinely on `τ`; such operators are smooth on spaces
of `C^ℓ` maps (`ContDiffMBMap.contDiffMBOn_compLeftOn`). -/
theorem smoothMBOn_transitionCk (f g : CkMap H E ℓ M N) :
    SmoothMBOn (A.chartCk g ∘ (A.chartCk f).symm) (A.transitionDomainCk f g) := by
  intro k
  have hW := A.isOpen_transitionDomainCk f g
  rcases isEmpty_or_nonempty M with hM | hM
  · exact (contDiffMBOn_const k 0 _).congr_of_isOpen hW fun _ _ ↦ Subsingleton.elim _ _
  have := locallyCompactSpace_of_compactSpace (H := H) M
  refine SecCk.contDiffMBOn_of_coordFun hW fun a ↦ ?_
  set D := chartDomOpens (CkMap.toC g) a.1 a.2
  let V : atlas E N → Opens H := fun i ↦ D ⊓ chartDomOpens (CkMap.toC f) a.1 i
  have hVU : ∀ i, V i ≤ D := fun _ ↦ inf_le_left
  have hcov : (D : Set H) ⊆ ⋃ i, (V i : Set H) := fun x hx ↦
    mem_iUnion.2 ⟨⟨chartAt E (f (a.1.1.symm x)), chart_mem_atlas E _⟩, hx,
      mem_chartDomOpens.2 ⟨(mem_chartDomOpens.1 hx).1, _root_.mem_chart_source E _⟩⟩
  refine ContDiffMBMap.contDiffMBOn_of_restrictCLM V hVU hcov hW fun i ↦ ?_
  have hVf : V i ≤ chartDomOpens (CkMap.toC f) a.1 i := inf_le_right
  let c_f : ContDiffMBMap E ℓ (V i) := ContDiffMBMap.restrictCLM hVf (CkMap.localRep f a.1 i)
  let c_g : ContDiffMBMap E ℓ (V i) := ContDiffMBMap.restrictCLM (hVU i) (CkMap.localRep g a.1 a.2)
  let L : SecCk H E ℓ (CkMap.toC f) →L[ℝ] ContDiffMBMap (E × E × E) ℓ (V i) :=
    ContDiffMBMap.prodMkCLM.comp ((ContinuousLinearMap.inr ℝ _ _).comp
      (ContDiffMBMap.prodMkCLM.comp ((ContinuousLinearMap.inr ℝ _ _).comp
        ((ContDiffMBMap.restrictCLM hVf).comp (SecCk.coordCLM (a.1, i))))))
  let c₀ : ContDiffMBMap (E × E × E) ℓ (V i) :=
    ContDiffMBMap.prodMkCLM (c_f, ContDiffMBMap.prodMkCLM (c_g, 0))
  have hΛ : ∀ τ, ∀ x ∈ V i, (c₀ + L τ) x = (i.1 (f (a.1.1.symm x)), a.2.1 (g (a.1.1.symm x)),
      localCoord (CkMap.toC f) a.1 i τ x) := fun τ x hx ↦ by
    have h1 : c_f x = i.1 (f (a.1.1.symm x)) := by
      simp only [c_f, ContDiffMBMap.restrictCLM_apply _ _ hx, CkMap.localRep_apply _ _ _ (hVf hx)]
    have h2 : c_g x = a.2.1 (g (a.1.1.symm x)) := by
      simp only [c_g, ContDiffMBMap.restrictCLM_apply _ _ hx,
        CkMap.localRep_apply _ _ _ (hVU i hx)]
    have h3 := ContDiffMBMap.restrictCLM_apply hVf (SecCk.coordFun (a.1, i) τ) hx
    simp only [c₀, L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      ContDiffMBMap.coe_add, Pi.add_apply]
    change (c_f x, c_g x, (0 : ContDiffMBMap E ℓ (V i)) x) + ((0 : ContDiffMBMap E ℓ (V i)) x,
      (0 : ContDiffMBMap E ℓ (V i)) x,
        ContDiffMBMap.restrictCLM hVf (SecCk.coordFun (a.1, i) τ) x) = _
    rw [h1, h2, h3, SecCk.coordFun_apply _ _ (hVf hx)]
    simp
  have hspec : ∀ τ ∈ A.transitionDomainCk f g, ∀ x ∈ V i,
      ((i.1 (f (a.1.1.symm x)), a.2.1 (g (a.1.1.symm x)), localCoord (CkMap.toC f) a.1 i τ x) :
        E × E × E) ∈ A.transDom i a.2 ∧
      A.transMap i a.2 (i.1 (f (a.1.1.symm x)), a.2.1 (g (a.1.1.symm x)),
        localCoord (CkMap.toC f) a.1 i τ x) =
        coordAt a.2 (A.toOpenPartialHomeomorph.symm (g (a.1.1.symm x),
          A.toFun ⟨f (a.1.1.symm x), τ (a.1.1.symm x)⟩)) := fun τ hτ x hx ↦ by
    have hq := hτ.2 (a.1.1.symm x)
    change (g (a.1.1.symm x), (A.chartCk f).symm τ (a.1.1.symm x)) ∈ _ at hq
    rw [A.chartCk_symm_apply f hτ.1] at hq
    exact A.transMap_spec i a.2 (v := ⟨f (a.1.1.symm x), τ (a.1.1.symm x)⟩)
      (mem_chartDomOpens.1 hx.2).2 (mem_chartDomOpens.1 hx.1).2 (hτ.1 _) hq
  have hmaps : ∀ τ ∈ A.transitionDomainCk f g, MapsTo (c₀ + L τ) (V i) (A.transDom i a.2) :=
    fun τ hτ x hx ↦ by
      rw [hΛ τ x hx]
      exact (hspec τ hτ x hx).1
  have hc := ContDiffMBMap.contDiffMBOn_compLeftOn ℓ (A.isOpen_transDom i a.2)
    (A.smoothMBOn_transMap i a.2) hW (contDiffMBOn_const_add_clm c₀ L k _) hmaps
  refine ContDiffMBOn.congr_of_isOpen hW (fun τ hτ ↦ ?_) hc
  ext x
  by_cases hx : x ∈ V i
  · rw [ContDiffMBMap.compLeftOn_apply (A.isOpen_transDom i a.2) (A.smoothMBOn_transMap i a.2 ℓ)
      (hmaps τ hτ) hx, hΛ τ x hx, (hspec τ hτ x hx).2, ContDiffMBMap.restrictCLM_apply _ _ hx,
      SecCk.coordFun_apply _ _ (hVU i hx)]
    change _ = coordAt a.2 (⟨g (a.1.1.symm x),
      A.chartCk g ((A.chartCk f).symm τ) (a.1.1.symm x)⟩ : TangentBundle E N)
    rw [A.mk_chartCk g _ hτ.2, A.chartCk_symm_apply f hτ.1]
  · rw [ContDiffMBMap.apply_of_notMem _ hx, ContDiffMBMap.apply_of_notMem _ hx]

/-- **The manifold of `C^ℓ` maps** `C^ℓ(M, N)`, `ℓ ∈ ℕ` (Glöckner–Neeb, Theorem 4.2.2(a) and (b),
for finite `ℓ`): for `M` a compact manifold and `N` admitting
a local addition, the charts `φ_f : O'_f → O_f ⊆ Γ_f`, `g ↦ θ⁻¹ ∘ (f, g)`, form an atlas of
`C^ℓ(M, N)` with varying models `Γ_f` and smooth transition maps. The charts are partial
homeomorphisms for the compact-open `C^ℓ` topology of `C^ℓ(M, N)`, so this topology underlies the
manifold structure (Theorem 4.2.2(b)). -/
def mappingAtlasCk : VaryingAtlas (CkMap H E ℓ M N) where
  ι := CkMap H E ℓ M N
  model f := SecCk H E ℓ (CkMap.toC f)
  chart := A.chartCk
  chartAt g := g
  mem_chartAt_source g := A.mem_chartCk_source g
  smoothMBOn_transition f g := A.smoothMBOn_transitionCk f g

/-- **Point evaluations are smooth** (Glöckner–Neeb, Theorem 4.2.2(c), for finite `ℓ`): in the
chart at `f`, the evaluation `ε_x : g ↦ g(x)` reads `τ ↦ Σ(τ(x))`, which is smooth on `O_f`. -/
theorem smoothMBMOn_eval_chartCk_symm (f : CkMap H E ℓ M N) (x : M) :
    SmoothMBMOn (SecCk H E ℓ (CkMap.toC f)) E (fun τ ↦ (A.chartCk f).symm τ x)
      (A.chartCk f).target := by
  intro k
  have hT := (A.chartCk f).open_target
  have h1 : ContMDiffMBOn (E := SecCk H E ℓ (CkMap.toC f)) (F := Sec E (CkMap.toC f)) k
      SecCk.toSec (A.chartCk f).target :=
    (contMDiffMBOn_iff_contDiffMBOn hT).2 (SecCk.toSec.contDiffMBOn k _)
  have h := ((A.smoothMBMOn_eval_chart_symm (CkMap.toC f) x) k).comp hT
    (A.chart (CkMap.toC f)).open_target h1 fun τ hτ ↦ hτ
  refine h.congr_of_isOpen hT fun τ hτ ↦ ?_
  change (A.chart (CkMap.toC f)).symm (SecCk.toSec τ) x = _
  rw [A.chartCk_symm_apply f hτ x, A.chart_symm_apply (CkMap.toC f) hτ x]
  rfl

end LocalAddition

end TransitionCk

/-! ### The case `ℓ = ∞` -/

section SmoothMaps

variable (H : Type u) [AddCommGroup H] [Module ℝ H] [TopologicalSpace H]
  (E : Type u) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
  (N : Type*) [TopologicalSpace N] [ChartedSpace E N]

/-- **The smooth maps** `M → N`. -/
def SmoothMap : Type _ := {f : M → N // SmoothMBM H E f}

namespace SmoothMap

variable {H E M N}

/-- A smooth map is a map. -/
instance : FunLike (SmoothMap H E M N) M N where
  coe f := f.1
  coe_injective := Subtype.val_injective

/-- Smooth maps are equal if they agree as maps. -/
@[ext]
theorem ext {f g : SmoothMap H E M N} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

/-- A smooth map as a `C^ℓ` map. -/
def toCk (ℓ : ℕ) (f : SmoothMap H E M N) : CkMap H E ℓ M N :=
  ⟨f.1, f.2 ℓ⟩

/-- `toCk ℓ f` is `f`. -/
@[simp]
theorem coe_toCk (ℓ : ℕ) (f : SmoothMap H E M N) : ⇑(toCk ℓ f) = f :=
  rfl

/-- A smooth map as a continuous map. -/
def toC (f : SmoothMap H E M N) : C(M, N) :=
  CkMap.toC (toCk 0 f)

/-- The continuous map underlying `toCk ℓ f` is that of `f`. -/
@[simp]
theorem toC_toCk (ℓ : ℕ) (f : SmoothMap H E M N) : CkMap.toC (toCk ℓ f) = toC f :=
  rfl

variable [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold H M] [MBManifold E N]

/-- On an empty manifold there is only one smooth map. -/
instance instSubsingleton [IsEmpty M] : Subsingleton (SmoothMap H E M N) :=
  ⟨fun _ _ ↦ SmoothMap.ext fun x ↦ isEmptyElim x⟩

variable (H E M N) in
/-- **The compact-open `C^∞` topology through jets**: the initial topology on `C^∞(M, N)` with
respect to the inclusions into the spaces `C^ℓ(M, N)`, `ℓ ∈ ℕ`, with their jet topologies
(compare Glöckner–Neeb, Remark 4.1.3(b)). This is the instance `SmoothMap.instTopologicalSpace`. -/
@[instance_reducible]
def jetTopologySm : TopologicalSpace (SmoothMap H E M N) :=
  ⨅ ℓ : ℕ, TopologicalSpace.induced (toCk ℓ) (CkMap.jetTopology H E ℓ M N)

variable (H E M N) in
/-- **The chart topology of `C^∞(M, N)`**: the initial topology with respect to the inclusions
into the spaces `C^ℓ(M, N)` with their chart topologies `CkMap.chartTopology`. It is the topology
of `C^∞(M, N)` for a locally compact model of `M` (`SmoothMap.chartTopologySm_eq_jetTopologySm`).
It is not the instance. -/
@[instance_reducible]
def chartTopologySm : TopologicalSpace (SmoothMap H E M N) :=
  ⨅ ℓ : ℕ, TopologicalSpace.induced (toCk ℓ) (CkMap.chartTopology H E ℓ M N)

/-- **The compact-open `C^∞` topology** on `C^∞(M, N)`: the initial topology with respect to the
inclusions into the spaces `C^ℓ(M, N)`, `ℓ ∈ ℕ`, each with its compact-open `C^ℓ` topology, the jet
topology (compare Glöckner–Neeb, Remark 4.1.3(b)). -/
instance instTopologicalSpace : TopologicalSpace (SmoothMap H E M N) :=
  jetTopologySm H E M N

omit [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold H M] [MBManifold E N] in
/-- The topology of `C^∞(M, N)` is the jet topology (by definition). -/
theorem topology_eq_jetTopologySm :
    (inferInstance : TopologicalSpace (SmoothMap H E M N)) = jetTopologySm H E M N :=
  rfl

/-- **For a locally compact model, the chart topology of `C^∞(M, N)` is its jet topology.** -/
theorem chartTopologySm_eq_jetTopologySm [LocallyCompactSpace H] :
    chartTopologySm H E M N = jetTopologySm H E M N :=
  iInf_congr fun ℓ ↦ congrArg (TopologicalSpace.induced (toCk ℓ))
    (CkMap.chartTopology_eq_jetTopology (ℓ := ℓ))

/-- **For `M` compact, the topology of `C^∞(M, N)` is the chart topology.** -/
theorem topology_eq_chartTopologySm_of_compactSpace [CompactSpace M] [T2Space M] :
    (inferInstance : TopologicalSpace (SmoothMap H E M N)) = chartTopologySm H E M N :=
  iInf_congr fun ℓ ↦ congrArg (TopologicalSpace.induced (toCk ℓ))
    (CkMap.topology_eq_chartTopology_of_compactSpace (ℓ := ℓ))

omit [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold H M] [MBManifold E N] in
/-- The inclusions `C^∞(M, N) → C^ℓ(M, N)` are continuous. -/
theorem continuous_toCk (ℓ : ℕ) : Continuous (toCk ℓ : SmoothMap H E M N → _) :=
  continuous_iInf_dom continuous_induced_dom

omit [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold H M] [MBManifold E N] in
/-- A map into `C^∞(M, N)` is continuous on `S` if its compositions with the inclusions into the
`C^ℓ(M, N)` are. -/
theorem continuousOn_of_toCk {P : Type*} [TopologicalSpace P] {ψ : P → SmoothMap H E M N}
    {S : Set P} (h : ∀ ℓ, ContinuousOn (fun p ↦ toCk ℓ (ψ p)) S) : ContinuousOn ψ S := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_iInf_rng.2 fun ℓ ↦ continuous_induced_rng.2
    (continuousOn_iff_continuous_domRestrict.1 (h ℓ))

end SmoothMap

end SmoothMaps

section SectionsSm

variable {H : Type u} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [IsTopologicalAddGroup H]
  [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [MBManifold E N]

variable (H E) in
/-- **The space `Γ_f` of smooth sections of `TN` along `f`** (Glöckner–Neeb, 4.2.1 for `ℓ = ∞`),
written in fiber coordinates: the sections that are `C^ℓ` for all `ℓ`, with the initial topology
with respect to the inclusions into the spaces of `C^ℓ` sections. -/
def SecSm (f : C(M, N)) : Type u := (⨅ ℓ : ℕ, sectionSubmoduleCk H E ℓ f : Submodule ℝ (M → E))

namespace SecSm

variable {f : C(M, N)}

/-- The vector space operations of `Γ_f` are pointwise. -/
instance : AddCommGroup (SecSm H E f) :=
  inferInstanceAs (AddCommGroup (⨅ ℓ : ℕ, sectionSubmoduleCk H E ℓ f : Submodule ℝ (M → E)))

/-- The vector space operations of `Γ_f` are pointwise. -/
instance : Module ℝ (SecSm H E f) :=
  inferInstanceAs (Module ℝ (⨅ ℓ : ℕ, sectionSubmoduleCk H E ℓ f : Submodule ℝ (M → E)))

/-- A section is given by its fiber coordinates `M → E`. -/
instance : FunLike (SecSm H E f) M E where
  coe u := Subtype.val (u : (⨅ ℓ : ℕ, sectionSubmoduleCk H E ℓ f : Submodule ℝ (M → E)))
  coe_injective := Subtype.val_injective

/-- Sections are equal if their coordinates agree. -/
@[ext]
theorem ext {u w : SecSm H E f} (h : ∀ x, u x = w x) : u = w :=
  DFunLike.ext _ _ h

/-- The smooth section with fiber coordinates `u`. -/
def mk (u : M → E) (hu : ∀ ℓ, u ∈ sectionSubmoduleCk H E ℓ f) : SecSm H E f :=
  ⟨u, Submodule.mem_iInf _ |>.2 hu⟩

/-- The coordinates of `SecSm.mk u hu` are `u`. -/
@[simp]
theorem coe_mk (u : M → E) (hu : ∀ ℓ, u ∈ sectionSubmoduleCk H E ℓ f) : ⇑(mk u hu) = u :=
  rfl

/-- A smooth section as a `C^ℓ` section, as a linear map. -/
def toCkL (ℓ : ℕ) : SecSm H E f →ₗ[ℝ] SecCk H E ℓ f where
  toFun u := ⟨u, (Submodule.mem_iInf _).1
    (u : (⨅ ℓ : ℕ, sectionSubmoduleCk H E ℓ f : Submodule ℝ (M → E))).2 ℓ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `toCkL ℓ u` has the same coordinates as `u`. -/
@[simp]
theorem coe_toCkL (ℓ : ℕ) (u : SecSm H E f) : ⇑(toCkL ℓ u) = u :=
  rfl

/-- All the inclusions into the spaces of `C^ℓ` sections. -/
def toPi : SecSm H E f →ₗ[ℝ] ∀ ℓ : ℕ, SecCk H E ℓ f :=
  LinearMap.pi toCkL

/-- **The topology of `Γ_f`** for `ℓ = ∞`: the initial topology with respect to the inclusions into
the spaces of `C^ℓ` sections. -/
instance : TopologicalSpace (SecSm H E f) := .induced toPi inferInstance

/-- `Γ_f` embeds in the product of the spaces of `C^ℓ` sections. -/
theorem isEmbedding_toPi : Topology.IsEmbedding (toPi (H := H) (E := E) (f := f)) :=
  ⟨⟨rfl⟩, fun _ _ h ↦ ext fun x ↦ congrArg (fun φ ↦ φ 0 x) h⟩

/-- `Γ_f` is a topological vector space. -/
instance : IsTopologicalAddGroup (SecSm H E f) := isTopologicalAddGroup_induced toPi

/-- `Γ_f` is a topological vector space. -/
instance : ContinuousSMul ℝ (SecSm H E f) := continuousSMul_induced toPi

/-- `Γ_f` is locally convex. -/
instance : LocallyConvexSpace ℝ (SecSm H E f) := LocallyConvexSpace.induced toPi

/-- `Γ_f` is Hausdorff. -/
instance : T2Space (SecSm H E f) := isEmbedding_toPi.t2Space

/-- The inclusion into the space of `C^ℓ` sections, as a continuous linear map. -/
def toCkCLM (ℓ : ℕ) : SecSm H E f →L[ℝ] SecCk H E ℓ f :=
  ⟨toCkL ℓ, (continuous_apply ℓ).comp (continuous_induced_dom : Continuous (toPi (f := f)))⟩

/-- All the inclusions, as a continuous linear map. -/
def toPiCLM : SecSm H E f →L[ℝ] ∀ ℓ : ℕ, SecCk H E ℓ f :=
  ⟨toPi, continuous_induced_dom⟩

/-- The inclusions into the spaces of `C^ℓ` sections have closed range. -/
theorem isClosed_range_toPi [T2Space M] :
    IsClosed (range (toPi (H := H) (E := E) (f := f))) := by
  let S : Set (∀ ℓ : ℕ, SecCk H E ℓ f) := {φ | ∀ ℓ, SecCk.toSec (φ ℓ) = SecCk.toSec (φ 0)}
  have hS : IsClosed S := by
    simp only [S, ofPred_forall]
    exact isClosed_iInter fun ℓ ↦ isClosed_eq (SecCk.toSec.continuous.comp (continuous_apply ℓ))
      (SecCk.toSec.continuous.comp (continuous_apply 0))
  convert hS using 1
  ext φ
  constructor
  · rintro ⟨u, rfl⟩ ℓ
    rfl
  · intro hφ
    have he : ∀ ℓ, (⇑(φ ℓ) : M → E) = ⇑(φ 0) := fun ℓ ↦ funext fun x ↦
      congrArg (fun w : Sec E f ↦ w x) (hφ ℓ)
    refine ⟨mk (φ 0) fun ℓ ↦ ?_, funext fun ℓ ↦ SecCk.ext fun x ↦ ?_⟩
    · rw [← he ℓ]
      exact (φ ℓ : sectionSubmoduleCk H E ℓ f).2
    · exact (congrFun (he ℓ) x).symm

/-- **`C^k` maps into `Γ_f`** for `ℓ = ∞`: a map is `C^k` if its compositions with all the
inclusions into the spaces of `C^ℓ` sections are. -/
theorem contDiffMBOn_of_toCk [T2Space M] {X : Type*} [AddCommGroup X] [Module ℝ X]
    [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
    [T2Space X] {k : ℕ} {ψ : X → SecSm H E f} {W : Set X} (hW : IsOpen W)
    (h : ∀ ℓ, ContDiffMBOn k (fun w ↦ toCkCLM ℓ (ψ w)) W) : ContDiffMBOn k ψ W :=
  contDiffMBOn_of_isClosedEmbedding toPiCLM isEmbedding_toPi isClosed_range_toPi hW
    (contDiffMBOn_pi hW h)

/-- A map into `Γ_f` is continuous on `S` if its compositions with all the inclusions into the
spaces of `C^ℓ` sections are. -/
theorem continuousOn_of_toCk {P : Type*} [TopologicalSpace P] {ψ : P → SecSm H E f} {S : Set P}
    (h : ∀ ℓ, ContinuousOn (fun p ↦ toCkCLM ℓ (ψ p)) S) : ContinuousOn ψ S :=
  isEmbedding_toPi.continuousOn_iff.2 (continuousOn_pi.2 h)

end SecSm

end SectionsSm

/-! ### The manifold `C^∞(M, N)` -/

section MappingManifoldSm

variable {H : Type u} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [IsTopologicalAddGroup H]
  [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [MBManifold H M] [CompactSpace M]
  [T2Space M]
  {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [MBManifold E N]
  (A : LocalAddition E N)

namespace LocalAddition

/-- The domain `O'_f` of the chart of `C^∞(M, N)` at `f`. -/
def chartSourceSm (f : SmoothMap H E M N) : Set (SmoothMap H E M N) :=
  SmoothMap.toCk 0 ⁻¹' A.chartSourceCk (SmoothMap.toCk 0 f)

/-- The range `O_f` of the chart of `C^∞(M, N)` at `f`. -/
def chartTargetSm (f : SmoothMap H E M N) : Set (SecSm H E (SmoothMap.toC f)) :=
  SecSm.toCkCLM 0 ⁻¹' A.chartTargetCk (SmoothMap.toCk 0 f)

open scoped Classical in
/-- The chart of `C^∞(M, N)` at `f`, `g ↦ θ⁻¹ ∘ (f, g)` on `O'_f` (and `0` elsewhere). -/
def chartFunSm (f g : SmoothMap H E M N) : SecSm H E (SmoothMap.toC f) :=
  if hg : g ∈ A.chartSourceSm f then
    SecSm.mk (fun x ↦ (A.toOpenPartialHomeomorph.symm (f x, g x)).vec) fun ℓ ↦
      (A.chartVec (SmoothMap.toCk ℓ f) (SmoothMap.toCk ℓ g) hg : sectionSubmoduleCk H E ℓ _).2
  else 0

/-- `Σ ∘ τ`, for `τ ∈ O_f`, as a smooth map. -/
def chartInvSm (f : SmoothMap H E M N) (τ : SecSm H E (SmoothMap.toC f))
    (hτ : τ ∈ A.chartTargetSm f) : SmoothMap H E M N :=
  ⟨fun x ↦ A.toFun ⟨f x, τ x⟩, fun ℓ ↦ (A.chartInv (SmoothMap.toCk ℓ f) (SecSm.toCkCLM ℓ τ) hτ).2⟩

open scoped Classical in
/-- The inverse of the chart of `C^∞(M, N)` at `f`, `τ ↦ Σ ∘ τ` on `O_f` (and `f` elsewhere). -/
def chartInvFunSm (f : SmoothMap H E M N) (τ : SecSm H E (SmoothMap.toC f)) :
    SmoothMap H E M N :=
  if hτ : τ ∈ A.chartTargetSm f then A.chartInvSm f τ hτ else f

omit [CompactSpace M] [T2Space M] in
/-- The chart of `C^∞(M, N)` is compatible with the charts of the `C^ℓ(M, N)`. -/
theorem toCkCLM_chartFunSm (f g : SmoothMap H E M N) (ℓ : ℕ) :
    SecSm.toCkCLM ℓ (A.chartFunSm f g) =
      A.chartFunCk (SmoothMap.toCk ℓ f) (SmoothMap.toCk ℓ g) := by
  by_cases hg : g ∈ A.chartSourceSm f
  · have hg' : SmoothMap.toCk ℓ g ∈ A.chartSourceCk (SmoothMap.toCk ℓ f) := hg
    rw [chartFunSm, dite_eq_left_of_eq_true (eq_true hg), chartFunCk,
      dite_eq_left_of_eq_true (eq_true hg')]
    rfl
  · have hg' : SmoothMap.toCk ℓ g ∉ A.chartSourceCk (SmoothMap.toCk ℓ f) := hg
    rw [chartFunSm, dite_eq_right_of_eq_false (eq_false hg), chartFunCk,
      dite_eq_right_of_eq_false (eq_false hg'), map_zero]
    rfl

omit [CompactSpace M] in
/-- The inverse chart of `C^∞(M, N)` is compatible with those of the `C^ℓ(M, N)`. -/
theorem toCk_chartInvFunSm (f : SmoothMap H E M N) (τ : SecSm H E (SmoothMap.toC f)) (ℓ : ℕ) :
    SmoothMap.toCk ℓ (A.chartInvFunSm f τ) =
      A.chartInvFunCk (SmoothMap.toCk ℓ f) (SecSm.toCkCLM ℓ τ) := by
  by_cases hτ : τ ∈ A.chartTargetSm f
  · have hτ' : SecSm.toCkCLM ℓ τ ∈ A.chartTargetCk (SmoothMap.toCk ℓ f) := hτ
    refine CkMap.ext fun x ↦ ?_
    have h₁ : A.chartInvFunSm f τ x = A.toFun ⟨f x, τ x⟩ := by
      rw [chartInvFunSm, dite_eq_left_of_eq_true (eq_true hτ)]
      rfl
    exact h₁.trans (A.chartInvFunCk_apply _ hτ' x).symm
  · have hτ' : SecSm.toCkCLM ℓ τ ∉ A.chartTargetCk (SmoothMap.toCk ℓ f) := hτ
    have h₁ : A.chartInvFunSm f τ = f := by
      rw [chartInvFunSm, dite_eq_right_of_eq_false (eq_false hτ)]
    rw [h₁]
    exact (chartInvFunCk_of_notMem A (SmoothMap.toCk ℓ f) hτ').symm

/-- **The chart of `C^∞(M, N)` at `f`** (Glöckner–Neeb, proof of Theorem 4.2.2, `ℓ = ∞`):
`g ↦ θ⁻¹ ∘ (f, g)`, with inverse `τ ↦ Σ ∘ τ`, a partial homeomorphism for the compact-open
`C^∞` topologies, modeled on the space `Γ_f` of smooth sections along `f`. -/
def chartSm (f : SmoothMap H E M N) :
    OpenPartialHomeomorph (SmoothMap H E M N) (SecSm H E (SmoothMap.toC f)) where
  toFun := A.chartFunSm f
  invFun := A.chartInvFunSm f
  source := A.chartSourceSm f
  target := A.chartTargetSm f
  map_source' g hg := by
    have h := (A.chartCk (SmoothMap.toCk 0 f)).map_source hg
    change A.chartFunCk (SmoothMap.toCk 0 f) (SmoothMap.toCk 0 g) ∈
      A.chartTargetCk (SmoothMap.toCk 0 f) at h
    change SecSm.toCkCLM 0 (A.chartFunSm f g) ∈ A.chartTargetCk (SmoothMap.toCk 0 f)
    exact (A.toCkCLM_chartFunSm f g 0).symm ▸ h
  map_target' τ hτ := by
    have h := (A.chartCk (SmoothMap.toCk 0 f)).map_target (x := SecSm.toCkCLM 0 τ) hτ
    change A.chartInvFunCk (SmoothMap.toCk 0 f) (SecSm.toCkCLM 0 τ) ∈
      A.chartSourceCk (SmoothMap.toCk 0 f) at h
    change SmoothMap.toCk 0 (A.chartInvFunSm f τ) ∈ A.chartSourceCk (SmoothMap.toCk 0 f)
    rw [A.toCk_chartInvFunSm f τ 0]
    exact h
  left_inv' g hg := by
    have h := (A.chartCk (SmoothMap.toCk 0 f)).left_inv hg
    have e : SmoothMap.toCk 0 (A.chartInvFunSm f (A.chartFunSm f g)) =
        (A.chartCk (SmoothMap.toCk 0 f)).symm
          ((A.chartCk (SmoothMap.toCk 0 f)) (SmoothMap.toCk 0 g)) :=
      (A.toCk_chartInvFunSm f _ 0).trans (congrArg (A.chartInvFunCk (SmoothMap.toCk 0 f))
        (A.toCkCLM_chartFunSm f g 0))
    exact SmoothMap.ext fun x ↦ congrArg (fun φ : CkMap H E 0 M N ↦ φ x) (e.trans h)
  right_inv' τ hτ := by
    have h := (A.chartCk (SmoothMap.toCk 0 f)).right_inv (x := SecSm.toCkCLM 0 τ) hτ
    have e : SecSm.toCkCLM 0 (A.chartFunSm f (A.chartInvFunSm f τ)) =
        (A.chartCk (SmoothMap.toCk 0 f)) ((A.chartCk (SmoothMap.toCk 0 f)).symm
          (SecSm.toCkCLM 0 τ)) :=
      (A.toCkCLM_chartFunSm f _ 0).trans (congrArg (A.chartFunCk (SmoothMap.toCk 0 f))
        (A.toCk_chartInvFunSm f τ 0))
    exact SecSm.ext fun x ↦ congrArg (fun φ : SecCk H E 0 _ ↦ φ x) (e.trans h)
  open_source := (A.isOpen_chartSourceCk (SmoothMap.toCk 0 f)).preimage
    (SmoothMap.continuous_toCk 0)
  open_target := (A.isOpen_chartTargetCk (SmoothMap.toCk 0 f)).preimage
    (SecSm.toCkCLM 0).continuous
  continuousOn_toFun := SecSm.continuousOn_of_toCk fun ℓ ↦ by
    refine ((A.continuousOn_chartFunCk (SmoothMap.toCk ℓ f)).comp
      (SmoothMap.continuous_toCk ℓ).continuousOn fun g hg ↦ hg).congr fun g _ ↦ ?_
    exact A.toCkCLM_chartFunSm f g ℓ
  continuousOn_invFun := SmoothMap.continuousOn_of_toCk fun ℓ ↦ by
    refine ((A.continuousOn_chartInvFunCk (SmoothMap.toCk ℓ f)).comp
      (SecSm.toCkCLM ℓ).continuous.continuousOn fun τ hτ ↦ hτ).congr fun τ _ ↦ ?_
    exact A.toCk_chartInvFunSm f τ ℓ

/-- The chart at `f` contains `f` in its domain. -/
theorem mem_chartSm_source (f : SmoothMap H E M N) : f ∈ (A.chartSm f).source :=
  A.mem_chartSourceCk (SmoothMap.toCk 0 f)

/-- **The transition maps of `C^∞(M, N)` are smooth** (Glöckner–Neeb, proof of Theorem 4.2.2,
`ℓ = ∞`): composed with the inclusions into the spaces of `C^ℓ` sections, they are the transition
maps of the `C^ℓ(M, N)`. -/
theorem smoothMBOn_transitionSm (f g : SmoothMap H E M N) :
    SmoothMBOn (A.chartSm g ∘ (A.chartSm f).symm)
      ((A.chartSm f).target ∩ (A.chartSm f).symm ⁻¹' (A.chartSm g).source) := by
  intro k
  have hW := (A.chartSm f).isOpen_inter_preimage_symm (A.chartSm g).open_source
  refine SecSm.contDiffMBOn_of_toCk hW fun ℓ ↦ ?_
  have hmaps : MapsTo (SecSm.toCkCLM ℓ)
      ((A.chartSm f).target ∩ (A.chartSm f).symm ⁻¹' (A.chartSm g).source)
      (A.transitionDomainCk (SmoothMap.toCk ℓ f) (SmoothMap.toCk ℓ g)) := fun τ hτ ↦ by
    refine ⟨hτ.1, ?_⟩
    have h := hτ.2
    change SmoothMap.toCk 0 (A.chartInvFunSm f τ) ∈ A.chartSourceCk (SmoothMap.toCk 0 g) at h
    change A.chartInvFunCk (SmoothMap.toCk ℓ f) (SecSm.toCkCLM ℓ τ) ∈
      A.chartSourceCk (SmoothMap.toCk ℓ g)
    exact (A.toCk_chartInvFunSm f τ ℓ) ▸ h
  have hc := ((A.smoothMBOn_transitionCk (SmoothMap.toCk ℓ f) (SmoothMap.toCk ℓ g)) k).comp hW
    (A.isOpen_transitionDomainCk _ _) ((SecSm.toCkCLM ℓ).contDiffMBOn k _) hmaps
  refine ContDiffMBOn.congr_of_isOpen hW (fun τ _ ↦ ?_) hc
  exact ((congrArg (A.chartFunCk (SmoothMap.toCk ℓ g)) (A.toCk_chartInvFunSm f τ ℓ)).symm.trans
    (A.toCkCLM_chartFunSm g _ ℓ).symm)

/-- **The manifold of smooth maps** `C^∞(M, N)` (Glöckner–Neeb, Theorem 4.2.2(a) and (b),
`ℓ = ∞`): the charts `g ↦ θ⁻¹ ∘ (f, g)` form an atlas of `C^∞(M, N)` with varying models (the
spaces `Γ_f` of smooth sections along `f`) and smooth transition maps; they are partial
homeomorphisms for the compact-open `C^∞` topology. -/
def mappingAtlasSm : VaryingAtlas (SmoothMap H E M N) where
  ι := SmoothMap H E M N
  model f := SecSm H E (SmoothMap.toC f)
  chart := A.chartSm
  chartAt g := g
  mem_chartAt_source g := A.mem_chartSm_source g
  smoothMBOn_transition f g := A.smoothMBOn_transitionSm f g

/-- **Point evaluations are smooth** (Glöckner–Neeb, Theorem 4.2.2(c), `ℓ = ∞`): in the chart at
`f`, the evaluation `ε_x : g ↦ g(x)` is smooth on `O_f`. -/
theorem smoothMBMOn_eval_chartSm_symm (f : SmoothMap H E M N) (x : M) :
    SmoothMBMOn (SecSm H E (SmoothMap.toC f)) E (fun τ ↦ (A.chartSm f).symm τ x)
      (A.chartSm f).target := by
  intro k
  have hT := (A.chartSm f).open_target
  have h1 : ContMDiffMBOn (E := SecSm H E (SmoothMap.toC f))
      (F := SecCk H E 0 (SmoothMap.toC f)) k (SecSm.toCkCLM 0) (A.chartSm f).target :=
    (contMDiffMBOn_iff_contDiffMBOn hT).2 ((SecSm.toCkCLM 0).contDiffMBOn k _)
  have h := ((A.smoothMBMOn_eval_chartCk_symm (SmoothMap.toCk 0 f) x) k).comp hT
    (A.chartCk (SmoothMap.toCk 0 f)).open_target h1 fun τ hτ ↦ hτ
  refine h.congr_of_isOpen hT fun τ _ ↦ ?_
  exact congrArg (fun φ : CkMap H E 0 M N ↦ φ x) (A.toCk_chartInvFunSm f τ 0).symm

end LocalAddition

end MappingManifoldSm

end LocallyConvex.Manifolds
