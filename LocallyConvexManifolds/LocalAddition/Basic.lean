/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.Tangent.Map
public import LocallyConvexManifolds.Manifold.Product

/-!
# Local additions

Reference: H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups* (arXiv:2602.12362),
§3.8, Definition 3.8.11 and Lemma 3.8.17.

A **local addition** on a manifold `M` modeled on a locally convex space `E` is a smooth map
`Σ : Ω → M` on an open subset `Ω ⊆ TM` containing the zero section, with `Σ(0ₓ) = x`, such that
`θ = (π, Σ) : Ω → M × M` is a smooth diffeomorphism onto an open subset of `M × M`. Local
additions are the basic tool for the manifold structure of spaces of mappings (Glöckner–Neeb,
Section 4.2).

## Main definitions and results

* `LocalAddition E M` (Definition 3.8.11), with `LocalAddition.toFun` (the map `Σ`),
  `LocalAddition.smoothMBMOn_toFun` and `LocalAddition.IsNormalized` ((3.55)).
* `openLocalAddition U`: for an open subset `U` of `E`, `Σ(x, v) = x + v` on
  `Ω = {(x, v) : x + v ∈ U}`, with `θ` a diffeomorphism of `Ω` onto `U × U`;
  it is normalized (`isNormalized_openLocalAddition`).
* `tangentProdHomeomorph`, `smoothMBM_tangentProdSplit`, `smoothMBM_tangentProdMk`: the
  identification `T(M₁ × M₂) ≅ TM₁ × TM₂`, smooth in both directions.
* `LocalAddition.prod` (Lemma 3.8.17): products of local additions.

## Implementation notes

* The data of a local addition is the map `θ`, bundled as an `OpenPartialHomeomorph` from `TM`
  to `M × M` with source `Ω`, whose first component is the bundle projection and which is smooth
  with smooth inverse; `Σ` is its second component. This is equivalent to Glöckner–Neeb's
  formulation (`Σ` smooth and `θ = (π, Σ)` a diffeomorphism onto an open set).
* Tangent vectors are written in the fiber coordinates of the preferred chart at their base point
  (`TangentBundle.vec`); accordingly (3.55) is stated in the preferred chart at `x`.
* The identification `T(M₁ × M₂) ≅ TM₁ × TM₂`, implicit in Glöckner–Neeb, is constructed here:
  the coordinate changes of the product are the products of the coordinate changes
  (`tangentCoordChange_prod`), so in charts the identification is a regrouping of coordinates.
-/

@[expose] public section

open Set Filter Bundle TopologicalSpace
open scoped Topology Manifold
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe u

/-! ### Local additions -/

section Vec

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

/-- The fiber coordinate `v ∈ E` of a tangent vector, in the preferred chart at its base point. -/
def TangentBundle.vec (p : TangentBundle E M) : E := p.2

/-- The fiber coordinate of `⟨x, v⟩` is `v`. -/
@[simp]
theorem TangentBundle.vec_mk (x : M) (v : E) :
    TangentBundle.vec (⟨x, v⟩ : TangentBundle E M) = v :=
  rfl

/-- Tangent vectors are determined by their base points and fiber coordinates. -/
theorem TangentBundle.ext_vec {p q : TangentBundle E M} (h₁ : p.proj = q.proj)
    (h₂ : p.vec = q.vec) : p = q := by
  obtain ⟨x, v⟩ := p
  obtain ⟨y, w⟩ := q
  simp only at h₁
  subst h₁
  exact congrArg (TotalSpace.mk x) h₂

end Vec

section Definition

variable (E : Type u) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  (M : Type*) [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

/-- **Local additions** (Glöckner–Neeb, Definition 3.8.11). A local addition on `M` is a smooth
map `Σ : Ω → M` on an open subset `Ω ⊆ TM` containing the zero section, with `Σ(0ₓ) = x`, such
that `θ = (π, Σ) : Ω → M × M` is a smooth diffeomorphism onto an open subset of `M × M`.

We bundle the data as the map `θ`, an open partial homeomorphism `TM → M × M` with source `Ω`,
whose first component is the bundle projection and which is smooth with smooth inverse; then
`Σ = pr₂ ∘ θ` (`LocalAddition.toFun`). -/
structure LocalAddition where
  /-- The map `θ = (π, Σ)`, a homeomorphism of `Ω` onto an open subset of `M × M`. -/
  toOpenPartialHomeomorph : OpenPartialHomeomorph (TangentBundle E M) (M × M)
  /-- The first component of `θ` is the bundle projection. -/
  fst_eq : ∀ v ∈ toOpenPartialHomeomorph.source, (toOpenPartialHomeomorph v).1 = v.proj
  /-- `θ` is smooth on `Ω`. -/
  smoothMBMOn : SmoothMBMOn (E × E) (ModelProd E E) toOpenPartialHomeomorph
    toOpenPartialHomeomorph.source
  /-- `θ⁻¹` is smooth on `θ(Ω)`. -/
  smoothMBMOn_symm : SmoothMBMOn (ModelProd E E) (E × E) toOpenPartialHomeomorph.symm
    toOpenPartialHomeomorph.target
  /-- `Ω` contains the zero section. -/
  zero_mem : ∀ x : M, (⟨x, 0⟩ : TangentBundle E M) ∈ toOpenPartialHomeomorph.source
  /-- `Σ(0ₓ) = x`. -/
  snd_zero : ∀ x : M, (toOpenPartialHomeomorph ⟨x, 0⟩).2 = x

namespace LocalAddition

variable {E M}
variable (A : LocalAddition E M)

/-- The local addition `Σ : Ω → M`. -/
def toFun (v : TangentBundle E M) : M := (A.toOpenPartialHomeomorph v).2

/-- The domain `Ω ⊆ TM` of the local addition. -/
def source : Set (TangentBundle E M) := A.toOpenPartialHomeomorph.source

/-- The domain `Ω` is open. -/
theorem isOpen_source : IsOpen A.source :=
  A.toOpenPartialHomeomorph.open_source

/-- `θ(v) = (π(v), Σ(v))` on `Ω`. -/
theorem toOpenPartialHomeomorph_apply {v : TangentBundle E M} (hv : v ∈ A.source) :
    A.toOpenPartialHomeomorph v = (v.proj, A.toFun v) :=
  Prod.ext (A.fst_eq v hv) rfl

/-- `Σ(0ₓ) = x`. -/
theorem toFun_zero (x : M) : A.toFun ⟨x, 0⟩ = x :=
  A.snd_zero x

/-- `θ(Ω)` is open in `M × M`. -/
theorem isOpen_image_source : IsOpen (A.toOpenPartialHomeomorph '' A.source) := by
  rw [source, A.toOpenPartialHomeomorph.image_source_eq_target]
  exact A.toOpenPartialHomeomorph.open_target

/-- The local addition `Σ` is smooth on `Ω`. -/
theorem smoothMBMOn_toFun : SmoothMBMOn (E × E) E A.toFun A.source :=
  SmoothMBMOn.comp A.isOpen_source isOpen_univ (fun k ↦ smoothMBM_snd (M := M) (N := M) k)
    A.smoothMBMOn (mapsTo_univ _ _)

/-- **Normalized local additions** (Glöckner–Neeb, (3.55)): the restriction of `Σ` to the fiber
`TₓM` has derivative the identity at `0ₓ`. Since the fiber coordinates of `TM` over `x` are
those of the preferred chart at `x`, this reads `d(φₓ ∘ Σ(x, ·))(0)(w) = w` for that chart
`φₓ`. -/
def IsNormalized : Prop :=
  ∀ (x : M) (w : E), dMB (fun v : E ↦ chartAt E x (A.toFun ⟨x, v⟩)) (0, w) = w

end LocalAddition

end Definition

/-! ### Open subsets of the model space -/

section OpenSubset

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] (U : Opens E)

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] in
/-- The charts of an open subset `U` of the model space are the inclusion `U → E`. -/
theorem opens_atlas_apply {U : Opens E} {e : OpenPartialHomeomorph U E} (he : e ∈ atlas E U)
    (z : U) : e z = z := by
  obtain ⟨x, rfl⟩ := Opens.chart_eq' ⟨z⟩ he
  rfl

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] in
/-- The charts of an open subset of the model space are defined everywhere. -/
theorem opens_atlas_source {U : Opens E} {e : OpenPartialHomeomorph U E} (he : e ∈ atlas E U) :
    e.source = univ := by
  ext z
  obtain ⟨x, rfl⟩ := Opens.chart_eq' ⟨z⟩ he
  simp

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] in
/-- The charts of an open subset `U` of the model space have target `U`. -/
theorem opens_atlas_target {U : Opens E} {e : OpenPartialHomeomorph U E} (he : e ∈ atlas E U) :
    e.target = U := by
  rw [← e.image_source_eq_target, opens_atlas_source he, image_univ]
  ext y
  simp only [mem_range, SetLike.mem_coe]
  constructor
  · rintro ⟨z, rfl⟩
    rw [opens_atlas_apply he]
    exact z.2
  · intro hy
    exact ⟨⟨y, hy⟩, opens_atlas_apply he _⟩

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] in
/-- The inverse charts of an open subset `U` of the model space are the identity of `U`. -/
theorem opens_atlas_symm {U : Opens E} {e : OpenPartialHomeomorph U E} (he : e ∈ atlas E U)
    {y : E} (hy : y ∈ U) : ((e.symm y : U) : E) = y := by
  rw [← opens_atlas_apply he]
  exact e.right_inv (by rw [opens_atlas_target he]; exact hy)

omit [LocallyConvexSpace ℝ E] in
/-- The tangent coordinate changes of an open subset of the model space are the identity. -/
theorem tangentCoordChange_opens (i j : atlas E U) (x : U) (v : E) :
    tangentCoordChange i j x v = v := by
  have hev : j.1 ∘ i.1.symm =ᶠ[𝓝 (i.1 x)] id := by
    rw [opens_atlas_apply i.2]
    exact Filter.eventually_of_mem (U.isOpen.mem_nhds x.2) fun y hy ↦ by
      simp only [Function.comp_apply, opens_atlas_apply j.2, opens_atlas_symm i.2 hy, id]
  rw [tangentCoordChange, dMB_congr_of_eventuallyEq hev v]
  exact ((ContinuousLinearMap.id ℝ E).hasDirDerivAt _ v).dMB_eq

/-- The charts of `TU`: `v ↦ (π v, v)`. -/
theorem chartAt_tangentBundle_opens_apply (p q : TangentBundle E U) :
    chartAt (E × E) p q = ((q.proj : E), q.vec) :=
  Prod.ext (opens_atlas_apply (chart_mem_atlas E _) q.proj) (tangentCoordChange_opens U _ _ _ _)

/-- The charts of `TU` are defined everywhere. -/
theorem chartAt_tangentBundle_opens_source (p : TangentBundle E U) :
    (chartAt (E × E) p).source = univ := by
  ext q
  rw [chartAt_tangentBundle, mem_tangentChart_source, opens_atlas_source (chart_mem_atlas E _)]
  simp

/-- The charts of `TU` have target `U × E`. -/
theorem mem_chartAt_tangentBundle_opens_target (p : TangentBundle E U) (q : E × E) :
    q ∈ (chartAt (E × E) p).target ↔ q.1 ∈ U := by
  rw [chartAt_tangentBundle, mem_tangentChart_target, opens_atlas_target (chart_mem_atlas E _),
    opens_atlas_source (chart_mem_atlas E _)]
  simp

/-- The inverse charts of `TU`: `(x, v) ↦ v ∈ TₓU`. -/
theorem chartAt_tangentBundle_opens_symm (p : TangentBundle E U) {q : E × E} (hq : q.1 ∈ U) :
    (chartAt (E × E) p).symm q = (⟨⟨q.1, hq⟩, (q.2 : E)⟩ : TangentBundle E U) := by
  have h1 : ((chartAt (E × E) p).symm q).proj = ⟨q.1, hq⟩ :=
    Subtype.ext (opens_atlas_symm (chart_mem_atlas E _) hq)
  have h2 : (((chartAt (E × E) p).symm q).2 : E) = q.2 := tangentCoordChange_opens U _ _ _ _
  revert h1 h2
  generalize (chartAt (E × E) p).symm q = r
  obtain ⟨b, w⟩ := r
  intro h1 h2
  simp only at h1
  subst h1
  change w = q.2 at h2
  subst h2
  rfl

/-- The fiber coordinates `v ↦ (π v, v) ∈ E × E` on `TU` are continuous. -/
theorem continuous_tangentBundle_opens_coord :
    Continuous fun p : TangentBundle E U ↦ ((p.proj : E), p.vec) := by
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  have h := (chartAt (E × E) p).continuousAt (mem_chart_source (E × E) p)
  exact h.congr (Filter.Eventually.of_forall fun q ↦ chartAt_tangentBundle_opens_apply U p q)

/-- `(x, v) ↦ v ∈ TₓU` is continuous on `U × E`. -/
theorem continuous_tangentBundle_opens_mk :
    Continuous fun q : U × E ↦ (⟨q.1, q.2⟩ : TangentBundle E U) := by
  refine continuous_iff_continuousAt.2 fun q ↦ ?_
  set p : TangentBundle E U := ⟨q.1, q.2⟩
  have hq : ((q.1 : E), q.2) ∈ (chartAt (E × E) p).target :=
    (mem_chartAt_tangentBundle_opens_target U p _).2 q.1.2
  have h := ((chartAt (E × E) p).continuousAt_symm hq).comp
    (f := fun q : U × E ↦ ((q.1 : E), q.2)) (by fun_prop : Continuous _).continuousAt
  refine h.congr (Filter.Eventually.of_forall fun q' ↦ ?_)
  change (chartAt (E × E) p).symm ((q'.1 : E), q'.2) = _
  exact chartAt_tangentBundle_opens_symm U p (q := ((q'.1 : E), q'.2)) q'.1.2

/-- `θ(x, v) = (x, x + v)` on `Ω = {(x, v) : x + v ∈ U}`, as an open partial homeomorphism
`TU → U × U` onto `U × U`. -/
def addOpen : OpenPartialHomeomorph (TangentBundle E U) (U × U) := by
  classical
  exact {
  toFun := fun p ↦ (p.proj, if h : (p.proj : E) + p.vec ∈ U then ⟨_, h⟩ else p.proj)
  invFun := fun q ↦ ⟨q.1, ((q.2 : E) - q.1 : E)⟩
  source := {p | (p.proj : E) + p.vec ∈ U}
  target := univ
  map_source' := fun _ _ ↦ mem_univ _
  map_target' := fun q _ ↦ by
    change (q.1 : E) + ((q.2 : E) - q.1) ∈ U
    rw [add_sub_cancel]
    exact q.2.2
  left_inv' := fun p hp ↦ by
    refine TangentBundle.ext_vec rfl ?_
    change (((if h : (p.proj : E) + p.vec ∈ U then (⟨_, h⟩ : U) else p.proj) : U) : E) - p.proj =
      p.vec
    have hp' : (p.proj : E) + p.vec ∈ U := hp
    simp only [hp', ↓reduceDIte]
    exact add_sub_cancel_left _ _
  right_inv' := fun q _ ↦ by
    have h : (q.1 : E) + ((q.2 : E) - q.1) ∈ U := by rw [add_sub_cancel]; exact q.2.2
    refine Prod.ext rfl ?_
    change (if h : (q.1 : E) + ((q.2 : E) - q.1) ∈ U then (⟨_, h⟩ : U) else q.1) = q.2
    simp only [h, ↓reduceDIte]
    exact Subtype.ext (add_sub_cancel _ _)
  open_source := U.isOpen.preimage
    ((continuous_fst.add continuous_snd).comp (continuous_tangentBundle_opens_coord U))
  open_target := isOpen_univ
  continuousOn_toFun := by
    refine (tangentBundleCore E U).continuous_proj.continuousOn.prodMk ?_
    rw [continuousOn_iff_continuous_domRestrict]
    have hc : Continuous fun p : {p : TangentBundle E U | (p.proj : E) + p.vec ∈ U} ↦
        (⟨(p.1.proj : E) + p.1.vec, p.2⟩ : U) :=
      (((continuous_fst.add continuous_snd).comp
        (continuous_tangentBundle_opens_coord U)).comp continuous_subtype_val).subtype_mk _
    refine hc.congr fun p ↦ ?_
    change _ = if h : (p.1.proj : E) + p.1.vec ∈ U then (⟨_, h⟩ : U) else p.1.proj
    have hp : (p.1.proj : E) + p.1.vec ∈ U := p.2
    simp only [hp, ↓reduceDIte]
  continuousOn_invFun := by
    refine Continuous.continuousOn ?_
    exact (continuous_tangentBundle_opens_mk U).comp (continuous_fst.prodMk
      ((continuous_subtype_val.comp continuous_snd).sub
        (continuous_subtype_val.comp continuous_fst))) }

/-- The second component of `θ(x, v)` is `x + v`. -/
theorem addOpen_snd {p : TangentBundle E U} (hp : p ∈ (addOpen U).source) :
    ((addOpen U p).2 : E) = p.proj + p.vec := by
  classical
  have hp' : (p.proj : E) + p.vec ∈ U := hp
  change (((if h : (p.proj : E) + p.vec ∈ U then (⟨_, h⟩ : U) else p.proj) : U) : E) = _
  simp only [hp', ↓reduceDIte]

/-- `θ⁻¹(x, y) = (x, y - x)`. -/
theorem addOpen_symm_apply (q : U × U) :
    (addOpen U).symm q = (⟨q.1, ((q.2 : E) - q.1 : E)⟩ : TangentBundle E U) :=
  rfl

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] in
/-- The charts of `U × U` are the inclusion `U × U → E × E`. -/
theorem chartAt_opens_prod_apply (z z' : U × U) :
    chartAt (ModelProd E E) z z' = ((z'.1 : E), (z'.2 : E)) :=
  Prod.ext (opens_atlas_apply (chart_mem_atlas E _) _) (opens_atlas_apply (chart_mem_atlas E _) _)

/-- `θ` is smooth. -/
theorem smoothMBMOn_addOpen :
    SmoothMBMOn (E × E) (ModelProd E E) (addOpen U) (addOpen U).source := by
  intro k
  refine ⟨(addOpen U).continuousOn, fun p _ ↦ ?_⟩
  let L : E × E →L[ℝ] E × E := (ContinuousLinearMap.fst ℝ E E).prod
    (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E)
  refine ContDiffMBOn.congr_of_isOpen
    (isOpen_chartDomain (addOpen U).open_source (addOpen U).continuousOn _ _) (fun q hq ↦ ?_)
    ((L.contDiffMBOn k univ).mono (subset_univ _))
  have hq1 : q.1 ∈ U := (mem_chartAt_tangentBundle_opens_target U p q).1 hq.1
  have hr := chartAt_tangentBundle_opens_symm U p hq1
  have hsrc : (⟨⟨q.1, hq1⟩, (q.2 : E)⟩ : TangentBundle E U) ∈ (addOpen U).source := by
    rw [← hr]; exact hq.2.1
  simp only [Function.comp_apply, hr, chartAt_opens_prod_apply]
  exact Prod.ext rfl (addOpen_snd U hsrc).symm

/-- `θ⁻¹` is smooth. -/
theorem smoothMBMOn_addOpen_symm :
    SmoothMBMOn (ModelProd E E) (E × E) (addOpen U).symm (addOpen U).target := by
  intro k
  refine ⟨(addOpen U).continuousOn_symm, fun q₀ _ ↦ ?_⟩
  let L : E × E →L[ℝ] E × E := (ContinuousLinearMap.fst ℝ E E).prod
    (ContinuousLinearMap.snd ℝ E E - ContinuousLinearMap.fst ℝ E E)
  refine ContDiffMBOn.congr_of_isOpen
    (isOpen_chartDomain (addOpen U).open_target (addOpen U).continuousOn_symm _ _)
    (fun z hz ↦ ?_) ((L.contDiffMBOn k univ).mono (subset_univ _))
  have hz1 : z.1 ∈ U := by
    have := hz.1.1
    rwa [opens_atlas_target (chart_mem_atlas E _)] at this
  have hz2 : z.2 ∈ U := by
    have := hz.1.2
    rwa [opens_atlas_target (chart_mem_atlas E _)] at this
  simp only [Function.comp_apply, chartAt_tangentBundle_opens_apply]
  refine Prod.ext ?_ ?_
  · exact (opens_atlas_symm (chart_mem_atlas E _) hz1).symm
  · change z.2 - z.1 = (((chartAt E q₀.2).symm z.2 : U) : E) - (((chartAt E q₀.1).symm z.1 : U) : E)
    rw [opens_atlas_symm (chart_mem_atlas E _) hz1, opens_atlas_symm (chart_mem_atlas E _) hz2]

/-- **Local addition of an open subset of a locally convex space** (Glöckner–Neeb, 3.8.11):
`Σ(x, v) = x + v` on `Ω = {(x, v) ∈ TU : x + v ∈ U}`, with `θ(x, v) = (x, x + v)` a
diffeomorphism of `Ω` onto `U × U`. -/
def openLocalAddition : LocalAddition E U where
  toOpenPartialHomeomorph := addOpen U
  fst_eq _ _ := rfl
  smoothMBMOn := smoothMBMOn_addOpen U
  smoothMBMOn_symm := smoothMBMOn_addOpen_symm U
  zero_mem x := by
    change (x : E) + (0 : E) ∈ U
    rw [add_zero]
    exact x.2
  snd_zero x := by
    have h : (⟨x, 0⟩ : TangentBundle E U) ∈ (addOpen U).source := by
      change (x : E) + (0 : E) ∈ U
      rw [add_zero]
      exact x.2
    exact Subtype.ext ((addOpen_snd U h).trans (add_zero _))

/-- The local addition `(x, v) ↦ x + v` of an open subset of a locally convex space. -/
theorem openLocalAddition_toFun {p : TangentBundle E U} (hp : (p.proj : E) + p.vec ∈ U) :
    ((openLocalAddition U).toFun p : E) = p.proj + p.vec :=
  addOpen_snd U hp

/-- The local addition `(x, v) ↦ x + v` is normalized. -/
theorem isNormalized_openLocalAddition : (openLocalAddition U).IsNormalized := by
  intro x w
  have hc : Continuous fun v : E ↦ (x : E) + v := by fun_prop
  have hmem : {v : E | (x : E) + v ∈ U} ∈ 𝓝 (0 : E) :=
    hc.continuousAt.preimage_mem_nhds (by rw [add_zero]; exact U.isOpen.mem_nhds x.2)
  have hev : (fun v : E ↦ chartAt E x ((openLocalAddition U).toFun ⟨x, v⟩)) =ᶠ[𝓝 0]
      fun v ↦ (x : E) + v :=
    Filter.eventually_of_mem hmem fun v hv ↦
      (opens_atlas_apply (chart_mem_atlas E x) _).trans
        (openLocalAddition_toFun U (p := ⟨x, v⟩) hv)
  rw [dMB_congr_of_eventuallyEq hev w]
  have h : HasDirDerivAt (fun v ↦ (x : E) + v) 0 w w :=
    ((ContinuousLinearMap.id ℝ E).hasDirDerivAt 0 w).congr fun t ↦ by simp
  exact h.dMB_eq

end OpenSubset

/-! ### The tangent bundle of a product -/

section TangentProd

variable {E₁ E₂ : Type u}
  [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁] [IsTopologicalAddGroup E₁]
  [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂] [IsTopologicalAddGroup E₂]
  [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace E₁ M₁] [MBManifold E₁ M₁]
  {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace E₂ M₂] [MBManifold E₂ M₂]

omit [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  [MBManifold E₁ M₁] [MBManifold E₂ M₂] [AddCommGroup E₁] [Module ℝ E₁] [AddCommGroup E₂]
  [Module ℝ E₂] in
/-- Products of charts are charts of the product. -/
theorem prodChart_mem_atlas {e₁ : OpenPartialHomeomorph M₁ E₁} (he₁ : e₁ ∈ atlas E₁ M₁)
    {e₂ : OpenPartialHomeomorph M₂ E₂} (he₂ : e₂ ∈ atlas E₂ M₂) :
    (e₁.prod e₂ : OpenPartialHomeomorph (M₁ × M₂) (ModelProd E₁ E₂)) ∈
      atlas (ModelProd E₁ E₂) (M₁ × M₂) :=
  mem_image2_of_mem he₁ he₂

/-- The tangent coordinate changes of `M₁ × M₂` between product charts are the products of the
tangent coordinate changes. -/
theorem tangentCoordChange_prod {e₁ f₁ : OpenPartialHomeomorph M₁ E₁} (he₁ : e₁ ∈ atlas E₁ M₁)
    (hf₁ : f₁ ∈ atlas E₁ M₁) {e₂ f₂ : OpenPartialHomeomorph M₂ E₂} (he₂ : e₂ ∈ atlas E₂ M₂)
    (hf₂ : f₂ ∈ atlas E₂ M₂) {x : M₁ × M₂} (hx₁ : x.1 ∈ e₁.source ∩ f₁.source)
    (hx₂ : x.2 ∈ e₂.source ∩ f₂.source) (v : ModelProd E₁ E₂) :
    tangentCoordChange (E := ModelProd E₁ E₂) (M := M₁ × M₂) ⟨_, prodChart_mem_atlas he₁ he₂⟩
      ⟨_, prodChart_mem_atlas hf₁ hf₂⟩ x v =
      ((tangentCoordChange ⟨e₁, he₁⟩ ⟨f₁, hf₁⟩ x.1 v.1,
        tangentCoordChange ⟨e₂, he₂⟩ ⟨f₂, hf₂⟩ x.2 v.2) : E₁ × E₂) := by
  have h₁ := (smoothMBOn_transition he₁ hf₁ 1).hasDirDerivAt (k := 0)
    (show e₁ x.1 ∈ e₁.target ∩ e₁.symm ⁻¹' f₁.source from
      ⟨e₁.map_source hx₁.1, by simp [e₁.left_inv hx₁.1, hx₁.2]⟩) v.1
  have h₂ := (smoothMBOn_transition he₂ hf₂ 1).hasDirDerivAt (k := 0)
    (show e₂ x.2 ∈ e₂.target ∩ e₂.symm ⁻¹' f₂.source from
      ⟨e₂.map_source hx₂.1, by simp [e₂.left_inv hx₂.1, hx₂.2]⟩) v.2
  have h : HasDirDerivAt ((f₁.prod f₂) ∘ (e₁.prod e₂).symm) (e₁ x.1, e₂ x.2) v
      (dMB (f₁ ∘ e₁.symm) (e₁ x.1, v.1), dMB (f₂ ∘ e₂.symm) (e₂ x.2, v.2)) := by
    have h₁' : HasDirDerivAt (fun y : E₁ × E₂ ↦ (f₁ ∘ e₁.symm) y.1) (e₁ x.1, e₂ x.2) v
        (dMB (f₁ ∘ e₁.symm) (e₁ x.1, v.1)) := by simpa [HasDirDerivAt] using h₁
    have h₂' : HasDirDerivAt (fun y : E₁ × E₂ ↦ (f₂ ∘ e₂.symm) y.2) (e₁ x.1, e₂ x.2) v
        (dMB (f₂ ∘ e₂.symm) (e₂ x.2, v.2)) := by simpa [HasDirDerivAt] using h₂
    exact h₁'.prodMk h₂'
  exact h.dMB_eq

/-- The tangent vector `(v₁, v₂)` at `(x₁, x₂)` determined by `v₁ ∈ T_{x₁}M₁`, `v₂ ∈ T_{x₂}M₂`:
the map `TM₁ × TM₂ → T(M₁ × M₂)`. -/
def tangentProdMk (q : TangentBundle E₁ M₁ × TangentBundle E₂ M₂) :
    TangentBundle (ModelProd E₁ E₂) (M₁ × M₂) :=
  ⟨(q.1.proj, q.2.proj), ((q.1.vec, q.2.vec) : E₁ × E₂)⟩

/-- The components `T(M₁ × M₂) → TM₁ × TM₂`. -/
def tangentProdSplit (p : TangentBundle (ModelProd E₁ E₂) (M₁ × M₂)) :
    TangentBundle E₁ M₁ × TangentBundle E₂ M₂ :=
  (⟨p.proj.1, p.vec.1⟩, ⟨p.proj.2, p.vec.2⟩)

/-- `TM₁ × TM₂ → T(M₁ × M₂) → TM₁ × TM₂` is the identity. -/
theorem tangentProdSplit_tangentProdMk (q : TangentBundle E₁ M₁ × TangentBundle E₂ M₂) :
    tangentProdSplit (tangentProdMk q) = q :=
  Prod.ext (TangentBundle.ext_vec rfl rfl) (TangentBundle.ext_vec rfl rfl)

/-- `T(M₁ × M₂) → TM₁ × TM₂ → T(M₁ × M₂)` is the identity. -/
theorem tangentProdMk_tangentProdSplit (p : TangentBundle (ModelProd E₁ E₂) (M₁ × M₂)) :
    tangentProdMk (tangentProdSplit p) = p :=
  TangentBundle.ext_vec rfl rfl

/-- The components of a tangent vector to `M₁ × M₂` are its images under the tangent maps of the
projections. -/
theorem tangentProdSplit_eq (p : TangentBundle (ModelProd E₁ E₂) (M₁ × M₂)) :
    tangentProdSplit p = (tangentMap (ModelProd E₁ E₂) E₁ Prod.fst p,
      tangentMap (ModelProd E₁ E₂) E₂ Prod.snd p) := by
  set c₁ := chartAt E₁ p.proj.1
  set c₂ := chartAt E₂ p.proj.2
  have hU : IsOpen (c₁.target ×ˢ c₂.target) := c₁.open_target.prod c₂.open_target
  have hmem : ((c₁ p.proj.1, c₂ p.proj.2) : E₁ × E₂) ∈ c₁.target ×ˢ c₂.target :=
    ⟨c₁.map_source (mem_chart_source E₁ _), c₂.map_source (mem_chart_source E₂ _)⟩
  refine Prod.ext (TangentBundle.ext_vec rfl ?_) (TangentBundle.ext_vec rfl ?_)
  · have hev : (chartAt E₁ p.proj.1 ∘ Prod.fst ∘ (chartAt (ModelProd E₁ E₂) p.proj).symm) =ᶠ[𝓝
        ((c₁ p.proj.1, c₂ p.proj.2) : E₁ × E₂)] Prod.fst :=
      Filter.eventually_of_mem (hU.mem_nhds hmem) fun y hy ↦ c₁.right_inv hy.1
    change p.vec.1 = dMB (chartAt E₁ p.proj.1 ∘ Prod.fst ∘ (chartAt (ModelProd E₁ E₂) p.proj).symm)
      ((c₁ p.proj.1, c₂ p.proj.2), p.vec)
    rw [dMB_congr_of_eventuallyEq hev]
    exact (((ContinuousLinearMap.fst ℝ E₁ E₂).hasDirDerivAt _ _).dMB_eq).symm
  · have hev : (chartAt E₂ p.proj.2 ∘ Prod.snd ∘ (chartAt (ModelProd E₁ E₂) p.proj).symm) =ᶠ[𝓝
        ((c₁ p.proj.1, c₂ p.proj.2) : E₁ × E₂)] Prod.snd :=
      Filter.eventually_of_mem (hU.mem_nhds hmem) fun y hy ↦ c₂.right_inv hy.2
    change p.vec.2 = dMB (chartAt E₂ p.proj.2 ∘ Prod.snd ∘ (chartAt (ModelProd E₁ E₂) p.proj).symm)
      ((c₁ p.proj.1, c₂ p.proj.2), p.vec)
    rw [dMB_congr_of_eventuallyEq hev]
    exact (((ContinuousLinearMap.snd ℝ E₁ E₂).hasDirDerivAt _ _).dMB_eq).symm

/-- `T(M₁ × M₂) → TM₁ × TM₂` is smooth. -/
theorem smoothMBM_tangentProdSplit :
    SmoothMBM (ModelProd E₁ E₂ × ModelProd E₁ E₂) (ModelProd (E₁ × E₁) (E₂ × E₂))
      (tangentProdSplit (E₁ := E₁) (E₂ := E₂) (M₁ := M₁) (M₂ := M₂)) := by
  intro k
  have h := ContMDiffMBOn.prodMk isOpen_univ
    (ContMDiffMB.tangentMap (smoothMBM_fst (E := E₁) (F := E₂) (M := M₁) (N := M₂) (k + 1)))
    (ContMDiffMB.tangentMap (smoothMBM_snd (E := E₁) (F := E₂) (M := M₁) (N := M₂) (k + 1)))
  have e : (tangentProdSplit (E₁ := E₁) (E₂ := E₂) (M₁ := M₁) (M₂ := M₂)) = fun p ↦
      (tangentMap (ModelProd E₁ E₂) E₁ Prod.fst p, tangentMap (ModelProd E₁ E₂) E₂ Prod.snd p) :=
    funext tangentProdSplit_eq
  rw [e]
  exact h

/-- The regrouping `((a, b), (c, d)) ↦ ((a, c), (b, d))`. -/
def regroupProd : (E₁ × E₁) × (E₂ × E₂) →L[ℝ] (E₁ × E₂) × (E₁ × E₂) :=
  (ContinuousLinearEquiv.prodProdProdComm ℝ E₁ E₁ E₂ E₂ :
    (E₁ × E₁) × (E₂ × E₂) →L[ℝ] (E₁ × E₂) × (E₁ × E₂))

omit [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂] in
/-- `regroupProd ((a, b), (c, d)) = ((a, c), (b, d))`. -/
@[simp]
theorem regroupProd_apply (y : (E₁ × E₁) × (E₂ × E₂)) :
    regroupProd y = ((y.1.1, y.2.1), (y.1.2, y.2.2)) :=
  rfl

/-- The source of the chart of `T(M₁ × M₂)` at `(v₁, v₂)`. -/
theorem mem_chartAt_tangentProdMk_source (q : TangentBundle E₁ M₁ × TangentBundle E₂ M₂)
    (p : TangentBundle (ModelProd E₁ E₂) (M₁ × M₂)) :
    p ∈ (chartAt (ModelProd E₁ E₂ × ModelProd E₁ E₂) (tangentProdMk q)).source ↔
      p.proj.1 ∈ (chartAt E₁ q.1.proj).source ∧ p.proj.2 ∈ (chartAt E₂ q.2.proj).source := by
  rw [chartAt_tangentBundle, mem_tangentChart_source]
  simp only [and_self]
  rfl

/-- In charts, `TM₁ × TM₂ → T(M₁ × M₂)` is the regrouping of the coordinates. -/
theorem chartAt_tangentProdMk (q q' : TangentBundle E₁ M₁ × TangentBundle E₂ M₂)
    (hq' : q'.1.proj ∈ (chartAt E₁ q.1.proj).source ∧ q'.2.proj ∈ (chartAt E₂ q.2.proj).source) :
    chartAt (ModelProd E₁ E₂ × ModelProd E₁ E₂) (tangentProdMk q) (tangentProdMk q') =
      regroupProd (chartAt (ModelProd (E₁ × E₁) (E₂ × E₂)) q q') := by
  have hcc := tangentCoordChange_prod (chart_mem_atlas E₁ q'.1.proj)
    (chart_mem_atlas E₁ q.1.proj) (chart_mem_atlas E₂ q'.2.proj) (chart_mem_atlas E₂ q.2.proj)
    (x := (q'.1.proj, q'.2.proj)) ⟨mem_chart_source _ _, hq'.1⟩ ⟨mem_chart_source _ _, hq'.2⟩
    ((q'.1.vec, q'.2.vec) : E₁ × E₂)
  exact Prod.ext rfl hcc

/-- `TM₁ × TM₂ → T(M₁ × M₂)` is continuous. -/
theorem continuous_tangentProdMk :
    Continuous (tangentProdMk (E₁ := E₁) (E₂ := E₂) (M₁ := M₁) (M₂ := M₂)) := by
  refine continuous_iff_continuousAt.2 fun q ↦ ?_
  set κ := chartAt (ModelProd (E₁ × E₁) (E₂ × E₂)) q
  set κ' := chartAt (ModelProd E₁ E₂ × ModelProd E₁ E₂) (tangentProdMk q)
  have hN : {q' : TangentBundle E₁ M₁ × TangentBundle E₂ M₂ |
      q'.1.proj ∈ (chartAt E₁ q.1.proj).source ∧ q'.2.proj ∈ (chartAt E₂ q.2.proj).source} ∈ 𝓝 q :=
    ((((chartAt E₁ q.1.proj).open_source.preimage
      (tangentBundleCore E₁ M₁).continuous_proj).preimage continuous_fst).inter
        (((chartAt E₂ q.2.proj).open_source.preimage
          (tangentBundleCore E₂ M₂).continuous_proj).preimage continuous_snd)).mem_nhds
      ⟨mem_chart_source _ _, mem_chart_source _ _⟩
  have hq : regroupProd (κ q) ∈ κ'.target := by
    rw [← chartAt_tangentProdMk q q ⟨mem_chart_source _ _, mem_chart_source _ _⟩]
    exact κ'.map_source (mem_chart_source _ _)
  have hκ : ContinuousAt (fun q' ↦ (κ q' : (E₁ × E₁) × (E₂ × E₂))) q :=
    κ.continuousAt (mem_chart_source _ q)
  have hr : ContinuousAt (fun q' ↦ regroupProd (κ q' : (E₁ × E₁) × (E₂ × E₂))) q :=
    regroupProd.continuous.continuousAt.comp hκ
  have h := ContinuousAt.comp (f := fun q' ↦ regroupProd (κ q' : (E₁ × E₁) × (E₂ × E₂))) (x := q)
    (κ'.continuousAt_symm hq) hr
  refine h.congr (Filter.eventually_of_mem hN fun q' hq' ↦ ?_)
  change κ'.symm (regroupProd (κ q')) = tangentProdMk q'
  rw [← chartAt_tangentProdMk q q' hq']
  exact κ'.left_inv ((mem_chartAt_tangentProdMk_source q _).2 hq')

/-- `TM₁ × TM₂ → T(M₁ × M₂)` is smooth. -/
theorem smoothMBM_tangentProdMk :
    SmoothMBM (ModelProd (E₁ × E₁) (E₂ × E₂)) (ModelProd E₁ E₂ × ModelProd E₁ E₂)
      (tangentProdMk (E₁ := E₁) (E₂ := E₂) (M₁ := M₁) (M₂ := M₂)) := by
  intro k
  refine contMDiffMB_of_chartAt continuous_tangentProdMk fun q ↦ ?_
  set κ := chartAt (ModelProd (E₁ × E₁) (E₂ × E₂)) q
  set κ' := chartAt (ModelProd E₁ E₂ × ModelProd E₁ E₂) (tangentProdMk q)
  have hD := isOpen_chartDomain isOpen_univ continuous_tangentProdMk.continuousOn κ κ'
  refine ⟨_, hD, ⟨κ.map_source (mem_chart_source _ q), by
    simp only [mem_preimage, κ.left_inv (mem_chart_source _ q)]
    exact ⟨mem_univ _, show tangentProdMk q ∈ κ'.source from mem_chart_source _ _⟩⟩,
    subset_rfl, ?_⟩
  refine ContDiffMBOn.congr_of_isOpen hD (fun y hy ↦ ?_)
    ((regroupProd.contDiffMBOn k univ).mono (subset_univ _))
  have hy' := (mem_chartAt_tangentProdMk_source q _).1 hy.2.2
  change regroupProd y = κ' (tangentProdMk (κ.symm y))
  rw [chartAt_tangentProdMk q _ hy', κ.right_inv hy.1]

/-- `T(M₁ × M₂) ≅ TM₁ × TM₂` as topological spaces; both directions are smooth
(`smoothMBM_tangentProdSplit`, `smoothMBM_tangentProdMk`). -/
def tangentProdHomeomorph :
    TangentBundle (ModelProd E₁ E₂) (M₁ × M₂) ≃ₜ TangentBundle E₁ M₁ × TangentBundle E₂ M₂ where
  toFun := tangentProdSplit
  invFun := tangentProdMk
  left_inv := tangentProdMk_tangentProdSplit
  right_inv := tangentProdSplit_tangentProdMk
  continuous_toFun := continuousOn_univ.1 (smoothMBM_tangentProdSplit 0).1
  continuous_invFun := continuous_tangentProdMk

end TangentProd

/-! ### Products of local additions: Lemma 3.8.17 -/

section ProdMaps

variable {E₁ E₂ F₁ F₂ : Type u}
  [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁] [IsTopologicalAddGroup E₁]
  [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂] [IsTopologicalAddGroup E₂]
  [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  [AddCommGroup F₁] [Module ℝ F₁] [TopologicalSpace F₁] [IsTopologicalAddGroup F₁]
  [ContinuousSMul ℝ F₁] [LocallyConvexSpace ℝ F₁] [T2Space F₁]
  [AddCommGroup F₂] [Module ℝ F₂] [TopologicalSpace F₂] [IsTopologicalAddGroup F₂]
  [ContinuousSMul ℝ F₂] [LocallyConvexSpace ℝ F₂] [T2Space F₂]
  {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace E₁ M₁] [MBManifold E₁ M₁]
  {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace E₂ M₂] [MBManifold E₂ M₂]
  {N₁ : Type*} [TopologicalSpace N₁] [ChartedSpace F₁ N₁] [MBManifold F₁ N₁]
  {N₂ : Type*} [TopologicalSpace N₂] [ChartedSpace F₂ N₂] [MBManifold F₂ N₂]

/-- Products of smooth maps are smooth. -/
theorem SmoothMBMOn.prodMap {f : M₁ → N₁} {g : M₂ → N₂} {U : Set M₁} {V : Set M₂}
    (hU : IsOpen U) (hV : IsOpen V) (hf : SmoothMBMOn E₁ F₁ f U) (hg : SmoothMBMOn E₂ F₂ g V) :
    SmoothMBMOn (ModelProd E₁ E₂) (ModelProd F₁ F₂) (Prod.map f g) (U ×ˢ V) := by
  intro k
  have hUV := hU.prod hV
  have h₁ : ContMDiffMBOn (E := ModelProd E₁ E₂) (F := E₁) k Prod.fst (U ×ˢ V) :=
    (smoothMBM_fst (E := E₁) (F := E₂) (M := M₁) (N := M₂) k).comp hUV isOpen_univ
      (smoothMBMOn_id hUV k) (mapsTo_univ _ _)
  have h₂ : ContMDiffMBOn (E := ModelProd E₁ E₂) (F := E₂) k Prod.snd (U ×ˢ V) :=
    (smoothMBM_snd (E := E₁) (F := E₂) (M := M₁) (N := M₂) k).comp hUV isOpen_univ
      (smoothMBMOn_id hUV k) (mapsTo_univ _ _)
  exact ContMDiffMBOn.prodMk hUV ((hf k).comp hUV hU h₁ fun p hp ↦ hp.1)
    ((hg k).comp hUV hV h₂ fun p hp ↦ hp.2)

omit [MBManifold E₁ M₁] [MBManifold E₂ M₂] [MBManifold F₁ N₁] [MBManifold F₂ N₂] in
/-- The regrouping `((a, b), (c, d)) ↦ ((a, c), (b, d))` of manifolds is smooth. -/
theorem smoothMBM_prodProdProdComm [MBManifold E₁ M₁] [MBManifold E₂ M₂] [MBManifold F₁ N₁]
    [MBManifold F₂ N₂] :
    SmoothMBM (ModelProd (ModelProd E₁ E₂) (ModelProd F₁ F₂))
      (ModelProd (ModelProd E₁ F₁) (ModelProd E₂ F₂))
      (Homeomorph.prodProdProdComm M₁ M₂ N₁ N₂) := by
  intro k
  have fst₁ := smoothMBM_fst (E := ModelProd E₁ E₂) (F := ModelProd F₁ F₂) (M := M₁ × M₂)
    (N := N₁ × N₂) k
  have snd₁ := smoothMBM_snd (E := ModelProd E₁ E₂) (F := ModelProd F₁ F₂) (M := M₁ × M₂)
    (N := N₁ × N₂) k
  have a := (smoothMBM_fst (E := E₁) (F := E₂) (M := M₁) (N := M₂) k).comp isOpen_univ
    isOpen_univ fst₁ (mapsTo_univ _ _)
  have b := (smoothMBM_snd (E := E₁) (F := E₂) (M := M₁) (N := M₂) k).comp isOpen_univ
    isOpen_univ fst₁ (mapsTo_univ _ _)
  have c := (smoothMBM_fst (E := F₁) (F := F₂) (M := N₁) (N := N₂) k).comp isOpen_univ
    isOpen_univ snd₁ (mapsTo_univ _ _)
  have d := (smoothMBM_snd (E := F₁) (F := F₂) (M := N₁) (N := N₂) k).comp isOpen_univ
    isOpen_univ snd₁ (mapsTo_univ _ _)
  exact ContMDiffMBOn.prodMk isOpen_univ (ContMDiffMBOn.prodMk isOpen_univ a c)
    (ContMDiffMBOn.prodMk isOpen_univ b d)

end ProdMaps

section ProdLocalAddition

variable {E₁ E₂ : Type u}
  [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁] [IsTopologicalAddGroup E₁]
  [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂] [IsTopologicalAddGroup E₂]
  [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace E₁ M₁] [MBManifold E₁ M₁]
  {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace E₂ M₂] [MBManifold E₂ M₂]

namespace LocalAddition

/-- The map `θ` of the product local addition: `T(M₁ × M₂) ≅ TM₁ × TM₂`, followed by `θ₁ × θ₂`
and the regrouping `(M₁ × M₁) × (M₂ × M₂) ≅ (M₁ × M₂) × (M₁ × M₂)`. -/
def prodTheta (A₁ : LocalAddition E₁ M₁) (A₂ : LocalAddition E₂ M₂) :
    OpenPartialHomeomorph (TangentBundle (ModelProd E₁ E₂) (M₁ × M₂)) ((M₁ × M₂) × (M₁ × M₂)) :=
  (tangentProdHomeomorph.toOpenPartialHomeomorph.trans
    (A₁.toOpenPartialHomeomorph.prod A₂.toOpenPartialHomeomorph)).trans
    (Homeomorph.prodProdProdComm M₁ M₁ M₂ M₂).toOpenPartialHomeomorph

/-- `θ(v) = ((θ₁ v₁).1, (θ₂ v₂).1), ((θ₁ v₁).2, (θ₂ v₂).2))` for `v = (v₁, v₂)`. -/
theorem prodTheta_apply (A₁ : LocalAddition E₁ M₁) (A₂ : LocalAddition E₂ M₂)
    (v : TangentBundle (ModelProd E₁ E₂) (M₁ × M₂)) :
    prodTheta A₁ A₂ v = Homeomorph.prodProdProdComm M₁ M₁ M₂ M₂
      (A₁.toOpenPartialHomeomorph (tangentProdSplit v).1,
        A₂.toOpenPartialHomeomorph (tangentProdSplit v).2) :=
  rfl

/-- The domain of the product local addition is `Ω₁ × Ω₂`. -/
theorem mem_prodTheta_source (A₁ : LocalAddition E₁ M₁) (A₂ : LocalAddition E₂ M₂)
    (v : TangentBundle (ModelProd E₁ E₂) (M₁ × M₂)) :
    v ∈ (prodTheta A₁ A₂).source ↔ (tangentProdSplit v).1 ∈ A₁.source ∧
      (tangentProdSplit v).2 ∈ A₂.source := by
  simp [prodTheta, LocalAddition.source, tangentProdHomeomorph]

/-- The image of `θ` for the product local addition is `θ₁(Ω₁) × θ₂(Ω₂)`, regrouped. -/
theorem mem_prodTheta_target (A₁ : LocalAddition E₁ M₁) (A₂ : LocalAddition E₂ M₂)
    (q : (M₁ × M₂) × (M₁ × M₂)) :
    q ∈ (prodTheta A₁ A₂).target ↔ ((q.1.1, q.2.1) : M₁ × M₁) ∈ A₁.toOpenPartialHomeomorph.target ∧
      ((q.1.2, q.2.2) : M₂ × M₂) ∈ A₂.toOpenPartialHomeomorph.target := by
  simp [prodTheta, tangentProdHomeomorph, Homeomorph.prodProdProdComm]

/-- **Glöckner–Neeb, Lemma 3.8.17**: if `Σ₁` and `Σ₂` are local additions on `M₁` and `M₂`, then,
identifying `T(M₁ × M₂)` with `TM₁ × TM₂`, `Σ₁ × Σ₂` is a local addition on `M₁ × M₂`. -/
def prod (A₁ : LocalAddition E₁ M₁) (A₂ : LocalAddition E₂ M₂) :
    LocalAddition (ModelProd E₁ E₂) (M₁ × M₂) where
  toOpenPartialHomeomorph := prodTheta A₁ A₂
  fst_eq v hv := by
    rw [mem_prodTheta_source] at hv
    rw [prodTheta_apply]
    change ((A₁.toOpenPartialHomeomorph (tangentProdSplit v).1).1,
      (A₂.toOpenPartialHomeomorph (tangentProdSplit v).2).1) = v.proj
    rw [A₁.fst_eq _ hv.1, A₂.fst_eq _ hv.2]
    rfl
  smoothMBMOn := by
    have hS : IsOpen (A₁.source ×ˢ A₂.source) := A₁.isOpen_source.prod A₂.isOpen_source
    have h1 := SmoothMBMOn.prodMap A₁.isOpen_source A₂.isOpen_source A₁.smoothMBMOn
      A₂.smoothMBMOn
    have h2 := SmoothMBMOn.comp (prodTheta A₁ A₂).open_source hS h1
      (fun k ↦ (smoothMBM_tangentProdSplit (E₁ := E₁) (E₂ := E₂) (M₁ := M₁) (M₂ := M₂) k).comp
        (prodTheta A₁ A₂).open_source isOpen_univ (smoothMBMOn_id (prodTheta A₁ A₂).open_source k)
        (mapsTo_univ _ _))
      fun v hv ↦ (mem_prodTheta_source A₁ A₂ v).1 hv
    intro k
    have h3 := ContMDiffMBOn.comp (prodTheta A₁ A₂).open_source isOpen_univ
      (smoothMBM_prodProdProdComm (E₁ := E₁) (E₂ := E₁) (F₁ := E₂) (F₂ := E₂) (M₁ := M₁)
        (M₂ := M₁) (N₁ := M₂) (N₂ := M₂) k) (h2 k) (mapsTo_univ _ _)
    exact h3
  smoothMBMOn_symm := by
    intro k
    have hθ := (prodTheta A₁ A₂).open_target
    have hT : IsOpen (A₁.toOpenPartialHomeomorph.target ×ˢ A₂.toOpenPartialHomeomorph.target) :=
      A₁.toOpenPartialHomeomorph.open_target.prod A₂.toOpenPartialHomeomorph.open_target
    have h1 := SmoothMBMOn.prodMap A₁.toOpenPartialHomeomorph.open_target
      A₂.toOpenPartialHomeomorph.open_target A₁.smoothMBMOn_symm A₂.smoothMBMOn_symm k
    have hsw := ContMDiffMBOn.comp hθ isOpen_univ
      (smoothMBM_prodProdProdComm (E₁ := E₁) (E₂ := E₂) (F₁ := E₁) (F₂ := E₂) (M₁ := M₁)
        (M₂ := M₂) (N₁ := M₁) (N₂ := M₂) k) (smoothMBMOn_id hθ k) (mapsTo_univ _ _)
    have h2 := ContMDiffMBOn.comp hθ hT h1 hsw fun q hq ↦ (mem_prodTheta_target A₁ A₂ q).1 hq
    have h3 := ContMDiffMBOn.comp hθ isOpen_univ
      (smoothMBM_tangentProdMk (E₁ := E₁) (E₂ := E₂) (M₁ := M₁) (M₂ := M₂) k) h2
      (mapsTo_univ _ _)
    exact h3
  zero_mem x := by
    rw [mem_prodTheta_source]
    exact ⟨A₁.zero_mem x.1, A₂.zero_mem x.2⟩
  snd_zero x := by
    rw [prodTheta_apply]
    change ((A₁.toOpenPartialHomeomorph ⟨x.1, 0⟩).2, (A₂.toOpenPartialHomeomorph ⟨x.2, 0⟩).2) = x
    rw [A₁.snd_zero, A₂.snd_zero]

end LocalAddition

end ProdLocalAddition

end LocallyConvex.Manifolds
