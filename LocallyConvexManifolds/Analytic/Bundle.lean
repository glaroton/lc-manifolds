/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Analytic.Operations
public import LocallyConvexManifolds.Manifold.LocalDiffeo

/-!
# Real analytic tangent bundles, products, and real analytic local additions

Let `M` be a real analytic manifold modeled on a real locally convex space `E` (no completeness,
`LocallyConvexManifolds.Analytic.Basic`). We show:

* `TangentBundle.realAnalyticManifold`: the tangent bundle `TM` is a real analytic manifold
  modeled on `E × E`. Its transition maps are `(y, w) ↦ (τ y, dσ(i (c⁻¹ y)) w)` for transition maps
  `τ`, `σ` of `M` (`Tangent/Bundle.lean`); the differential of a real analytic map is real analytic
  (`LocallyConvex.Analysis.RealAnalyticOn.dMB`).
* `Prod.realAnalyticManifold`: products of real analytic manifolds are real analytic manifolds;
  `realAnalyticMOn_fst`, `realAnalyticMOn_snd`, `RealAnalyticMOn.prodMk`: projections and pairs.
* `LocalAddition.IsRealAnalytic`: a local addition `Σ` on a real analytic manifold is *real
  analytic* if `θ = (π, Σ)` is a real analytic diffeomorphism onto its (open) image (H. Glöckner,
  K.-H. Neeb, *Infinite-Dimensional Lie Groups*, arXiv:2602.12362v1, p. 325, after
  Definition 3.8.11).

## Implementation notes

* A real analytic manifold is a smooth manifold (`RealAnalyticManifold.mbManifold`), so a
  `LocalAddition` on it makes sense; `IsRealAnalytic` is a property of the smooth local addition.
  Real analytic maps are smooth (`RealAnalyticMOn.smoothMBMOn`), so a real analytic `θ` with real
  analytic inverse already gives the smoothness fields.
* The two maximal atlases (real analytic and smooth) are different; the charted space structure
  of `TM` is built from the atlas of `M`, and here this atlas is assumed real analytic.
-/

@[expose] public section

open Set Filter Function
open scoped Topology Manifold
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe u

/-! ### The tangent bundle of a real analytic manifold -/

section Tangent

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [RealAnalyticManifold E M]

/-- The transition maps of the tangent bundle of a real analytic manifold,
`(y, w) ↦ (τ y, dσ(i (c⁻¹ y)) w)`, are real analytic. -/
theorem realAnalyticOn_tangentChart_transition (i j : atlas E M)
    {c c' : OpenPartialHomeomorph M E} (hc : c ∈ atlas E M) (hc' : c' ∈ atlas E M) :
    RealAnalyticOn ⇑((tangentChart i c).symm ≫ₕ tangentChart j c')
      ((tangentChart i c).symm ≫ₕ tangentChart j c').source := by
  set ψ := tangentChart i c
  set ψ' := tangentChart j c'
  set D := c.target ∩ c.symm ⁻¹' (i.1.source ∩ j.1.source ∩ c'.source)
  have hsrc : (ψ.symm ≫ₕ ψ').source ⊆ D ×ˢ univ := by
    rintro q ⟨hq, hq'⟩
    replace hq : q ∈ ψ.target := hq
    rw [mem_tangentChart_target] at hq
    rw [mem_preimage, mem_tangentChart_source] at hq'
    simp only [OpenPartialHomeomorph.symm_symm] at hq'
    exact ⟨⟨hq.1, ⟨hq.2, hq'.1⟩, hq'.2⟩, mem_univ _⟩
  set G : E × E → E × E := fun q ↦
    (c' (c.symm q.1), dMB (j.1 ∘ i.1.symm) (i.1 (c.symm q.1), q.2))
  have hG : ∀ q ∈ D ×ˢ (univ : Set E), (ψ.symm ≫ₕ ψ') q = G q := by
    rintro q ⟨⟨-, ⟨hi, hj⟩, -⟩, -⟩
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, tangentChart_apply,
      tangentChart_symm_proj, tangentChart_symm_snd,
      tangentCoordChange_comp i _ j ⟨⟨hi, mem_chart_source E _⟩, hj⟩]
    rfl
  have hmax : ∀ {e : OpenPartialHomeomorph M E}, e ∈ atlas E M →
      e ∈ (realAnalyticGroupoid E).maximalAtlas M :=
    fun he ↦ StructureGroupoid.subset_maximalAtlas _ he
  have hfst : RealAnalyticOn (ContinuousLinearMap.fst ℝ E E) (D ×ˢ univ) :=
    (ContinuousLinearMap.fst ℝ E E).realAnalyticOn _
  have hsnd : RealAnalyticOn (ContinuousLinearMap.snd ℝ E E) (D ×ˢ univ) :=
    (ContinuousLinearMap.snd ℝ E E).realAnalyticOn _
  have h1 : RealAnalyticOn ((c' ∘ c.symm) ∘ ContinuousLinearMap.fst ℝ E E) (D ×ˢ univ) :=
    (realAnalyticOn_transition (hmax hc) (hmax hc')).comp hfst fun q hq ↦ ⟨hq.1.1, hq.1.2.2⟩
  have hic : RealAnalyticOn ((i.1 ∘ c.symm) ∘ ContinuousLinearMap.fst ℝ E E) (D ×ˢ univ) :=
    (realAnalyticOn_transition (hmax hc) (hmax i.2)).comp hfst fun q hq ↦ ⟨hq.1.1, hq.1.2.1.1⟩
  have hd : RealAnalyticOn (dMB (j.1 ∘ i.1.symm))
      ((i.1.target ∩ i.1.symm ⁻¹' j.1.source) ×ˢ univ) :=
    RealAnalyticOn.dMB (realAnalyticOn_transition (hmax i.2) (hmax j.2))
      (isOpen_transition_domain i j)
  have h2 := RealAnalyticOn.comp hd (RealAnalyticOn.prodMk hic hsnd)
    fun (q : E × E) (hq : q ∈ D ×ˢ univ) ↦ ⟨⟨i.1.map_source hq.1.2.1.1, by
      simp [i.1.left_inv hq.1.2.1.1, hq.1.2.1.2]⟩, mem_univ _⟩
  exact realAnalyticOn_congr (fun q hq ↦ (hG q (hsrc hq)).symm)
    ((RealAnalyticOn.prodMk h1 h2).mono hsrc)

theorem tangentChart_transition_mem_realAnalyticGroupoid (i j : atlas E M)
    {c c' : OpenPartialHomeomorph M E} (hc : c ∈ atlas E M) (hc' : c' ∈ atlas E M) :
    (tangentChart i c).symm ≫ₕ tangentChart j c' ∈ realAnalyticGroupoid (E × E) := by
  refine ⟨realAnalyticOn_tangentChart_transition i j hc hc', ?_⟩
  have h := realAnalyticOn_tangentChart_transition j i hc' hc
  rw [OpenPartialHomeomorph.trans_source] at h
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm,
    OpenPartialHomeomorph.trans_target, ← OpenPartialHomeomorph.symm_source,
    OpenPartialHomeomorph.symm_target]
  exact h

/-- **The tangent bundle of a real analytic manifold is a real analytic manifold**, modeled on
`E × E`. -/
instance TangentBundle.realAnalyticManifold :
    RealAnalyticManifold (E × E) (TangentBundle E M) where
  compatible := by
    rintro _ _ ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, _, ⟨c, hc, r, hr, rfl⟩, rfl⟩
      ⟨_, ⟨_, ⟨j, rfl⟩, rfl⟩, _, ⟨c', hc', r', hr', rfl⟩, rfl⟩
    rw [chartedSpaceSelf_atlas] at hr hr'
    subst hr hr'
    exact tangentChart_transition_mem_realAnalyticGroupoid i j hc hc'

end Tangent

/-! ### Products -/

section Product

variable {E F : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

/-- Products of real analytic maps are real analytic. -/
theorem RealAnalyticOn.prodMap {g : E → E} {h : F → F} {U : Set E} {V : Set F}
    (hg : RealAnalyticOn g U) (hh : RealAnalyticOn h V) :
    RealAnalyticOn (fun p : E × F ↦ (g p.1, h p.2)) (U ×ˢ V) :=
  RealAnalyticOn.prodMk
    (hg.comp ((ContinuousLinearMap.fst ℝ E F).realAnalyticOn _)
      fun (p : E × F) (hp : p ∈ U ×ˢ V) ↦ hp.1)
    (hh.comp ((ContinuousLinearMap.snd ℝ E F).realAnalyticOn _)
      fun (p : E × F) (hp : p ∈ U ×ˢ V) ↦ hp.2)

/-- The product of two real analytic diffeomorphisms between open sets is one. -/
theorem prod_mem_realAnalyticGroupoid {g : OpenPartialHomeomorph E E}
    {h : OpenPartialHomeomorph F F} (hg : g ∈ realAnalyticGroupoid E)
    (hh : h ∈ realAnalyticGroupoid F) : g.prod h ∈ realAnalyticGroupoid (ModelProd E F) :=
  ⟨RealAnalyticOn.prodMap hg.1 hh.1, RealAnalyticOn.prodMap hg.2 hh.2⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N]

/-- **The product of two real analytic manifolds is a real analytic manifold.** -/
instance Prod.realAnalyticManifold [RealAnalyticManifold E M] [RealAnalyticManifold F N] :
    RealAnalyticManifold (ModelProd E F) (M × N) where
  compatible := by
    rintro _ _ ⟨e, he, f, hf, rfl⟩ ⟨e', he', f', hf', rfl⟩
    rw [OpenPartialHomeomorph.prod_symm_trans_prod]
    exact prod_mem_realAnalyticGroupoid (HasGroupoid.compatible he he')
      (HasGroupoid.compatible hf hf')

/-- The first projection `M × N → M` is real analytic. -/
theorem realAnalyticMOn_fst :
    RealAnalyticMOn (E := ModelProd E F) (F := E) (Prod.fst : M × N → M) univ := by
  refine ⟨continuous_fst.continuousOn, fun x _ ↦ ?_⟩
  set c := chartAt E x.1
  set d := chartAt F x.2
  have hD : chartDomain Prod.fst univ (chartAt (ModelProd E F) x) c ⊆ c.target ×ˢ d.target :=
    fun y hy ↦ hy.1
  refine realAnalyticOn_congr (fun y hy ↦ ?_)
    (((ContinuousLinearMap.fst ℝ E F).realAnalyticOn univ).mono (subset_univ _))
  change y.1 = c (c.symm y.1)
  rw [c.right_inv (hD hy).1]

/-- The second projection `M × N → N` is real analytic. -/
theorem realAnalyticMOn_snd :
    RealAnalyticMOn (E := ModelProd E F) (F := F) (Prod.snd : M × N → N) univ := by
  refine ⟨continuous_snd.continuousOn, fun x _ ↦ ?_⟩
  set c := chartAt E x.1
  set d := chartAt F x.2
  have hD : chartDomain Prod.snd univ (chartAt (ModelProd E F) x) d ⊆ c.target ×ˢ d.target :=
    fun y hy ↦ hy.1
  refine realAnalyticOn_congr (fun y hy ↦ ?_)
    (((ContinuousLinearMap.snd ℝ E F).realAnalyticOn univ).mono (subset_univ _))
  change y.2 = d (d.symm y.2)
  rw [d.right_inv (hD hy).2]

/-- A pair of real analytic maps into `M` and `N` is a real analytic map into `M × N`. -/
theorem RealAnalyticMOn.prodMk {G : Type u} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G]
    {P : Type*} [TopologicalSpace P] [ChartedSpace G P] {f : P → M} {g : P → N}
    {U : Set P} (hf : RealAnalyticMOn (E := G) (F := E) f U)
    (hg : RealAnalyticMOn (E := G) (F := F) g U) :
    RealAnalyticMOn (E := G) (F := ModelProd E F) (fun p ↦ (f p, g p)) U := by
  refine ⟨hf.1.prodMk hg.1, fun x hx ↦ ?_⟩
  have hD : chartDomain (fun p ↦ (f p, g p)) U (chartAt G x) (chartAt (ModelProd E F) (f x, g x))
      ⊆ chartDomain f U (chartAt G x) (chartAt E (f x)) ∩
        chartDomain g U (chartAt G x) (chartAt F (g x)) :=
    fun y hy ↦ ⟨⟨hy.1, hy.2.1, hy.2.2.1⟩, ⟨hy.1, hy.2.1, hy.2.2.2⟩⟩
  exact (RealAnalyticOn.prodMk ((hf.2 x hx).mono inter_subset_left)
    ((hg.2 x hx).mono inter_subset_right)).mono hD

/-- A pair of real analytic maps into the model spaces `E`, `F` is a real analytic map into the
model space `E × F` (with its own chart, not the product structure `ModelProd E F`). -/
theorem RealAnalyticMOn.prodMk_model {G : Type u} [AddCommGroup G] [Module ℝ G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G]
    [T2Space G] {P : Type*} [TopologicalSpace P] [ChartedSpace G P] {f : P → E}
    {g : P → F} {U : Set P} (hf : RealAnalyticMOn (E := G) (F := E) f U)
    (hg : RealAnalyticMOn (E := G) (F := F) g U) :
    RealAnalyticMOn (E := G) (F := E × F) (fun p ↦ (f p, g p)) U := by
  refine ⟨hf.1.prodMk hg.1, fun x hx ↦ ?_⟩
  have h1 := (hf.2 x hx).mono (U' := chartDomain (fun p ↦ (f p, g p)) U (chartAt G x)
    (chartAt (E × F) (f x, g x))) fun y hy ↦ ⟨hy.1, hy.2.1, mem_univ _⟩
  have h2 := (hg.2 x hx).mono (U' := chartDomain (fun p ↦ (f p, g p)) U (chartAt G x)
    (chartAt (E × F) (f x, g x))) fun y hy ↦ ⟨hy.1, hy.2.1, mem_univ _⟩
  exact RealAnalyticOn.prodMk h1 h2

end Product

/-! ### Elementary properties of real analytic maps -/

section Maps

variable {E F : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N]

/-- Restriction of a real analytic map to a smaller set. -/
theorem RealAnalyticMOn.mono {f : M → N} {U V : Set M}
    (hf : RealAnalyticMOn (E := E) (F := F) f U) (hVU : V ⊆ U) :
    RealAnalyticMOn (E := E) (F := F) f V :=
  ⟨hf.1.mono hVU, fun x hx ↦ (hf.2 x (hVU hx)).mono fun _ hy ↦ ⟨hy.1, hVU hy.2.1, hy.2.2⟩⟩

/-- Real analyticity only depends on the values on the set. -/
theorem RealAnalyticMOn.congr {f g : M → N} {U : Set M}
    (hf : RealAnalyticMOn (E := E) (F := F) f U) (h : EqOn f g U) :
    RealAnalyticMOn (E := E) (F := F) g U := by
  refine ⟨hf.1.congr fun x hx ↦ (h hx).symm, fun x hx ↦ ?_⟩
  have hD : chartDomain g U (chartAt E x) (chartAt F (g x)) =
      chartDomain f U (chartAt E x) (chartAt F (f x)) := by
    ext y
    simp only [chartDomain, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      rw [h h2, h hx]; exact h3
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      rw [← h h2, ← h hx]; exact h3
  rw [hD]
  refine realAnalyticOn_congr (fun y hy ↦ ?_) (hf.2 x hx)
  simp only [comp_apply, h hy.2.1, h hx]

end Maps

/-! ### Real analytic local additions -/

section LocalAddition

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [RealAnalyticManifold E M]

/-- **Real analytic local additions** (Glöckner–Neeb, p. 325, after Definition 3.8.11): a local
addition `Σ` on a real analytic manifold is real analytic if `θ = (π, Σ)` is a diffeomorphism of
real analytic manifolds from its domain onto its (open) image in `M × M`. -/
def LocalAddition.IsRealAnalytic (A : LocalAddition E M) : Prop :=
  RealAnalyticMOn (E := E × E) (F := ModelProd E E) A.toOpenPartialHomeomorph
      A.toOpenPartialHomeomorph.source ∧
    RealAnalyticMOn (E := ModelProd E E) (F := E × E) A.toOpenPartialHomeomorph.symm
      A.toOpenPartialHomeomorph.target

/-- The local addition `Σ = pr₂ ∘ θ` of a real analytic local addition is real analytic. -/
theorem LocalAddition.IsRealAnalytic.realAnalyticMOn_toFun {A : LocalAddition E M}
    (hA : A.IsRealAnalytic) : RealAnalyticMOn (E := E × E) (F := E) A.toFun A.source :=
  RealAnalyticMOn.comp A.isOpen_source isOpen_univ (realAnalyticMOn_snd (M := M) (N := M))
    hA.1 (mapsTo_univ _ _)

end LocalAddition

end LocallyConvex.Manifolds
