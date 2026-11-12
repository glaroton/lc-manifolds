/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.MappingSpace.Basic

/-!
# Smooth maps between atlases with varying models

Manifolds of mappings are not pure: the chart of `C^ℓ(M, N)` at `f` is modeled on the space `Γ_f` of
sections along `f`, which depends on `f`. They are therefore presented as atlases with varying
models (`VaryingAtlas`, compare [GN26, Definition 3.2.13]). This file develops the basic theory of
`C^k` maps between such atlases. A manifold with a single model is an atlas with varying models
through all the charts of its atlas (`VaryingAtlas.ofChartedSpace`), so the theory covers maps from
and into manifolds of the library as well.

## Main definitions

* `VaryingAtlas.ContMDiffOn A B k f U`: `f` is continuous on `U` and its local representatives
  `ψ_j ∘ f ∘ φ_i⁻¹`, for all charts `φ_i` of `A` and `ψ_j` of `B`, are `C^k` in the sense of
  Michal–Bastiani on their domains; `SmoothOn`, `Smooth`: for all `k ∈ ℕ`.
* `VaryingAtlas.ofChartedSpace G M`: a manifold modeled on `G`, as an atlas with varying models.
* `VaryingAtlas.Equivalent A A'`: the identity is smooth in both directions;
  `VaryingAtlas.Compatible A A'`: all the transition maps between charts of `A` and of `A'` are
  smooth; `VaryingAtlas.union A A' h`: the union of two compatible atlases.

## Main results

* `VaryingAtlas.contMDiffOn_iff_local`: **chart independence**, it suffices to check one pair of
  charts around each point.
* `VaryingAtlas.ContMDiffOn.comp`, `VaryingAtlas.smoothOn_id`, `VaryingAtlas.ContMDiffOn.mono`:
  composition, identity, restriction.
* `VaryingAtlas.contMDiffOn_ofChartedSpace_iff`: for manifolds with a single model, these are the
  `C^k` maps of the library (`ContMDiffMBOn`).
* `VaryingAtlas.smoothOn_chart`, `VaryingAtlas.smoothOn_chart_symm`: charts are smooth, with smooth
  inverses.
* `VaryingAtlas.equivalent_iff_compatible`: two atlases define the same smooth structure if and
  only if they are compatible, that is, if and only if their union is an atlas.
* `VaryingAtlas.TangentSpace A x`: the tangent space at `x`, the model of the preferred chart
  `A.chartAt x`; `VaryingAtlas.tangentCoordChangeEquiv`: the changes of tangent coordinates
  `d(φ_j ∘ φ_i⁻¹)(φ_i x)` are isomorphisms of topological vector spaces, with the cocycle
  condition (`VaryingAtlas.tangentCoordChange_comp`, `VaryingAtlas.tangentCoordChange_self`).
* `VaryingAtlas.tangentMapAt`: the tangent map `T_x f` of a `C^1` map;
  `VaryingAtlas.dMB_chart_eq_tangentMapAt`: in any charts it is `T_x f` conjugated by the changes
  of tangent coordinates, so it does not depend on the preferred charts.

## Implementation notes

* Only `k ∈ ℕ` is an argument; `k = ∞` is the conjunction over `k ∈ ℕ` (`SmoothOn`), as for
  `ContDiffMBOn` and `SmoothMBOn` in [LCA].
* All the model spaces of the atlases involved live in one universe.
* An atlas with varying models comes with a preferred chart at each point (`VaryingAtlas.chartAt`),
  as Mathlib's `ChartedSpace`; tangent spaces are the models of the preferred charts. This is the
  kinematic tangent space in chart coordinates; in infinite dimensions it need not agree with the
  operational tangent space (derivations).

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
* [glaroton, *lc-analysis: Michal–Bastiani calculus on locally convex spaces*][LCA]
-/

@[expose] public section

open Set Function TopologicalSpace
open scoped Topology
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe u

attribute [instance] VaryingAtlas.addCommGroup VaryingAtlas.module VaryingAtlas.topologicalSpace
  VaryingAtlas.isTopologicalAddGroup VaryingAtlas.continuousSMul VaryingAtlas.locallyConvexSpace
  VaryingAtlas.t2Space

namespace VaryingAtlas

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

section Defs

variable (A : VaryingAtlas.{u, _, _} X) (B : VaryingAtlas.{u, _, _} Y)

/-- **`C^k` maps between atlases with varying models**: `f` is continuous on the open set `U`,
and its local representatives `ψ_j ∘ f ∘ φ_i⁻¹` in all pairs of charts are `C^k` in the sense of
Michal–Bastiani on their (open) domains. -/
def ContMDiffOn (k : ℕ) (f : X → Y) (U : Set X) : Prop :=
  ContinuousOn f U ∧ ∀ i j, ContDiffMBOn k (B.chart j ∘ f ∘ (A.chart i).symm)
    (chartDomain f U (A.chart i) (B.chart j))

/-- Smooth maps on `U`: `C^k` for every `k ∈ ℕ`. -/
def SmoothOn (f : X → Y) (U : Set X) : Prop := ∀ k, A.ContMDiffOn B k f U

/-- Smooth maps. -/
def Smooth (f : X → Y) : Prop := A.SmoothOn B f univ

end Defs

variable {A : VaryingAtlas.{u, _, _} X} {B : VaryingAtlas.{u, _, _} Y}
  {C : VaryingAtlas.{u, _, _} Z}

/-- Transition maps are smooth. -/
theorem smoothMBOn_chart_trans (A : VaryingAtlas.{u, _, _} X) (i i' : A.ι) :
    SmoothMBOn (A.chart i' ∘ (A.chart i).symm)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (A.chart i').source) :=
  A.smoothMBOn_transition i i'

/-- `C^k` maps are continuous. -/
theorem ContMDiffOn.continuousOn {k : ℕ} {f : X → Y} {U : Set X} (hf : A.ContMDiffOn B k f U) :
    ContinuousOn f U :=
  hf.1

/-- The local representatives of a `C^k` map are `C^k`. -/
theorem ContMDiffOn.contDiffMBOn {k : ℕ} {f : X → Y} {U : Set X} (hf : A.ContMDiffOn B k f U)
    (i : A.ι) (j : B.ι) :
    ContDiffMBOn k (B.chart j ∘ f ∘ (A.chart i).symm) (chartDomain f U (A.chart i) (B.chart j)) :=
  hf.2 i j

/-- **Chart independence**: a continuous map is `C^k` on the open set `U` as soon as, around each
point `x` of `U`, one of its local representatives (in a chart `φ_i` at `x`) is `C^k` near
`φ_i(x)`. -/
theorem contMDiffOn_of_local {k : ℕ} {f : X → Y} {U : Set X} (hU : IsOpen U)
    (hf : ContinuousOn f U)
    (h : ∀ x ∈ U, ∃ (i : A.ι) (j : B.ι) (O : Set (A.model i)), x ∈ (A.chart i).source ∧
      IsOpen O ∧ A.chart i x ∈ O ∧ O ⊆ chartDomain f U (A.chart i) (B.chart j) ∧
      ContDiffMBOn k (B.chart j ∘ f ∘ (A.chart i).symm) O) :
    A.ContMDiffOn B k f U := by
  refine ⟨hf, fun i' j' ↦ ?_⟩
  set e := A.chart i'
  set e' := B.chart j'
  have hD := isOpen_chartDomain hU hf e e'
  refine ContDiffMBOn.of_local hD fun y hy ↦ ?_
  obtain ⟨hye, hyU, hyf⟩ := hy
  set p := e.symm y
  obtain ⟨i, j, O, hpc, hO, hpO, hOD, hμ⟩ := h p hyU
  set c := A.chart i
  set c' := B.chart j
  -- near `y`, `e' ∘ f ∘ e⁻¹ = (e' ∘ c'⁻¹) ∘ (c' ∘ f ∘ c⁻¹) ∘ (c ∘ e⁻¹)`
  have hτ : ContDiffMBOn k (c ∘ e.symm) (e.target ∩ e.symm ⁻¹' c.source) :=
    A.smoothMBOn_transition i' i k
  have hτc : ContinuousOn (c ∘ e.symm) (e.target ∩ e.symm ⁻¹' c.source) := hτ.continuousOn
  set W := (e.target ∩ e.symm ⁻¹' (U ∩ c.source ∩ f ⁻¹' e'.source)) ∩ (c ∘ e.symm) ⁻¹' O
  have hW : IsOpen W := by
    have h1 : IsOpen (e.target ∩ e.symm ⁻¹' (U ∩ c.source ∩ f ⁻¹' e'.source)) :=
      e.isOpen_inter_preimage_symm ((hf.mono inter_subset_left).isOpen_inter_preimage
        (hU.inter c.open_source) e'.open_source)
    exact (hτc.mono fun z (hz : z ∈ e.target ∩ e.symm ⁻¹' (U ∩ c.source ∩ f ⁻¹' e'.source)) ↦
      ⟨hz.1, hz.2.1.2⟩).isOpen_inter_preimage h1 hO
  have hyW : y ∈ W := ⟨⟨hye, ⟨hyU, hpc⟩, hyf⟩, hpO⟩
  set T := c'.target ∩ c'.symm ⁻¹' e'.source
  have hT : IsOpen T := c'.isOpen_inter_preimage_symm e'.open_source
  have hτ' : ContDiffMBOn k (e' ∘ c'.symm) T := B.smoothMBOn_transition j j' k
  have h2 : MapsTo (c' ∘ f ∘ c.symm) (O ∩ (c' ∘ f ∘ c.symm) ⁻¹' T) T := fun z hz ↦ hz.2
  have hOT : IsOpen (O ∩ (c' ∘ f ∘ c.symm) ⁻¹' T) := hμ.continuousOn.isOpen_inter_preimage hO hT
  have hzc' : ∀ z ∈ W, f (e.symm z) ∈ c'.source := by
    rintro z ⟨⟨-, ⟨-, hzc⟩, -⟩, hzO⟩
    have := (hOD hzO).2.2
    change f (c.symm (c (e.symm z))) ∈ c'.source at this
    rwa [c.left_inv hzc] at this
  have h1' : MapsTo (c ∘ e.symm) W (O ∩ (c' ∘ f ∘ c.symm) ⁻¹' T) := by
    intro z hz
    have hz' := hzc' z hz
    obtain ⟨⟨-, ⟨-, hzc⟩, hzf⟩, hzO⟩ := hz
    have hcz : c.symm (c (e.symm z)) = e.symm z := c.left_inv hzc
    refine ⟨hzO, ?_⟩
    refine ⟨by simp only [Function.comp_apply, hcz]; exact c'.map_source hz', ?_⟩
    simp only [Function.comp_apply, mem_preimage, hcz, c'.left_inv hz']
    exact hzf
  have hcomp := (hτ'.comp hOT hT (hμ.mono inter_subset_left) h2).comp hW hOT
    (hτ.mono fun z hz ↦ ⟨hz.1.1, hz.1.2.1.2⟩) h1'
  refine ⟨W, hW, hyW, (ContDiffMBOn.congr_of_isOpen hW ?_ hcomp).mono inter_subset_right⟩
  intro z hz
  have hcz : c.symm (c (e.symm z)) = e.symm z := c.left_inv hz.1.2.1.2
  change e' (c'.symm (c' (f (c.symm (c (e.symm z)))))) = e' (f (e.symm z))
  rw [hcz, c'.left_inv (hzc' z hz)]

/-- **Chart independence**: a map is `C^k` on the open set `U` if and only if it is continuous and,
around each point of `U`, one of its local representatives is `C^k`. -/
theorem contMDiffOn_iff_local {k : ℕ} {f : X → Y} {U : Set X} (hU : IsOpen U) :
    A.ContMDiffOn B k f U ↔ ContinuousOn f U ∧
      ∀ x ∈ U, ∃ (i : A.ι) (j : B.ι) (O : Set (A.model i)), x ∈ (A.chart i).source ∧
        IsOpen O ∧ A.chart i x ∈ O ∧ O ⊆ chartDomain f U (A.chart i) (B.chart j) ∧
        ContDiffMBOn k (B.chart j ∘ f ∘ (A.chart i).symm) O := by
  refine ⟨fun hf ↦ ⟨hf.1, fun x hx ↦ ?_⟩, fun h ↦ contMDiffOn_of_local hU h.1 h.2⟩
  obtain ⟨i, hi⟩ := A.exists_mem_source x
  obtain ⟨j, hj⟩ := B.exists_mem_source (f x)
  refine ⟨i, j, _, hi, isOpen_chartDomain hU hf.1 _ _, ⟨(A.chart i).map_source hi, ?_⟩,
    subset_rfl, hf.2 i j⟩
  simp only [mem_preimage, (A.chart i).left_inv hi]
  exact ⟨hx, hj⟩

/-- `C^k` maps are `C^l` for `l ≤ k`. -/
theorem ContMDiffOn.of_le {k l : ℕ} {f : X → Y} {U : Set X} (hf : A.ContMDiffOn B k f U)
    (hlk : l ≤ k) : A.ContMDiffOn B l f U :=
  ⟨hf.1, fun i j ↦ (hf.2 i j).of_le hlk⟩

/-- Restriction of `C^k` maps to smaller sets. -/
theorem ContMDiffOn.mono {k : ℕ} {f : X → Y} {U V : Set X} (hf : A.ContMDiffOn B k f U)
    (hVU : V ⊆ U) : A.ContMDiffOn B k f V :=
  ⟨hf.1.mono hVU, fun i j ↦ (hf.2 i j).mono fun _ hx ↦ ⟨hx.1, hVU hx.2.1, hx.2.2⟩⟩

/-- `C^k` maps only depend on their values on the open set. -/
theorem ContMDiffOn.congr {k : ℕ} {f g : X → Y} {U : Set X} (hf : A.ContMDiffOn B k f U)
    (hU : IsOpen U) (heq : EqOn f g U) : A.ContMDiffOn B k g U := by
  refine ⟨hf.1.congr fun x hx ↦ (heq hx).symm, fun i j ↦ ?_⟩
  have hD : chartDomain g U (A.chart i) (B.chart j) = chartDomain f U (A.chart i) (B.chart j) := by
    ext y
    simp only [chartDomain, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by rw [heq h2]; exact h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by rw [← heq h2]; exact h3⟩
  rw [hD]
  refine (hf.2 i j).congr_of_isOpen (isOpen_chartDomain hU hf.1 _ _) fun y hy ↦ ?_
  simp only [Function.comp_apply, heq hy.2.1]

/-- **Compositions of `C^k` maps are `C^k`.** -/
theorem ContMDiffOn.comp {k : ℕ} {f : X → Y} {g : Y → Z} {U : Set X} {V : Set Y}
    (hU : IsOpen U) (hV : IsOpen V) (hg : B.ContMDiffOn C k g V) (hf : A.ContMDiffOn B k f U)
    (hUV : MapsTo f U V) : A.ContMDiffOn C k (g ∘ f) U := by
  have hgf : ContinuousOn (g ∘ f) U := hg.1.comp hf.1 hUV
  refine contMDiffOn_of_local hU hgf fun x hx ↦ ?_
  obtain ⟨i, hi⟩ := A.exists_mem_source x
  obtain ⟨j, hj⟩ := B.exists_mem_source (f x)
  obtain ⟨l, hl⟩ := C.exists_mem_source (g (f x))
  set c := A.chart i
  set d := B.chart j
  set c'' := C.chart l
  set W := chartDomain f U c d ∩ chartDomain (g ∘ f) U c c''
  have hW : IsOpen W := (isOpen_chartDomain hU hf.1 c d).inter (isOpen_chartDomain hU hgf c c'')
  have hxW : c x ∈ W := by
    refine ⟨⟨c.map_source hi, ?_⟩, ⟨c.map_source hi, ?_⟩⟩ <;>
      simp only [mem_preimage, c.left_inv hi]
    · exact ⟨hx, hj⟩
    · exact ⟨hx, hl⟩
  have hmaps : MapsTo (d ∘ f ∘ c.symm) W (chartDomain g V d c'') := by
    rintro z ⟨⟨-, hzU, hzd⟩, -, -, hzg⟩
    refine ⟨d.map_source hzd, ?_, ?_⟩
    · simp only [Function.comp_apply, d.left_inv hzd]; exact hUV hzU
    · simp only [Function.comp_apply, mem_preimage, d.left_inv hzd]; exact hzg
  have hcomp := (hg.2 j l).comp hW (isOpen_chartDomain hV hg.1 d c'')
    ((hf.2 i j).mono inter_subset_left) hmaps
  refine ⟨i, l, W, hi, hW, hxW, inter_subset_right,
    ContDiffMBOn.congr_of_isOpen hW ?_ hcomp⟩
  rintro z ⟨⟨-, -, hzd⟩, -⟩
  have hzd' : (B.chart j).symm (B.chart j (f ((A.chart i).symm z))) = f ((A.chart i).symm z) :=
    d.left_inv hzd
  simp only [Function.comp_apply, hzd']

/-- Compositions of smooth maps are smooth. -/
theorem SmoothOn.comp {f : X → Y} {g : Y → Z} {U : Set X} {V : Set Y} (hU : IsOpen U)
    (hV : IsOpen V) (hg : B.SmoothOn C g V) (hf : A.SmoothOn B f U) (hUV : MapsTo f U V) :
    A.SmoothOn C (g ∘ f) U :=
  fun k ↦ (hg k).comp hU hV (hf k) hUV

/-- Compositions of smooth maps are smooth. -/
theorem Smooth.comp {f : X → Y} {g : Y → Z} (hg : B.Smooth C g) (hf : A.Smooth B f) :
    A.Smooth C (g ∘ f) :=
  SmoothOn.comp isOpen_univ isOpen_univ hg hf (mapsTo_univ _ _)

/-- The domain of the local representative of the identity is the domain of the transition
map. -/
theorem chartDomain_id (A A' : VaryingAtlas.{u, _, _} X) (i : A.ι) (i' : A'.ι) :
    chartDomain id univ (A.chart i) (A'.chart i') =
      (A.chart i).target ∩ (A.chart i).symm ⁻¹' (A'.chart i').source := by
  ext y
  simp [chartDomain]

/-- **The identity is smooth.** -/
theorem smoothOn_id (A : VaryingAtlas.{u, _, _} X) (U : Set X) : A.SmoothOn A id U :=
  fun k ↦ ⟨continuousOn_id, fun i i' ↦ (A.smoothMBOn_transition i i' k).mono fun _ hy ↦
    ⟨hy.1, hy.2.2⟩⟩

/-! ### Manifolds with a single model as atlases with varying models -/

section OfChartedSpace

variable (G : Type u) [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
  [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G]
  (M : Type*) [TopologicalSpace M] [ChartedSpace G M] [MBManifold G M]

/-- A manifold modeled on `G`, as an atlas with varying models: all its charts, each modeled on
`G`. -/
def ofChartedSpace : VaryingAtlas.{u, _, _} M where
  ι := atlas G M
  model _ := G
  chart e := e.1
  chartAt x := ⟨_root_.chartAt G x, chart_mem_atlas G x⟩
  mem_chartAt_source x := mem_chart_source G x
  smoothMBOn_transition e e' := LocallyConvex.Manifolds.smoothMBOn_transition e.2 e'.2

variable {G M}
variable {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N] [MBManifold F N]

/-- For manifolds with a single model, `C^k` maps in the sense of atlases with varying models are
the `C^k` maps of the library (`ContMDiffMBOn`). -/
theorem contMDiffOn_ofChartedSpace_iff {k : ℕ} {f : M → N} {U : Set M} (hU : IsOpen U) :
    (ofChartedSpace G M).ContMDiffOn (ofChartedSpace F N) k f U ↔
      ContMDiffMBOn (E := G) (F := F) k f U :=
  ⟨fun h ↦ ⟨h.1, fun x _ ↦ h.2 ⟨_root_.chartAt G x, chart_mem_atlas G x⟩
    ⟨_root_.chartAt F (f x), chart_mem_atlas F (f x)⟩⟩,
    fun h ↦ ⟨h.1, fun e e' ↦ h.contDiffMBOn_chart hU e.2 e'.2⟩⟩

/-- The model space as a manifold: `C^k` maps into it are the maps whose compositions with the
charts are `C^k`. -/
theorem contMDiffOn_ofChartedSpace_self_iff {k : ℕ} {f : X → F} {U : Set X} :
    A.ContMDiffOn (ofChartedSpace F F) k f U ↔
      ContinuousOn f U ∧ ∀ i, ContDiffMBOn k (f ∘ (A.chart i).symm)
        ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) := by
  have hD : ∀ i, chartDomain f U (A.chart i) (OpenPartialHomeomorph.refl F) =
      (A.chart i).target ∩ (A.chart i).symm ⁻¹' U := fun i ↦ by
    ext y; simp [chartDomain]
  constructor
  · intro h
    refine ⟨h.1, fun i ↦ ?_⟩
    have := h.2 i ⟨OpenPartialHomeomorph.refl F, chartedSpaceSelf_atlas.2 rfl⟩
    change ContDiffMBOn k (f ∘ (A.chart i).symm)
      (chartDomain f U (A.chart i) (OpenPartialHomeomorph.refl F)) at this
    rw [hD] at this
    exact this
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun i ⟨e, he⟩ ↦ ?_⟩
    obtain rfl : e = OpenPartialHomeomorph.refl F := chartedSpaceSelf_atlas.1 he
    change ContDiffMBOn k (f ∘ (A.chart i).symm)
      (chartDomain f U (A.chart i) (OpenPartialHomeomorph.refl F))
    rw [hD]
    exact h2 i

end OfChartedSpace

/-! ### Charts are smooth -/

/-- **Charts are smooth** on their domains, as maps into their model spaces. -/
theorem smoothOn_chart (A : VaryingAtlas.{u, _, _} X) (i : A.ι) :
    A.SmoothOn (ofChartedSpace (A.model i) (A.model i)) (A.chart i) (A.chart i).source := by
  intro k
  refine contMDiffOn_ofChartedSpace_self_iff.2 ⟨(A.chart i).continuousOn, fun i' ↦ ?_⟩
  exact (A.smoothMBOn_transition i' i k).mono fun _ hy ↦ hy

/-- **Inverses of charts are smooth** on the targets. -/
theorem smoothOn_chart_symm (A : VaryingAtlas.{u, _, _} X) (i : A.ι) :
    (ofChartedSpace (A.model i) (A.model i)).SmoothOn A (A.chart i).symm (A.chart i).target := by
  intro k
  refine ⟨(A.chart i).continuousOn_symm, fun ⟨e, he⟩ j ↦ ?_⟩
  obtain rfl : e = OpenPartialHomeomorph.refl (A.model i) := chartedSpaceSelf_atlas.1 he
  refine (A.smoothMBOn_transition i j k).mono fun y hy ↦ ⟨hy.2.1, hy.2.2⟩

/-! ### Equivalent atlases -/

/-- Two atlases with varying models on the same space **define the same smooth structure** if the
identity is smooth in both directions. -/
def Equivalent (A A' : VaryingAtlas.{u, _, _} X) : Prop := A.Smooth A' id ∧ A'.Smooth A id

/-- Two atlases are **compatible** if all the transition maps between their charts are smooth. -/
def Compatible (A A' : VaryingAtlas.{u, _, _} X) : Prop :=
  ∀ i i', SmoothMBOn (A'.chart i' ∘ (A.chart i).symm)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (A'.chart i').source) ∧
    SmoothMBOn (A.chart i ∘ (A'.chart i').symm)
      ((A'.chart i').target ∩ (A'.chart i').symm ⁻¹' (A.chart i).source)

/-- The identity `A → A'` is smooth if and only if the transition maps from the charts of `A` to
those of `A'` are smooth. -/
theorem smooth_id_iff (A A' : VaryingAtlas.{u, _, _} X) :
    A.Smooth A' id ↔ ∀ i i', SmoothMBOn (A'.chart i' ∘ (A.chart i).symm)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (A'.chart i').source) := by
  constructor
  · intro h i i' k
    have := (h k).2 i i'
    rwa [chartDomain_id] at this
  · intro h k
    refine ⟨continuousOn_id, fun i i' ↦ ?_⟩
    rw [chartDomain_id]
    exact h i i' k

/-- **Two atlases define the same smooth structure if and only if they are compatible.** -/
theorem equivalent_iff_compatible (A A' : VaryingAtlas.{u, _, _} X) :
    A.Equivalent A' ↔ A.Compatible A' := by
  rw [Equivalent, smooth_id_iff, smooth_id_iff]
  exact ⟨fun h i i' ↦ ⟨h.1 i i', h.2 i' i⟩, fun h ↦ ⟨fun i i' ↦ (h i i').1, fun i' i ↦ (h i i').2⟩⟩

/-- **The union of two compatible atlases** is an atlas with varying models. -/
def union (A A' : VaryingAtlas.{u, _, _} X) (h : A.Compatible A') : VaryingAtlas.{u, _, _} X where
  ι := A.ι ⊕ A'.ι
  model := Sum.elim A.model A'.model
  addCommGroup i := match i with
    | .inl a => A.addCommGroup a
    | .inr b => A'.addCommGroup b
  module i := match i with
    | .inl a => A.module a
    | .inr b => A'.module b
  topologicalSpace i := match i with
    | .inl a => A.topologicalSpace a
    | .inr b => A'.topologicalSpace b
  isTopologicalAddGroup i := match i with
    | .inl a => A.isTopologicalAddGroup a
    | .inr b => A'.isTopologicalAddGroup b
  continuousSMul i := match i with
    | .inl a => A.continuousSMul a
    | .inr b => A'.continuousSMul b
  locallyConvexSpace i := match i with
    | .inl a => A.locallyConvexSpace a
    | .inr b => A'.locallyConvexSpace b
  t2Space i := match i with
    | .inl a => A.t2Space a
    | .inr b => A'.t2Space b
  chart i := match i with
    | .inl a => A.chart a
    | .inr b => A'.chart b
  chartAt x := .inl (A.chartAt x)
  mem_chartAt_source x := A.mem_chartAt_source x
  smoothMBOn_transition i j := match i, j with
    | .inl a, .inl b => A.smoothMBOn_transition a b
    | .inl a, .inr b => (h a b).1
    | .inr a, .inl b => (h b a).2
    | .inr a, .inr b => A'.smoothMBOn_transition a b


/-! ### Tangent spaces and tangent maps -/

section Tangent

variable (A : VaryingAtlas.{u, _, _} X)

/-- **The tangent space** of an atlas with varying models at `x`: the model space of the preferred
chart at `x`. Other charts at `x` give isomorphic spaces, through the derivatives of the transition
maps (`VaryingAtlas.tangentCoordChangeEquiv`). -/
def TangentSpace (x : X) : Type u := A.model (A.chartAt x)

/-- The tangent space carries the structure of the model space. -/
instance (x : X) : AddCommGroup (A.TangentSpace x) :=
  inferInstanceAs (AddCommGroup (A.model (A.chartAt x)))

/-- The tangent space carries the structure of the model space. -/
instance (x : X) : Module ℝ (A.TangentSpace x) := inferInstanceAs (Module ℝ (A.model (A.chartAt x)))

/-- The tangent space carries the structure of the model space. -/
instance (x : X) : TopologicalSpace (A.TangentSpace x) :=
  inferInstanceAs (TopologicalSpace (A.model (A.chartAt x)))

/-- The tangent space carries the structure of the model space. -/
instance (x : X) : IsTopologicalAddGroup (A.TangentSpace x) :=
  inferInstanceAs (IsTopologicalAddGroup (A.model (A.chartAt x)))

/-- The tangent space carries the structure of the model space. -/
instance (x : X) : ContinuousSMul ℝ (A.TangentSpace x) :=
  inferInstanceAs (ContinuousSMul ℝ (A.model (A.chartAt x)))

/-- The tangent space carries the structure of the model space. -/
instance (x : X) : LocallyConvexSpace ℝ (A.TangentSpace x) :=
  inferInstanceAs (LocallyConvexSpace ℝ (A.model (A.chartAt x)))

/-- The tangent space carries the structure of the model space. -/
instance (x : X) : T2Space (A.TangentSpace x) := inferInstanceAs (T2Space (A.model (A.chartAt x)))

/-- The domain of the transition map from the chart `i` to the chart `j`. -/
def transDom (i j : A.ι) : Set (A.model i) :=
  (A.chart i).target ∩ (A.chart i).symm ⁻¹' (A.chart j).source

/-- The domain of a transition map is open. -/
theorem isOpen_transDom (i j : A.ι) : IsOpen (A.transDom i j) :=
  (A.chart i).isOpen_inter_preimage_symm (A.chart j).open_source

/-- A point in the sources of `i` and `j` is sent by `i` into the domain of the transition map. -/
theorem chart_mem_transDom {i j : A.ι} {x : X} (hx : x ∈ (A.chart i).source ∩ (A.chart j).source) :
    A.chart i x ∈ A.transDom i j :=
  ⟨(A.chart i).map_source hx.1, by rw [mem_preimage, (A.chart i).left_inv hx.1]; exact hx.2⟩

/-- **The change of tangent coordinates** from the chart `i` to the chart `j` at a point `x` of
both sources: the derivative `d(φ_j ∘ φ_i⁻¹)(φ_i x)`, a continuous linear map. -/
def tangentCoordChange (i j : A.ι) {x : X} (hx : x ∈ (A.chart i).source ∩ (A.chart j).source) :
    A.model i →L[ℝ] A.model j where
  toFun v := dMB (A.chart j ∘ (A.chart i).symm) (A.chart i x, v)
  map_add' v w := ((A.smoothMBOn_transition i j) 1).dMB_add (A.isOpen_transDom i j)
    (A.chart_mem_transDom hx) v w
  map_smul' c v := ((A.smoothMBOn_transition i j) 1).dMB_smul (A.chart_mem_transDom hx) c v
  cont := ((A.smoothMBOn_transition i j) 1).continuous_dMB (A.chart_mem_transDom hx)

/-- The change of tangent coordinates from a chart to itself is the identity. -/
theorem tangentCoordChange_self (i : A.ι) {x : X} (hx : x ∈ (A.chart i).source) (v : A.model i) :
    A.tangentCoordChange i i ⟨hx, hx⟩ v = v := by
  change dMB (A.chart i ∘ (A.chart i).symm) (A.chart i x, v) = v
  have hev : (A.chart i ∘ (A.chart i).symm) =ᶠ[𝓝 (A.chart i x)] id :=
    Filter.eventually_of_mem ((A.chart i).open_target.mem_nhds ((A.chart i).map_source hx))
      fun y hy ↦ (A.chart i).right_inv hy
  rw [dMB_congr_of_eventuallyEq hev]
  exact ((ContinuousLinearMap.id ℝ (A.model i)).hasDirDerivAt _ v).dMB_eq

/-- **The cocycle condition** for the changes of tangent coordinates (chain rule). -/
theorem tangentCoordChange_comp (i j k : A.ι) {x : X}
    (hx : x ∈ (A.chart i).source ∩ (A.chart j).source ∩ (A.chart k).source) (v : A.model i) :
    A.tangentCoordChange j k ⟨hx.1.2, hx.2⟩ (A.tangentCoordChange i j hx.1 v) =
      A.tangentCoordChange i k ⟨hx.1.1, hx.2⟩ v := by
  set φi := A.chart i
  set φj := A.chart j
  set φk := A.chart k
  set W := φi.target ∩ φi.symm ⁻¹' (φj.source ∩ φk.source)
  have hW : IsOpen W := φi.isOpen_inter_preimage_symm (φj.open_source.inter φk.open_source)
  have hxW : φi x ∈ W := by
    refine ⟨φi.map_source hx.1.1, ?_⟩
    rw [mem_preimage, φi.left_inv hx.1.1]
    exact ⟨hx.1.2, hx.2⟩
  have hmaps : MapsTo (φj ∘ φi.symm) W (A.transDom j k) := fun y hy ↦ by
    refine ⟨φj.map_source hy.2.1, ?_⟩
    change φj.symm (φj (φi.symm y)) ∈ φk.source
    rw [φj.left_inv hy.2.1]
    exact hy.2.2
  have hc := ContDiffMBOn.dMB_comp (A.isOpen_transDom j k) ((A.smoothMBOn_transition j k) 1)
    (((A.smoothMBOn_transition i j) 1).mono fun (y : A.model i) (hy : y ∈ W) ↦ ⟨hy.1, hy.2.1⟩)
    hmaps hxW v
  change dMB (φk ∘ φj.symm) (φj x, dMB (φj ∘ φi.symm) (φi x, v)) = dMB (φk ∘ φi.symm) (φi x, v)
  have hjx : (φj ∘ φi.symm) (φi x) = φj x := by
    simp only [Function.comp_apply, φi.left_inv hx.1.1]
  rw [← hjx, ← hc]
  refine dMB_congr_of_eventuallyEq (Filter.eventually_of_mem (hW.mem_nhds hxW) fun y hy ↦ ?_) v
  change φk (φj.symm (φj (φi.symm y))) = φk (φi.symm y)
  rw [φj.left_inv hy.2.1]

/-- The change of tangent coordinates, as an isomorphism of topological vector spaces. -/
def tangentCoordChangeEquiv (i j : A.ι) {x : X}
    (hx : x ∈ (A.chart i).source ∩ (A.chart j).source) : A.model i ≃L[ℝ] A.model j :=
  ContinuousLinearEquiv.equivOfInverse (A.tangentCoordChange i j hx)
    (A.tangentCoordChange j i ⟨hx.2, hx.1⟩)
    (fun v ↦ (A.tangentCoordChange_comp i j i ⟨hx, hx.1⟩ v).trans
      (A.tangentCoordChange_self i hx.1 v))
    (fun v ↦ (A.tangentCoordChange_comp j i j ⟨⟨hx.2, hx.1⟩, hx.2⟩ v).trans
      (A.tangentCoordChange_self j hx.2 v))

variable {A}

/-- A point of `U` is sent by the preferred chart into the domain of the local representative of
`f` in the preferred charts. -/
theorem chartAt_mem_chartDomain {f : X → Y} {U : Set X} {x : X} (hx : x ∈ U) :
    A.chart (A.chartAt x) x ∈ chartDomain f U (A.chart (A.chartAt x)) (B.chart (B.chartAt (f x))) :=
  ⟨(A.chart _).map_source (A.mem_chartAt_source x), by
    rw [mem_preimage, (A.chart _).left_inv (A.mem_chartAt_source x)]
    exact ⟨hx, B.mem_chartAt_source (f x)⟩⟩

/-- **The tangent map** `T_x f : T_x X → T_{f x} Y` of a `C^1` map, the derivative of its local
representative in the preferred charts. -/
def tangentMapAt {f : X → Y} {U : Set X} (hU : IsOpen U) (hf : A.ContMDiffOn B 1 f U) {x : X}
    (hx : x ∈ U) : A.TangentSpace x →L[ℝ] B.TangentSpace (f x) where
  toFun v := dMB (B.chart (B.chartAt (f x)) ∘ f ∘ (A.chart (A.chartAt x)).symm)
    (A.chart (A.chartAt x) x, v)
  map_add' v w := (hf.2 _ _).dMB_add (isOpen_chartDomain hU hf.1 _ _)
    (chartAt_mem_chartDomain (B := B) hx) v w
  map_smul' c v := (hf.2 _ _).dMB_smul (chartAt_mem_chartDomain (B := B) hx) c v
  cont := (hf.2 _ _).continuous_dMB (chartAt_mem_chartDomain (B := B) hx)

/-- **The tangent map does not depend on the charts**: in charts `i` at `x` and `j` at `f x`, the
derivative of the local representative of `f` is the tangent map `T_x f` composed with the
changes of tangent coordinates. -/
theorem dMB_chart_eq_tangentMapAt {f : X → Y} {U : Set X} (hU : IsOpen U)
    (hf : A.ContMDiffOn B 1 f U) {x : X} (hx : x ∈ U) {i : A.ι} {j : B.ι}
    (hi : x ∈ (A.chart i).source) (hj : f x ∈ (B.chart j).source) (v : A.TangentSpace x) :
    dMB (B.chart j ∘ f ∘ (A.chart i).symm)
      (A.chart i x, A.tangentCoordChange (A.chartAt x) i ⟨A.mem_chartAt_source x, hi⟩ v) =
    B.tangentCoordChange (B.chartAt (f x)) j ⟨B.mem_chartAt_source (f x), hj⟩
      (tangentMapAt hU hf hx v) := by
  set c := A.chartAt x
  set c' := B.chartAt (f x)
  set φi := A.chart i
  set φc := A.chart c
  set ψc := B.chart c'
  set ψj := B.chart j
  have hcx : x ∈ φc.source := A.mem_chartAt_source x
  have hcy : f x ∈ ψc.source := B.mem_chartAt_source (f x)
  set W := φi.target ∩ φi.symm ⁻¹' (U ∩ φc.source ∩ f ⁻¹' (ψc.source ∩ ψj.source))
  have hW : IsOpen W := φi.isOpen_inter_preimage_symm
    ((hf.1.mono inter_subset_left).isOpen_inter_preimage
    (hU.inter φc.open_source) (ψc.open_source.inter ψj.open_source))
  have hxW : φi x ∈ W := by
    refine ⟨φi.map_source hi, ?_⟩
    rw [mem_preimage, φi.left_inv hi]
    exact ⟨⟨hx, hcx⟩, hcy, hj⟩
  set T := φc ∘ φi.symm
  set R := ψc ∘ f ∘ φc.symm
  set T' := ψj ∘ ψc.symm
  have hT : ContDiffMBOn 1 T W :=
    ((A.smoothMBOn_transition i c) 1).mono fun (y : A.model i) (hy : y ∈ W) ↦ ⟨hy.1, hy.2.1.2⟩
  have hTmaps : MapsTo T W (chartDomain f U φc ψc) := fun y hy ↦ by
    refine ⟨φc.map_source hy.2.1.2, ?_⟩
    change φc.symm (φc (φi.symm y)) ∈ U ∩ f ⁻¹' ψc.source
    rw [φc.left_inv hy.2.1.2]
    exact ⟨hy.2.1.1, hy.2.2.1⟩
  have hR : ContDiffMBOn 1 R (chartDomain f U φc ψc) := hf.2 c c'
  have hRT : ContDiffMBOn 1 (R ∘ T) W :=
    hR.comp hW (isOpen_chartDomain hU hf.1 _ _) hT hTmaps
  have hRTmaps : MapsTo (R ∘ T) W (B.transDom c' j) := fun y hy ↦ by
    have h1 : φc.symm (φc (φi.symm y)) = φi.symm y := φc.left_inv hy.2.1.2
    refine ⟨?_, ?_⟩
    · change ψc (f (φc.symm (φc (φi.symm y)))) ∈ ψc.target
      rw [h1]; exact ψc.map_source hy.2.2.1
    · change ψc.symm (ψc (f (φc.symm (φc (φi.symm y))))) ∈ ψj.source
      rw [h1, ψc.left_inv hy.2.2.1]; exact hy.2.2.2
  have hev : (ψj ∘ f ∘ φi.symm) =ᶠ[𝓝 (φi x)] T' ∘ (R ∘ T) :=
    Filter.eventually_of_mem (hW.mem_nhds hxW) fun y hy ↦ by
      change ψj (f (φi.symm y)) = ψj (ψc.symm (ψc (f (φc.symm (φc (φi.symm y))))))
      rw [φc.left_inv hy.2.1.2, ψc.left_inv hy.2.2.1]
  rw [dMB_congr_of_eventuallyEq hev, ContDiffMBOn.dMB_comp (B.isOpen_transDom c' j)
    ((B.smoothMBOn_transition c' j) 1) hRT hRTmaps hxW, ContDiffMBOn.dMB_comp
    (isOpen_chartDomain hU hf.1 _ _) hR hT hTmaps hxW]
  have hTx : T (φi x) = φc x := by
    change φc (φi.symm (φi x)) = φc x
    rw [φi.left_inv hi]
  have hTv : dMB T (φi x, A.tangentCoordChange c i ⟨hcx, hi⟩ v) = v :=
    (A.tangentCoordChange_comp c i c ⟨⟨hcx, hi⟩, hcx⟩ v).trans (A.tangentCoordChange_self c hcx v)
  have hRTx : (R ∘ T) (φi x) = ψc (f x) := by
    change ψc (f (φc.symm (φc (φi.symm (φi x))))) = ψc (f x)
    rw [φi.left_inv hi, φc.left_inv hcx]
  rw [hTv, hTx, hRTx]
  rfl

end Tangent
end VaryingAtlas

end LocallyConvex.Manifolds
