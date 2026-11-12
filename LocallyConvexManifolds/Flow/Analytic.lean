/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.ODE.FlowAnalytic
public import LocallyConvexManifolds.Flow.Maximal
public import LocallyConvexManifolds.Analytic.Bundle
public import LocallyConvexManifolds.Manifold.LocalDiffeo
public import LocallyConvexManifolds.Analytic.Form

/-!
# The maximal flow of a real analytic vector field is real analytic

Let `M` be a Hausdorff real analytic manifold modeled on a real Banach space `E`, and `X` a smooth
vector field on `M` whose local representatives in the charts of the atlas are real analytic
(`SmoothVectorField.IsRealAnalytic`, from `LocallyConvexManifolds.Analytic.Form`). We prove:

* `SmoothVectorField.exists_flowBox_realAnalyticMOn`: **real analytic flow boxes**: around every
  point there is a flow box `φ : (-ε, ε) × V → M` which is real analytic, from the real analytic
  local flows on Banach spaces (`LocallyConvex.Analysis.exists_realAnalyticOn_flow`, Glöckner–Neeb,
  Theorem 2.4.34) read in a chart.
* `SmoothVectorField.realAnalyticMOn_flow`: **the maximal flow is real analytic** on its open
  domain `D ⊆ ℝ × M` (Glöckner–Neeb, *Infinite-Dimensional Lie Groups*, arXiv:2602.12362,
  Theorem 2.5.18 (b), p. 220, and Corollary 2.5.21, last assertion, p. 222).

The proof is that of the smooth case (`SmoothVectorField.smoothMBMOn_flow`, after GN's proof of
Theorem 2.5.18): the set of times `t ∈ J_{x₀}` near which the flow is real analytic is open,
contains `0`, and is closed in `J_{x₀}`, since near `t` the flow is
`Fl(τ, x) = φ(τ - t₁, Fl(t₁, x))` for a real analytic flow box `φ` at `Fl(t, x₀)`.

## Implementation notes

* A vector field is real analytic if its local representatives in the charts of the atlas are
  (`SmoothVectorField.IsRealAnalytic`). GN define real analytic vector fields as real analytic
  sections of the tangent bundle; we do not prove that the two notions agree.
* The model space `E` lives in `Type`: the calculus of real analytic maps between manifolds in
  `LocallyConvexManifolds.Analytic.Basic` is stated for model spaces in a common universe, and the
  time variable is modeled on `ℝ : Type`.
* As for the smooth maximal flow, `E` is a Banach space and `M` is Hausdorff.
-/

@[expose] public section

open Set Filter Function
open LocallyConvex.Analysis
open scoped Topology

noncomputable section

namespace LocallyConvex.Manifolds

universe v

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [RealAnalyticManifold E M]

/-! ### Charts are real analytic -/

/-- A chart of the atlas is a real analytic map on its source. -/
theorem realAnalyticMOn_coe_chart (i : atlas E M) :
    RealAnalyticMOn (E := E) (F := E) (i.1 : M → E) i.1.source := by
  refine ⟨i.1.continuousOn, fun x _ ↦ ?_⟩
  have h := realAnalyticOn_transition ((realAnalyticGroupoid E).chart_mem_maximalAtlas x)
    ((realAnalyticGroupoid E).subset_maximalAtlas i.2)
  refine realAnalyticOn_congr (fun y _ ↦ ?_) (h.mono fun y hy ↦ ⟨hy.1, hy.2.1⟩)
  simp [chartAt_self_eq]

/-- The inverse of a chart of the atlas is a real analytic map on its target. -/
theorem realAnalyticMOn_chart_symm (i : atlas E M) :
    RealAnalyticMOn (E := E) (F := E) (i.1.symm : E → M) i.1.target := by
  refine ⟨i.1.continuousOn_symm, fun x _ ↦ ?_⟩
  have h := realAnalyticOn_transition ((realAnalyticGroupoid E).subset_maximalAtlas i.2)
    ((realAnalyticGroupoid E).chart_mem_maximalAtlas (i.1.symm x))
  refine realAnalyticOn_congr (fun y _ ↦ ?_) (h.mono fun y hy ↦ ?_)
  · simp [chartAt_self_eq]
  · exact hy.2

namespace SmoothVectorField

variable {X : SmoothVectorField E M} [CompleteSpace E] [T2Space M]

omit [T2Space M] in
/-- **Real analytic flow boxes.** Around every point, a real analytic vector field has a flow box
`φ : (-ε, ε) × V → M` which is real analytic: the real analytic local flow of the local
representative in a chart (`LocallyConvex.Analysis.exists_realAnalyticOn_flow`), transported to
`M`. -/
theorem exists_flowBox_realAnalyticMOn (hX : X.IsRealAnalytic) (z : M) :
    ∃ B : X.FlowBox z, RealAnalyticMOn (E := ModelProd ℝ E) (F := E) B.φ B.box := by
  set i : atlas E M := ⟨chartAt E z, chart_mem_atlas E z⟩
  have hz : z ∈ i.1.source := mem_chart_source E z
  obtain ⟨ε, hε, V', hV', hzV', ψ, hψ, H⟩ :=
    exists_realAnalyticOn_flow i.1.open_target (hX i) (i.1.map_source hz)
  set V := i.1.source ∩ i.1 ⁻¹' V'
  have hV : IsOpen V := i.1.isOpen_inter_preimage hV'
  set φ : ℝ × M → M := fun p ↦ i.1.symm (ψ (p.1, i.1 p.2))
  have hbox : IsOpen (Ioo (-ε) ε ×ˢ V) := isOpen_Ioo.prod hV
  -- `p ↦ (p.1, i p.2)` is real analytic on `ℝ × i.source`
  have hpair : RealAnalyticMOn (E := ModelProd ℝ E) (F := ℝ × E)
      (fun p : ℝ × M ↦ (p.1, i.1 p.2)) (univ ×ˢ i.1.source) :=
    RealAnalyticMOn.prodMk_model ((realAnalyticMOn_fst (E := ℝ) (F := E)).mono (subset_univ _))
      ((realAnalyticMOn_coe_chart i).comp (isOpen_univ.prod i.1.open_source) i.1.open_source
        ((realAnalyticMOn_snd (E := ℝ) (F := E)).mono (subset_univ _)) fun p hp ↦ hp.2)
  have hψM : RealAnalyticMOn (E := ℝ × E) (F := E) ψ (Ioo (-ε) ε ×ˢ V') :=
    (realAnalyticMOn_iff_realAnalyticOn (isOpen_Ioo.prod hV')).2 hψ
  have hgM : RealAnalyticMOn (E := ModelProd ℝ E) (F := E)
      (ψ ∘ fun p : ℝ × M ↦ (p.1, i.1 p.2)) (Ioo (-ε) ε ×ˢ V) :=
    hψM.comp hbox (isOpen_Ioo.prod hV') (hpair.mono fun p hp ↦ ⟨mem_univ _, hp.2.1⟩)
      fun p hp ↦ ⟨hp.1, hp.2.2⟩
  have hφ : RealAnalyticMOn (E := ModelProd ℝ E) (F := E) φ (Ioo (-ε) ε ×ˢ V) :=
    (realAnalyticMOn_chart_symm i).comp hbox i.1.open_target hgM fun p hp ↦
      ((H _ hp.2.2).2 p.1 hp.1).1
  refine ⟨⟨ε, hε, V, hV, ⟨hz, hzV'⟩, φ, hφ.smoothMBMOn hbox, fun y hy ↦ ?_, fun y hy ↦ ?_⟩, hφ⟩
  · simp [φ, (H _ hy.2).1, i.1.left_inv hy.1]
  · refine X.isIntegralCurveOn_of_exists_chart fun t ht ↦ ?_
    obtain ⟨htU, hd⟩ := (H _ hy.2).2 t ht
    refine ⟨(i.1.continuousAt_symm htU).comp (f := fun s ↦ ψ (s, i.1 y)) hd.continuousAt, i,
      i.1.map_target htU, ?_⟩
    have hev : (fun s ↦ ψ (s, i.1 y)) =ᶠ[𝓝 t] i.1 ∘ fun s ↦ φ (s, y) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      simp [φ, i.1.right_inv ((H _ hy.2).2 s hs).1]
    have hval : i.1 (φ (t, y)) = ψ (t, i.1 y) := by simp [φ, i.1.right_inv htU]
    rw [hval]
    exact hd.congr_of_eventuallyEq hev.symm

omit [CompleteSpace E] [T2Space M] in
/-- If `f : ℝ × M → M` is real analytic on an open set `W`, then `(τ, x) ↦ (τ - a, f(b, x))` is
real analytic on `{(τ, x) | (b, x) ∈ W}`. -/
theorem realAnalyticMOn_sub_prod_slice {f : ℝ × M → M} {W : Set (ℝ × M)} (hW : IsOpen W)
    (hf : RealAnalyticMOn (E := ModelProd ℝ E) (F := E) f W) (a b : ℝ) :
    RealAnalyticMOn (E := ModelProd ℝ E) (F := ModelProd ℝ E)
      (fun p : ℝ × M ↦ ((p.1 - a, f (b, p.2)) : ℝ × M)) {p : ℝ × M | (b, p.2) ∈ W} := by
  have hsl : Continuous fun p : ℝ × M ↦ ((b, p.2) : ℝ × M) :=
    continuous_const.prodMk continuous_snd
  have hW₁ : IsOpen {p : ℝ × M | (b, p.2) ∈ W} := hW.preimage hsl
  -- `τ ↦ τ - a`
  have hsubR : RealAnalyticMOn (E := ℝ) (F := ℝ) (fun τ : ℝ ↦ τ - a) univ :=
    (realAnalyticMOn_iff_realAnalyticOn isOpen_univ).2
      (((ContinuousLinearMap.id ℝ ℝ).realAnalyticOn univ).sub (realAnalyticOn_const a univ))
  have h1 : RealAnalyticMOn (E := ModelProd ℝ E) (F := ℝ) (fun p : ℝ × M ↦ p.1 - a) univ :=
    hsubR.comp isOpen_univ isOpen_univ (realAnalyticMOn_fst (E := ℝ) (F := E)) (mapsTo_univ _ _)
  -- `p ↦ (b, p.2)`
  have hsl' : RealAnalyticMOn (E := ModelProd ℝ E) (F := ModelProd ℝ E)
      (fun p : ℝ × M ↦ ((b, p.2) : ℝ × M)) univ :=
    (realAnalyticMOn_const univ b).prodMk (realAnalyticMOn_snd (E := ℝ) (F := E))
  have h2 : RealAnalyticMOn (E := ModelProd ℝ E) (F := E) (fun p : ℝ × M ↦ f (b, p.2))
      {p : ℝ × M | (b, p.2) ∈ W} :=
    hf.comp hW₁ hW (hsl'.mono (subset_univ _)) fun _ hp ↦ hp
  exact (h1.mono (subset_univ _)).prodMk h2

/-- The flow is real analytic near `(t, x₀)` and its domain is a neighbourhood of `(t, x₀)`. -/
private def GoodTimeω (X : SmoothVectorField E M) (x₀ : M) (t : ℝ) : Prop :=
  ∃ W : Set (ℝ × M), IsOpen W ∧ (t, x₀) ∈ W ∧ W ⊆ X.flowDomain ∧
    RealAnalyticMOn (E := ModelProd ℝ E) (F := E) X.flow W

/-- **Propagation along a real analytic flow box**, as in the smooth case. -/
private theorem goodTimeω_of_flowBox {x₀ : M} {t τ : ℝ} (ht : GoodTimeω X x₀ t) {z : M}
    (B : X.FlowBox z) (hB : RealAnalyticMOn (E := ModelProd ℝ E) (F := E) B.φ B.box)
    (hV : X.flow (t, x₀) ∈ B.V) (hτ : τ - t ∈ Ioo (-B.ε) B.ε) : GoodTimeω X x₀ τ := by
  obtain ⟨W, hW, htW, hWD, han⟩ := ht
  set W₁ : Set (ℝ × M) := {p | (t, p.2) ∈ W}
  have hsl : Continuous fun p : ℝ × M ↦ ((t, p.2) : ℝ × M) :=
    continuous_const.prodMk continuous_snd
  have hW₁ : IsOpen W₁ := hW.preimage hsl
  set G : ℝ × M → ℝ × M := fun p ↦ (p.1 - t, X.flow (t, p.2))
  have hG : RealAnalyticMOn (E := ModelProd ℝ E) (F := ModelProd ℝ E) G W₁ :=
    realAnalyticMOn_sub_prod_slice hW han t t
  set W' : Set (ℝ × M) := W₁ ∩ G ⁻¹' B.box
  have hW' : IsOpen W' := hG.1.isOpen_inter_preimage hW₁ B.isOpen_box
  have hrep : ∀ p ∈ W', p ∈ X.flowDomain ∧ X.flow p = B.φ (G p) := fun p hp ↦ by
    have h := B.flow_add (hWD hp.1) hp.2.2 hp.2.1
    rwa [sub_add_cancel] at h
  refine ⟨W', hW', ⟨htW, hτ, hV⟩, fun p hp ↦ (hrep p hp).1, ?_⟩
  refine RealAnalyticMOn.congr ?_ fun p hp ↦ ((hrep p hp).2).symm
  exact hB.comp hW' B.isOpen_box (hG.mono inter_subset_left) fun p hp ↦ hp.2

/-- Every `t ∈ J_{x₀}` is a good time. -/
private theorem goodTimeω_of_mem (hX : X.IsRealAnalytic) {x₀ : M} {t : ℝ}
    (ht : t ∈ X.maxInterval x₀) : GoodTimeω X x₀ t := by
  set S := {τ | GoodTimeω X x₀ τ}
  have hS : IsOpen S := isOpen_iff_mem_nhds.2 fun τ ⟨W, hW, hτW, hWD, han⟩ ↦
    Filter.mem_of_superset
      ((hW.preimage (continuous_id.prodMk continuous_const)).mem_nhds hτW)
      fun σ hσ ↦ ⟨W, hW, hσ, hWD, han⟩
  have h0 : (0 : ℝ) ∈ S := by
    obtain ⟨B, hB⟩ := X.exists_flowBox_realAnalyticMOn hX x₀
    refine ⟨B.box, B.isOpen_box, ⟨⟨neg_lt_zero.2 B.ε_pos, B.ε_pos⟩, B.mem⟩,
      B.box_subset_flowDomain, ?_⟩
    exact hB.congr fun p hp ↦ (B.flow_eq hp).symm
  have hsub : X.maxInterval x₀ ⊆ S := by
    refine (X.ordConnected_maxInterval x₀).isPreconnected.subset_of_closure_inter_subset hS
      ⟨0, X.zero_mem_maxInterval x₀, h0⟩ ?_
    rintro τ ⟨hτc, hτ⟩
    obtain ⟨B, hB⟩ := X.exists_flowBox_realAnalyticMOn hX (X.flow (τ, x₀))
    have hcont : ContinuousAt (fun σ ↦ X.flow (σ, x₀)) τ := (X.isIntegralCurveOn_flow x₀ τ hτ).1
    have hN : Ioo (τ - B.ε) (τ + B.ε) ∩ (fun σ ↦ X.flow (σ, x₀)) ⁻¹' B.V ∈ 𝓝 τ :=
      inter_mem (Ioo_mem_nhds (by linarith [B.ε_pos]) (by linarith [B.ε_pos]))
        (hcont.preimage_mem_nhds (B.isOpen.mem_nhds B.mem))
    obtain ⟨σ, ⟨hσ, hσV⟩, hσS⟩ := mem_closure_iff_nhds.1 hτc _ hN
    exact goodTimeω_of_flowBox hσS B hB hσV ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  exact hsub ht

/-- **The maximal flow of a real analytic vector field is real analytic** on its open domain
`D ⊆ ℝ × M` (Glöckner–Neeb, *Infinite-Dimensional Lie Groups*, Theorem 2.5.18 (b), p. 220, and
Corollary 2.5.21, last assertion, p. 222), for a Hausdorff real analytic manifold `M` modeled on
a real Banach space. -/
theorem realAnalyticMOn_flow (hX : X.IsRealAnalytic) :
    RealAnalyticMOn (E := ModelProd ℝ E) (F := E) X.flow X.flowDomain :=
  realAnalyticMOn_of_local X.isOpen_flowDomain fun _ hp ↦
    let ⟨W, hW, hpW, _, han⟩ := goodTimeω_of_mem hX hp
    ⟨W, hW, hpW, W, X.flow, hW, le_rfl, han, fun _ _ ↦ rfl⟩

end SmoothVectorField

end LocallyConvex.Manifolds
