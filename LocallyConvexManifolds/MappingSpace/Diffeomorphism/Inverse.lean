/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Calculus.ImplicitFinite
public import LocallyConvexManifolds.MappingSpace.Diffeomorphism.Open

/-!
# Inverses of families of diffeomorphisms of a compact manifold

Let `K` be a compact manifold and `f : P × K → K` a family of diffeomorphisms `f_p = f(p, ·)`,
parametrized by a space `P` with an atlas with varying models (for instance an open subset of a
manifold of mappings). If `f` is `C^{n,n}` for all `n`, then the inverse family
`g(p, y) = f_p⁻¹(y)` is `C^{k,ℓ}` for all `k, ℓ` ([GN26, Lemma 13.1.8], for compact `K`).

## Main results

* `isUnit_fderiv_normedRep_of_leftInverse`: a `C^1` map with a `C^1` left inverse has invertible
  derivatives, in any charts.
* `continuous_of_leftInverse_rightInverse`: the inverse family is continuous (closed graph,
  `K` compact).
* `ContMDiffMB₂.inverse`: [GN26, Lemma 13.1.8] for compact `K`.

## Implementation notes

Glöckner–Neeb deduce Lemma 13.1.8 from an implicit function theorem with parameters whose
reference is still to be added in the manuscript. Here the model of `K` is finite-dimensional, and
we use `contDiffMBOn_of_implicit` (parameters in a locally convex space, values in a
finite-dimensional space): in charts, `g` solves `c(f(φ⁻¹ u, e⁻¹ z)) = w` for `z` as a function
of `(u, w)`. Its continuity, which the implicit function theorem needs as an input, comes from
compactness: its graph `{((p, y), x) : f(p, x) = y}` is closed and `K` is compact.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Function Filter
open scoped Topology
open LocallyConvex.Analysis

noncomputable section

universe u

namespace LocallyConvex.Manifolds

/-- **The inverse family is continuous**: if `f : P × K → K` is continuous, `K` is compact
Hausdorff, and `g(p, ·)` is a two-sided inverse of `f(p, ·)` for each `p`, then `g` is
continuous, since its graph `{((p, y), x) : f(p, x) = y}` is closed. -/
theorem continuous_of_leftInverse_rightInverse {P K : Type*} [TopologicalSpace P]
    [TopologicalSpace K] [CompactSpace K] [T2Space K] {f g : P × K → K} (hf : Continuous f)
    (hgf : ∀ p x, g (p, f (p, x)) = x) (hfg : ∀ p y, f (p, g (p, y)) = y) : Continuous g := by
  refine continuous_of_isClosed_graph ?_
  have : graph g = {s : (P × K) × K | f (s.1.1, s.2) = s.1.2} := by
    ext ⟨⟨p, y⟩, x⟩
    change g (p, y) = x ↔ f (p, x) = y
    constructor
    · rintro rfl
      exact hfg p y
    · rintro rfl
      exact hgf p x
  rw [this]
  exact isClosed_eq (hf.comp (by fun_prop)) (by fun_prop)

variable {H : Type u} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [IsTopologicalAddGroup H]
  [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  {K : Type u} [TopologicalSpace K] [ChartedSpace H K] [MBManifold H K]

section Lemma

variable [FiniteDimensional ℝ H]

/-- **A map with a `C^1` left inverse has invertible derivatives**, in any charts: if
`δ ∘ γ = id` with `γ`, `δ` of class `C^1`, `x ∈ e.source` and `γ x ∈ c.source`, then the derivative
of the Euclidean local representative of `γ` at `L(e x)` is invertible. -/
theorem isUnit_fderiv_normedRep_of_leftInverse {γ δ : K → K} (hγ : ContMDiffMB H H 1 γ)
    (hδ : ContMDiffMB H H 1 δ) (hδγ : ∀ x, δ (γ x) = x) {e c : OpenPartialHomeomorph K H}
    (he : e ∈ atlas H K) (hc : c ∈ atlas H K) {x : K} (hx : x ∈ e.source)
    (hγx : γ x ∈ c.source) : IsUnit (fderiv ℝ (normedRep γ e c) (euclideanEquiv H (e x))) := by
  set L := euclideanEquiv H
  set f := normedRep γ e c
  set g := normedRep δ c e
  set z₀ := L (e x)
  have hγc : Continuous γ := continuousOn_univ.1 hγ.1
  have hδc : Continuous δ := continuousOn_univ.1 hδ.1
  have hz₀ : z₀ ∈ normedDom γ e c := mem_normedDom hx hγx
  have hfz₀ : f z₀ = L (c (γ x)) := normedRep_euclideanEquiv hx
  have hfz₀' : f z₀ ∈ normedDom δ c e := by
    rw [hfz₀]
    exact mem_normedDom hγx (by rw [hδγ]; exact hx)
  have hf : ContDiffOn ℝ 1 f (normedDom γ e c) := contDiffOn_normedRep (k := 1) hγ he hc
  have hg : ContDiffOn ℝ 1 g (normedDom δ c e) := contDiffOn_normedRep (k := 1) hδ hc he
  have hfd : HasFDerivAt f (fderiv ℝ f z₀) z₀ :=
    ((hf.contDiffAt ((isOpen_normedDom hγc e c).mem_nhds hz₀)).differentiableAt
      one_ne_zero).hasFDerivAt
  have hgd : HasFDerivAt g (fderiv ℝ g (f z₀)) (f z₀) :=
    ((hg.contDiffAt ((isOpen_normedDom hδc c e).mem_nhds hfz₀')).differentiableAt
      one_ne_zero).hasFDerivAt
  -- `g ∘ f = id` near `z₀`
  have hgf : (g ∘ f) =ᶠ[𝓝 z₀] id := by
    filter_upwards [(isOpen_normedDom hγc e c).mem_nhds hz₀] with z hz
    obtain ⟨hzt, -, hzc⟩ := hz
    simp only [Function.comp_apply, id, g, f, normedRep, ContinuousLinearEquiv.symm_apply_apply,
      c.left_inv hzc, hδγ, e.right_inv hzt, ContinuousLinearEquiv.apply_symm_apply]
  have hcomp : (fderiv ℝ g (f z₀)).comp (fderiv ℝ f z₀) = ContinuousLinearMap.id ℝ _ :=
    (hgd.comp z₀ hfd).unique ((hasFDerivAt_id z₀).congr_of_eventuallyEq hgf)
  have hinj : Injective (fderiv ℝ f z₀) := by
    intro v w hvw
    have := congrArg (fderiv ℝ g (f z₀)) hvw
    simpa [← ContinuousLinearMap.comp_apply, hcomp] using this
  have hsurj : Surjective (fderiv ℝ f z₀) :=
    (LinearMap.injective_iff_surjective (f := ((fderiv ℝ f z₀ :
      EuclideanModel H →L[ℝ] EuclideanModel H) : EuclideanModel H →ₗ[ℝ] EuclideanModel H))).1 hinj
  refine ⟨(ContinuousLinearEquiv.ofBijective (fderiv ℝ f z₀) (LinearMap.ker_eq_bot.2 hinj)
    (LinearMap.range_eq_top.2 hsurj)).toUnit, ?_⟩
  ext v
  rfl

variable [CompactSpace K] [T2Space K] {P : Type*} [TopologicalSpace P]
  {B : VaryingAtlas.{u, _, _} P}

/-- **[GN26, Lemma 13.1.8]**, for a compact manifold `K`: let `f : P × K → K` be `C^{n,n}` for
every `n`, with `C^1` partial maps `f_p = f(p, ·)`, and let `g : P × K → K` be the inverse family,
`g(p, ·) = f_p⁻¹`, with `C^1` partial maps. Then `g` is `C^{k,ℓ}` for all `k, ℓ`. -/
theorem ContMDiffMB₂.inverse {f g : P × K → K} (hf : ∀ n, ContMDiffMB₂ H H B n n f)
    (hf1 : ∀ p, ContMDiffMB H H 1 (fun x ↦ f (p, x)))
    (hg1 : ∀ p, ContMDiffMB H H 1 (fun y ↦ g (p, y)))
    (hgf : ∀ p x, g (p, f (p, x)) = x) (hfg : ∀ p y, f (p, g (p, y)) = y) (k ℓ : ℕ) :
    ContMDiffMB₂ H H B k ℓ g := by
  intro p₀ y₀
  have : Nonempty K := ⟨y₀⟩
  have := locallyCompactSpace_of_compactSpace (H := H) K
  have hfc : Continuous f := (hf 0).continuous
  have hgc : Continuous g := continuous_of_leftInverse_rightInverse hfc hgf hfg
  set L := euclideanEquiv H
  set x₀ := g (p₀, y₀)
  set i := B.chartAt p₀
  set φ := B.chart i
  set e := chartAt H x₀
  set c := chartAt H y₀
  have he : e ∈ atlas H K := chart_mem_atlas H x₀
  have hc : c ∈ atlas H K := chart_mem_atlas H y₀
  have hp₀ : p₀ ∈ φ.source := B.mem_chartAt_source p₀
  have hx₀ : x₀ ∈ e.source := mem_chart_source H x₀
  have hy₀ : y₀ ∈ c.source := mem_chart_source H y₀
  -- a box `U × V` for `f` around `(φ p₀, e x₀)`, on which its local representative is smooth
  set O : Set (B.model i × H) :=
    (φ.target ×ˢ e.target) ∩ (fun a ↦ f (φ.symm a.1, e.symm a.2)) ⁻¹' c.source
  have hFc : ContinuousOn (fun a : B.model i × H ↦ f (φ.symm a.1, e.symm a.2))
      (φ.target ×ˢ e.target) :=
    hfc.comp_continuousOn ((φ.continuousOn_symm.comp
      (continuousOn_fst (s := φ.target ×ˢ e.target)) fun _ h ↦ h.1).prodMk
      (e.continuousOn_symm.comp (continuousOn_snd (s := φ.target ×ˢ e.target)) fun _ h ↦ h.2))
  have hO : IsOpen O := hFc.isOpen_inter_preimage (φ.open_target.prod e.open_target) c.open_source
  have hq₀O : (φ p₀, e x₀) ∈ O := by
    refine ⟨⟨φ.map_source hp₀, e.map_source hx₀⟩, ?_⟩
    simp only [mem_preimage, φ.left_inv hp₀, e.left_inv hx₀, x₀, hfg]
    exact hy₀
  obtain ⟨U, V, hU, hV, hpU, hxV, hUV⟩ := isOpen_prod_iff.1 hO _ _ hq₀O
  have hbox : IsChartBox f φ e c U V :=
    ⟨hU, hV, fun a ha ↦ (hUV (mk_mem_prod ha hxV)).1.1, fun b hb ↦ (hUV (mk_mem_prod hpU hb)).1.2,
      fun a ha b hb ↦ (hUV (mk_mem_prod ha hb)).2⟩
  set R := localRep₂ f φ e c
  have hR : ∀ n, ContDiffMBOn n R (U ×ˢ V) := fun n ↦
    ((hf n).contDiffMBOn₂ i he hc hbox).contDiffMBOn_prod hU hV
  -- the implicit equation `L (R (u, L⁻¹ z)) = L w`
  set Φ : (B.model i × H) × EuclideanModel H → EuclideanModel H :=
    fun s ↦ L (R (s.1.1, L.symm s.2)) - L s.1.2
  set Ũ : Set ((B.model i × H) × EuclideanModel H) :=
    (fun s ↦ s.1.1) ⁻¹' U ∩ (fun s ↦ L.symm s.2) ⁻¹' V
  have hŨ : IsOpen Ũ := (hU.preimage (by fun_prop)).inter (hV.preimage (by fun_prop))
  have hΦ : SmoothMBOn Φ Ũ := fun n ↦ by
    set T : (B.model i × H) × EuclideanModel H →L[ℝ] B.model i × H :=
      ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _)).prod
        ((L.symm : EuclideanModel H →L[ℝ] H).comp (ContinuousLinearMap.snd ℝ _ _))
    have h1 : ContDiffMBOn n (fun s ↦ R (s.1.1, L.symm s.2)) Ũ :=
      ContDiffMBOn.comp (f := T) hŨ (hU.prod hV) (hR n) (T.contDiffMBOn n Ũ)
        fun s hs ↦ ⟨hs.1, hs.2⟩
    have h2 := ContDiffMBOn.comp hŨ isOpen_univ ((L : H →L[ℝ] EuclideanModel H).contDiffMBOn n univ)
      h1 (mapsTo_univ _ _)
    have h3 : ContDiffMBOn n (fun s : (B.model i × H) × EuclideanModel H ↦ L s.1.2) Ũ :=
      ((L : H →L[ℝ] EuclideanModel H).comp ((ContinuousLinearMap.snd ℝ _ _).comp
        (ContinuousLinearMap.fst ℝ _ _))).contDiffMBOn n Ũ
    exact ContDiffMBOn.sub hŨ h2 h3
  -- the solution `ψ(u, w) = L (e (g (φ⁻¹ u, c⁻¹ w)))`, on an open set `P'`
  set G : B.model i × H → K := fun q ↦ g (φ.symm q.1, c.symm q.2)
  have hGc : ContinuousOn G (φ.target ×ˢ c.target) :=
    hgc.comp_continuousOn ((φ.continuousOn_symm.comp
      (continuousOn_fst (s := φ.target ×ˢ c.target)) fun _ h ↦ h.1).prodMk
      (c.continuousOn_symm.comp (continuousOn_snd (s := φ.target ×ˢ c.target)) fun _ h ↦ h.2))
  set S₁ : Set (B.model i × H) := (φ.target ×ˢ c.target) ∩ G ⁻¹' e.source
  have hS₁ : IsOpen S₁ :=
    hGc.isOpen_inter_preimage (φ.open_target.prod c.open_target) e.open_source
  have heG : ContinuousOn (fun q ↦ e (G q)) S₁ :=
    e.continuousOn.comp (hGc.mono inter_subset_left) fun _ hq ↦ hq.2
  set P' : Set (B.model i × H) := (S₁ ∩ (fun q ↦ q.1) ⁻¹' U) ∩ (fun q ↦ e (G q)) ⁻¹' V
  have hP' : IsOpen P' :=
    (heG.mono inter_subset_left).isOpen_inter_preimage (hS₁.inter (hU.preimage continuous_fst)) hV
  set ψ : B.model i × H → EuclideanModel H := fun q ↦ L (e (G q))
  have hψc : ContinuousOn ψ P' :=
    L.continuous.comp_continuousOn (heG.mono fun _ hq ↦ hq.1.1)
  have hmaps : ∀ q ∈ P', (q, ψ q) ∈ Ũ := fun q hq ↦
    ⟨hq.1.2, by simpa [ψ] using hq.2⟩
  have hzero : ∀ q ∈ P', Φ (q, ψ q) = 0 := by
    intro q hq
    have hGe : G q ∈ e.source := hq.1.1.2
    have hct : q.2 ∈ c.target := hq.1.1.1.2
    simp only [Φ, ψ, R, localRep₂, ContinuousLinearEquiv.symm_apply_apply, e.left_inv hGe, G,
      hfg, c.right_inv hct, sub_self]
  have hB : ∀ q ∈ P', IsUnit (partialFDeriv₂ Φ (q, ψ q)) := by
    intro q hq
    have hGe : G q ∈ e.source := hq.1.1.2
    have hct : q.2 ∈ c.target := hq.1.1.1.2
    have hfG : f (φ.symm q.1, G q) ∈ c.source := by
      simp only [G, hfg]
      exact c.map_target hct
    have h := isUnit_fderiv_normedRep_of_leftInverse (hf1 (φ.symm q.1)) (hg1 (φ.symm q.1))
      (hgf (φ.symm q.1)) he hc hGe hfG
    have heq : (fun z ↦ Φ (q, z)) =
        fun z ↦ normedRep (fun x ↦ f (φ.symm q.1, x)) e c z - L q.2 := rfl
    change IsUnit (fderiv ℝ (fun z ↦ Φ (q, z)) (ψ q))
    rw [heq, fderiv_sub_const]
    exact h
  have hψ : SmoothMBOn ψ P' := smoothMBOn_of_implicit hŨ hΦ hP' hψc hmaps hzero hB
  -- the local representative of `g` is `L⁻¹ ∘ ψ`
  have hrep : ∀ n, ContDiffMBOn n (localRep₂ g φ c e) P' := fun n ↦
    ContDiffMBOn.congr_of_isOpen hP' (fun q _ ↦ by simp [ψ, G, localRep₂])
      (ContDiffMBOn.comp hP' isOpen_univ
        ((L.symm : EuclideanModel H →L[ℝ] H).contDiffMBOn n univ) (hψ n) (mapsTo_univ _ _))
  have hq₀ : (φ p₀, c y₀) ∈ P' := by
    have hG₀ : G (φ p₀, c y₀) = x₀ := by simp [G, φ.left_inv hp₀, c.left_inv hy₀, x₀]
    refine ⟨⟨⟨⟨φ.map_source hp₀, c.map_source hy₀⟩, ?_⟩, hpU⟩, ?_⟩
    · simp only [mem_preimage, hG₀]
      exact hx₀
    · simp only [mem_preimage, hG₀]
      exact hxV
  obtain ⟨U₀, W₀, hU₀, hW₀, h₁, h₂, hsub⟩ := isOpen_prod_iff.1 hP' _ _ hq₀
  refine ⟨i, c, hc, e, he, U₀, W₀, hp₀, hy₀, h₁, h₂,
    ⟨hU₀, hW₀, fun a ha ↦ (hsub (mk_mem_prod ha h₂)).1.1.1.1,
      fun b hb ↦ (hsub (mk_mem_prod h₁ hb)).1.1.1.2,
      fun a ha b hb ↦ (hsub (mk_mem_prod ha hb)).1.1.2⟩, ?_⟩
  exact ContDiffMBOn.contDiffMBOn₂ hU₀ hW₀ ((hrep (k + ℓ)).mono hsub)

end Lemma

end LocallyConvex.Manifolds
