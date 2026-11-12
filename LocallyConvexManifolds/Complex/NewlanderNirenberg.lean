/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.Complex.Basic
public import LocallyConvexAnalysis.Complex.NewlanderNirenberg

/-!
# The Newlander–Nirenberg theorem for real analytic almost complex structures

Let `M` be a manifold modeled on a real Banach space `E` and `J` an almost complex structure on
`M` which is **real analytic** (`AlmostComplexStructure.IsRealAnalytic`: in every chart its local
representative is a real analytic map into `L(E)`) and **integrable** (vanishing Nijenhuis
torsion). Then:

* every point of `M` lies in the domain of a **`J`-holomorphic chart** (`IsHolomorphicChart`):
  a chart `ψ` into a complex Banach space, smooth with smooth inverse in the real sense, whose
  differential is complex linear for `J`, `Dψ(J v) = i Dψ(v)`; its model is `E` with the complex
  structure `J(x₀)` (`AlmostComplexStructure.exists_holomorphic_chart`);
* the transition maps between `J`-holomorphic charts are complex analytic
  (`AlmostComplexStructure.IsHolomorphicChart.complexAnalyticOn_transition`).

So the `J`-holomorphic charts form a holomorphic atlas of `M` inducing `J`. This is the
real analytic Newlander–Nirenberg theorem on Banach manifolds ([Pen70, Théorème 3.5,
pp. 75–76]; compare [Bel05, Theorem 7]). The converse, that the structure induced by a complex
analytic atlas is integrable, is `canonicalJ_isIntegrable`.

## Main definitions

* `AlmostComplexStructure.IsRealAnalytic`: in every chart the local representative of `J` is a
  real analytic map into `L(E)`.
* `AlmostComplexStructure.IsHolomorphicChart`: a chart into a complex Banach space, smooth with
  smooth inverse in the real sense, whose differential is complex linear for `J`.

## Main results

* `AlmostComplexStructure.exists_holomorphic_chart` ([Pen70, Théorème 3.5]): every point lies in
  the domain of a `J`-holomorphic chart.
* `AlmostComplexStructure.IsHolomorphicChart.complexAnalyticOn_transition`: the transition maps
  between `J`-holomorphic charts are complex analytic.
* `nijenhuis_eq_neg_nijenhuisLoc`: the two conventions for the Nijenhuis tensor differ by a sign.

## Proof

In the preferred chart at `x₀`, `J` is a real analytic `Ĵ : U → L(E)` with `Ĵ² = −1` and
vanishing Nijenhuis tensor (`nijenhuis_eq_neg_nijenhuisLoc`: the two conventions differ by a
sign). The local theorem ([LCA], `exists_holomorphic_chart`) gives a chart `φ` of `U` with
`Dφ ∘ Ĵ = i Dφ`, and `ψ = φ ∘ chart` is `J`-holomorphic. For two `J`-holomorphic charts, the real
derivative of `ψ₂ ∘ ψ₁⁻¹` is `B ∘ A` with `A = D(c ∘ ψ₁⁻¹)` and `B = D(ψ₂ ∘ c⁻¹)` in a chart `c`;
`A` intertwines `i` and `J` and `B` intertwines `J` and `i`, so `B ∘ A` is complex linear and
`ψ₂ ∘ ψ₁⁻¹` is complex differentiable, hence analytic (the target is complete).

## Infinite-dimensional subtleties

* **Real analyticity is needed.** For smooth almost complex structures the theorem fails on some
  Banach manifolds ([Pat99, Theorem 3.1, p. 401]) and on some Fréchet manifolds
  ([Lem98, §2, pp. 489–490]).
* **The model.** The chart at `x₀` takes values in `E^{1,0}_{x₀} = ker(J(x₀)_ℂ − i)`, which is
  isomorphic to `(E, J(x₀))`; we do not identify the models at different points, so no
  `ChartedSpace` over a fixed complex model is built.
* Real analyticity of the charts themselves is not proved.

## References

* [D. Beltiță, *Integrability of analytic almost complex structures on Banach manifolds*][Bel05]
* [glaroton, *lc-analysis: Michal–Bastiani calculus on locally convex spaces*][LCA]
* [L. Lempert, *The Dolbeault complex in infinite dimensions I*][Lem98]
* [I. Patyi, *On the ∂̄-equation in a Banach space*][Pat99]
* [J.-P. Penot, *Sur le théorème de Frobenius*][Pen70]
-/

@[expose] public section

open Set Filter Function
open scoped Topology Manifold ContDiff
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

/-- On a normed space, the local Nijenhuis torsion of a differentiable field `Ĵ` of operators is
minus the Nijenhuis tensor of lc-analysis. -/
theorem nijenhuis_eq_neg_nijenhuisLoc {Ĵ : E → E →L[ℝ] E} {y : E} (hĴ : DifferentiableAt ℝ Ĵ y)
    (a b : E) : nijenhuis ℝ Ĵ y a b = -nijenhuisLoc (fun z v ↦ Ĵ z v) y a b := by
  have hD : ∀ w ξ, endD (fun z v ↦ Ĵ z v) y w ξ = fderiv ℝ Ĵ y w ξ := fun w ξ ↦ by
    have h := (hĴ.hasFDerivAt.clm_apply (hasFDerivAt_const ξ y)).hasDirDerivAt w
    rw [endD, h.dMB_eq]
    simp
  simp only [nijenhuis_apply, nijenhuisLoc, hD, map_sub]
  abel

namespace AlmostComplexStructure

variable (J : AlmostComplexStructure E M)

/-- `J` is **real analytic**: in every chart of the atlas its local representative is a real
analytic map `Ĵ : i(U) → L(E)`. -/
def IsRealAnalytic : Prop :=
  ∀ i : atlas E M, ∃ Ĵ : E → E →L[ℝ] E, RealAnalyticOn Ĵ i.1.target ∧
    ∀ y ∈ i.1.target, ∀ v, Ĵ y v = J.loc i y v

/-- A **`J`-holomorphic chart** `ψ` of `M` into a complex normed space `Y`: smooth with smooth
inverse with respect to the charts of `M`, and with complex linear differential,
`Dψ(J v) = i Dψ(v)`, the differential being computed in the preferred chart. -/
structure IsHolomorphicChart {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (ψ : OpenPartialHomeomorph M Y) : Prop where
  smooth : ∀ c ∈ atlas E M, ContDiffOn ℝ ∞ (ψ ∘ c.symm) (c.target ∩ c.symm ⁻¹' ψ.source)
  smooth_symm : ∀ c ∈ atlas E M, ContDiffOn ℝ ∞ (c ∘ ψ.symm) (ψ.target ∩ ψ.symm ⁻¹' c.source)
  complex : ∀ x ∈ ψ.source, ∀ v, fderiv ℝ (ψ ∘ (chartAt E x).symm) (chartAt E x x) (J.toFun x v)
    = Complex.I • fderiv ℝ (ψ ∘ (chartAt E x).symm) (chartAt E x x) v

/-- The local Nijenhuis torsion only depends on the germ of the field. -/
theorem nijenhuisLoc_congr {N N' : E → E → E} {y : E} (h : ∀ᶠ z in 𝓝 y, ∀ v, N z v = N' z v)
    (u v : E) : nijenhuisLoc N y u v = nijenhuisLoc N' y u v := by
  have hD : ∀ w ξ, endD N y w ξ = endD N' y w ξ := fun w ξ ↦
    dMB_congr_of_eventuallyEq (h.mono fun z hz ↦ hz ξ) w
  have hy : ∀ w, N y w = N' y w := h.self_of_nhds
  simp only [nijenhuisLoc, hD, hy]

/-- **The Newlander–Nirenberg theorem, real analytic case, on Banach manifolds**: every point
`x₀` of `M` lies in the domain of a `J`-holomorphic chart into `E^{1,0} = ker(J(x₀)_ℂ − i)`
([Pen70, Théorème 3.5, (6) ⇒ (1), pp. 75–76]). Here `T` is `J(x₀)`
as a continuous linear map. -/
theorem exists_holomorphic_chart [CompleteSpace E] (hω : J.IsRealAnalytic)
    (hJ : J.IsIntegrable) (x₀ : M) :
    ∃ T : E →L[ℝ] E, (∀ v, T v = J.toFun x₀ v) ∧
      ∃ ψ : OpenPartialHomeomorph M (typeOneZero (complexifyCLM T)),
        x₀ ∈ ψ.source ∧ J.IsHolomorphicChart ψ := by
  set c := chartAt E x₀ with hcdef
  set i : atlas E M := prefChart x₀
  have hx₀ : x₀ ∈ c.source := mem_chart_source E x₀
  obtain ⟨Ĵ, hĴω, hĴ⟩ := hω i
  have hU : IsOpen c.target := c.open_target
  have hĴs : ContDiffOn ℝ ∞ Ĵ c.target := (smoothMBOn_iff_contDiffOn hU).1 (hĴω.smoothMBOn hU)
  have hĴd : ∀ y ∈ c.target, DifferentiableAt ℝ Ĵ y := fun y hy ↦
    (hĴs.differentiableOn (by simp) y hy).differentiableAt (hU.mem_nhds hy)
  have hsq : ∀ y ∈ c.target, ∀ v, Ĵ y (Ĵ y v) = -v := fun y hy v ↦ by
    rw [hĴ y hy, hĴ y hy]
    exact J.loc_sq i hy v
  have hN : ∀ y ∈ c.target, nijenhuis ℝ Ĵ y = 0 := fun y hy ↦ by
    refine LinearMap.ext fun a ↦ LinearMap.ext fun b ↦ ?_
    rw [nijenhuis_eq_neg_nijenhuisLoc (hĴd y hy),
      nijenhuisLoc_congr (N' := J.loc i) (Filter.eventually_of_mem (hU.mem_nhds hy)
        fun z hz v ↦ hĴ z hz v), hJ i y hy a b]
    simp
  obtain ⟨φ, hx₀φ, hφU, hφs, hφs', hφc, -, -⟩ :=
    LocallyConvex.Analysis.exists_holomorphic_chart hU hĴω hsq hN (c.map_source hx₀)
  have hcx₀ : c x₀ ∈ c.target := c.map_source hx₀
  refine ⟨Ĵ (c x₀), fun v ↦ by rw [hĴ _ hcx₀]; exact J.loc_pref x₀ v, c ≫ₕ φ,
    ⟨hx₀, hx₀φ⟩, ⟨fun c' hc' ↦ ?_, fun c' hc' ↦ ?_, fun x hx v ↦ ?_⟩⟩
  · -- smoothness of `ψ ∘ c'⁻¹ = φ ∘ (c ∘ c'⁻¹)`
    have hτ : ContDiffOn ℝ ∞ (c ∘ c'.symm) (c'.target ∩ c'.symm ⁻¹' c.source) :=
      (smoothMBOn_iff_contDiffOn (isOpen_transition_domain ⟨c', hc'⟩ i)).1
        (smoothMBOn_transition' ⟨c', hc'⟩ i)
    refine (hφs.comp (s := c'.target ∩ c'.symm ⁻¹' (c ≫ₕ φ).source)
      (hτ.mono fun y (hy : y ∈ c'.target ∩ c'.symm ⁻¹' (c ≫ₕ φ).source) ↦ ⟨hy.1, hy.2.1⟩)
      fun y (hy : y ∈ c'.target ∩ c'.symm ⁻¹' (c ≫ₕ φ).source) ↦ hy.2.2).congr fun y _ ↦ rfl
  · -- smoothness of `c' ∘ ψ⁻¹ = (c' ∘ c⁻¹) ∘ φ⁻¹`
    have hτ : ContDiffOn ℝ ∞ (c' ∘ c.symm) (c.target ∩ c.symm ⁻¹' c'.source) :=
      (smoothMBOn_iff_contDiffOn (isOpen_transition_domain i ⟨c', hc'⟩)).1
        (smoothMBOn_transition' i ⟨c', hc'⟩)
    refine (hτ.comp (s := (c ≫ₕ φ).target ∩ (c ≫ₕ φ).symm ⁻¹' c'.source)
      (hφs'.mono fun z (hz : z ∈ (c ≫ₕ φ).target ∩ (c ≫ₕ φ).symm ⁻¹' c'.source) ↦ hz.1.1)
      fun z (hz : z ∈ (c ≫ₕ φ).target ∩ (c ≫ₕ φ).symm ⁻¹' c'.source) ↦
        ⟨hz.1.2, hz.2⟩).congr fun z _ ↦ rfl
  · -- complex linearity
    set cx := chartAt E x
    have hxc : x ∈ c.source := hx.1
    have hxφ : c x ∈ φ.source := hx.2
    have hcxx : cx x ∈ cx.target ∩ cx.symm ⁻¹' c.source :=
      ⟨cx.map_source (mem_chart_source E x), by
        rw [mem_preimage, cx.left_inv (mem_chart_source E x)]; exact hxc⟩
    have hτd : HasFDerivAt (c ∘ cx.symm) (fderiv ℝ (c ∘ cx.symm) (cx x)) (cx x) := by
      have hτ : ContDiffOn ℝ ∞ (c ∘ cx.symm) (cx.target ∩ cx.symm ⁻¹' c.source) :=
        (smoothMBOn_iff_contDiffOn (isOpen_transition_domain (prefChart x) i)).1
          (smoothMBOn_transition' (prefChart x) i)
      exact ((hτ.contDiffAt ((isOpen_transition_domain (prefChart x) i).mem_nhds
        hcxx)).differentiableAt (by simp)).hasFDerivAt
    have hφd : HasFDerivAt φ (fderiv ℝ φ (c x)) ((c ∘ cx.symm) (cx x)) := by
      have h1 : (c ∘ cx.symm) (cx x) = c x := by
        simp [cx.left_inv (mem_chart_source E x)]
      rw [h1]
      exact ((hφs.contDiffAt (φ.open_source.mem_nhds hxφ)).differentiableAt (by simp)).hasFDerivAt
    have hcomp := hφd.comp (cx x) hτd
    have hfun : ⇑(c ≫ₕ φ) ∘ cx.symm = φ ∘ (c ∘ cx.symm) := rfl
    rw [hfun, hcomp.fderiv]
    simp only [ContinuousLinearMap.comp_apply]
    -- `Dτ(J v) = Ĵ(c x)(Dτ v)`, by the local representative of `J` in `c`
    obtain ⟨T, S, hloc, hTS, -, -, hS⟩ := J.loc_eq i (c.map_source hxc)
    have hcl : i.1.symm (c x) = x := c.left_inv hxc
    rw [hcl] at hloc hS
    have hSτ : ∀ w, S w = fderiv ℝ (c ∘ cx.symm) (cx x) w := fun w ↦ by
      rw [← hS w, tangentCoordChange, ((hτd.hasDirDerivAt w).dMB_eq)]
    have hJτ : fderiv ℝ (c ∘ cx.symm) (cx x) (J.toFun x v) =
        Ĵ (c x) (fderiv ℝ (c ∘ cx.symm) (cx x) v) := by
      rw [hĴ _ (c.map_source hxc), ← hSτ, ← hSτ, hloc, hTS]
    rw [hJτ]
    exact hφc (c x) hxφ _

namespace IsHolomorphicChart

variable {J}

omit [MBManifold E M] in
/-- **Transition maps between `J`-holomorphic charts are complex analytic**: their real
differentials are complex linear, so they are complex differentiable, hence complex analytic. -/
theorem complexAnalyticOn_transition {Y₁ Y₂ : Type*} [NormedAddCommGroup Y₁] [NormedSpace ℂ Y₁]
    [NormedAddCommGroup Y₂] [NormedSpace ℂ Y₂] [CompleteSpace Y₂]
    {ψ₁ : OpenPartialHomeomorph M Y₁} {ψ₂ : OpenPartialHomeomorph M Y₂}
    (h₁ : J.IsHolomorphicChart ψ₁) (h₂ : J.IsHolomorphicChart ψ₂) :
    ComplexAnalyticOn (ψ₂ ∘ ψ₁.symm) (ψ₁.target ∩ ψ₁.symm ⁻¹' ψ₂.source) := by
  have hO : IsOpen (ψ₁.target ∩ ψ₁.symm ⁻¹' ψ₂.source) :=
    ψ₁.isOpen_inter_preimage_symm ψ₂.open_source
  refine DifferentiableOn.complexAnalyticOn hO fun z hz ↦ ?_
  refine DifferentiableAt.differentiableWithinAt ?_
  set p := ψ₁.symm z with hpdef
  set c := chartAt E p
  have hpc : p ∈ c.source := mem_chart_source E p
  have hc : c ∈ atlas E M := chart_mem_atlas E p
  have hp₁ : p ∈ ψ₁.source := ψ₁.map_target hz.1
  have hp₂ : p ∈ ψ₂.source := hz.2
  have hcp₁ : c p ∈ c.target ∩ c.symm ⁻¹' ψ₁.source :=
    ⟨c.map_source hpc, by rw [mem_preimage, c.left_inv hpc]; exact hp₁⟩
  have hcp₂ : c p ∈ c.target ∩ c.symm ⁻¹' ψ₂.source :=
    ⟨c.map_source hpc, by rw [mem_preimage, c.left_inv hpc]; exact hp₂⟩
  have hS₁ : IsOpen (ψ₁.target ∩ ψ₁.symm ⁻¹' c.source) :=
    ψ₁.isOpen_inter_preimage_symm c.open_source
  have hzS₁ : z ∈ ψ₁.target ∩ ψ₁.symm ⁻¹' c.source := ⟨hz.1, hpc⟩
  have hT₁ : IsOpen (c.target ∩ c.symm ⁻¹' ψ₁.source) :=
    c.isOpen_inter_preimage_symm ψ₁.open_source
  have hT₂ : IsOpen (c.target ∩ c.symm ⁻¹' ψ₂.source) :=
    c.isOpen_inter_preimage_symm ψ₂.open_source
  -- the real derivatives `A = D(c ∘ ψ₁⁻¹)(z)`, `P = D(ψ₁ ∘ c⁻¹)(c p)`, `B = D(ψ₂ ∘ c⁻¹)(c p)`
  set A := fderiv ℝ (c ∘ ψ₁.symm) z
  set P := fderiv ℝ (ψ₁ ∘ c.symm) (c p)
  set B := fderiv ℝ (ψ₂ ∘ c.symm) (c p)
  have hA : HasFDerivAt (c ∘ ψ₁.symm) A z :=
    (((h₁.smooth_symm c hc).contDiffAt (hS₁.mem_nhds hzS₁)).differentiableAt
      (by simp)).hasFDerivAt
  have hP : HasFDerivAt (ψ₁ ∘ c.symm) P (c p) :=
    (((h₁.smooth c hc).contDiffAt (hT₁.mem_nhds hcp₁)).differentiableAt (by simp)).hasFDerivAt
  have hB : HasFDerivAt (ψ₂ ∘ c.symm) B (c p) :=
    (((h₂.smooth c hc).contDiffAt (hT₂.mem_nhds hcp₂)).differentiableAt (by simp)).hasFDerivAt
  have hAz : (c ∘ ψ₁.symm) z = c p := rfl
  -- `P ∘ A = id`
  have hPA : ∀ w, P (A w) = w := by
    have hc1 := (hAz ▸ hP).comp z hA
    have hev : (ψ₁ ∘ c.symm) ∘ (c ∘ ψ₁.symm) =ᶠ[𝓝 z] id :=
      Filter.eventuallyEq_of_mem (hS₁.mem_nhds hzS₁) fun z' hz' ↦ by
        simp only [Function.comp_apply, c.left_inv hz'.2, ψ₁.right_inv hz'.1, id]
    have hL := (hc1.congr_of_eventuallyEq hev.symm).unique (hasFDerivAt_id z)
    exact fun w ↦ congrArg (fun L : Y₁ →L[ℝ] Y₁ ↦ L w) hL
  -- `A ∘ P = id`
  have hAP : ∀ u, A (P u) = u := by
    have hPc : (ψ₁ ∘ c.symm) (c p) = z := by
      change ψ₁ (c.symm (c p)) = z
      rw [c.left_inv hpc, hpdef, ψ₁.right_inv hz.1]
    have hc2 := (hPc ▸ hA).comp (c p) hP
    have hev : (c ∘ ψ₁.symm) ∘ (ψ₁ ∘ c.symm) =ᶠ[𝓝 (c p)] id :=
      Filter.eventuallyEq_of_mem (hT₁.mem_nhds hcp₁) fun y hy ↦ by
        simp only [Function.comp_apply, ψ₁.left_inv hy.2, c.right_inv hy.1, id]
    have hL := (hc2.congr_of_eventuallyEq hev.symm).unique (hasFDerivAt_id (c p))
    exact fun u ↦ congrArg (fun L : E →L[ℝ] E ↦ L u) hL
  -- complex linearity of `B ∘ A`
  have hcx : chartAt E p = c := rfl
  have hAI : ∀ w, A (Complex.I • w) = J.toFun p (A w) := fun w ↦ by
    have h := h₁.complex p hp₁ (A w)
    rw [hcx, hPA] at h
    rw [← h, hAP]
  have hBA : ∀ w, B (A (Complex.I • w)) = Complex.I • B (A w) := fun w ↦ by
    rw [hAI]
    have h := h₂.complex p hp₂ (A w)
    rw [hcx] at h
    exact h
  -- the transition is complex differentiable at `z`
  have hT : HasFDerivAt (ψ₂ ∘ ψ₁.symm) (B.comp A) z := by
    have hc3 := (hAz ▸ hB).comp z hA
    have hev : (ψ₂ ∘ c.symm) ∘ (c ∘ ψ₁.symm) =ᶠ[𝓝 z] ψ₂ ∘ ψ₁.symm :=
      Filter.eventuallyEq_of_mem (hS₁.mem_nhds hzS₁) fun z' hz' ↦ by
        simp only [Function.comp_apply, c.left_inv hz'.2]
    exact hc3.congr_of_eventuallyEq hev.symm
  let Lℂ : Y₁ →L[ℂ] Y₂ :=
    { toFun := B.comp A
      map_add' := (B.comp A).map_add
      map_smul' := fun c w ↦ map_smul_of_map_I_smul (T := B.comp A) (B.comp A).map_add
        (fun r w ↦ (B.comp A).map_smul r w) hBA c w
      cont := (B.comp A).continuous }
  exact (hasFDerivAt_of_restrictScalars ℝ hT (f' := Lℂ) rfl).differentiableAt

end IsHolomorphicChart

end AlmostComplexStructure

end LocallyConvex.Manifolds
