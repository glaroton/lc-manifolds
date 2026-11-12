/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.Analytic.Submanifold
public import LocallyConvexManifolds.Examples.SphereLocalAddition
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# Example: the sphere is a real analytic manifold with a real analytic local addition

Let `H` be a real inner product space, not necessarily complete, `e ∈ H` a unit vector and
`S ⊆ H` the unit sphere. We show that `S` is a real analytic manifold, and that the radial
projection is a real analytic local addition on it. This is the real analytic case of
`sphereLocalAddition` (`Examples/SphereLocalAddition.lean`).

## Main definitions

* `sphereAnalyticLocalAddition`: the radial projection as a local addition on the real analytic
  manifold `S`.

## Main results

* `isSplitAnalyticSubmanifold_sphere`: `S` is a split real analytic submanifold of `H` modeled
  on `e^⊥`; hence (`IsSplitAnalyticSubmanifold.realAnalyticManifold`) **a real analytic
  manifold**, with the restrictions of the real analytic slice charts as atlas.
* `sphereAnalyticLocalAddition`: the radial projection

    `Σ(p, w) = (p + w) / ‖p + w‖ = (p + w) / √⟪p + w, p + w⟫`,   `w ⊥ p`,

  defined on all of `TS`, with `θ = (π, Σ)` mapping `TS` onto `{(p, q) : ⟪p, q⟫ > 0}` and inverse
  `(p, q) ↦ (p, q/⟪p, q⟫ - p)`, is a local addition on the real analytic manifold `S`, and
  `isRealAnalytic_sphereAnalyticLocalAddition`: **it is a real analytic local addition**
  ([GN26, p. 325, after Definition 3.8.11]: `θ` is a diffeomorphism of real analytic manifolds;
  page numbers refer to arXiv:2602.12362v1).

## Real analyticity of the formulas

Real analyticity is meant in Milnor's sense (`LocallyConvex.Analysis.RealAnalyticOn`: local
restrictions of complex analytic maps on the complexification), without completeness. The scalar
product `⟪·, ·⟫` is a continuous bilinear form, hence real analytic (`RealAnalyticOn.bilin`); its
complexification is the complex *bilinear* (not sesquilinear) extension to `H_ℂ × H_ℂ`. The
functions `t ↦ √t` on `t > 0` and `t ↦ t⁻¹` on `t ≠ 0` extend holomorphically to the slit plane
and to `ℂ \ {0}` (`realAnalyticOn_of_differentiableOn`); the norm itself is never used as an
analytic function, only `‖x‖ = √⟪x, x⟫` on `x ≠ 0`. The charts of the sphere (`Sphere.chart`,
built from the height `√(1 - ‖tang q‖²)`, composed with Householder reflections) are real
analytic for the same reasons.

## Implementation notes

* The real analytic atlas consists of the real analytic slice charts; it is not the atlas of all
  smooth slice charts used by `isEmbeddedSubmanifold_sphere`, so `TS` here is a different type
  from the tangent bundle of `sphereLocalAddition`, and the two local additions are different
  objects given by the same formula. The tangent spaces `T_p S = p^⊥ ⊆ H` agree.
* The model `e^⊥` is complemented by the orthogonal projection (it is the orthogonal complement of
  the finite-dimensional, hence complete, line `ℝ e`); this is what `IsSplitAnalyticSubmanifold`
  needs (see `LocallyConvexManifolds.Analytic.Submanifold` for why).
* Universes: the analytic calculus for bilinear maps requires the factors to live in one universe,
  so scalar multiplication by real analytic functions goes through `ULift ℝ`
  (`RealAnalyticOn.smul_real`).
* Normalization of the analytic local addition ([GN26, (3.55)]) is not proved here; for
  the smooth structure it is `isNormalized_sphereLocalAddition`.
* Glöckner–Neeb do not treat the sphere. We do not claim this construction is new.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function
open scoped Topology RealInnerProductSpace
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

/-! ### Real analytic functions of one variable -/

namespace ScalarAnalytic

open Complexification

/-- `ℂ → ℝ_ℂ`, `z ↦ Re z + i Im z`. -/
def toCx : ℂ →L[ℂ] Complexification ℝ where
  toFun z := Complexification.mk z.re z.im
  map_add' z w := Complexification.ext (by simp) (by simp)
  map_smul' c z := Complexification.ext (by simp [Complex.mul_re]) (by
    simp only [Complex.mul_im, im_mk, RingHom.id_apply, im_smul, re_mk, smul_eq_mul])
  cont := continuous_mk Complex.continuous_re Complex.continuous_im

@[simp] theorem re_toCx (z : ℂ) : re (toCx z) = z.re := rfl
@[simp] theorem im_toCx (z : ℂ) : im (toCx z) = z.im := rfl

/-- `ℝ_ℂ → ℂ`, `u + i v ↦ u + i v`. -/
def ofCx : Complexification ℝ →L[ℂ] ℂ where
  toFun p := ⟨re p, im p⟩
  map_add' p q := Complex.ext rfl rfl
  map_smul' c p := Complex.ext (by simp) (by simp)
  cont := Complex.equivRealProdCLM.symm.continuous.comp
    (continuous_re.prodMk continuous_im)

/-- A complex differentiable function on an open subset of `ℂ` is complex analytic in the sense of
`LocallyConvex.Analysis` (smooth with complex linear differentials). -/
theorem complexAnalyticOn_of_differentiableOn {g : ℂ → ℂ} {W : Set ℂ} (hW : IsOpen W)
    (hg : DifferentiableOn ℂ g W) : ComplexAnalyticOn g W := by
  rw [complexAnalyticOn_iff_holomorphicOn hW]
  refine ⟨(smoothMBOn_iff_contDiffOn hW).2 ((hg.contDiffOn hW).restrict_scalars ℝ),
    fun x hx c h ↦ ?_⟩
  have key : ∀ v : ℂ, dMB g (x, v) = deriv g x * v := fun v ↦ by
    refine HasDirDerivAt.dMB_eq ?_
    have hgx : HasDerivAt g (deriv g x) (x + 0 * v) := by
      rw [zero_mul, add_zero]
      exact (hg.differentiableAt (hW.mem_nhds hx)).hasDerivAt
    have hl : HasDerivAt (fun w : ℂ ↦ x + w * v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).mul_const v).const_add x
    have he : HasDerivAt (fun w : ℂ ↦ g (x + w * v)) (deriv g x * v) ((0 : ℝ) : ℂ) := by
      rw [Complex.ofReal_zero]
      exact hgx.comp (0 : ℂ) hl
    have := hasDerivAt_iff_tendsto_slope_zero.1 he.comp_ofReal
    unfold HasDirDerivAt
    refine this.congr fun t ↦ ?_
    simp [Complex.real_smul]
  rw [key, key, smul_eq_mul, smul_eq_mul]
  ring

/-- **Real functions with a holomorphic extension are real analytic** (Milnor's sense, as in
`LocallyConvex.Analysis.RealAnalyticOn`): if `g` is complex differentiable on an open `W ⊆ ℂ`
containing `U ⊆ ℝ` and `g t = f t` on `U`, then `f` is real analytic on `U`. -/
theorem realAnalyticOn_of_differentiableOn {f : ℝ → ℝ} {U : Set ℝ} {g : ℂ → ℂ} {W : Set ℂ}
    (hW : IsOpen W) (hg : DifferentiableOn ℂ g W) (hUW : ∀ t ∈ U, (t : ℂ) ∈ W)
    (hgf : ∀ t ∈ U, g t = f t) : RealAnalyticOn f U := by
  have hW' : IsOpen (ofCx ⁻¹' W) := hW.preimage ofCx.continuous
  have hof : ∀ t : ℝ, ofCx (ofReal t) = (t : ℂ) := fun t ↦ by
    apply Complex.ext <;> rfl
  refine ⟨ofCx ⁻¹' W, hW', toCx ∘ g ∘ ofCx, ?_, fun t ht ↦ ⟨?_, ?_⟩⟩
  · exact (toCx.complexAnalyticOn isOpen_univ).comp
      ((complexAnalyticOn_of_differentiableOn hW hg).comp (ofCx.complexAnalyticOn hW') hW' hW
        fun _ hp ↦ hp) hW' isOpen_univ (mapsTo_univ _ _)
  · change ofCx (ofReal t) ∈ W
    rw [hof]; exact hUW t ht
  · change toCx (g (ofCx (ofReal t))) = ofReal (f t)
    rw [hof, hgf t ht]
    exact Complexification.ext (by simp) (by simp)

/-- `√` is real analytic on `(0, ∞)`. -/
theorem realAnalyticOn_sqrt : RealAnalyticOn Real.sqrt (Ioi 0) := by
  refine realAnalyticOn_of_differentiableOn (g := fun z ↦ z ^ (1 / 2 : ℂ))
    Complex.isOpen_slitPlane (fun z hz ↦ (HasStrictDerivAt.hasDerivAt
      (Complex.hasStrictDerivAt_cpow_const hz)).differentiableAt.differentiableWithinAt)
    (fun t ht ↦ Complex.ofReal_mem_slitPlane.2 ht) fun t ht ↦ ?_
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (le_of_lt ht)]
  norm_num

/-- `t ↦ t⁻¹` is real analytic on `ℝ \ {0}`. -/
theorem realAnalyticOn_inv : RealAnalyticOn (fun t : ℝ ↦ t⁻¹) {t | t ≠ 0} := by
  refine realAnalyticOn_of_differentiableOn (g := fun z ↦ z⁻¹) isOpen_compl_singleton
    (fun z hz ↦ (differentiableAt_inv hz).differentiableWithinAt)
    (fun t ht ↦ Complex.ofReal_ne_zero.2 ht) fun t _ ↦ ?_
  simp

end ScalarAnalytic

open ScalarAnalytic

/-! ### Scalar multiplication and inner products -/

section Operations

universe u v

/-- Real analyticity only depends on the values on the set (domain and target in arbitrary
universes). -/
theorem realAnalyticOn_congr' {E : Type u} {F : Type v} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] {f g : E → F}
    {U : Set E} (h : EqOn f g U) (hf : RealAnalyticOn f U) : RealAnalyticOn g U := by
  obtain ⟨V, hV, G, hG, hext⟩ := hf
  exact ⟨V, hV, G, hG, fun x hx ↦ ⟨(hext x hx).1, by rw [← h hx]; exact (hext x hx).2⟩⟩

variable {E F : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] {U : Set E}

/-- Products of a real analytic function and a real analytic map are real analytic. The bilinear
map `(c, x) ↦ c • x` is applied with the scalars lifted to the universe of `F`. -/
theorem RealAnalyticOn.smul_real {c : E → ℝ} {s : E → F} (hc : RealAnalyticOn c U)
    (hs : RealAnalyticOn s U) : RealAnalyticOn (fun x ↦ c x • s x) U := by
  let L : ℝ →L[ℝ] ULift.{u} ℝ :=
    (ContinuousLinearEquiv.ulift (R₁ := ℝ) (M₁ := ℝ)).symm.toContinuousLinearMap
  have hc' : RealAnalyticOn (fun x ↦ L (c x)) U :=
    (L.realAnalyticOn univ).comp hc (mapsTo_univ _ _)
  let β : ULift.{u} ℝ →ₗ[ℝ] F →ₗ[ℝ] F := LinearMap.mk₂ ℝ (fun a x ↦ a.down • x)
    (fun a b x ↦ by simp [add_smul]) (fun r a x ↦ by simp [smul_smul])
    (fun a x y ↦ smul_add _ _ _) (fun r a x ↦ smul_comm _ _ _)
  have hβ : Continuous fun p : ULift.{u} ℝ × F ↦ β p.1 p.2 :=
    (continuous_uliftDown.comp continuous_fst).smul continuous_snd
  exact RealAnalyticOn.bilin β hβ hc' hs

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Inner products of real analytic maps are real analytic. -/
theorem RealAnalyticOn.inner_real {f g : E → H} (hf : RealAnalyticOn f U)
    (hg : RealAnalyticOn g U) : RealAnalyticOn (fun x ↦ ⟪f x, g x⟫) U :=
  RealAnalyticOn.bilin (innerₗ H) continuous_inner hf hg

end Operations

/-! ### The formulas on the sphere are real analytic -/

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

namespace Sphere

/-- `t ↦ 1/√t` is real analytic on `(0, ∞)`. -/
theorem realAnalyticOn_inv_sqrt : RealAnalyticOn (fun t : ℝ ↦ (√t)⁻¹) (Ioi 0) :=
  realAnalyticOn_inv.comp realAnalyticOn_sqrt fun _ ht ↦ Real.sqrt_ne_zero'.2 ht

/-- `σ(p, w) = (p + w)/‖p + w‖` is real analytic where `p + w ≠ 0`. -/
theorem realAnalyticOn_sigma : RealAnalyticOn (sigma (H := H)) {z : H × H | z.1 + z.2 ≠ 0} := by
  have hs : RealAnalyticOn (fun z : H × H ↦ z.1 + z.2) univ :=
    (ContinuousLinearMap.fst ℝ H H + ContinuousLinearMap.snd ℝ H H).realAnalyticOn univ
  have hq : RealAnalyticOn (fun z : H × H ↦ ⟪z.1 + z.2, z.1 + z.2⟫) univ :=
    RealAnalyticOn.inner_real hs hs
  have hc : RealAnalyticOn (fun z : H × H ↦ (√⟪z.1 + z.2, z.1 + z.2⟫)⁻¹)
      {z : H × H | z.1 + z.2 ≠ 0} :=
    realAnalyticOn_inv_sqrt.comp (hq.mono (subset_univ _)) fun z hz ↦ by
      change 0 < ⟪z.1 + z.2, z.1 + z.2⟫
      exact real_inner_self_pos.2 hz
  refine realAnalyticOn_congr (fun z _ ↦ ?_) (RealAnalyticOn.smul_real hc (hs.mono (subset_univ _)))
  simp only [sigma, ← norm_eq_sqrt_real_inner]

/-- `τ(p, q) = q/⟪p, q⟫ - p` is real analytic where `⟪p, q⟫ > 0`. -/
theorem realAnalyticOn_tau : RealAnalyticOn (tau (H := H)) {z : H × H | 0 < ⟪z.1, z.2⟫} := by
  have hfst := (ContinuousLinearMap.fst ℝ H H).realAnalyticOn {z : H × H | 0 < ⟪z.1, z.2⟫}
  have hsnd := (ContinuousLinearMap.snd ℝ H H).realAnalyticOn {z : H × H | 0 < ⟪z.1, z.2⟫}
  have ha : RealAnalyticOn (fun z : H × H ↦ ⟪z.1, z.2⟫⁻¹) {z : H × H | 0 < ⟪z.1, z.2⟫} :=
    realAnalyticOn_inv.comp (RealAnalyticOn.inner_real hfst hsnd) fun z hz ↦ ne_of_gt hz
  exact RealAnalyticOn.sub (RealAnalyticOn.smul_real ha hsnd) hfst

variable {e : H}

/-- The tangential part `q ↦ q - ⟪q, e⟫ e` is real analytic. -/
theorem realAnalyticOn_tang (e : H) (U : Set H) : RealAnalyticOn (tang e) U := by
  have hid := (ContinuousLinearMap.id ℝ H).realAnalyticOn U
  exact RealAnalyticOn.sub hid (RealAnalyticOn.smul_real
    (RealAnalyticOn.inner_real hid (realAnalyticOn_const e U)) (realAnalyticOn_const e U))

/-- The height `q ↦ √(1 - ‖tang q‖²)` is real analytic where `‖tang q‖ < 1`. -/
theorem realAnalyticOn_height (e : H) : RealAnalyticOn (height e) {q | ‖tang e q‖ < 1} := by
  have ht := realAnalyticOn_tang e {q | ‖tang e q‖ < 1}
  have hr : RealAnalyticOn (fun q ↦ 1 - ⟪tang e q, tang e q⟫) {q | ‖tang e q‖ < 1} :=
    RealAnalyticOn.sub (realAnalyticOn_const 1 _) (RealAnalyticOn.inner_real ht ht)
  refine realAnalyticOn_congr' (fun q _ ↦ ?_) (realAnalyticOn_sqrt.comp hr fun q hq ↦ ?_)
  · simp only [comp_apply, height, real_inner_self_eq_norm_sq]
  · change 0 < 1 - ⟪tang e q, tang e q⟫
    rw [real_inner_self_eq_norm_sq]
    have h0 := norm_nonneg (tang e q)
    nlinarith [hq.out]

/-- The chart of the hemisphere around `e` is a real analytic diffeomorphism. -/
theorem chart_mem_realAnalyticGroupoid (he : ‖e‖ = 1) : chart he ∈ realAnalyticGroupoid H := by
  refine ⟨RealAnalyticOn.add ((ContinuousLinearMap.id ℝ H).realAnalyticOn _)
      (RealAnalyticOn.smul_real (RealAnalyticOn.neg ((realAnalyticOn_height e).mono
        fun q (hq : q ∈ (chart he).source) ↦ hq.1)) (realAnalyticOn_const e _)),
    RealAnalyticOn.add ((ContinuousLinearMap.id ℝ H).realAnalyticOn _)
      (RealAnalyticOn.smul_real ((realAnalyticOn_height e).mono
        fun q (hq : q ∈ (chart he).target) ↦ hq.1) (realAnalyticOn_const e _))⟩

/-- Householder reflections are real analytic diffeomorphisms. -/
theorem refl_mem_realAnalyticGroupoid (e p : H) :
    (refl e p).toHomeomorph.toOpenPartialHomeomorph ∈ realAnalyticGroupoid H :=
  ⟨(refl e p).toContinuousLinearEquiv.toContinuousLinearMap.realAnalyticOn _,
    (refl e p).symm.toContinuousLinearEquiv.toContinuousLinearMap.realAnalyticOn _⟩

/-- The slice charts of the sphere are real analytic diffeomorphisms. -/
theorem chartAt'_mem_realAnalyticGroupoid (he : ‖e‖ = 1) (p : H) :
    chartAt' he p ∈ realAnalyticGroupoid H :=
  (realAnalyticGroupoid H).trans (refl_mem_realAnalyticGroupoid e p)
    (chart_mem_realAnalyticGroupoid he)

end Sphere

open Sphere

variable {e : H}

/-- **The unit sphere of a real inner product space is a split real analytic submanifold**,
modeled on `e^⊥` for any unit vector `e`. No completeness is assumed. -/
theorem isSplitAnalyticSubmanifold_sphere (he : ‖e‖ = 1) :
    IsSplitAnalyticSubmanifold (Metric.sphere (0 : H) 1) (ℝ ∙ e)ᗮ := by
  refine ⟨⟨(ℝ ∙ e)ᗮ.orthogonalProjectionOnto,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self⟩,
    fun p hp ↦ ⟨chartAt' he p, ⟨chartAt'_mem_realAnalyticGroupoid he p, fun q hq ↦ ?_⟩, ?_⟩⟩
  · rw [mem_sphere_zero_iff_norm, ← (refl e p).norm_map q]
    exact norm_eq_one_iff he hq.2
  · exact mem_chartAt'_source he (mem_sphere_zero_iff_norm.mp hp)

/-- **The unit sphere is a real analytic manifold** modeled on `e^⊥`. -/
theorem realAnalyticManifold_sphere (he : ‖e‖ = 1) :
    letI := (isSplitAnalyticSubmanifold_sphere he).chartedSpace
    RealAnalyticManifold (ℝ ∙ e)ᗮ (Metric.sphere (0 : H) 1) :=
  (isSplitAnalyticSubmanifold_sphere he).realAnalyticManifold

/-- The tangent space of the sphere at `p` is `p^⊥`. -/
theorem tangentSpace_sphere_analytic (he : ‖e‖ = 1) (p : Metric.sphere (0 : H) 1) :
    (isSplitAnalyticSubmanifold_sphere he).tangentSpace p = {w | ⟪(p : H), w⟫ = 0} :=
  tangentSpace_sphere he p

/-- The real analytic ambient data `σ(p, w) = (p + w)/‖p + w‖`, `τ(p, q) = q/⟪p, q⟫ - p` of the
local addition of the sphere. -/
def sphereAnalyticAmbientAddition (he : ‖e‖ = 1) :
    AnalyticAmbientAddition (isSplitAnalyticSubmanifold_sphere he) where
  Ω := {z : H × H | z.1 + z.2 ≠ 0}
  isOpen_Ω := isOpen_ne_fun (by fun_prop) continuous_const
  σ := sigma
  realAnalyticOn_σ := realAnalyticOn_sigma
  V := {z : H × H | 0 < ⟪z.1, z.2⟫}
  isOpen_V := isOpen_lt continuous_const (by fun_prop)
  τ := tau
  realAnalyticOn_τ := realAnalyticOn_tau
  zero_mem p := by
    have hp : ‖(p : H)‖ = 1 := mem_sphere_zero_iff_norm.mp p.2
    change (p : H) + 0 ≠ 0
    rw [add_zero, ← norm_ne_zero_iff, hp]
    exact one_ne_zero
  σ_zero p := by
    have hp : ‖(p : H)‖ = 1 := mem_sphere_zero_iff_norm.mp p.2
    simp [sigma, hp]
  σ_mem p w _ hΩ := mem_sphere_zero_iff_norm.mpr (norm_sigma hΩ)
  mem_V p w hw _ := by
    have hp : ‖(p : H)‖ = 1 := mem_sphere_zero_iff_norm.mp p.2
    rw [tangentSpace_sphere_analytic he p] at hw
    change 0 < ⟪(p : H), sigma ((p : H), w)⟫
    rw [inner_sigma hp hw]
    exact inv_pos.2 (norm_pos_iff.2 (add_ne_zero_of_inner hp hw))
  τ_σ p w hw _ := by
    rw [tangentSpace_sphere_analytic he p] at hw
    exact tau_sigma (mem_sphere_zero_iff_norm.mp p.2) hw
  τ_mem p q hV := by
    rw [tangentSpace_sphere_analytic he p]
    exact inner_tau hV (mem_sphere_zero_iff_norm.mp p.2)
  mem_Ω p q hV := by
    have hq : ‖(q : H)‖ = 1 := mem_sphere_zero_iff_norm.mp q.2
    change (p : H) + tau ((p : H), (q : H)) ≠ 0
    rw [add_tau]
    refine smul_ne_zero (inv_ne_zero (ne_of_gt hV)) ?_
    rw [← norm_ne_zero_iff, hq]
    exact one_ne_zero
  σ_τ p q hV := sigma_tau hV (mem_sphere_zero_iff_norm.mp q.2)

/-- **The real analytic local addition on the unit sphere** of a real inner product space (no
completeness): `Σ(p, w) = (p + w)/‖p + w‖` for `w ∈ T_p S = p^⊥` (ambient vector), defined on all
of `TS`, with `θ = (π, Σ)` mapping `TS` onto `{(p, q) : ⟪p, q⟫ > 0}` and inverse
`(p, q) ↦ (p, q/⟪p, q⟫ - p)`. Here `S` carries its real analytic structure
(`realAnalyticManifold_sphere`). -/
def sphereAnalyticLocalAddition (he : ‖e‖ = 1) :
    letI := (isSplitAnalyticSubmanifold_sphere he).chartedSpace
    haveI := realAnalyticManifold_sphere he
    LocalAddition (ℝ ∙ e)ᗮ (Metric.sphere (0 : H) 1) :=
  letI := (isSplitAnalyticSubmanifold_sphere he).chartedSpace
  haveI := realAnalyticManifold_sphere he
  (sphereAnalyticAmbientAddition he).toLocalAddition rfl

/-- `Σ(p, w) = (p + w)/‖p + w‖`, where `w` is the ambient vector of the tangent vector; every
tangent vector lies in the domain. -/
theorem sphereAnalyticLocalAddition_toFun (he : ‖e‖ = 1) :
    letI := (isSplitAnalyticSubmanifold_sphere he).chartedSpace
    haveI := realAnalyticManifold_sphere he
    ∀ v : TangentBundle (ℝ ∙ e)ᗮ (Metric.sphere (0 : H) 1),
      v ∈ (sphereAnalyticLocalAddition he).source ∧
      (((sphereAnalyticLocalAddition he).toFun v : Metric.sphere (0 : H) 1) : H) =
        ‖(v.proj : H) + (isSplitAnalyticSubmanifold_sphere he).ambVec v‖⁻¹ •
          ((v.proj : H) + (isSplitAnalyticSubmanifold_sphere he).ambVec v) := by
  let _ := (isSplitAnalyticSubmanifold_sphere he).chartedSpace
  have _ := realAnalyticManifold_sphere he
  intro v
  have hw := (isSplitAnalyticSubmanifold_sphere he).ambVec_mem_tangentSpace rfl v
  rw [tangentSpace_sphere_analytic he] at hw
  have hv : v ∈ (sphereAnalyticAmbientAddition he).source :=
    add_ne_zero_of_inner (mem_sphere_zero_iff_norm.mp v.proj.2) hw
  exact ⟨hv, (sphereAnalyticAmbientAddition he).toLocalAddition_toFun rfl hv⟩

/-- `θ = (π, Σ)` maps `TS` onto `{(p, q) : ⟪p, q⟫ > 0}`. -/
theorem mem_sphereAnalyticLocalAddition_target (he : ‖e‖ = 1) :
    letI := (isSplitAnalyticSubmanifold_sphere he).chartedSpace
    haveI := realAnalyticManifold_sphere he
    ∀ z : Metric.sphere (0 : H) 1 × Metric.sphere (0 : H) 1,
      z ∈ (sphereAnalyticLocalAddition he).toOpenPartialHomeomorph.target ↔
        0 < ⟪(z.1 : H), (z.2 : H)⟫ :=
  fun _ ↦ Iff.rfl

/-- **The local addition of the sphere is real analytic**: `θ = (π, Σ)` is a real analytic
diffeomorphism of `TS` onto the open set `{(p, q) ∈ S × S : ⟪p, q⟫ > 0}` ([GN26, p. 325,
after Definition 3.8.11]). -/
theorem isRealAnalytic_sphereAnalyticLocalAddition (he : ‖e‖ = 1) :
    letI := (isSplitAnalyticSubmanifold_sphere he).chartedSpace
    haveI := realAnalyticManifold_sphere he
    (sphereAnalyticLocalAddition he).IsRealAnalytic :=
  letI := (isSplitAnalyticSubmanifold_sphere he).chartedSpace
  haveI := realAnalyticManifold_sphere he
  (sphereAnalyticAmbientAddition he).isRealAnalytic_toLocalAddition rfl

end LocallyConvex.Manifolds
