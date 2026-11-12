/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.Symplectic.Darboux
public import LocallyConvexAnalysis.Analytic.OperatorValued

/-!
# The real analytic Darboux theorem

Let `M` be a **real analytic** manifold modeled on a Banach space `E` and `ω` a closed real
`2`-form on `M`, strongly nondegenerate at `x₀` and real analytic. Then the Darboux
chart of `DifferentialForm.exists_darboux_chart` can be chosen in the real analytic maximal atlas
(`DifferentialForm.exists_realAnalytic_darboux_chart`). Real analyticity is in the sense of
Milnor (`LocallyConvex.Analysis.RealAnalyticOn`; Glöckner–Neeb, *Infinite-Dimensional Lie
Groups*, arXiv:2602.12362, Definition 2.2.2).

## Main results

* `Darboux.radialPrimitive`, `Darboux.radialPrimitive_spec`: the radial primitive
  `α(y) = ∫₀¹ s Θ(p + s (y - p))(y - p) ds` of a closed skew `Θ : B(p, r) → L(E, D)`,
  `D ≃ E'`, with `Θ(p) = 0`: `dα = Θ`, `α(p) = 0`, `dα(p) = 0` (differentiation under the
  integral sign, the closedness of `Θ`, and the fundamental theorem of calculus);
* `Darboux.realAnalyticOn_radialPrimitive`: if `Θ` is real analytic, so is `α` near `p`;
* `Darboux.exists_primitive_realAnalytic`: **a real analytic primitive**;
* `Darboux.exists_darboux_local_realAnalytic`: **the real analytic local Darboux theorem**: for
  `Ω : U → L(E, E')` real analytic, closed, skew-symmetric and bijective at `p`, the Darboux map
  `ψ` and its inverse are real analytic;
* `DifferentialForm.IsRealAnalytic.exists_clm_localRep`: a real analytic `2`-form is, in a chart,
  a real analytic map into `L(E, E')` for the operator norm;
* `DifferentialForm.exists_realAnalytic_darboux_chart`,
  `SymplecticForm.IsStrong.exists_realAnalytic_darboux_chart`: **real analytic Darboux charts**
  for real analytic closed `2`-forms.

## Moser's method is real analytic

Each step of the proof of `Darboux.exists_darboux_local'` preserves real analyticity:

1. *The primitive.* The primitive given by the Poincaré lemma
   (`DifferentialForm.IsClosed.isExact_of_starConvex`) is a weak integral, and lc-analysis has no
   real analytic parametric integrals. We use the radial primitive instead, and obtain its real
   analyticity from that of flows: `α(y)` is the value at time `1` of the solution of
   `ẏ = 0`, `ȧ = s Θ(p + s (y - p))(y - p)` starting at `(y, 0)`, a real analytic ordinary
   differential equation on `E × D`.
2. *Moser's field* `Xₜ = -Ωₜ⁻¹ α` is real analytic, since inversion in the Banach algebra
   `L(E)` is (`LocallyConvex.Analysis.realAnalyticOn_inverse`, Glöckner–Neeb,
   Proposition 2.2.13).
3. *The flow up to time `1`* is real analytic, since the maximal flow of a real analytic vector
   field is (`SmoothVectorField.realAnalyticMOn_flow`; Glöckner–Neeb, Theorem 2.5.18 (b)).
4. *The inverse of `ψ = F₁`.* No real analytic inverse function theorem is needed: `ψ⁻¹` is the
   map `y ↦ Fl(-1, (1, y))` of the suspended flow, which is real analytic
   (`Darboux.exists_flow_of_stationary`, `Darboux.exists_darboux_local_of_primitive`).

## The hypothesis on `ω`

The manifold version asks `ω` to be real analytic in the sense of
`LocallyConvexManifolds.Analytic.Form` (`DifferentialForm.IsRealAnalytic`, Glöckner–Neeb,
Remark 3.6.18): its local representatives `(y, u, v) ↦ Ω(y)(u, v)` are jointly real analytic. The
local theorem needs `y ↦ Ω(y) ∈ L(E, E')` real analytic for the operator norm; this follows from
lc-analysis's `RealAnalyticOn.of_unc_clm₂`, the real analytic counterpart of
`contDiffMBOn_of_unc_clm` (`DifferentialForm.IsRealAnalytic.exists_clm_localRep`).

## References

The smooth theorem is A. Weinstein, *Symplectic structures on Banach manifolds*, Bull. Amer. Math.
Soc. 75 (1969), §1, Theorem, and S. Lang, *Fundamentals of Differential Geometry*, GTM 191,
Theorem V.8.1; neither treats the real analytic case, nor does Glöckner–Neeb (who mention
Weinstein's theorem in the introduction, p. 13). We are not aware of a reference for the real
analytic case on Banach manifolds; we do not claim this argument is new.

## Infinite-dimensional subtleties

* Besides those of the smooth theorem (`LocallyConvexManifolds.Symplectic.Darboux`), real
  analyticity is measured by complex extensions to the complexification (Milnor), not by power
  series; the three analytic inputs above (inversion, maximal flows, compositions) are proved in
  that framework.
* The radial primitive is only shown to be real analytic near `p` (on a ball where the solution
  of the auxiliary equation exists up to time `1` near `(p, 0)`), which suffices for a local
  statement.
-/

@[expose] public section

open Set Function Filter Metric
open LocallyConvex.Analysis
open scoped Topology Interval

noncomputable section

namespace LocallyConvex.Manifolds

namespace Darboux

open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- The derivative of a family of skew-symmetric forms is skew-symmetric. -/
theorem fderiv_skew (ev : D ≃L[ℝ] (E →L[ℝ] ℝ)) {Θ : E → E →L[ℝ] D} {U : Set E} (hU : IsOpen U)
    (hΘ : ∀ y ∈ U, HasFDerivAt Θ (fderiv ℝ Θ y) y)
    (hskew : ∀ y ∈ U, ∀ a b, ev (Θ y a) b = -ev (Θ y b) a) {y : E} (hy : y ∈ U) (w a b : E) :
    ev (fderiv ℝ Θ y w a) b = -ev (fderiv ℝ Θ y w b) a := by
  have hd : ∀ a b : E, HasFDerivAt (fun z ↦ ev (Θ z a) b)
      (((ev : D →L[ℝ] E →L[ℝ] ℝ).comp ((fderiv ℝ Θ y).flip a)).flip b) y := fun a b ↦ by
    have := ((ev : D →L[ℝ] E →L[ℝ] ℝ).hasFDerivAt.comp y
      ((hΘ y hy).clm_apply (hasFDerivAt_const a y))).clm_apply (hasFDerivAt_const b y)
    simpa using this
  have hev : (fun z ↦ ev (Θ z a) b + ev (Θ z b) a) =ᶠ[𝓝 y] fun _ ↦ (0 : ℝ) :=
    eventually_of_mem (hU.mem_nhds hy) fun z hz ↦ by simp only [hskew z hz a b]; ring
  have h := ((hd a b).add (hd b a)).unique ((hasFDerivAt_const (0 : ℝ) y).congr_of_eventuallyEq hev)
  have h' := congrArg (fun L : E →L[ℝ] ℝ ↦ L w) h
  simp only [add_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.coe_comp, comp_apply, ContinuousLinearEquiv.coe_coe,
    zero_apply] at h'
  linarith

/-- The radial primitive `α(y) = ∫₀¹ s Θ(p + s (y - p))(y - p) ds` of a closed `2`-form `Θ`. -/
def radialPrimitive (Θ : E → E →L[ℝ] D) (p y : E) : D :=
  ∫ s in (0 : ℝ)..1, s • Θ (p + s • (y - p)) (y - p)

/-- Balls are star-shaped with respect to their centers: `p + s (y - p) ∈ B(p, r)` for
`y ∈ B(p, r)` and `|s| ≤ 1`. -/
theorem mem_ball_segment {p y : E} {r : ℝ} (hy : y ∈ ball p r) {s : ℝ} (hs : |s| ≤ 1) :
    p + s • (y - p) ∈ ball p r := by
  rw [mem_ball_iff_norm] at hy ⊢
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  calc |s| * ‖y - p‖ ≤ 1 * ‖y - p‖ := by gcongr
    _ < r := by rwa [one_mul]

/-- Points of `[0, 1]` have absolute value at most `1`. -/
theorem abs_le_one_of_mem_uIcc {s : ℝ} (hs : s ∈ uIcc (0 : ℝ) 1) : |s| ≤ 1 := by
  rw [uIcc_of_le zero_le_one] at hs
  rw [abs_le]; constructor <;> linarith [hs.1, hs.2]

/-- **The radial primitive of a closed `2`-form** (the Poincaré lemma on a ball, in the explicit
form of the homotopy operator for the radial contraction). Let `Θ : B(p, r) → L(E, D)`, `D ≃ E'`,
be smooth, skew-symmetric and closed, with `Θ(p) = 0`, and with `Θ` and `dΘ` bounded on
`B(p, r)`. Then `α = radialPrimitive Θ p` satisfies `dα = Θ` on `B(p, r)`, `α(p) = 0` and
`dα(p) = 0`. -/
theorem radialPrimitive_spec [CompleteSpace D] (ev : D ≃L[ℝ] (E →L[ℝ] ℝ)) {Θ : E → E →L[ℝ] D}
    {p : E} {r : ℝ} (hr : 0 < r) (hΘs : ContDiffOn ℝ ∞ Θ (ball p r))
    (hskew : ∀ y ∈ ball p r, ∀ a b, ev (Θ y a) b = -ev (Θ y b) a)
    (hclosed : ∀ y ∈ ball p r, ∀ u v w,
      ev (fderiv ℝ Θ y u v) w - ev (fderiv ℝ Θ y v u) w + ev (fderiv ℝ Θ y w u) v = 0)
    (hp : Θ p = 0) {C K : ℝ} (hC : ∀ z ∈ ball p r, ‖Θ z‖ ≤ C)
    (hK : ∀ z ∈ ball p r, ‖fderiv ℝ Θ z‖ ≤ K) :
    radialPrimitive Θ p p = 0 ∧ fderiv ℝ (radialPrimitive Θ p) p = 0 ∧
      ∀ y ∈ ball p r, HasFDerivAt (radialPrimitive Θ p) (fderiv ℝ (radialPrimitive Θ p) y) y ∧
        ∀ a b, ev (fderiv ℝ (radialPrimitive Θ p) y a) b -
          ev (fderiv ℝ (radialPrimitive Θ p) y b) a = ev (Θ y a) b := by
  have hB : IsOpen (ball p r) := isOpen_ball
  have hΘd : ∀ y ∈ ball p r, HasFDerivAt Θ (fderiv ℝ Θ y) y := fun y hy ↦
    ((hΘs.contDiffAt (hB.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
  have hΘc : ContinuousOn Θ (ball p r) := hΘs.continuousOn
  have hDΘc : ContinuousOn (fderiv ℝ Θ) (ball p r) :=
    hΘs.continuousOn_fderiv_of_isOpen hB (by simp)
  set seg : E → ℝ → E := fun y s ↦ p + s • (y - p) with hseg
  have hsegc : ∀ y, Continuous (seg y) := fun y ↦ by fun_prop
  have hsegB : ∀ y ∈ ball p r, ∀ s ∈ uIcc (0 : ℝ) 1, seg y s ∈ ball p r := fun y hy s hs ↦
    mem_ball_segment hy (abs_le_one_of_mem_uIcc hs)
  -- the integrand and its derivative in `y`
  set F : E → ℝ → D := fun y s ↦ s • Θ (seg y s) (y - p) with hFdef
  set F' : E → ℝ → E →L[ℝ] D := fun y s ↦
    s • (Θ (seg y s) + s • (ContinuousLinearMap.apply ℝ D (y - p)).comp (fderiv ℝ Θ (seg y s)))
    with hF'def
  have hFc : ∀ y ∈ ball p r, ContinuousOn (F y) (uIcc 0 1) := fun y hy ↦
    continuousOn_id.smul (((hΘc.comp (hsegc y).continuousOn (hsegB y hy)).clm_apply
      continuousOn_const))
  have hF'c : ∀ y ∈ ball p r, ContinuousOn (F' y) (uIcc 0 1) := fun y hy ↦ by
    have h1 := hΘc.comp (hsegc y).continuousOn (hsegB y hy)
    have h2 := hDΘc.comp (hsegc y).continuousOn (hsegB y hy)
    exact continuousOn_id.smul (h1.add (continuousOn_id.smul (continuousOn_const.clm_comp h2)))
  have hF'd : ∀ y ∈ ball p r, ∀ s ∈ uIcc (0 : ℝ) 1, HasFDerivAt (fun x ↦ F x s) (F' y s) y := by
    intro y hy s hs
    have hz : HasFDerivAt (fun x ↦ seg x s) (s • ContinuousLinearMap.id ℝ E) y :=
      (((hasFDerivAt_id y).sub_const p).const_smul s).const_add p
    have h := (((hΘd _ (hsegB y hy s hs)).comp y hz).clm_apply
      ((hasFDerivAt_id y).sub_const p)).const_smul s
    refine h.congr_fderiv (ContinuousLinearMap.ext fun a ↦ ?_)
    simp [hF'def]
  have hF'b : ∀ y ∈ ball p r, ∀ s ∈ uIcc (0 : ℝ) 1, ‖F' y s‖ ≤ C + K * r := by
    intro y hy s hs
    have hs1 := abs_le_one_of_mem_uIcc hs
    have hz := hsegB y hy s hs
    have hyp : ‖y - p‖ ≤ r := (mem_ball_iff_norm.1 hy).le
    have hK0 : 0 ≤ K := (ContinuousLinearMap.opNorm_nonneg _).trans (hK _ hz)
    have hr0 : 0 ≤ r := (norm_nonneg _).trans hyp
    have happ : ‖(ContinuousLinearMap.apply ℝ D (y - p)).comp (fderiv ℝ Θ (seg y s))‖ ≤
        K * r := by
      refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hK0 hr0) fun a ↦ ?_
      calc ‖fderiv ℝ Θ (seg y s) a (y - p)‖ ≤ ‖fderiv ℝ Θ (seg y s) a‖ * ‖y - p‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ (‖fderiv ℝ Θ (seg y s)‖ * ‖a‖) * ‖y - p‖ :=
            mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
        _ ≤ (K * ‖a‖) * r :=
            mul_le_mul (mul_le_mul_of_nonneg_right (hK _ hz) (norm_nonneg a)) hyp
              (norm_nonneg _) (mul_nonneg hK0 (norm_nonneg a))
        _ = K * r * ‖a‖ := by ring
    have hC0 : 0 ≤ C := (ContinuousLinearMap.opNorm_nonneg _).trans (hC _ hz)
    calc ‖F' y s‖ ≤ |s| * (‖Θ (seg y s)‖ + |s| * ‖(ContinuousLinearMap.apply ℝ D (y - p)).comp
          (fderiv ℝ Θ (seg y s))‖) := by
          simp only [hF'def, norm_smul, Real.norm_eq_abs]
          gcongr
          exact (norm_add_le _ _).trans (by rw [norm_smul, Real.norm_eq_abs])
      _ ≤ 1 * (C + 1 * (K * r)) := by
          gcongr
          · exact hC _ hz
      _ = C + K * r := by ring
  -- the derivative of `α`
  have hαd : ∀ y ∈ ball p r, HasFDerivAt (radialPrimitive Θ p)
      (∫ s in (0 : ℝ)..1, F' y s) y := by
    intro y hy
    have hIoc : ∀ s ∈ Ι (0 : ℝ) 1, s ∈ uIcc (0 : ℝ) 1 := fun s hs ↦ uIoc_subset_uIcc hs
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (bound := fun _ ↦ C + K * r)
      (hB.mem_nhds hy) ?_ ((hFc y hy).intervalIntegrable) ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards [hB.mem_nhds hy] with x hx
      exact ((hFc x hx).mono fun s hs ↦ hIoc s hs).aestronglyMeasurable measurableSet_uIoc
    · exact ((hF'c y hy).mono fun s hs ↦ hIoc s hs).aestronglyMeasurable measurableSet_uIoc
    · exact Eventually.of_forall fun s hs x hx ↦ hF'b x hx s (hIoc s hs)
    · exact Eventually.of_forall fun s hs x hx ↦ hF'd x hx s (hIoc s hs)
  have hfd : ∀ y ∈ ball p r, fderiv ℝ (radialPrimitive Θ p) y = ∫ s in (0 : ℝ)..1, F' y s :=
    fun y hy ↦ (hαd y hy).fderiv
  have hpB : p ∈ ball p r := mem_ball_self hr
  refine ⟨by simp [radialPrimitive], ?_, fun y hy ↦ ⟨by rw [hfd y hy]; exact hαd y hy,
    fun a b ↦ ?_⟩⟩
  · rw [hfd p hpB]
    have : ∀ s, F' p s = 0 := fun s ↦ by simp [hF'def, hseg, hp]
    simp [this]
  · -- `dα = Θ`: the integrand is `d/ds (s² Θ(p + s (y - p))(a, b))`
    set h := y - p with hh
    have hint : IntervalIntegrable (F' y) MeasureTheory.volume 0 1 :=
      (hF'c y hy).intervalIntegrable
    set Lb : D →L[ℝ] ℝ := (ContinuousLinearMap.apply ℝ ℝ b).comp (ev : D →L[ℝ] E →L[ℝ] ℝ)
    set La : D →L[ℝ] ℝ := (ContinuousLinearMap.apply ℝ ℝ a).comp (ev : D →L[ℝ] E →L[ℝ] ℝ)
    have hia : IntervalIntegrable (fun s ↦ F' y s a) MeasureTheory.volume 0 1 :=
      ((hF'c y hy).clm_apply continuousOn_const).intervalIntegrable
    have hib : IntervalIntegrable (fun s ↦ F' y s b) MeasureTheory.volume 0 1 :=
      ((hF'c y hy).clm_apply continuousOn_const).intervalIntegrable
    have e1 : ev (fderiv ℝ (radialPrimitive Θ p) y a) b = ∫ s in (0 : ℝ)..1, Lb (F' y s a) := by
      rw [hfd y hy, ContinuousLinearMap.intervalIntegral_apply hint a,
        Lb.intervalIntegral_comp_comm hia]
      rfl
    have e2 : ev (fderiv ℝ (radialPrimitive Θ p) y b) a = ∫ s in (0 : ℝ)..1, La (F' y s b) := by
      rw [hfd y hy, ContinuousLinearMap.intervalIntegral_apply hint b,
        La.intervalIntegral_comp_comm hib]
      rfl
    have h1 : IntervalIntegrable (fun s ↦ Lb (F' y s a)) MeasureTheory.volume 0 1 :=
      (Lb.continuous.comp_continuousOn ((hF'c y hy).clm_apply
        (continuousOn_const (c := a)))).intervalIntegrable
    have h2 : IntervalIntegrable (fun s ↦ La (F' y s b)) MeasureTheory.volume 0 1 :=
      (La.continuous.comp_continuousOn ((hF'c y hy).clm_apply
        (continuousOn_const (c := b)))).intervalIntegrable
    rw [e1, e2, ← intervalIntegral.integral_sub h1 h2]
    set g' : ℝ → ℝ := fun s ↦ 2 * s * ev (Θ (seg y s) a) b +
      s ^ 2 * ev (fderiv ℝ Θ (seg y s) h a) b with hg'def
    have hcongr : EqOn (fun s ↦ Lb (F' y s a) - La (F' y s b)) g' (uIcc 0 1) := by
      intro s hs
      have hz := hsegB y hy s hs
      have k1 := hskew _ hz a b
      have k2 := hclosed _ hz a h b
      have k3 := fderiv_skew ev hB hΘd hskew hz b a h
      simp only [hF'def, hg'def, Lb, La, ContinuousLinearMap.coe_comp, comp_apply,
        ContinuousLinearMap.apply_apply, smul_apply, add_apply, map_add,
        map_smul, smul_eq_mul, ContinuousLinearEquiv.coe_coe]
      linear_combination (-s) * k1 + s ^ 2 * k2 - s ^ 2 * k3
    rw [intervalIntegral.integral_congr hcongr]
    set g : ℝ → ℝ := fun s ↦ s ^ 2 * ev (Θ (seg y s) a) b with hgdef
    have hseg' : ∀ s : ℝ, HasDerivAt (seg y) h s := fun s ↦
      (((hasDerivAt_id s).smul_const h).const_add p).congr_deriv (one_smul ℝ h)
    have hgd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt g (g' s) s := by
      intro s hs
      have hz := hsegB y hy s hs
      have hT : HasDerivAt (fun s ↦ ev (Θ (seg y s) a) b) (ev (fderiv ℝ Θ (seg y s) h a) b) s := by
        have := Lb.hasFDerivAt.comp_hasDerivAt s
          ((ContinuousLinearMap.apply ℝ D a).hasFDerivAt.comp_hasDerivAt s
            ((hΘd _ hz).comp_hasDerivAt s (hseg' s)))
        exact this
      have := (hasDerivAt_pow 2 s).mul hT
      convert this using 1
      simp only [hg'def]
      push_cast
      ring
    have hg'c : ContinuousOn g' (uIcc 0 1) := by
      have hc1 := (Lb.continuous.comp_continuousOn
        (((hΘc.comp (hsegc y).continuousOn (hsegB y hy)).clm_apply
          (continuousOn_const (c := a)))))
      have hc2 := (Lb.continuous.comp_continuousOn
        ((((hDΘc.comp (hsegc y).continuousOn (hsegB y hy)).clm_apply
          (continuousOn_const (c := h))).clm_apply (continuousOn_const (c := a)))))
      exact ((continuousOn_const.mul continuousOn_id).mul hc1).add
        ((continuousOn_id.pow 2).mul hc2)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hgd hg'c.intervalIntegrable]
    simp [hgdef, hseg]

/-- **The radial primitive of a real analytic form is real analytic** near the center. It is the
solution at time `1` of the ordinary differential equation `ȧ = s Θ(p + s (y - p))(y - p)`,
`ẏ = 0`, whose right-hand side is real analytic; the real analytic dependence of solutions on
initial values up to time `1` comes from the real analyticity of the maximal flow
(`exists_flow_of_stationary`). This avoids real analytic parametric integrals. -/
theorem realAnalyticOn_radialPrimitive [CompleteSpace E] [CompleteSpace D] {Θ : E → E →L[ℝ] D}
    {p : E} {r : ℝ} (hr : 0 < r) (hΘa : RealAnalyticOn Θ (ball p r)) :
    ∃ r' > 0, r' ≤ r ∧ RealAnalyticOn (radialPrimitive Θ p) (ball p r') := by
  classical
  have hB : IsOpen (ball p r) := isOpen_ball
  have hΘc : ContinuousOn Θ (ball p r) := ((hΘa.smoothMBOn hB) 0).continuousOn
  set seg₂ : ℝ × (E × D) → E := fun q ↦ p + q.1 • (q.2.1 - p) with hseg₂
  set W₂ : Set (ℝ × (E × D)) := seg₂ ⁻¹' ball p r with hW₂def
  have hW₂ : IsOpen W₂ := hB.preimage (by fun_prop)
  set Xf₂ : ℝ × (E × D) → E × D := fun q ↦ ((0 : E), q.1 • Θ (seg₂ q) (q.2.1 - p)) with hXf₂
  -- the right-hand side is real analytic
  have hfst : RealAnalyticOn (fun q : ℝ × (E × D) ↦ q.1) univ :=
    (ContinuousLinearMap.fst ℝ ℝ (E × D)).realAnalyticOn _
  have hy : RealAnalyticOn (fun q : ℝ × (E × D) ↦ q.2.1 - p) univ :=
    (((ContinuousLinearMap.fst ℝ E D).comp (ContinuousLinearMap.snd ℝ ℝ (E × D))).realAnalyticOn
      _).sub (realAnalyticOn_const p _)
  have hseg₂a : RealAnalyticOn seg₂ univ :=
    (realAnalyticOn_const p _).add
      (RealAnalyticOn.bilin (LinearMap.lsmul ℝ E) (continuous_fst.smul continuous_snd) hfst hy)
  have hΘseg : RealAnalyticOn (fun q ↦ Θ (seg₂ q)) W₂ :=
    hΘa.comp (hseg₂a.mono (subset_univ _)) fun q hq ↦ hq
  have happ := RealAnalyticOn.bilin (ContinuousLinearMap.coeLM ℝ : (E →L[ℝ] D) →ₗ[ℝ] E →ₗ[ℝ] D)
    (continuous_fst.clm_apply continuous_snd) hΘseg (hy.mono (subset_univ W₂))
  have hsm := RealAnalyticOn.bilin (LinearMap.lsmul ℝ D) (continuous_fst.smul continuous_snd)
    (hfst.mono (subset_univ W₂)) happ
  have hXa : RealAnalyticOn Xf₂ W₂ := (realAnalyticOn_const (0 : E) _).prodMk hsm
  have hXs : ContDiffOn ℝ ∞ Xf₂ W₂ := (smoothMBOn_iff_contDiffOn hW₂).1 (hXa.smoothMBOn hW₂)
  have hpW : ∀ t : ℝ, (t, ((p, 0) : E × D)) ∈ W₂ := fun t ↦ by
    simp [hW₂def, hseg₂, mem_ball_self hr]
  have hXp : ∀ t : ℝ, Xf₂ (t, ((p, 0) : E × D)) = 0 := fun t ↦ by simp [hXf₂]
  obtain ⟨δ, hδ, V₂, hV₂, hpV₂, F₂, -, -, hF₂x, hF₂a⟩ := exists_flow_of_stationary hW₂ hXs hpW hXp
  obtain ⟨hF₂an, -⟩ := hF₂a hXa
  set I := Ioo (-δ) (1 + δ) with hIdef
  have hI0 : (0 : ℝ) ∈ I := ⟨by linarith, by linarith⟩
  have hI1 : (1 : ℝ) ∈ I := ⟨by linarith, by linarith⟩
  have hIcc : uIcc (0 : ℝ) 1 ⊆ I := fun t ht ↦ by
    rw [uIcc_of_le zero_le_one] at ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  set B₁ : Set E := (fun y : E ↦ (y, (0 : D))) ⁻¹' V₂ ∩ ball p r with hB₁def
  have hB₁ : IsOpen B₁ := (hV₂.preimage (continuous_id.prodMk continuous_const)).inter hB
  have hpB₁ : p ∈ B₁ := ⟨hpV₂, mem_ball_self hr⟩
  -- on `B₁`, the radial primitive is a component of the flow at time `1`
  have key : ∀ y ∈ B₁, radialPrimitive Θ p y = (F₂ (1, (y, 0))).2 := by
    intro y hyB
    obtain ⟨hc0, hc⟩ := hF₂x (y, 0) hyB.1
    have hc1 : ∀ t ∈ I, (F₂ (t, (y, 0))).1 = y := by
      have hd : ∀ t ∈ I, HasDerivAt (fun s ↦ (F₂ (s, (y, 0))).1) 0 t := fun t ht ↦ by
        have h := (hasFDerivAt_fst (p := F₂ (t, (y, 0)))).comp_hasDerivAt t (hc t ht).2
        exact h
      intro t ht
      have := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
        (fun s hs ↦ (hd s hs).differentiableAt.differentiableWithinAt)
        (fun s hs ↦ (hd s hs).deriv) ht hI0
      rw [this, hc0]
    have hc2 : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s ↦ (F₂ (s, (y, 0))).2)
        (t • Θ (p + t • (y - p)) (y - p)) t := fun t ht ↦ by
      have h := (hasFDerivAt_snd (p := F₂ (t, (y, 0)))).comp_hasDerivAt t (hc t (hIcc ht)).2
      have e : (ContinuousLinearMap.snd ℝ E D) (Xf₂ (t, F₂ (t, (y, 0)))) =
          t • Θ (p + t • (y - p)) (y - p) := by
        simp only [hXf₂, hseg₂, ContinuousLinearMap.coe_snd', hc1 t (hIcc ht)]
      rw [e] at h
      exact h
    have hint : IntervalIntegrable (fun t : ℝ ↦ t • Θ (p + t • (y - p)) (y - p))
        MeasureTheory.volume 0 1 := by
      refine ContinuousOn.intervalIntegrable ?_
      exact continuousOn_id.smul ((hΘc.comp (by fun_prop : Continuous fun t : ℝ ↦
        p + t • (y - p)).continuousOn fun t ht ↦
          mem_ball_segment hyB.2 (abs_le_one_of_mem_uIcc ht)).clm_apply continuousOn_const)
    rw [radialPrimitive, intervalIntegral.integral_eq_sub_of_hasDerivAt hc2 hint, hc0]
    simp
  have hB₁a : RealAnalyticOn (radialPrimitive Θ p) B₁ := by
    have hin : RealAnalyticOn (fun y : E ↦ ((1 : ℝ), (y, (0 : D)))) B₁ :=
      (realAnalyticOn_const (1 : ℝ) _).prodMk
        (((ContinuousLinearMap.id ℝ E).realAnalyticOn _).prodMk (realAnalyticOn_const 0 _))
    have h := ((ContinuousLinearMap.snd ℝ E D).realAnalyticOn _).comp
      (hF₂an.comp hin fun y hy ↦ ⟨hI1, hy.1⟩) (mapsTo_univ _ _)
    exact realAnalyticOn_congr (fun y hy ↦ (key y hy).symm) h
  obtain ⟨ε, hε, hεB⟩ := Metric.isOpen_iff.1 hB₁ p hpB₁
  exact ⟨min ε r, lt_min hε hr, min_le_right _ _,
    hB₁a.mono ((ball_subset_ball (min_le_left _ _)).trans hεB)⟩

/-- **A real analytic primitive** (the real analytic Poincaré lemma for `2`-forms near a point).
Let `E` and `D ≃ E'` be Banach spaces and `Θ : B(p, r) → L(E, D)` real analytic (as a map into
the operator space), skew-symmetric and closed, with `Θ(p) = 0`. Then on a smaller ball
`B(p, r')`, `Θ = dα` for a real analytic `α` with `α(p) = 0` and `dα(p) = 0`: the radial
primitive (`radialPrimitive_spec`, `realAnalyticOn_radialPrimitive`). -/
theorem exists_primitive_realAnalytic [CompleteSpace E] [CompleteSpace D]
    (ev : D ≃L[ℝ] (E →L[ℝ] ℝ)) {Θ : E → E →L[ℝ] D} {p : E} {r : ℝ} (hr : 0 < r)
    (hΘa : RealAnalyticOn Θ (ball p r))
    (hskew : ∀ y ∈ ball p r, ∀ a b, ev (Θ y a) b = -ev (Θ y b) a)
    (hclosed : ∀ y ∈ ball p r, ∀ u v w,
      ev (fderiv ℝ Θ y u v) w - ev (fderiv ℝ Θ y v u) w + ev (fderiv ℝ Θ y w u) v = 0)
    (hp : Θ p = 0) :
    ∃ r' > 0, r' ≤ r ∧ ∃ α : E → D, ContDiffOn ℝ ∞ α (ball p r') ∧
      RealAnalyticOn α (ball p r') ∧ α p = 0 ∧ fderiv ℝ α p = 0 ∧
      ∀ y ∈ ball p r', ∀ a b,
        ev (fderiv ℝ α y a) b - ev (fderiv ℝ α y b) a = ev (Θ y a) b := by
  have hB : IsOpen (ball p r) := isOpen_ball
  have hpB : p ∈ ball p r := mem_ball_self hr
  have hΘs : ContDiffOn ℝ ∞ Θ (ball p r) :=
    (smoothMBOn_iff_contDiffOn hB).1 (hΘa.smoothMBOn hB)
  -- `Θ` and `dΘ` are bounded near `p`
  have h1 : ∀ᶠ z in 𝓝 p, ‖Θ z‖ < ‖Θ p‖ + 1 :=
    (hΘs.continuousOn.continuousAt (hB.mem_nhds hpB)).norm.eventually
      (gt_mem_nhds (lt_add_one _))
  have h2 : ∀ᶠ z in 𝓝 p, ‖fderiv ℝ Θ z‖ < ‖fderiv ℝ Θ p‖ + 1 :=
    ((hΘs.continuousOn_fderiv_of_isOpen hB (by simp)).continuousAt
      (hB.mem_nhds hpB)).norm.eventually (gt_mem_nhds (lt_add_one _))
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff_ball.1 (h1.and h2)
  set r₀ := min ε r with hr₀def
  have hr₀ : 0 < r₀ := lt_min hε hr
  have hr₀r : ball p r₀ ⊆ ball p r := ball_subset_ball (min_le_right _ _)
  have hr₀ε : ball p r₀ ⊆ ball p ε := ball_subset_ball (min_le_left _ _)
  obtain ⟨hα0, hdα0, hαd⟩ := radialPrimitive_spec ev hr₀ (hΘs.mono hr₀r)
    (fun y hy ↦ hskew y (hr₀r hy)) (fun y hy ↦ hclosed y (hr₀r hy)) hp
    (C := ‖Θ p‖ + 1) (K := ‖fderiv ℝ Θ p‖ + 1)
    (fun z hz ↦ (hεb z (hr₀ε hz)).1.le) (fun z hz ↦ (hεb z (hr₀ε hz)).2.le)
  obtain ⟨r', hr', hr'r₀, hαa⟩ := realAnalyticOn_radialPrimitive hr₀ (hΘa.mono hr₀r)
  have hr'B : ball p r' ⊆ ball p r₀ := ball_subset_ball hr'r₀
  exact ⟨r', hr', hr'r₀.trans (min_le_right _ _), radialPrimitive Θ p,
    (smoothMBOn_iff_contDiffOn isOpen_ball).1 (hαa.smoothMBOn isOpen_ball), hαa, hα0, hdα0,
    fun y hy ↦ (hαd y (hr'B hy)).2⟩

/-- **The real analytic local Darboux theorem**, for forms with values in `L(E, D)`, `D ≃ E'`.
Let `E` be a Banach space, `U ⊆ E` open and `Ω : U → L(E, D)` **real analytic** (in the sense of
Milnor, as a map into the operator space), with `Ω(y)` skew-symmetric, `dΩ = 0`, and `Ω(p)`
bijective. Then there is a real analytic diffeomorphism `ψ` (with real analytic inverse) between
open neighbourhoods of `p` in `U`, with `ψ(p) = p`, `dψ(p) = id` and `ψ*Ω = Ω(p)`.

Every step of Moser's method is real analytic: the radial primitive
(`exists_primitive_realAnalytic`), Moser's field `Xₜ = -Ωₜ⁻¹ α` (inversion is real analytic), and
the flow up to time `1` and its inverse (`exists_flow_of_stationary`). -/
theorem exists_darboux_local_realAnalytic' [CompleteSpace E] [CompleteSpace D]
    (ev : D ≃L[ℝ] (E →L[ℝ] ℝ)) {Ω : E → E →L[ℝ] D} {U : Set E} (hU : IsOpen U)
    (hΩa : RealAnalyticOn Ω U)
    (hskew : ∀ y ∈ U, ∀ a b, ev (Ω y a) b = -ev (Ω y b) a)
    (hclosed : ∀ y ∈ U, ∀ u v w,
      ev (fderiv ℝ Ω y u v) w - ev (fderiv ℝ Ω y v u) w + ev (fderiv ℝ Ω y w u) v = 0)
    {p : E} (hp : p ∈ U) (hstrong : Bijective (Ω p)) :
    ∃ ψ : OpenPartialHomeomorph E E, p ∈ ψ.source ∧ ψ p = p ∧
      fderiv ℝ ψ p = ContinuousLinearMap.id ℝ E ∧ ψ.source ⊆ U ∧ ψ.target ⊆ U ∧
      RealAnalyticOn ψ ψ.source ∧ RealAnalyticOn ψ.symm ψ.target ∧
      ∀ x ∈ ψ.source, ∀ u v,
        ev (Ω (ψ x) (fderiv ℝ ψ x u)) (fderiv ℝ ψ x v) = ev (Ω p u) v := by
  have hΩs : ContDiffOn ℝ ∞ Ω U := (smoothMBOn_iff_contDiffOn hU).1 (hΩa.smoothMBOn hU)
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU p hp
  have hΩd : ∀ y ∈ U, HasFDerivAt Ω (fderiv ℝ Ω y) y := fun y hy ↦
    ((hΩs.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
  have hfdΘ : ∀ y ∈ ball p r, fderiv ℝ (fun y ↦ Ω y - Ω p) y = fderiv ℝ Ω y := fun y hy ↦
    ((hΩd y (hrU hy)).sub_const (Ω p)).fderiv
  obtain ⟨r', hr', hr'r, α, hα, hαa, hαp, hdαp, hdα⟩ := exists_primitive_realAnalytic ev hr
    (Θ := fun y ↦ Ω y - Ω p) ((hΩa.mono hrU).sub (realAnalyticOn_const _ _))
    (fun y hy a b ↦ by
      simp only [sub_apply, map_sub]
      rw [hskew y (hrU hy) a b, hskew p hp a b]; ring)
    (fun y hy u v w ↦ by rw [hfdΘ y hy]; exact hclosed y (hrU hy) u v w)
    (by simp)
  obtain ⟨ψ, h1, h2, h3, h4, h5, -, -, h8, han⟩ := exists_darboux_local_of_primitive ev hU hΩs
    hskew hclosed hp hstrong hr' ((ball_subset_ball hr'r).trans hrU) hα hαp hdαp
    (fun y hy a b ↦ hdα y hy a b)
  exact ⟨ψ, h1, h2, h3, h4, h5, (han hΩa hαa).1, (han hΩa hαa).2, h8⟩

/-- **The real analytic local Darboux theorem** for `Ω : U → L(E, E')` real analytic, closed,
skew-symmetric and strongly nondegenerate at `p` (the case `D = E'` of
`exists_darboux_local_realAnalytic'`). -/
theorem exists_darboux_local_realAnalytic [CompleteSpace E] {Ω : E → E →L[ℝ] E →L[ℝ] ℝ}
    {U : Set E} (hU : IsOpen U) (hΩa : RealAnalyticOn Ω U)
    (hskew : ∀ y ∈ U, ∀ a b, Ω y a b = -Ω y b a)
    (hclosed : ∀ y ∈ U, ∀ u v w,
      fderiv ℝ Ω y u v w - fderiv ℝ Ω y v u w + fderiv ℝ Ω y w u v = 0)
    {p : E} (hp : p ∈ U) (hstrong : Bijective (Ω p)) :
    ∃ ψ : OpenPartialHomeomorph E E, p ∈ ψ.source ∧ ψ p = p ∧
      fderiv ℝ ψ p = ContinuousLinearMap.id ℝ E ∧ ψ.source ⊆ U ∧ ψ.target ⊆ U ∧
      RealAnalyticOn ψ ψ.source ∧ RealAnalyticOn ψ.symm ψ.target ∧
      ∀ x ∈ ψ.source, ∀ u v, Ω (ψ x) (fderiv ℝ ψ x u) (fderiv ℝ ψ x v) = Ω p u v :=
  exists_darboux_local_realAnalytic' (ContinuousLinearEquiv.refl ℝ (E →L[ℝ] ℝ)) hU hΩa hskew
    hclosed hp hstrong

end Darboux

/-! ### Real analytic Darboux charts -/

section Manifold

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [RealAnalyticManifold E M]

/-- **A real analytic `2`-form in a chart, as an operator-valued map.** If `ω` is real analytic
(`DifferentialForm.IsRealAnalytic`: its local representatives `(y, u, v) ↦ Ω(y)(u, v)` are jointly
real analytic), its local representative in the preferred chart at `x₀` is real analytic as a map
`y ↦ Ω(y) ∈ L(E, E')` for the operator norm (lc-analysis, `RealAnalyticOn.of_unc_clm₂`). -/
theorem DifferentialForm.IsRealAnalytic.exists_clm_localRep {ω : DifferentialForm E M ℝ 2}
    (hωa : ω.IsRealAnalytic) (x₀ : M) :
    ∃ Ω : E → E →L[ℝ] E →L[ℝ] ℝ, RealAnalyticOn Ω (chartAt E x₀).target ∧
      ∀ y ∈ (chartAt E x₀).target, ∀ a b, Ω y a b = ω.localRep (prefChart x₀) (y, ![a, b]) := by
  obtain ⟨Ω, -, hΩ⟩ := ω.exists_clm_localRep x₀
  refine ⟨Ω, RealAnalyticOn.of_unc_clm₂ ?_, hΩ⟩
  set Lc : (E × E) × E →L[ℝ] E × (Fin 2 → E) :=
    ((ContinuousLinearMap.fst ℝ E E).comp (ContinuousLinearMap.fst ℝ (E × E) E)).prod
      (ContinuousLinearMap.pi ![(ContinuousLinearMap.snd ℝ E E).comp
        (ContinuousLinearMap.fst ℝ (E × E) E), ContinuousLinearMap.snd ℝ (E × E) E])
  have h := (hωa (prefChart x₀)).comp_clm_of_mapsTo Lc
    (U := ((chartAt E x₀).target ×ˢ univ) ×ˢ univ) fun r hr ↦ ⟨hr.1.1, mem_univ _⟩
  refine realAnalyticOn_congr (fun r hr ↦ ?_) h
  change ω.localRep (prefChart x₀) (Lc r) = Ω r.1.1 r.1.2 r.2
  rw [hΩ _ hr.1.1]
  congr 1
  refine Prod.ext rfl ?_
  funext j; fin_cases j <;> rfl

/-- **Real analytic Darboux charts.** Let `M` be a real analytic manifold modeled on a Banach space
`E` (not necessarily Hausdorff) and `ω` a closed, **real analytic**
(`DifferentialForm.IsRealAnalytic`, Glöckner–Neeb, Remark 3.6.18) real `2`-form on `M`, strongly
nondegenerate at `x₀`. Then the
Darboux chart can be chosen in the **real analytic** maximal atlas: there is a chart `φ` of the real
analytic structure around `x₀`, with `φ(x₀) = i(x₀)` and the same differential at `x₀` as the
preferred chart `i` at `x₀`, in which `ω` has constant coefficients.

The local representative `(y, u, v) ↦ Ω(y)(u, v)` of `ω` in `i` is jointly real analytic; by
`DifferentialForm.IsRealAnalytic.exists_clm_localRep` (lc-analysis, `RealAnalyticOn.of_unc_clm₂`)
`y ↦ Ω(y) ∈ L(E, E')` is real analytic for the operator norm, and
`Darboux.exists_darboux_local_realAnalytic` applies. -/
theorem DifferentialForm.exists_realAnalytic_darboux_chart [CompleteSpace E]
    (ω : DifferentialForm E M ℝ 2) (hω : ω.IsClosed) (x₀ : M)
    (hinj : ∀ v, (∀ w, ω x₀ ![v, w] = 0) → v = 0)
    (hsurj : ∀ φ : E →L[ℝ] ℝ, ∃ v, ∀ w, ω x₀ ![v, w] = φ w)
    (hωa : ω.IsRealAnalytic) :
    ∃ φ : OpenPartialHomeomorph M E, x₀ ∈ φ.source ∧
      φ ∈ (realAnalyticGroupoid E).maximalAtlas M ∧
      φ x₀ = chartAt E x₀ x₀ ∧ (∀ u, dMB (chartAt E x₀ ∘ φ.symm) (φ x₀, u) = u) ∧
      ∀ x ∈ φ.source, ∀ u v : E,
        ω x ![dMB (chartAt E x ∘ φ.symm) (φ x, u), dMB (chartAt E x ∘ φ.symm) (φ x, v)] =
          ω x₀ ![u, v] := by
  obtain ⟨Ω, hΩa, hΩ⟩ := hωa.exists_clm_localRep x₀
  have hT : IsOpen (chartAt E x₀).target := (chartAt E x₀).open_target
  have hΩs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ω (chartAt E x₀).target :=
    (smoothMBOn_iff_contDiffOn hT).1 (hΩa.smoothMBOn hT)
  obtain ⟨hskew, hclosed, hΩp⟩ := ω.clm_localRep_spec hω x₀ hΩs hΩ
  have hpT : chartAt E x₀ x₀ ∈ (chartAt E x₀).target :=
    (chartAt E x₀).map_source (mem_chart_source E x₀)
  have hstrong : Bijective (Ω (chartAt E x₀ x₀)) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun a ha ↦ hinj a fun w ↦ ?_, fun φ ↦ ?_⟩
    · rw [← hΩp, ha]; rfl
    · obtain ⟨v, hv⟩ := hsurj φ
      exact ⟨v, ContinuousLinearMap.ext fun w ↦ by rw [hΩp, hv]⟩
  obtain ⟨ψ, hpψ, hψp, hDψp, -, -, hψa, hψa', hψpull⟩ :=
    Darboux.exists_darboux_local_realAnalytic hT hΩa hskew hclosed hpT hstrong
  have hψs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ψ.source :=
    (smoothMBOn_iff_contDiffOn ψ.open_source).1 (hψa.smoothMBOn ψ.open_source)
  have hψs' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ.symm ψ.target :=
    (smoothMBOn_iff_contDiffOn ψ.open_target).1 (hψa'.smoothMBOn ψ.open_target)
  obtain ⟨h1, -, h3, h4, h5⟩ :=
    ω.darboux_chart_of_local x₀ hΩ hpψ hψp hDψp hψs hψs' hψpull hΩp
  -- `φ = ψ⁻¹ ∘ i` belongs to the real analytic maximal atlas
  have hψG : ψ.symm ∈ realAnalyticGroupoid E :=
    (mem_realAnalyticGroupoid E).2 ⟨hψa', by simpa using hψa⟩
  have hψG' : ψ ∈ realAnalyticGroupoid E := (mem_realAnalyticGroupoid E).2 ⟨hψa, hψa'⟩
  have hi : chartAt E x₀ ∈ atlas E M := chart_mem_atlas E x₀
  refine ⟨_, h1, ?_, h3, h4, h5⟩
  refine mem_maximalAtlas_iff.2 fun e' he' ↦ ⟨?_, ?_⟩
  · rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm,
      OpenPartialHomeomorph.trans_assoc]
    exact (realAnalyticGroupoid E).trans hψG' ((realAnalyticGroupoid E).compatible hi he')
  · rw [← OpenPartialHomeomorph.trans_assoc]
    exact (realAnalyticGroupoid E).trans ((realAnalyticGroupoid E).compatible he' hi) hψG

/-- **Real analytic Darboux charts for strong symplectic forms**: on a real analytic manifold
modeled on a Banach space, a real analytic strong symplectic form has constant coefficients in a
chart of the real analytic structure around each point `x₀`. -/
theorem SymplecticForm.IsStrong.exists_realAnalytic_darboux_chart [CompleteSpace E]
    {ω : SymplecticForm E M} (hω : ω.IsStrong) (hωa : ω.form.IsRealAnalytic) (x₀ : M) :
    ∃ φ : OpenPartialHomeomorph M E, x₀ ∈ φ.source ∧
      φ ∈ (realAnalyticGroupoid E).maximalAtlas M ∧
      φ x₀ = chartAt E x₀ x₀ ∧ (∀ u, dMB (chartAt E x₀ ∘ φ.symm) (φ x₀, u) = u) ∧
      ∀ x ∈ φ.source, ∀ u v : E,
        ω.form x ![dMB (chartAt E x ∘ φ.symm) (φ x, u), dMB (chartAt E x ∘ φ.symm) (φ x, v)] =
          ω.form x₀ ![u, v] :=
  ω.form.exists_realAnalytic_darboux_chart ω.isClosed x₀ (ω.nondegenerate x₀) (hω x₀) hωa

end Manifold

end LocallyConvex.Manifolds
