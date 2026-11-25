/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.Metric.FinslerMetricSpace
public import LocallyConvexManifolds.Metric.Bilinear
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# The topology of a Finsler metric is coarser than that of the manifold

For a Finsler metric `μ` (continuous on `TM`) on a manifold modeled on any locally convex space,
points that are close in `M` are close for the Finsler distance, in both directions:
`d(x₀, y) → 0` and `d(y, x₀) → 0` as `y → x₀`. Consequently `d : M × M → [0, ∞]` is continuous
and the identity `M → (M, d)` is continuous ([Lar19, Prop. 2.10(1), (2)]).

No normability or completeness of the model is needed, and no bound on `μ`: compare
`FinslerLengthStructure.continuous_toFinsler_of_isBoundedAbove`, which needs a normed model. The
proof is that of [Lar19, Prop. 2.10(1)], written in an arbitrary chart instead of a chart at the
identity of a Lie group: the segment from `φ x₀` to `φ y` in a chart `φ`, reparametrized by
`Real.smoothTransition`, has length at most `ε` as soon as `φ y − φ x₀` lies in a convex
neighborhood `W` of `0` such that `μ(φ⁻¹(φ x₀ + w'), w) < ε` for `w, w' ∈ W`. Such a `W` exists
because `μ` is continuous on `TM` and vanishes on the zero section.

**On the statement of [Lar19, Prop. 2.10(2)].** There it is said that the topology `τ_μ` of the
distance is *finer* than the manifold topology `τ_G`. What (1) proves, and what is formalized
here, is the opposite inclusion: the identity `(M, τ_M) → (M, τ_μ)` is continuous, so every
`τ_μ`-open set is open in `M`, that is, `τ_μ` is **coarser** than `τ_M`. The reverse inclusion
fails in general (the distance may even vanish between distinct points, [MM05, Thm. 5.2]); for
bounded below metrics on normed models it holds (`FinslerLengthStructure.continuous_ofFinsler`).

## Main results

* `FinslerLengthStructure.dist_le_of_segment`: the distance between the endpoints of a segment in
  a chart is bounded by a uniform bound of `μ` along the segment.
* `FinslerMetric.tendsto_dist_left`, `FinslerMetric.tendsto_dist_right`: `d(x₀, y) → 0` and
  `d(y, x₀) → 0` as `y → x₀` ([Lar19, Prop. 2.10(1)]).
* `FinslerMetric.continuous_dist`: `d : M × M → [0, ∞]` is continuous ([Lar19, Prop. 2.10(2)]).
* `FinslerMetric.continuous_toFinsler`: the identity `M → (M, d)` is continuous.

## References

* [G. Larotonda, *The metric geometry of infinite dimensional Lie groups and their homogeneous
  spaces*][Lar19]
* [P. W. Michor, D. Mumford, *Vanishing geodesic distance on spaces of submanifolds and
  diffeomorphisms*][MM05]
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology ENNReal
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe u

variable {E : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

omit [LocallyConvexSpace ℝ E] [T2Space E] [ContinuousSMul ℝ E] [IsTopologicalAddGroup E] in
/-- The derivative of the affine map `s ↦ a + s • w` on `ℝ`. -/
theorem hasDirDerivAt_affine (a w : E) (s h : ℝ) :
    HasDirDerivAt (fun s : ℝ ↦ a + s • w) s h (h • w) := by
  refine tendsto_nhdsWithin_congr (fun t ht ↦ ?_) tendsto_const_nhds
  have ht' : t ≠ 0 := ht
  have : a + (s + t • h) • w - (a + s • w) = (t * h) • w := by
    rw [smul_eq_mul, add_smul, mul_smul]; abel
  rw [this, smul_smul, inv_mul_cancel_left₀ ht']

omit [LocallyConvexSpace ℝ E] in
/-- The affine map `s ↦ a + s • w` on `ℝ` is `C¹` in the sense of Michal–Bastiani. -/
theorem contDiffMBOn_affine (a w : E) : ContDiffMBOn 1 (fun s : ℝ ↦ a + s • w) univ := by
  have hdMB : dMB (fun s : ℝ ↦ a + s • w) = fun p ↦ p.2 • w :=
    funext fun p ↦ (hasDirDerivAt_affine a w p.1 p.2).dMB_eq
  refine ⟨(continuous_const.add (continuous_id.smul continuous_const)).continuousOn,
    fun s _ h ↦ ?_, ?_⟩
  · rw [hdMB]; exact hasDirDerivAt_affine a w s h
  · rw [hdMB]
    exact (continuous_snd.smul continuous_const).continuousOn

/-- The coordinate change of tangent vectors is homogeneous. -/
theorem tangentCoordChange_smul' (i j : atlas E M) {x : M} (hi : x ∈ i.1.source)
    (hj : x ∈ j.1.source) (c : ℝ) (v : E) :
    tangentCoordChange i j x (c • v) = c • tangentCoordChange i j x v := by
  have hmem : i.1 x ∈ i.1.target ∩ i.1.symm ⁻¹' j.1.source :=
    ⟨i.1.map_source hi, by simp [i.1.left_inv hi, hj]⟩
  exact (smoothMBOn_transition' i j 1).dMB_smul hmem c v

namespace FinslerSeminormField

variable (μ : FinslerSeminormField E M)

/-- In the chart `i` of the tangent bundle, `μ` is positively homogeneous in the fiber
coordinate. -/
theorem apply_tangentChart_symm_smul (i : atlas E M) {y : E} (hy : y ∈ i.1.target) {r : ℝ}
    (hr : 0 ≤ r) (v : E) :
    μ ((tangentChart i i.1).symm (y, r • v)) = r * μ ((tangentChart i i.1).symm (y, v)) := by
  set x := i.1.symm y
  have hx : x ∈ i.1.source := i.1.map_target hy
  change μ (⟨x, (tangentCoordChange i (prefAtlas E x) x (r • v) : E)⟩ : TangentBundle E M) =
    r * μ (⟨x, (tangentCoordChange i (prefAtlas E x) x v : E)⟩ : TangentBundle E M)
  rw [tangentCoordChange_smul' i (prefAtlas E x) hx (mem_chart_source E x)]
  exact μ.smul_eq' x r hr _

end FinslerSeminormField

namespace FinslerLengthStructure

variable (μ : FinslerLengthStructure E M)

/-- **The distance between the endpoints of a segment in a chart.** If the segment from `a` to
`b` lies in the image of the chart `i`, and `μ(φ⁻¹(a + s (b − a)), b − a) ≤ ε` along it, then
`d(φ⁻¹ a, φ⁻¹ b) ≤ ε`. The segment is reparametrized by `Real.smoothTransition`, so that it is a
`C¹` curve defined on all of `ℝ`. -/
theorem dist_le_of_segment (i : atlas E M) {a b : E} {ε : ℝ}
    (hseg : ∀ s ∈ Icc (0 : ℝ) 1, a + s • (b - a) ∈ i.1.target ∧
      μ.toFun ((tangentChart i i.1).symm (a + s • (b - a), b - a)) ≤ ε) :
    μ.dist (i.1.symm a) (i.1.symm b) ≤ ENNReal.ofReal ε := by
  set w := b - a
  set σ := Real.smoothTransition
  set c : ℝ → E := fun t ↦ a + σ t • w
  have hσ01 : ∀ t, σ t ∈ Icc (0 : ℝ) 1 := fun t ↦
    ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
  have hcT : ∀ t, c t ∈ i.1.target := fun t ↦ (hseg _ (hσ01 t)).1
  have hσd : ContDiff ℝ 1 σ := Real.smoothTransition.contDiff (n := 1)
  have hσMB : ContDiffMBOn 1 σ univ := ContDiffOn.contDiffMBOn isOpen_univ hσd.contDiffOn
  have hcMB : ContDiffMBOn 1 c univ :=
    ContDiffMBOn.comp (g := fun s : ℝ ↦ a + s • w) (f := σ) isOpen_univ isOpen_univ
      (contDiffMBOn_affine a w) hσMB (mapsTo_univ _ _)
  have hcc : Continuous c := continuousOn_univ.mp hcMB.continuousOn
  set γ : ℝ → M := fun t ↦ i.1.symm (c t)
  have hγ : IsCkCurve E 1 γ := by
    refine ⟨i.1.continuousOn_symm.comp_continuous hcc hcT, fun j ↦ ?_⟩
    set T := i.1.target ∩ i.1.symm ⁻¹' j.1.source
    have hT : IsOpen T := isOpen_transition_domain i j
    have hpre : γ ⁻¹' j.1.source = c ⁻¹' T := by
      ext t; simp [γ, T, hcT t]
    rw [hpre]
    exact ContDiffMBOn.comp (g := j.1 ∘ i.1.symm) (f := c) (hT.preimage hcc) hT
      (smoothMBOn_transition' i j 1) (hcMB.mono (subset_univ _)) (fun t ht ↦ ht)
  have hγ0 : γ 0 = i.1.symm a := by simp [γ, c, σ, Real.smoothTransition.zero]
  have hγ1 : γ 1 = i.1.symm b := by simp [γ, c, σ, Real.smoothTransition.one, w]
  have hdist := μ.dist_le hγ zero_le_one
  rw [hγ0, hγ1] at hdist
  refine hdist.trans (ENNReal.ofReal_le_ofReal ?_)
  -- the velocity in the chart is `σ'(t) w`
  have hdMB : ∀ t, dMB (i.1 ∘ γ) (t, 1) = deriv σ t • w := by
    intro t
    have hfun : i.1 ∘ γ = c := funext fun t ↦ i.1.right_inv (hcT t)
    have hσ1 : HasDirDerivAt σ t 1 (deriv σ t) := by
      simpa [HasDirDerivAt] using
        ((hσd.differentiable one_ne_zero t).hasDerivAt).tendsto_slope_zero
    have hc : c = (fun s : ℝ ↦ a + s • w) ∘ σ := rfl
    rw [hfun, hc, ContDiffMBOn.dMB_comp isOpen_univ (contDiffMBOn_affine a w) hσMB
      (mapsTo_univ _ _) (mem_univ t) 1, hσ1.dMB_eq]
    exact (hasDirDerivAt_affine a w _ _).dMB_eq
  have hvel : ∀ t, velocity E γ t = (tangentChart i i.1).symm (c t, deriv σ t • w) := by
    intro t
    have hγt : γ t ∈ i.1.source := i.1.map_target (hcT t)
    have hsrc : velocity E γ t ∈ (tangentChart i i.1).source :=
      (mem_tangentChart_source i i.1 _).mpr ⟨hγt, hγt⟩
    have hch : tangentChart i i.1 (velocity E γ t) = (c t, deriv σ t • w) := by
      refine Prod.ext (i.1.right_inv (hcT t)) ?_
      change liftCoord i (velocity E γ) t = _
      rw [liftCoord_velocity hγ i hγt, hdMB]
    rw [← hch, (tangentChart i i.1).left_inv hsrc]
  have hσ'nonneg : ∀ t, 0 ≤ deriv σ t := fun t ↦ Real.smoothTransition.monotone.deriv_nonneg
  have hσ'cont : Continuous (deriv σ) := hσd.continuous_deriv le_rfl
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1, μ.toFun (velocity E γ t) ≤ deriv σ t * ε := by
    intro t _
    rw [hvel, μ.toFinslerSeminormField.apply_tangentChart_symm_smul i (hcT t) (hσ'nonneg t)]
    exact mul_le_mul_of_nonneg_left (hseg _ (hσ01 t)).2 (hσ'nonneg t)
  calc μ.length γ 0 1 ≤ ∫ t in (0 : ℝ)..1, deriv σ t * ε :=
        intervalIntegral.integral_mono_on zero_le_one
          ((μ.continuous_velocity hγ).intervalIntegrable _ _)
          ((hσ'cont.mul continuous_const).intervalIntegrable _ _) hbound
    _ = (∫ t in (0 : ℝ)..1, deriv σ t) * ε := intervalIntegral.integral_mul_const _ _
    _ = ε := by
        rw [intervalIntegral.integral_deriv_eq_sub
          (fun t _ ↦ (hσd.differentiable one_ne_zero t)) (hσ'cont.intervalIntegrable _ _)]
        simp [σ, Real.smoothTransition.one, Real.smoothTransition.zero]

end FinslerLengthStructure

namespace FinslerMetric

variable (μ : FinslerMetric E M)

/-- **A convex neighborhood where `μ` is small.** For `ε > 0` and the preferred chart `φ` at `x₀`
there is a symmetric convex neighborhood `W` of `0` such that `φ x₀ + w'` lies in the image of
`φ` and `μ(φ⁻¹(φ x₀ + w'), w) < ε` for all `w, w' ∈ W`. -/
theorem exists_convex_nhds_lt (x₀ : M) {ε : ℝ} (hε : 0 < ε) :
    ∃ W : Set E, W ∈ 𝓝 (0 : E) ∧ Convex ℝ W ∧ (∀ w ∈ W, -w ∈ W) ∧
      ∀ w ∈ W, ∀ w' ∈ W, chartAt E x₀ x₀ + w' ∈ (chartAt E x₀).target ∧
        μ.toFun ((tangentChart (prefAtlas E x₀) (chartAt E x₀)).symm
          (chartAt E x₀ x₀ + w', w)) < ε := by
  set i := prefAtlas E x₀
  set φ := chartAt E x₀
  set Φ := tangentChart i φ
  set F : E × E → ℝ := fun q ↦ μ.toFun (Φ.symm q)
  have hF : ContinuousOn F Φ.target := μ.continuous'.comp_continuousOn Φ.continuousOn_symm
  set S := Φ.target ∩ F ⁻¹' Iio ε
  have hS : IsOpen S := hF.isOpen_inter_preimage Φ.open_target isOpen_Iio
  have hx₀ : x₀ ∈ φ.source := mem_chart_source E x₀
  have hφx₀ : φ x₀ ∈ φ.target := φ.map_source hx₀
  have hmem : (φ x₀, (0 : E)) ∈ S := by
    refine ⟨(mem_tangentChart_target i φ _).mpr ⟨hφx₀, by rw [φ.left_inv hx₀]; exact hx₀⟩, ?_⟩
    have h0 := μ.toFinslerSeminormField.apply_tangentChart_symm_smul i hφx₀ le_rfl (0 : E)
    simp only [zero_smul, zero_mul] at h0
    change F (φ x₀, 0) < ε
    exact h0.trans_lt hε
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp (hS.mem_nhds hmem)
  have hu' : (fun w ↦ φ x₀ + w) ⁻¹' u ∈ 𝓝 (0 : E) :=
    (continuous_const_add (φ x₀)).continuousAt.preimage_mem_nhds (by simpa using hu)
  set N := (fun w ↦ φ x₀ + w) ⁻¹' u ∩ v
  have hN : N ∈ 𝓝 (0 : E) := inter_mem hu' hv
  obtain ⟨W₀, ⟨hW₀, hW₀c⟩, hW₀N⟩ := (LocallyConvexSpace.convex_basis_zero ℝ E).mem_iff.mp hN
  refine ⟨W₀ ∩ -W₀, inter_mem hW₀ (neg_mem_nhds_zero E hW₀), hW₀c.inter hW₀c.neg,
    fun w hw ↦ ⟨hw.2, by simpa using hw.1⟩, fun w hw w' hw' ↦ ?_⟩
  have hq : (φ x₀ + w', w) ∈ S := huv ⟨(hW₀N hw'.1).1, (hW₀N hw.1).2⟩
  refine ⟨((mem_tangentChart_target i φ _).mp hq.1).1, hq.2⟩

/-- Two points `φ⁻¹(φ x₀ + w₁)`, `φ⁻¹(φ x₀ + w₂)` with `w₁, w₂, w₂ − w₁` in the neighborhood `W`
of `exists_convex_nhds_lt` are at distance at most `ε`. -/
theorem dist_le_of_mem_convex_nhds (x₀ : M) {ε : ℝ} {W : Set E} (hWc : Convex ℝ W)
    (hW : ∀ w ∈ W, ∀ w' ∈ W, chartAt E x₀ x₀ + w' ∈ (chartAt E x₀).target ∧
      μ.toFun ((tangentChart (prefAtlas E x₀) (chartAt E x₀)).symm
        (chartAt E x₀ x₀ + w', w)) < ε)
    {w₁ w₂ : E} (h₁ : w₁ ∈ W) (h₂ : w₂ ∈ W) (h₂₁ : w₂ - w₁ ∈ W) :
    μ.dist ((chartAt E x₀).symm (chartAt E x₀ x₀ + w₁))
      ((chartAt E x₀).symm (chartAt E x₀ x₀ + w₂)) ≤ ENNReal.ofReal ε := by
  set φ := chartAt E x₀
  refine μ.toFinslerLengthStructure.dist_le_of_segment (prefAtlas E x₀) fun s hs ↦ ?_
  have hseg : φ x₀ + w₁ + s • (φ x₀ + w₂ - (φ x₀ + w₁)) = φ x₀ + ((1 - s) • w₁ + s • w₂) := by
    module
  have hmem : (1 - s) • w₁ + s • w₂ ∈ W :=
    hWc h₁ h₂ (by linarith [hs.2]) hs.1 (by ring)
  have hv : φ x₀ + w₂ - (φ x₀ + w₁) = w₂ - w₁ := by abel
  rw [hseg, hv]
  exact ⟨(hW _ h₂₁ _ hmem).1, (hW _ h₂₁ _ hmem).2.le⟩

/-- Points near `x₀` in `M` are near `x₀` for `d`, in the forward direction
([Lar19, Prop. 2.10(1)]). -/
theorem tendsto_dist_left (x₀ : M) : Tendsto (fun y ↦ μ.dist x₀ y) (𝓝 x₀) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨ρ, -, hρpos, hρε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
  have hρ : 0 < ρ := ENNReal.ofReal_pos.mp hρpos
  obtain ⟨W, hW0, hWc, -, hW⟩ := μ.exists_convex_nhds_lt x₀ hρ
  set φ := chartAt E x₀
  have hx₀ : x₀ ∈ φ.source := mem_chart_source E x₀
  have hev : ∀ᶠ y in 𝓝 x₀, y ∈ φ.source ∧ φ y - φ x₀ ∈ W := by
    have : (fun y ↦ φ y - φ x₀) ⁻¹' W ∈ 𝓝 x₀ :=
      ((φ.continuousAt hx₀).sub continuousAt_const).preimage_mem_nhds (by simpa using hW0)
    exact Filter.inter_mem (φ.open_source.mem_nhds hx₀) this
  filter_upwards [hev] with y ⟨hy, hyW⟩
  have h := μ.dist_le_of_mem_convex_nhds x₀ hWc hW (mem_of_mem_nhds hW0) hyW (by simpa using hyW)
  rw [add_zero, φ.left_inv hx₀, add_sub_cancel, φ.left_inv hy] at h
  exact h.trans hρε.le

/-- Points near `x₀` in `M` are near `x₀` for `d`, in the backward direction
([Lar19, Prop. 2.10(1)]). -/
theorem tendsto_dist_right (x₀ : M) : Tendsto (fun y ↦ μ.dist y x₀) (𝓝 x₀) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨ρ, -, hρpos, hρε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
  have hρ : 0 < ρ := ENNReal.ofReal_pos.mp hρpos
  obtain ⟨W, hW0, hWc, hWneg, hW⟩ := μ.exists_convex_nhds_lt x₀ hρ
  set φ := chartAt E x₀
  have hx₀ : x₀ ∈ φ.source := mem_chart_source E x₀
  have hev : ∀ᶠ y in 𝓝 x₀, y ∈ φ.source ∧ φ y - φ x₀ ∈ W := by
    have : (fun y ↦ φ y - φ x₀) ⁻¹' W ∈ 𝓝 x₀ :=
      ((φ.continuousAt hx₀).sub continuousAt_const).preimage_mem_nhds (by simpa using hW0)
    exact Filter.inter_mem (φ.open_source.mem_nhds hx₀) this
  filter_upwards [hev] with y ⟨hy, hyW⟩
  have h := μ.dist_le_of_mem_convex_nhds x₀ hWc hW hyW (mem_of_mem_nhds hW0)
    (by simpa using hWneg _ hyW)
  rw [add_zero, φ.left_inv hx₀, add_sub_cancel, φ.left_inv hy] at h
  exact h.trans hρε.le

/-- **The Finsler distance is continuous** on `M × M` ([Lar19, Prop. 2.10(2)]), as a function
with values in `[0, ∞]`. -/
theorem continuous_dist : Continuous fun p : M × M ↦ μ.dist p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨x₀, y₀⟩
  set d₀ := μ.dist x₀ y₀
  have hA : Tendsto (fun p : M × M ↦ μ.dist x₀ p.1) (𝓝 (x₀, y₀)) (𝓝 0) :=
    (μ.tendsto_dist_left x₀).comp continuous_fst.continuousAt
  have hA' : Tendsto (fun p : M × M ↦ μ.dist p.1 x₀) (𝓝 (x₀, y₀)) (𝓝 0) :=
    (μ.tendsto_dist_right x₀).comp continuous_fst.continuousAt
  have hB : Tendsto (fun p : M × M ↦ μ.dist p.2 y₀) (𝓝 (x₀, y₀)) (𝓝 0) :=
    (μ.tendsto_dist_right y₀).comp continuous_snd.continuousAt
  have hB' : Tendsto (fun p : M × M ↦ μ.dist y₀ p.2) (𝓝 (x₀, y₀)) (𝓝 0) :=
    (μ.tendsto_dist_left y₀).comp continuous_snd.continuousAt
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun a ha ↦ ?_⟩
  · -- lower bound: `d₀ ≤ d(x₀, x) + d(x, y) + d(y, y₀)`
    have hlim : Tendsto (fun p : M × M ↦ μ.dist x₀ p.1 + a + μ.dist p.2 y₀) (𝓝 (x₀, y₀))
        (𝓝 (0 + a + 0)) := (hA.add tendsto_const_nhds).add hB
    rw [zero_add, add_zero] at hlim
    filter_upwards [(tendsto_order.1 hlim).2 d₀ ha] with p hp
    by_contra hle
    rw [not_lt] at hle
    have htri : d₀ ≤ μ.dist x₀ p.1 + μ.dist p.1 p.2 + μ.dist p.2 y₀ :=
      (μ.toFinslerLengthStructure.dist_triangle x₀ p.2 y₀).trans (add_le_add_left (μ.toFinslerLengthStructure.dist_triangle x₀ p.1 p.2) _)
    exact absurd (htri.trans (by gcongr)) (not_le.mpr hp)
  · -- upper bound: `d(x, y) ≤ d(x, x₀) + d₀ + d(y₀, y)`
    have hlim : Tendsto (fun p : M × M ↦ μ.dist p.1 x₀ + d₀ + μ.dist y₀ p.2) (𝓝 (x₀, y₀))
        (𝓝 (0 + d₀ + 0)) := (hA'.add tendsto_const_nhds).add hB'
    rw [zero_add, add_zero] at hlim
    filter_upwards [(tendsto_order.1 hlim).2 a ha] with p hp
    refine lt_of_le_of_lt ?_ hp
    exact (μ.toFinslerLengthStructure.dist_triangle p.1 y₀ p.2).trans
      (add_le_add_left (μ.toFinslerLengthStructure.dist_triangle p.1 x₀ y₀) _)

/-- **The identity `M → (M, d)` is continuous**: the topology of the Finsler distance is coarser
than that of `M` ([Lar19, Prop. 2.10(1)]; see the module docstring for the direction of the
inclusion). -/
theorem continuous_toFinsler : Continuous μ.toFinslerLengthStructure.toFinsler := by
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [ContinuousAt, tendsto_iff_edist_tendsto_0]
  have h := (μ.tendsto_dist_right x₀).max (μ.tendsto_dist_left x₀)
  rw [max_self] at h
  refine h.congr fun y ↦ ?_
  rw [edist_eq_max_bdist]
  rfl

end FinslerMetric

end LocallyConvex.Manifolds
