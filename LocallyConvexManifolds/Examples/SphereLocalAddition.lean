/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.Submanifold.LocalAddition
public import LocallyConvexManifolds.Examples.Sphere
public import LocallyConvexAnalysis.Calculus.MBFrechet

/-!
# Example: a local addition on the unit sphere

Let `H` be a real inner product space, not necessarily complete, and `S ⊆ H` its unit sphere,
an embedded submanifold modeled on `e^⊥` (`isEmbeddedSubmanifold_sphere`) with `T_p S = p^⊥`
(`tangentSpace_sphere`). The radial projection

  `Σ(p, w) = (p + w) / ‖p + w‖`,   `w ⊥ p`,

is a normalized local addition on `S` ([GN26, Definition 3.8.11 and (3.55)]), defined on all of
`TS`: `θ = (π, Σ)` maps `TS` diffeomorphically onto `{(p, q) ∈ S × S : ⟪p, q⟫ > 0}`, with inverse
`(p, q) ↦ (p, q / ⟪p, q⟫ - p)`. Hence the manifolds of mappings `C^ℓ(K, S)` of
`MappingSpace/Ck.lean` are available for the sphere.

## Main results

* `sphereAmbientAddition`: the ambient data `σ`, `τ` (`AmbientAddition`);
* `sphereLocalAddition`, `sphereLocalAddition_toFun`, `mem_sphereLocalAddition_target`: the
  local addition, its formula, its image;
* `isNormalized_sphereLocalAddition`: it is normalized.

## Implementation notes

* Smoothness of `σ` and `τ` is checked in the Fréchet sense and transferred with
  `smoothMBOn_iff_contDiffOn` ([GN26, Proposition 2.3.17]); no completeness is needed.
* Glöckner–Neeb do not treat the sphere: their local additions come from Lie group structures
  ([GN26, Proposition 3.8.12]) and from sprays on smoothly paracompact Banach manifolds
  ([GN26, Proposition 3.8.13]). The exponential map of the round metric,
  `w ↦ cos ‖w‖ p + sin ‖w‖ w/‖w‖` on `‖w‖ < π`, would be another natural choice; the radial
  projection avoids the singularity of `w ↦ w/‖w‖` at `0` and has explicit rational formulas. We do
  not claim this construction is new.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

namespace Sphere

/-- The ambient formula `σ(p, w) = (p + w) / ‖p + w‖`. -/
def sigma (z : H × H) : H := ‖z.1 + z.2‖⁻¹ • (z.1 + z.2)

/-- The ambient formula of the inverse, `τ(p, q) = q / ⟪p, q⟫ - p`. -/
def tau (z : H × H) : H := ⟪z.1, z.2⟫⁻¹ • z.2 - z.1

/-- `σ` is Fréchet smooth where `p + w ≠ 0`. -/
theorem contDiffOn_sigma :
    ContDiffOn ℝ ∞ (sigma (H := H)) {z : H × H | z.1 + z.2 ≠ 0} := by
  intro z hz
  have hs : ContDiffAt ℝ ∞ (fun z : H × H ↦ z.1 + z.2) z :=
    (contDiff_fst.add contDiff_snd).contDiffAt
  have hn := (hs.norm ℝ hz).inv (norm_ne_zero_iff.2 hz)
  exact (hn.smul hs).contDiffWithinAt

/-- `τ` is Fréchet smooth where `⟪p, q⟫ > 0`. -/
theorem contDiffOn_tau :
    ContDiffOn ℝ ∞ (tau (H := H)) {z : H × H | 0 < ⟪z.1, z.2⟫} := by
  intro z hz
  have hi : ContDiffAt ℝ ∞ (fun z : H × H ↦ ⟪z.1, z.2⟫) z :=
    (contDiff_fst.inner ℝ contDiff_snd).contDiffAt
  exact (((hi.inv (ne_of_gt hz)).smul contDiff_snd.contDiffAt).sub
    contDiff_fst.contDiffAt).contDiffWithinAt

/-- `σ` is smooth in the sense of Michal–Bastiani where `p + w ≠ 0`. -/
theorem smoothMBOn_sigma : SmoothMBOn (sigma (H := H)) {z : H × H | z.1 + z.2 ≠ 0} :=
  (smoothMBOn_iff_contDiffOn (isOpen_ne_fun (by fun_prop) continuous_const)).2 contDiffOn_sigma

/-- `τ` is smooth in the sense of Michal–Bastiani where `⟪p, q⟫ > 0`. -/
theorem smoothMBOn_tau : SmoothMBOn (tau (H := H)) {z : H × H | 0 < ⟪z.1, z.2⟫} :=
  (smoothMBOn_iff_contDiffOn (isOpen_lt continuous_const (by fun_prop))).2 contDiffOn_tau

variable {p w q : H}

/-- For `‖p‖ = 1` and `w ⊥ p`, `p + w ≠ 0`. -/
theorem add_ne_zero_of_inner (hp : ‖p‖ = 1) (hpw : ⟪p, w⟫ = 0) : p + w ≠ 0 := by
  intro h0
  have : ⟪p, p + w⟫ = 1 := by
    rw [inner_add_right, hpw, add_zero, real_inner_self_eq_norm_sq, hp, one_pow]
  rw [h0, inner_zero_right] at this
  exact zero_ne_one this

/-- For `‖p‖ = 1` and `w ⊥ p`, `⟪p, σ(p, w)⟫ = 1/‖p + w‖`. -/
theorem inner_sigma (hp : ‖p‖ = 1) (hpw : ⟪p, w⟫ = 0) : ⟪p, sigma (p, w)⟫ = ‖p + w‖⁻¹ := by
  simp only [sigma, inner_smul_right, inner_add_right, hpw, add_zero,
    real_inner_self_eq_norm_sq, hp, one_pow, mul_one]

/-- `σ` takes values in the unit sphere. -/
theorem norm_sigma (hpw : p + w ≠ 0) : ‖sigma (p, w)‖ = 1 := by
  simp only [sigma, norm_smul, norm_inv, norm_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.2 hpw)

/-- `τ(p, σ(p, w)) = w` for `‖p‖ = 1` and `w ⊥ p`. -/
theorem tau_sigma (hp : ‖p‖ = 1) (hpw : ⟪p, w⟫ = 0) : tau (p, sigma (p, w)) = w := by
  have hn : ‖p + w‖ ≠ 0 := norm_ne_zero_iff.2 (add_ne_zero_of_inner hp hpw)
  simp only [tau]
  rw [inner_sigma hp hpw, inv_inv, sigma, smul_smul, mul_inv_cancel₀ hn, one_smul,
    add_sub_cancel_left]

/-- `τ(p, q) ⊥ p` when `‖p‖ = 1` and `⟪p, q⟫ > 0`. -/
theorem inner_tau (hq : 0 < ⟪p, q⟫) (hp : ‖p‖ = 1) : ⟪p, tau (p, q)⟫ = 0 := by
  simp only [tau, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hp, one_pow]
  rw [inv_mul_cancel₀ (ne_of_gt hq), sub_self]

/-- `p + τ(p, q) = q / ⟪p, q⟫`. -/
theorem add_tau (p q : H) : p + tau (p, q) = ⟪p, q⟫⁻¹ • q := by
  simp only [tau]; abel

/-- `σ(p, τ(p, q)) = q` for `‖q‖ = 1` and `⟪p, q⟫ > 0`. -/
theorem sigma_tau (hq : 0 < ⟪p, q⟫) (hq1 : ‖q‖ = 1) : sigma (p, tau (p, q)) = q := by
  simp only [sigma]
  rw [add_tau, norm_smul, hq1, mul_one, norm_inv, Real.norm_of_nonneg hq.le, inv_inv, smul_smul,
    mul_inv_cancel₀ (ne_of_gt hq), one_smul]

/-- `w ↦ σ(p, w)` has derivative the identity at `0` along `p^⊥`. -/
theorem dMB_sigma (hp : ‖p‖ = 1) (hpw : ⟪p, w⟫ = 0) :
    dMB (fun u ↦ sigma (p, u)) (0, w) = w := by
  have hg : HasDerivAt (fun t : ℝ ↦ p + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add p
  have hm := hg.norm_sq
  have hm0 : ‖p + (0 : ℝ) • w‖ ^ 2 ≠ 0 := by simp [hp]
  have hn := (hm.sqrt hm0).inv (by simp [hp])
  have hγ := hn.smul hg
  have hγ' : HasDerivAt (fun t : ℝ ↦ sigma (p, t • w)) w 0 := by
    convert hγ using 1
    · funext t
      simp only [sigma, Real.sqrt_sq (norm_nonneg _)]
      rfl
    · simp [hp, hpw]
  refine HasDirDerivAt.dMB_eq ?_
  have := hasDerivAt_iff_tendsto_slope_zero.1 hγ'
  unfold HasDirDerivAt
  refine this.congr fun t ↦ ?_
  simp

end Sphere

open Sphere

variable {e : H}

/-- The ambient data `σ(p, w) = (p + w)/‖p + w‖`, `τ(p, q) = q/⟪p, q⟫ - p` of the local addition of
the sphere. -/
def sphereAmbientAddition (he : ‖e‖ = 1) : AmbientAddition (isEmbeddedSubmanifold_sphere he) where
  Ω := {z : H × H | z.1 + z.2 ≠ 0}
  isOpen_Ω := isOpen_ne_fun (by fun_prop) continuous_const
  σ := sigma
  smoothMBOn_σ := smoothMBOn_sigma
  V := {z : H × H | 0 < ⟪z.1, z.2⟫}
  isOpen_V := isOpen_lt continuous_const (by fun_prop)
  τ := tau
  smoothMBOn_τ := smoothMBOn_tau
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
    rw [tangentSpace_sphere he p] at hw
    change 0 < ⟪(p : H), sigma ((p : H), w)⟫
    rw [inner_sigma hp hw]
    exact inv_pos.2 (norm_pos_iff.2 (add_ne_zero_of_inner hp hw))
  τ_σ p w hw _ := by
    rw [tangentSpace_sphere he p] at hw
    exact tau_sigma (mem_sphere_zero_iff_norm.mp p.2) hw
  τ_mem p q hV := by
    rw [tangentSpace_sphere he p]
    exact inner_tau hV (mem_sphere_zero_iff_norm.mp p.2)
  mem_Ω p q hV := by
    have hq : ‖(q : H)‖ = 1 := mem_sphere_zero_iff_norm.mp q.2
    change (p : H) + tau ((p : H), (q : H)) ≠ 0
    rw [add_tau]
    refine smul_ne_zero (inv_ne_zero (ne_of_gt hV)) ?_
    rw [← norm_ne_zero_iff, hq]
    exact one_ne_zero
  σ_τ p q hV := sigma_tau hV (mem_sphere_zero_iff_norm.mp q.2)

/-- **A local addition on the unit sphere** of a real inner product space (no completeness):
`Σ(p, w) = (p + w)/‖p + w‖` for `w ∈ T_p S = p^⊥` (ambient vector), defined on all of `TS`, with
`θ = (π, Σ)` mapping `TS` onto `{(p, q) : ⟪p, q⟫ > 0}` and inverse `(p, q) ↦ (p, q/⟪p, q⟫ - p)`. -/
def sphereLocalAddition (he : ‖e‖ = 1) :
    letI := (isEmbeddedSubmanifold_sphere he).chartedSpace
    haveI := (isEmbeddedSubmanifold_sphere he).mbManifold
    LocalAddition (ℝ ∙ e)ᗮ (Metric.sphere (0 : H) 1) :=
  letI := (isEmbeddedSubmanifold_sphere he).chartedSpace
  haveI := (isEmbeddedSubmanifold_sphere he).mbManifold
  (sphereAmbientAddition he).toLocalAddition rfl

/-- `Σ(p, w) = (p + w)/‖p + w‖`, where `w` is the ambient vector of the tangent vector. -/
theorem sphereLocalAddition_toFun (he : ‖e‖ = 1) :
    letI := (isEmbeddedSubmanifold_sphere he).chartedSpace
    haveI := (isEmbeddedSubmanifold_sphere he).mbManifold
    ∀ v : TangentBundle (ℝ ∙ e)ᗮ (Metric.sphere (0 : H) 1),
      v ∈ (sphereLocalAddition he).source ∧
      (((sphereLocalAddition he).toFun v : Metric.sphere (0 : H) 1) : H) =
        ‖(v.proj : H) + (isEmbeddedSubmanifold_sphere he).ambVec v‖⁻¹ •
          ((v.proj : H) + (isEmbeddedSubmanifold_sphere he).ambVec v) := by
  let _ := (isEmbeddedSubmanifold_sphere he).chartedSpace
  have _ := (isEmbeddedSubmanifold_sphere he).mbManifold
  intro v
  have hw := (isEmbeddedSubmanifold_sphere he).ambVec_mem_tangentSpace rfl v
  rw [tangentSpace_sphere he] at hw
  have hv : v ∈ (sphereAmbientAddition he).source :=
    add_ne_zero_of_inner (mem_sphere_zero_iff_norm.mp v.proj.2) hw
  exact ⟨hv, (sphereAmbientAddition he).toLocalAddition_toFun rfl hv⟩

/-- `θ = (π, Σ)` maps `TS` onto `{(p, q) : ⟪p, q⟫ > 0}`. -/
theorem mem_sphereLocalAddition_target (he : ‖e‖ = 1) :
    letI := (isEmbeddedSubmanifold_sphere he).chartedSpace
    haveI := (isEmbeddedSubmanifold_sphere he).mbManifold
    ∀ z : Metric.sphere (0 : H) 1 × Metric.sphere (0 : H) 1,
      z ∈ (sphereLocalAddition he).toOpenPartialHomeomorph.target ↔
        0 < ⟪(z.1 : H), (z.2 : H)⟫ :=
  fun _ ↦ Iff.rfl

/-- The local addition of the sphere is normalized. -/
theorem isNormalized_sphereLocalAddition (he : ‖e‖ = 1) :
    letI := (isEmbeddedSubmanifold_sphere he).chartedSpace
    haveI := (isEmbeddedSubmanifold_sphere he).mbManifold
    (sphereLocalAddition he).IsNormalized := by
  let _ := (isEmbeddedSubmanifold_sphere he).chartedSpace
  have _ := (isEmbeddedSubmanifold_sphere he).mbManifold
  refine (sphereAmbientAddition he).isNormalized_toLocalAddition rfl fun p w hw ↦ ?_
  rw [tangentSpace_sphere he p] at hw
  exact dMB_sigma (mem_sphere_zero_iff_norm.mp p.2) hw

end LocallyConvex.Manifolds
