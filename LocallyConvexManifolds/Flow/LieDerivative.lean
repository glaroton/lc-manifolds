/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.DifferentialForm.LieDerivative
public import LocallyConvexManifolds.DifferentialForm.Homotopy
public import LocallyConvexAnalysis.Calculus.CklMaps

/-!
# The Lie derivative along a local flow

On manifolds modeled on locally convex spaces vector fields need not have flows, which is why
the Lie derivative `L_X ω` is defined algebraically
(`LocallyConvexManifolds.DifferentialForm.LieDerivative`). When `X` does have a local flow `Fl`, we
prove H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups* (arXiv:2602.12362), Remark 3.6.17,
formula (3.36) (their Exercise 3.6.15):

`d/dt|_{t=0} ((Fl_t)* ω)ₓ(v₁, …, vₙ) = (L_X ω)ₓ(v₁, …, vₙ)`.

## Main results

* `IsLocalForm.hasDirDerivAt_flow`: the formula in a chart, for a `C²` local flow
  `φ : ℝ × E → E` of `X : E → E`.
* `IsLocalFlow`: local flows of a smooth vector field on a manifold (compare GN,
  Definition 2.5.23), given as a hypothesis: an open `Ω ⊆ ℝ × M` containing `{0} × M`, a `C²`
  map `Fl : Ω → M` with `Fl(0, x) = x` whose curves `t ↦ Fl(t, x)` are integral curves of `X`.
* `IsLocalFlow.hasDirDerivAt_pullback`: (3.36), read in any chart around `x`.

## Implementation notes

* GN assume local `C¹`-flows. We assume `C²`: the proof differentiates `∂_v Fl(t, ·)` in `t`
  and exchanges the order of differentiation (`hasDirDerivAt_comm`, a Schwarz theorem without
  completeness), using `∂_t Fl = X ∘ Fl`. GN's hint goes through their Exercises 2.5.1 and
  2.4.9; we do not claim this argument is new.
* The pullback `(Fl_t)* ω` at `x` is written in a chart `i` around `x`: the vectors are pushed
  forward by the derivative of `i ∘ Fl_t ∘ i⁻¹` at `i x` and `ω` is evaluated at `Fl_t x` through
  its local representative in `i`. No pullback of forms along local diffeomorphisms is needed.
* No completeness is assumed.
-/

@[expose] public section

open Set Function Filter
open LocallyConvex.Analysis
open scoped Topology

noncomputable section

namespace LocallyConvex.Manifolds

universe u v

/-! ### The local formula -/

section Local

variable {E F : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {n : ℕ}

/-- **The Lie derivative along a local flow, in a chart** (the local form of Glöckner–Neeb,
(3.36)). Let `φ : ℝ × E → E` be `C²` on an open set `D`, with values in `U`, solving
`∂ₜφ(t, z) = X(φ(t, z))`, and with `φ(0, z) = z` near `y`. Then
`t ↦ ω(φ(t, y))(∂_z φ(t, y) v₁, …, ∂_z φ(t, y) vₙ)` has derivative `(L_X ω)(y)(v)` at `t = 0`. -/
theorem IsLocalForm.hasDirDerivAt_flow {ω : E × (Fin n → E) → F} {U : Set E}
    (hω : IsLocalForm n ω U) (hU : IsOpen U) {X : E → E} (hX : ContDiffMBOn 1 X U)
    {φ : ℝ × E → E} {D : Set (ℝ × E)} (hD : IsOpen D) (hφ : ContDiffMBOn 2 φ D)
    (hφU : MapsTo φ D U) (hφt : ∀ z ∈ D, dMB φ (z, (1, 0)) = X (φ z)) {y : E}
    (hy : ((0 : ℝ), y) ∈ D) (hφ0 : ∀ᶠ z in 𝓝 y, φ (0, z) = z) (v : Fin n → E) :
    HasDirDerivAt (fun t : ℝ ↦ ω (φ (t, y), fun k ↦ dMB φ ((t, y), (0, v k)))) 0 1
      (lieLoc X ω (y, v)) := by
  classical
  have hφ1 : ContDiffMBOn (1 + 1) φ D := hφ
  have hφy : φ (0, y) = y := hφ0.self_of_nhds
  have hyU : y ∈ U := hφy ▸ hφU hy
  -- `∂_{(0, w)} φ (0, y) = w`
  have hd0 : ∀ w : E, dMB φ (((0 : ℝ), y), (0, w)) = w := fun w ↦ by
    refine HasDirDerivAt.dMB_eq ?_
    have hc : Tendsto (fun s : ℝ ↦ y + s • w) (𝓝[≠] 0) (𝓝 y) := by
      have : Continuous fun s : ℝ ↦ y + s • w := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hc hφ0, self_mem_nhdsWithin] with s hs hs0
    simp only [Prod.mk_add_mk, Prod.smul_mk, smul_zero, add_zero, mem_preimage] at hs ⊢
    rw [hs, hφy, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  -- the derivative of `t ↦ ∂_{(0, w)} φ (t, y)` at `0` is `dX(y) w`
  have hW : ∀ w : E, HasDirDerivAt (fun t : ℝ ↦ dMB φ ((t, y), (0, w))) 0 1 (dMB X (y, w)) := by
    intro w
    have hdX : ContinuousOn (dMB X) (U ×ˢ univ) := hX.2.2
    have hdφ : ContinuousOn (dMB φ) (D ×ˢ univ) := (hφ1.2.2 : ContDiffMBOn 1 _ _).continuousOn
    have hc := hasDirDerivAt_comm (g := φ) (A := fun z ↦ dMB φ (z, (0, w)))
      (B := fun z ↦ X (φ z)) (M := fun z ↦ dMB X (φ z, dMB φ (z, (0, w)))) hD
      (a := (0, w)) (b := (1, 0))
      (fun z hz ↦ hφ1.hasDirDerivAt hz _)
      (fun z hz ↦ (hφt z hz) ▸ hφ1.hasDirDerivAt hz _)
      (hX.continuousOn.comp hφ.continuousOn hφU)
      (fun z hz ↦ hX.hasDirDerivAt_comp hU (hφ1.hasDirDerivAt hz _) (hφU hz))
      (hdX.comp (hφ.continuousOn.prodMk (hdφ.comp (continuousOn_id.prodMk continuousOn_const)
        fun z hz ↦ ⟨hz, mem_univ _⟩)) fun z hz ↦ ⟨hφU hz, mem_univ _⟩) hy
    have := hasDirDerivAt_line hc
    rwa [hφy, hd0] at this
  have hc : HasDirDerivAt (fun t : ℝ ↦ φ (t, y)) 0 1 (X y) := by
    have := hasDirDerivAt_line (hφ1.hasDirDerivAt hy (1, 0))
    rwa [hφt _ hy, hφy] at this
  have hΨ : HasDirDerivAt (fun t : ℝ ↦ (φ (t, y), fun k ↦ dMB φ ((t, y), (0, v k)))) 0 1
      (X y, fun k ↦ dMB X (y, v k)) :=
    hc.prodMk (hasDirDerivAt_pi.mpr fun k ↦ hW (v k))
  have hη1 : ContDiffMBOn 1 ω (U ×ˢ univ) := hω.smooth 1
  have hV' : IsOpen (U ×ˢ (univ : Set (Fin n → E))) := hU.prod isOpen_univ
  have hΨ0 : (φ ((0 : ℝ), y), fun k ↦ dMB φ (((0 : ℝ), y), (0, v k))) = (y, v) := by
    simp only [hφy, hd0]
  have hchain := hη1.hasDirDerivAt_comp hV' hΨ (by rw [hΨ0]; exact ⟨hyU, mem_univ _⟩)
  rw [hΨ0] at hchain
  have hsplit : dMB ω ((y, v), (X y, fun k ↦ dMB X (y, v k))) =
      dMB ω ((y, v), (X y, 0)) + dMB ω ((y, v), (0, fun k ↦ dMB X (y, v k))) := by
    rw [← hη1.dMB_add hV' ⟨hyU, mem_univ _⟩]; simp
  have h0 : ContinuousOn ω (U ×ˢ univ) := hω.smooth 0
  have hcont : Continuous fun w' : Fin n → E ↦ ω (y, w') :=
    continuousOn_univ.mp <| h0.comp (Continuous.continuousOn (by fun_prop))
      fun _ _ ↦ ⟨hyU, mem_univ _⟩
  have hmult := hasDirDerivAt_of_multilinear hcont
    (fun w' k a b ↦ hω.map_update_add hyU w' k a b)
    (fun w' k c a ↦ hω.map_update_smul hyU w' k c a) v (fun k ↦ dMB X (y, v k))
  have hval : lieLoc X ω (y, v) = dMB ω ((y, v), (X y, fun k ↦ dMB X (y, v k))) := by
    rw [hsplit, dMB_slice, dMB_slice₂, hmult.dMB_eq]
    rfl
  rw [hval]
  exact hchain

end Local

/-! ### Local flows on manifolds -/

section Manifold

variable {E : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]
  {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] {n : ℕ}

/-- `Fl : Ω → M` is a **local flow** of the vector field `X` (compare Glöckner–Neeb,
Definition 2.5.23): `Ω ⊆ ℝ × M` is an open set containing `{0} × M`, `Fl` is `C²` on `Ω`,
`Fl(0, x) = x`, and each curve `t ↦ Fl(t, x)` is an integral curve of `X`, read in any chart. -/
structure IsLocalFlow (X : SmoothVectorField E M) (Fl : ℝ × M → M) (Ω : Set (ℝ × M)) :
    Prop where
  isOpen : IsOpen Ω
  zero_mem : ∀ x, ((0 : ℝ), x) ∈ Ω
  map_zero : ∀ x, Fl (0, x) = x
  contMDiffMBOn : ContMDiffMBOn (E := ModelProd ℝ E) (F := E) 2 Fl Ω
  hasDirDerivAt : ∀ p ∈ Ω, ∀ i : atlas E M, Fl p ∈ i.1.source →
    HasDirDerivAt (fun s : ℝ ↦ i.1 (Fl (s, p.2))) p.1 1 (X.rep i (i.1 (Fl p)))

/-- **The Lie derivative along a local flow** (Glöckner–Neeb, Remark 3.6.17, (3.36), and
Exercise 3.6.15): if `X` has a local flow `Fl`, then in every chart `i` around `x`,
`d/dt|₀ ω(Fl_t x)(T_x Fl_t v₁, …, T_x Fl_t vₙ) = (L_X ω)ₓ(v₁, …, vₙ)`, where `T_x Fl_t` is read as
the derivative of `i ∘ Fl_t ∘ i⁻¹` at `i x`. That is, `d/dt|₀ (Fl_t* ω)ₓ = (L_X ω)ₓ`. -/
theorem IsLocalFlow.hasDirDerivAt_pullback {X : SmoothVectorField E M} {Fl : ℝ × M → M}
    {Ω : Set (ℝ × M)} (hFl : IsLocalFlow X Fl Ω) (ω : DifferentialForm E M F n) (i : atlas E M)
    {x : M} (hx : x ∈ i.1.source) (v : Fin n → E) :
    HasDirDerivAt (fun t : ℝ ↦ ω.localRep i (i.1 (Fl (t, x)),
        fun k ↦ dMB (fun z ↦ i.1 (Fl (t, i.1.symm z))) (i.1 x, v k))) 0 1
      ((DifferentialForm.lieDeriv X ω).localRep i (i.1 x, v)) := by
  set φ : ℝ × E → E := fun q ↦ i.1 (Fl (q.1, i.1.symm q.2))
  set D := chartDomain Fl Ω (prodAtlas i).1 i.1
  have hD : IsOpen D := isOpen_chartDomain hFl.isOpen hFl.contMDiffMBOn.continuousOn _ _
  have hφ : ContDiffMBOn 2 φ D :=
    hFl.contMDiffMBOn.contDiffMBOn_chart hFl.isOpen (prodAtlas i).2 i.2
  have hmem : ∀ q ∈ D, (q.1, i.1.symm q.2) ∈ Ω ∧ Fl (q.1, i.1.symm q.2) ∈ i.1.source :=
    fun q hq ↦ ⟨hq.2.1, hq.2.2⟩
  have hφU : MapsTo φ D i.1.target := fun q hq ↦ i.1.map_source (hmem q hq).2
  have hφt : ∀ q ∈ D, dMB φ (q, (1, 0)) = X.rep i (φ q) := fun q hq ↦
    (hasDirDerivAt_of_line (hFl.hasDirDerivAt _ (hmem q hq).1 i (hmem q hq).2)).dMB_eq
  have hix : i.1 x ∈ i.1.target := i.1.map_source hx
  have hy : ((0 : ℝ), i.1 x) ∈ D := by
    refine ⟨?_, ?_, ?_⟩
    · rw [prodAtlas_target]; exact ⟨mem_univ _, hix⟩
    · change ((0 : ℝ), i.1.symm (i.1 x)) ∈ Ω
      rw [i.1.left_inv hx]; exact hFl.zero_mem x
    · change Fl ((0 : ℝ), i.1.symm (i.1 x)) ∈ i.1.source
      rw [i.1.left_inv hx, hFl.map_zero]; exact hx
  have hφ0 : ∀ᶠ z in 𝓝 (i.1 x), φ (0, z) = z :=
    Filter.eventually_of_mem (i.1.open_target.mem_nhds hix) fun z hz ↦ by
      change i.1 (Fl (0, i.1.symm z)) = z
      rw [hFl.map_zero, i.1.right_inv hz]
  have h := (ω.isLocalForm_localRep i).hasDirDerivAt_flow i.1.open_target
    ((X.smoothMBOn_localRep i) 1) hD hφ hφU hφt hy hφ0 v
  rw [← DifferentialForm.localRep_lieDeriv X ω i hix] at h
  convert h using 2 with t
  simp only [φ, i.1.left_inv hx, dMB_slice₂]

end Manifold

end LocallyConvex.Manifolds
