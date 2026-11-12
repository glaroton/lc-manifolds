/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.MappingSpace.Ck

/-!
# Normalized local additions

We prove [GN26, Remark 3.8.16]: every local addition `Σ` on a manifold `N` can be normalized. With
`α_y = T_{0_y}(Σ|_{T_y N}) ∈ GL(T_y N)`, the map `F : TN → TN`, `F(v) = α_{π v}⁻¹ v`, is a
diffeomorphism preserving fibres, and `Σ ∘ F` is a normalized local addition
(`LocalAddition.IsNormalized`, [GN26, (3.55)]).

## Main results

* `LocalAddition.alpha`, `LocalAddition.beta`: `α_y` and its inverse, in the preferred chart at
  `y`; `LocalAddition.alpha_beta`, `LocalAddition.beta_alpha`.
* `smoothMBM_of_coordAt`: a fibre-preserving map of `TN` that is given in all tangent charts by
  `(z, w) ↦ (z, g(z, w))` with `g` smooth is smooth.
* `LocalAddition.normEquiv`: the homeomorphism `F : v ↦ α_{π v}⁻¹ v` of `TN`, smooth in both
  directions (`smoothMBM_normMap`, `smoothMBM_normMapInv`).
* `LocalAddition.normalize`, `LocalAddition.normalize_toFun`,
  `LocalAddition.isNormalized_normalize`: the normalized local addition `Σ ∘ F`.

## Implementation notes

* Glöckner–Neeb argue that `θ = (π, Σ)` restricts to diffeomorphisms of fibres
  `T_y N ∩ Ω → ({y} × N) ∩ θ(Ω)`, so that `α_y` is invertible, and then state that `F` is smooth.
  Here everything is computed in charts: in the preferred chart `φ` at `y`, the fibre map
  `v ↦ φ(Σ(y, v))` has the local inverse `z ↦ (θ⁻¹)(φ⁻¹(φ y), φ⁻¹ z)` (read in the tangent chart),
  so `α_y` is invertible with inverse `β_y` by the chain rule. In an arbitrary tangent chart `ψ`,
  `α_y` and `β_y` are conjugated by the derivative of the transition map, and depend smoothly on
  the base point because they are partial derivatives of smooth chart representatives of `θ` and
  `θ⁻¹`; this gives the smoothness of `F` and `F⁻¹`. We do not claim this argument is new.
* No completeness or local convexity beyond the standing assumptions on the model is used.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function TopologicalSpace
open scoped Topology
open LocallyConvex.Analysis

noncomputable section

universe u

namespace LocallyConvex.Manifolds

section Normalize

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [MBManifold E N]
  (A : LocalAddition E N)

namespace LocalAddition

/-- `θ⁻¹(y, y) = 0_y`. -/
theorem symm_self (y : N) :
    A.toOpenPartialHomeomorph.symm (y, y) = (⟨y, 0⟩ : TangentBundle E N) := by
  have h := A.toOpenPartialHomeomorph.left_inv (A.zero_mem y)
  rw [A.toOpenPartialHomeomorph_apply (A.zero_mem y), A.toFun_zero] at h
  exact h

/-- Near `0`, `v ↦ φ_y(Σ(y, v))` (`φ_y` the preferred chart at `y`) is smooth. -/
theorem exists_smoothMBOn_chart_toFun (y : N) :
    ∃ O : Set E, IsOpen O ∧ (0 : E) ∈ O ∧
      SmoothMBOn (fun w : E ↦ chartAt E y (A.toFun ⟨y, w⟩)) O := by
  let i : atlas E N := ⟨chartAt E y, chart_mem_atlas E y⟩
  have hy : y ∈ i.1.source := _root_.mem_chart_source E y
  set O := (fun w : E ↦ ((i.1 y, w) : E × E)) ⁻¹' A.invLocalDom i i
  have hO : IsOpen O := (A.isOpen_invLocalDom i i).preimage (by fun_prop)
  have hsymm : ∀ w : E, (tangentChart i i.1).symm (i.1 y, w) = (⟨y, w⟩ : TangentBundle E N) :=
    fun w ↦ by
      have h := tangentChart_symm_coordAt i (v := (⟨y, w⟩ : TangentBundle E N)) hy
      rwa [show coordAt i (⟨y, w⟩ : TangentBundle E N) = w from coordAt_chartAt y w] at h
  have h0 : (0 : E) ∈ O := by
    have h := (A.invLocal_spec i i (v := (⟨y, 0⟩ : TangentBundle E N)) hy (A.zero_mem y)
      (by rw [A.toFun_zero]; exact hy)).1
    rwa [show coordAt i (⟨y, 0⟩ : TangentBundle E N) = 0 from coordAt_chartAt y 0] at h
  refine ⟨O, hO, h0, fun k ↦ ?_⟩
  have hc := ContDiffMBOn.comp (g := A.invLocal i i) hO (A.isOpen_invLocalDom i i)
    (A.smoothMBOn_invLocal i i k)
    ((contDiffMBOn_const_add_clm ((i.1 y, 0) : E × E) (ContinuousLinearMap.inr ℝ E E) k univ).mono
      (subset_univ O)) fun w hw ↦ by
        simp only [ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add]
        exact hw
  refine ContDiffMBOn.congr_of_isOpen hO (fun w _ ↦ ?_) hc
  simp only [Function.comp_apply, ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero,
    zero_add, invLocal, hsymm]
  rfl

/-- The preferred chart at `y`, as an element of the atlas. -/
abbrev chartIdx (y : N) : atlas E N := ⟨chartAt E y, chart_mem_atlas E y⟩

/-- The local addition on the fiber over `y`, in the preferred chart: `v ↦ φ_y(Σ(y, v))`. -/
def fibreMap (y : N) (v : E) : E := chartAt E y (A.toFun ⟨y, v⟩)

/-- The inverse of `fibreMap`: `z ↦ θ⁻¹(y, φ_y⁻¹ z)`, in the fiber coordinates of `φ_y`. -/
def fibreInv (y : N) (z : E) : E := A.chartLocal (chartIdx y) (chartIdx y) (z, chartAt E y y)

/-- The domain of `fibreMap`. -/
def fibreMapDom (y : N) : Set E :=
  (fun w : E ↦ ((chartAt E y y, w) : E × E)) ⁻¹' A.invLocalDom (chartIdx y) (chartIdx y)

/-- The domain of `fibreInv`. -/
def fibreInvDom (y : N) : Set E :=
  (fun z : E ↦ ((z, chartAt E y y) : E × E)) ⁻¹' A.chartLocalDom (chartIdx y) (chartIdx y)

/-- The domain of the fibre map is open. -/
theorem isOpen_fibreMapDom (y : N) : IsOpen (A.fibreMapDom y) :=
  (A.isOpen_invLocalDom _ _).preimage (by fun_prop)

/-- The domain of the local inverse of the fibre map is open. -/
theorem isOpen_fibreInvDom (y : N) : IsOpen (A.fibreInvDom y) :=
  (A.isOpen_chartLocalDom _ _).preimage (by fun_prop)

/-- `(φ_y × id)⁻¹(φ_y y, w) = ⟨y, w⟩` in the tangent bundle. -/
theorem tangentChart_symm_chartAt (y : N) (w : E) :
    (tangentChart (chartIdx y) (chartAt E y)).symm (chartAt E y y, w) =
      (⟨y, w⟩ : TangentBundle E N) := by
  have h := tangentChart_symm_coordAt (chartIdx y) (v := (⟨y, w⟩ : TangentBundle E N))
    (_root_.mem_chart_source E y)
  rwa [show coordAt (chartIdx y) (⟨y, w⟩ : TangentBundle E N) = w from coordAt_chartAt y w] at h

/-- Membership in the domain of `fibreMap`. -/
theorem mem_fibreMapDom {y : N} {w : E} (hw : w ∈ A.fibreMapDom y) :
    (⟨y, w⟩ : TangentBundle E N) ∈ A.source ∧ A.toFun ⟨y, w⟩ ∈ (chartAt E y).source := by
  have h : (chartAt E y y, w) ∈ A.invLocalDom (chartIdx y) (chartIdx y) := hw
  obtain ⟨⟨-, h1⟩, h2⟩ := h
  change (tangentChart (chartIdx y) (chartAt E y)).symm _ ∈ A.source at h1
  change A.toFun ((tangentChart (chartIdx y) (chartAt E y)).symm _) ∈ (chartAt E y).source at h2
  rw [tangentChart_symm_chartAt] at h1 h2
  exact ⟨h1, h2⟩

/-- `fibreMap` is smooth on its domain, which contains `0`. -/
theorem smoothMBOn_fibreMap (y : N) : SmoothMBOn (A.fibreMap y) (A.fibreMapDom y) := fun k ↦ by
  have hc := ContDiffMBOn.comp (g := A.invLocal (chartIdx y) (chartIdx y)) (A.isOpen_fibreMapDom y)
    (A.isOpen_invLocalDom _ _) (A.smoothMBOn_invLocal _ _ k)
    ((contDiffMBOn_const_add_clm ((chartAt E y y, 0) : E × E) (ContinuousLinearMap.inr ℝ E E) k
      univ).mono (subset_univ _)) fun w hw ↦ by
        simp only [ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add]
        exact hw
  refine ContDiffMBOn.congr_of_isOpen (A.isOpen_fibreMapDom y) (fun w _ ↦ ?_) hc
  simp only [Function.comp_apply, ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero,
    zero_add, invLocal]
  rw [tangentChart_symm_chartAt]
  rfl

/-- The zero vector lies in the domain of the fibre map. -/
theorem zero_mem_fibreMapDom (y : N) : (0 : E) ∈ A.fibreMapDom y := by
  have h := (A.invLocal_spec (chartIdx y) (chartIdx y) (v := (⟨y, 0⟩ : TangentBundle E N))
    (_root_.mem_chart_source E y) (A.zero_mem y)
    (by rw [A.toFun_zero]; exact _root_.mem_chart_source E y)).1
  rwa [show coordAt (chartIdx y) (⟨y, 0⟩ : TangentBundle E N) = 0 from coordAt_chartAt y 0] at h

/-- `fibreInv` is smooth on its domain. -/
theorem smoothMBOn_fibreInv (y : N) : SmoothMBOn (A.fibreInv y) (A.fibreInvDom y) := fun k ↦
  ContDiffMBOn.comp (g := A.chartLocal (chartIdx y) (chartIdx y)) (A.isOpen_fibreInvDom y)
    (A.isOpen_chartLocalDom _ _) (A.smoothMBOn_chartLocal _ _ k)
    ((((ContinuousLinearMap.id ℝ E).prod 0).contDiffMBOn k univ |>.add isOpen_univ
      (contDiffMBOn_const k ((0 : E), chartAt E y y) univ)).mono (subset_univ _) |>.congr_of_isOpen
      (A.isOpen_fibreInvDom y) fun z _ ↦ by simp) fun z hz ↦ hz

/-- **The value of `fibreInv`**: for `z` in the target of `φ_y` with `(y, φ_y⁻¹ z)` in the range of
`θ`, `fibreInv y z` is the fiber coordinate of `θ⁻¹(y, φ_y⁻¹ z)`. -/
theorem fibreInv_spec {y : N} {z : E} (hz : z ∈ (chartAt E y).target)
    (hθ : (y, (chartAt E y).symm z) ∈ A.toOpenPartialHomeomorph.target) :
    z ∈ A.fibreInvDom y ∧
      A.fibreInv y z = (A.toOpenPartialHomeomorph.symm (y, (chartAt E y).symm z)).vec := by
  have h := A.chartLocal_spec (chartIdx y) (chartIdx y) ((chartAt E y).map_target hz)
    (_root_.mem_chart_source E y) hθ
  rw [(chartAt E y).right_inv hz] at h
  refine ⟨h.1, h.2.trans ?_⟩
  exact coordAt_chartAt_of_proj_eq (A.proj_symm hθ)

/-- `(y, y)` is in the range of `θ`. -/
theorem self_mem_target (y : N) : (y, y) ∈ A.toOpenPartialHomeomorph.target := by
  have h := A.toOpenPartialHomeomorph.map_source (A.zero_mem y)
  rwa [A.toOpenPartialHomeomorph_apply (A.zero_mem y), A.toFun_zero] at h

/-- `fibreInv y (φ_y y) = 0`, and `φ_y y` lies in the domain of `fibreInv`. -/
theorem fibreInv_self (y : N) :
    chartAt E y y ∈ A.fibreInvDom y ∧ A.fibreInv y (chartAt E y y) = 0 := by
  have hz := (chartAt E y).map_source (_root_.mem_chart_source E y)
  have hθ : (y, (chartAt E y).symm (chartAt E y y)) ∈ A.toOpenPartialHomeomorph.target := by
    rw [(chartAt E y).left_inv (_root_.mem_chart_source E y)]
    exact A.self_mem_target y
  refine ⟨(A.fibreInv_spec hz hθ).1, (A.fibreInv_spec hz hθ).2.trans ?_⟩
  rw [(chartAt E y).left_inv (_root_.mem_chart_source E y), A.symm_self]
  rfl

/-- `fibreMap y ∘ fibreInv y = id` where `fibreInv` is given by `θ⁻¹`. -/
theorem fibreMap_fibreInv {y : N} {z : E} (hz : z ∈ (chartAt E y).target)
    (hθ : (y, (chartAt E y).symm z) ∈ A.toOpenPartialHomeomorph.target) :
    A.fibreMap y (A.fibreInv y z) = z := by
  rw [(A.fibreInv_spec hz hθ).2, fibreMap, A.mk_vec_symm hθ]
  change chartAt E y (A.toOpenPartialHomeomorph (A.toOpenPartialHomeomorph.symm _)).2 = z
  rw [A.toOpenPartialHomeomorph.right_inv hθ]
  exact (chartAt E y).right_inv hz

/-- `fibreInv y ∘ fibreMap y = id` on the domain of `fibreMap`. -/
theorem fibreInv_fibreMap {y : N} {v : E} (hv : v ∈ A.fibreMapDom y) :
    A.fibreMap y v ∈ A.fibreInvDom y ∧ A.fibreInv y (A.fibreMap y v) = v := by
  obtain ⟨hvA, hvc⟩ := A.mem_fibreMapDom hv
  have hz : A.fibreMap y v ∈ (chartAt E y).target := (chartAt E y).map_source hvc
  have hsymm : (chartAt E y).symm (A.fibreMap y v) = A.toFun ⟨y, v⟩ := (chartAt E y).left_inv hvc
  have hθ : (y, (chartAt E y).symm (A.fibreMap y v)) ∈ A.toOpenPartialHomeomorph.target := by
    rw [hsymm, ← show ((⟨y, v⟩ : TangentBundle E N).proj, A.toFun ⟨y, v⟩) = (y, A.toFun ⟨y, v⟩)
      from rfl, ← A.toOpenPartialHomeomorph_apply hvA]
    exact A.toOpenPartialHomeomorph.map_source hvA
  refine ⟨(A.fibreInv_spec hz hθ).1, (A.fibreInv_spec hz hθ).2.trans ?_⟩
  rw [hsymm, ← show ((⟨y, v⟩ : TangentBundle E N).proj, A.toFun ⟨y, v⟩) = (y, A.toFun ⟨y, v⟩)
    from rfl, ← A.toOpenPartialHomeomorph_apply hvA, A.toOpenPartialHomeomorph.left_inv hvA]
  rfl

/-- `α_y = T_0(Σ|_{T_y N})` in the preferred chart at `y`: `w ↦ d(fibreMap y)(0, w)`. -/
def alpha (y : N) : E →L[ℝ] E where
  toFun w := dMB (A.fibreMap y) (0, w)
  map_add' := ((A.smoothMBOn_fibreMap y) 1).dMB_add (A.isOpen_fibreMapDom y)
    (A.zero_mem_fibreMapDom y)
  map_smul' := ((A.smoothMBOn_fibreMap y) 1).dMB_smul (A.zero_mem_fibreMapDom y)
  cont := ((A.smoothMBOn_fibreMap y) 1).continuous_dMB (A.zero_mem_fibreMapDom y)

/-- `β_y = α_y⁻¹`, the derivative of `fibreInv y` at `φ_y y`. -/
def beta (y : N) : E →L[ℝ] E where
  toFun w := dMB (A.fibreInv y) (chartAt E y y, w)
  map_add' := ((A.smoothMBOn_fibreInv y) 1).dMB_add (A.isOpen_fibreInvDom y)
    (A.fibreInv_self y).1
  map_smul' := ((A.smoothMBOn_fibreInv y) 1).dMB_smul (A.fibreInv_self y).1
  cont := ((A.smoothMBOn_fibreInv y) 1).continuous_dMB (A.fibreInv_self y).1

/-- `α_y ∘ β_y = id`. -/
theorem alpha_beta (y : N) (w : E) : A.alpha y (A.beta y w) = w := by
  set c := chartAt E y
  set W₁ := c.target ∩ c.symm ⁻¹' ((fun q : N ↦ (y, q)) ⁻¹' A.toOpenPartialHomeomorph.target)
  have hW₁ : IsOpen W₁ := c.isOpen_inter_preimage_symm
    (A.toOpenPartialHomeomorph.open_target.preimage (by fun_prop))
  have hK := (A.smoothMBOn_fibreInv y) 1
  set U' := (A.fibreInvDom y ∩ W₁) ∩ A.fibreInv y ⁻¹' A.fibreMapDom y
  have hU' : IsOpen U' := (hK.continuousOn.mono inter_subset_left).isOpen_inter_preimage
    ((A.isOpen_fibreInvDom y).inter hW₁) (A.isOpen_fibreMapDom y)
  have hcy : c y ∈ U' := by
    refine ⟨⟨(A.fibreInv_self y).1, c.map_source (_root_.mem_chart_source E y), ?_⟩, ?_⟩
    · change (y, c.symm (c y)) ∈ A.toOpenPartialHomeomorph.target
      rw [c.left_inv (_root_.mem_chart_source E y)]
      exact A.self_mem_target y
    · change A.fibreInv y (c y) ∈ A.fibreMapDom y
      rw [(A.fibreInv_self y).2]
      exact A.zero_mem_fibreMapDom y
  have hc := ContDiffMBOn.dMB_comp (A.isOpen_fibreMapDom y) ((A.smoothMBOn_fibreMap y) 1)
    (hK.mono fun (z : E) (hz : z ∈ U') ↦ hz.1.1) (fun (z : E) (hz : z ∈ U') ↦ hz.2) hcy w
  have hev : (A.fibreMap y ∘ A.fibreInv y) =ᶠ[𝓝 (c y)] id :=
    Filter.eventually_of_mem (hU'.mem_nhds hcy) fun z hz ↦ A.fibreMap_fibreInv hz.1.2.1 hz.1.2.2
  rw [dMB_congr_of_eventuallyEq hev, (A.fibreInv_self y).2] at hc
  rw [show dMB id (c y, w) = w from ((ContinuousLinearMap.id ℝ E).hasDirDerivAt _ w).dMB_eq]
    at hc
  exact hc.symm

/-- `β_y ∘ α_y = id`. -/
theorem beta_alpha (y : N) (w : E) : A.beta y (A.alpha y w) = w := by
  have hG := (A.smoothMBOn_fibreMap y) 1
  set U' := A.fibreMapDom y ∩ A.fibreMap y ⁻¹' A.fibreInvDom y
  have hU' : IsOpen U' := hG.continuousOn.isOpen_inter_preimage (A.isOpen_fibreMapDom y)
    (A.isOpen_fibreInvDom y)
  have h0 : (0 : E) ∈ U' := ⟨A.zero_mem_fibreMapDom y,
    (A.fibreInv_fibreMap (A.zero_mem_fibreMapDom y)).1⟩
  have hc := ContDiffMBOn.dMB_comp (A.isOpen_fibreInvDom y) ((A.smoothMBOn_fibreInv y) 1)
    (hG.mono fun (z : E) (hz : z ∈ U') ↦ hz.1) (fun (z : E) (hz : z ∈ U') ↦ hz.2) h0 w
  have hev : (A.fibreInv y ∘ A.fibreMap y) =ᶠ[𝓝 0] id :=
    Filter.eventually_of_mem (hU'.mem_nhds h0) fun v hv ↦ (A.fibreInv_fibreMap hv.1).2
  have hG0 : A.fibreMap y 0 = chartAt E y y := congrArg (chartAt E y) (A.toFun_zero y)
  rw [dMB_congr_of_eventuallyEq hev, hG0] at hc
  rw [show dMB id ((0 : E), w) = w from ((ContinuousLinearMap.id ℝ E).hasDirDerivAt _ w).dMB_eq]
    at hc
  exact hc.symm

omit [T2Space E] [LocallyConvexSpace ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] in
/-- A derivative of a map of pairs in a direction `(w, 0)` is the derivative of the first slice. -/
theorem dMB_slice_fst {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    (f : E × E → F) (a b w : E) : dMB f ((a, b), (w, 0)) = dMB (fun z ↦ f (z, b)) (a, w) := by
  unfold dMB
  congr 1
  funext t
  simp

omit [T2Space E] [LocallyConvexSpace ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] in
/-- A derivative of a map of pairs in a direction `(0, w)` is the derivative of the second
slice. -/
theorem dMB_slice_snd {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    (f : E × E → F) (a b w : E) : dMB f ((a, b), (0, w)) = dMB (fun u ↦ f (a, u)) (b, w) := by
  unfold dMB
  congr 1
  funext t
  simp

/-- The change of tangent coordinates at `y`, as a continuous linear map. -/
def tcc (i j : atlas E N) {y : N} (hy : y ∈ i.1.source ∩ j.1.source) : E →L[ℝ] E where
  toFun := tangentCoordChange i j y
  map_add' := tangentCoordChange_map_add i j hy
  map_smul' := tangentCoordChange_map_smul i j hy
  cont := continuous_tangentCoordChange i j hy

/-- `coordAt i ⟨y, w⟩ = tangentCoordChange (chartAt y) i y w`. -/
theorem coordAt_mk (i : atlas E N) (y : N) (w : E) :
    coordAt i (⟨y, w⟩ : TangentBundle E N) = tangentCoordChange (chartIdx y) i y w :=
  rfl

/-- `coordAt i (θ⁻¹(p, q))`, for the fibre coordinate in the preferred chart at `p`. -/
theorem coordAt_symm {i : atlas E N} {p q : N}
    (hpq : (p, q) ∈ A.toOpenPartialHomeomorph.target) :
    coordAt i (A.toOpenPartialHomeomorph.symm (p, q)) =
      tangentCoordChange (chartIdx p) i p (A.toOpenPartialHomeomorph.symm (p, q)).vec := by
  rw [← A.mk_vec_symm hpq]
  rfl

/-- **`β` in an arbitrary chart**: in the chart `i`, `β_y` is the derivative of
`z ↦ θ⁻¹(i⁻¹ a, i⁻¹ z)` (fiber coordinates in `i`) at `z = a = i y`. -/
theorem coordAt_beta (i : atlas E N) {y : N} (hy : y ∈ i.1.source) (w : E) :
    tangentCoordChange (chartIdx y) i y (A.beta y w) =
      dMB (A.chartLocal i i) ((i.1 y, i.1 y), (tangentCoordChange (chartIdx y) i y w, 0)) := by
  set c := chartIdx (E := E) y
  have hyc : y ∈ c.1.source := _root_.mem_chart_source E y
  rw [dMB_slice_fst]
  -- near `i y`, `z ↦ chartLocal i i (z, i y)` is `T ∘ fibreInv y ∘ (c ∘ i⁻¹)`
  set τ := c.1 ∘ i.1.symm
  set O := i.1.target ∩ i.1.symm ⁻¹' (c.1.source ∩ (fun q : N ↦ (y, q)) ⁻¹'
    A.toOpenPartialHomeomorph.target)
  have hO : IsOpen O := i.1.isOpen_inter_preimage_symm (c.1.open_source.inter
    (A.toOpenPartialHomeomorph.open_target.preimage (by fun_prop)))
  have hiy : i.1 y ∈ O := by
    refine ⟨i.1.map_source hy, ?_⟩
    rw [mem_preimage, i.1.left_inv hy]
    exact ⟨hyc, A.self_mem_target y⟩
  set T := tcc c i ⟨hyc, hy⟩
  have hev : (fun z ↦ A.chartLocal i i (z, i.1 y)) =ᶠ[𝓝 (i.1 y)]
      (fun z ↦ T (A.fibreInv y (τ z))) := Filter.eventually_of_mem (hO.mem_nhds hiy) fun z hz ↦ by
    have hq : i.1.symm z ∈ i.1.source := i.1.map_target hz.1
    have h := (A.chartLocal_spec i i hq hy hz.2.2).2
    rw [i.1.right_inv hz.1] at h
    change A.chartLocal i i (z, i.1 y) = T (A.fibreInv y (τ z))
    rw [h, A.coordAt_symm hz.2.2]
    have hzc : τ z ∈ c.1.target := c.1.map_source hz.2.1
    have hθ : (y, c.1.symm (τ z)) ∈ A.toOpenPartialHomeomorph.target := by
      change (y, c.1.symm (c.1 (i.1.symm z))) ∈ _
      rw [c.1.left_inv hz.2.1]
      exact hz.2.2
    rw [(A.fibreInv_spec hzc hθ).2]
    change _ = tangentCoordChange c i y _
    have e : c.1.symm (τ z) = i.1.symm z := c.1.left_inv hz.2.1
    rw [e]
  rw [dMB_congr_of_eventuallyEq hev]
  have hτ : HasDirDerivAt τ (i.1 y) (tangentCoordChange c i y w)
      (tangentCoordChange i c y (tangentCoordChange c i y w)) :=
    ((smoothMBOn_transition' i c) 1).hasDirDerivAt
      (⟨i.1.map_source hy, by rw [mem_preimage, i.1.left_inv hy]; exact hyc⟩ :
        i.1 y ∈ i.1.target ∩ i.1.symm ⁻¹' c.1.source) _
  have hτy : τ (i.1 y) = c.1 y := by
    change c.1 (i.1.symm (i.1 y)) = _
    rw [i.1.left_inv hy]
  have hK := ContDiffMBOn.hasDirDerivAt_comp (A.isOpen_fibreInvDom y) ((A.smoothMBOn_fibreInv y) 1)
    hτ (by rw [hτy]; exact (A.fibreInv_self y).1)
  have hT := hK.clm_comp_real T
  change _ = dMB (fun z ↦ T ((A.fibreInv y ∘ τ) z)) _
  rw [hT.dMB_eq, hτy, tangentCoordChange_comp c i c ⟨⟨hyc, hy⟩, hyc⟩, tangentCoordChange_self c hyc]
  rfl

/-- **`α` in an arbitrary chart**: in the chart `i`, `α_y` is the derivative of
`u ↦ i(Σ((tangentChart i i)⁻¹(a, u)))` at `u = 0`, `a = i y`. -/
theorem coordAt_alpha (i : atlas E N) {y : N} (hy : y ∈ i.1.source) (w : E) :
    tangentCoordChange (chartIdx y) i y (A.alpha y w) =
      dMB (A.invLocal i i) ((i.1 y, 0), (0, tangentCoordChange (chartIdx y) i y w)) := by
  set c := chartIdx (E := E) y
  have hyc : y ∈ c.1.source := _root_.mem_chart_source E y
  rw [dMB_slice_snd]
  set S := tcc i c ⟨hy, hyc⟩
  have hSc : ∀ u, tangentCoordChange c i y (S u) = u := fun u ↦
    (tangentCoordChange_comp i c i ⟨⟨hy, hyc⟩, hy⟩ u).trans (tangentCoordChange_self i hy u)
  have hsymm : ∀ u, (tangentChart i i.1).symm (i.1 y, u) = (⟨y, S u⟩ : TangentBundle E N) :=
    fun u ↦ by
      have h := tangentChart_symm_coordAt i (v := (⟨y, S u⟩ : TangentBundle E N)) hy
      rwa [show coordAt i (⟨y, S u⟩ : TangentBundle E N) = u from hSc u] at h
  set O := S ⁻¹' A.fibreMapDom y
  have hO : IsOpen O := (A.isOpen_fibreMapDom y).preimage S.continuous
  have h0 : (0 : E) ∈ O := by
    change S 0 ∈ A.fibreMapDom y
    rw [map_zero]
    exact A.zero_mem_fibreMapDom y
  set τ := i.1 ∘ c.1.symm
  have hev : (fun u ↦ A.invLocal i i (i.1 y, u)) =ᶠ[𝓝 0] (fun u ↦ τ (A.fibreMap y (S u))) :=
    Filter.eventually_of_mem (hO.mem_nhds h0) fun u hu ↦ by
      have hc := (A.mem_fibreMapDom hu).2
      change i.1 (A.toFun ((tangentChart i i.1).symm (i.1 y, u))) =
        i.1 (c.1.symm (c.1 (A.toFun ⟨y, S u⟩)))
      rw [hsymm, c.1.left_inv hc]
  rw [dMB_congr_of_eventuallyEq hev]
  have hG0 : A.fibreMap y 0 = c.1 y := congrArg (chartAt E y) (A.toFun_zero y)
  have h1 := ContDiffMBOn.hasDirDerivAt_comp (A.isOpen_fibreMapDom y)
    ((A.smoothMBOn_fibreMap y) 1) (S.hasDirDerivAt 0 (tangentCoordChange c i y w))
    (by rw [map_zero]; exact A.zero_mem_fibreMapDom y)
  have hdom : A.fibreMap y (S 0) ∈ c.1.target ∩ c.1.symm ⁻¹' i.1.source := by
    rw [map_zero, hG0]
    exact ⟨c.1.map_source hyc, by rw [mem_preimage, c.1.left_inv hyc]; exact hy⟩
  have h2 := ContDiffMBOn.hasDirDerivAt_comp (isOpen_transition_domain c i)
    ((smoothMBOn_transition' c i) 1) h1 hdom
  change _ = dMB (τ ∘ (A.fibreMap y ∘ S)) _
  have hcS : S (tangentCoordChange c i y w) = w :=
    (tangentCoordChange_comp c i c ⟨⟨hyc, hy⟩, hyc⟩ w).trans (tangentCoordChange_self c hyc w)
  rw [h2.dMB_eq, map_zero, hcS, show (A.fibreMap y ∘ S) 0 = c.1 y by
    simp only [Function.comp_apply, map_zero, hG0]]
  rfl

end LocalAddition

/-- **Fiber-preserving maps of `TN` given in tangent charts.** A map `F : TN → TN` over the
identity of `N` whose fiber coordinates in each chart `i` are `Φᵢ(i(π v), v in the chart i)`, with
`(a, w) ↦ (a, Φᵢ(a, w))` smooth on the target of `tangentChart i i`, is smooth. -/
theorem smoothMBM_of_coordAt {F : TangentBundle E N → TangentBundle E N}
    (hproj : ∀ v, (F v).proj = v.proj) (Φ : atlas E N → E × E → E)
    (hΦ : ∀ i, SmoothMBOn (fun q : E × E ↦ (q.1, Φ i q)) (tangentChart i i.1).target)
    (hF : ∀ i v, v.proj ∈ i.1.source → coordAt i (F v) = Φ i (i.1 v.proj, coordAt i v)) :
    SmoothMBM (E × E) (E × E) F := by
  -- in the chart `tangentChart i i`, `F` reads `q ↦ (q.1, Φᵢ q)`
  have hrep : ∀ (i : atlas E N) (q : E × E), q ∈ (tangentChart i i.1).target →
      tangentChart i i.1 (F ((tangentChart i i.1).symm q)) = (q.1, Φ i q) := fun i q hq ↦ by
    set T := tangentChart i i.1
    have hs : T.symm q ∈ T.source := T.map_target hq
    have hp : (T.symm q).proj ∈ i.1.source := (mem_tangentChart_self_source i _).1 hs
    have hq' : (i.1 (T.symm q).proj, coordAt i (T.symm q)) = q := by
      rw [← tangentChart_self_apply]; exact T.right_inv hq
    rw [tangentChart_self_apply, hproj, hF i _ hp, hq']
    have h1 : i.1 (T.symm q).proj = q.1 := congrArg Prod.fst hq'
    rw [h1]
  have hcont : Continuous F := continuous_iff_continuousAt.2 fun x ↦ by
    set i : atlas E N := ⟨chartAt E x.proj, chart_mem_atlas E _⟩
    set T := tangentChart i i.1
    have hx : x ∈ T.source := (mem_tangentChart_self_source i x).2 (mem_chart_source E _)
    have hFx : F x ∈ T.source := by
      rw [mem_tangentChart_self_source, hproj]; exact mem_chart_source E _
    have hTx : T x ∈ T.target := T.map_source hx
    have hr : ContinuousAt (fun q : E × E ↦ (q.1, Φ i q)) (T x) :=
      ((hΦ i) 0).continuousOn.continuousAt (T.open_target.mem_nhds hTx)
    have hval : ((T x).1, Φ i (T x)) = T (F x) := by
      have := hrep i (T x) hTx
      rw [T.left_inv hx] at this
      exact this.symm
    have hsy : ContinuousAt T.symm ((T x).1, Φ i (T x)) := by
      rw [hval]; exact T.continuousAt_symm (T.map_source hFx)
    refine ((ContinuousAt.comp (f := fun q : E × E ↦ (q.1, Φ i q)) hsy hr).comp
      (f := T) (T.continuousAt hx)).congr
      (Filter.eventually_of_mem (T.open_source.mem_nhds hx) fun v hv ↦ ?_)
    have h := hrep i (T v) (T.map_source hv)
    rw [T.left_inv hv] at h
    change T.symm ((T v).1, Φ i (T v)) = F v
    rw [← h, T.left_inv]
    rw [mem_tangentChart_self_source, hproj]
    exact (mem_tangentChart_self_source i v).1 hv
  intro k
  refine ⟨hcont.continuousOn, fun x _ ↦ ?_⟩
  set i : atlas E N := ⟨chartAt E x.proj, chart_mem_atlas E _⟩
  have hD := isOpen_chartDomain isOpen_univ hcont.continuousOn (chartAt (E × E) x)
    (chartAt (E × E) (F x))
  have hc : chartAt (E × E) (F x) = tangentChart i i.1 := by
    rw [chartAt_tangentBundle, hproj]
  rw [hc] at hD ⊢
  refine ContDiffMBOn.congr_of_isOpen hD (fun q hq ↦ (hrep i q hq.1).symm)
    (((hΦ i) k).mono fun q hq ↦ hq.1)

namespace LocalAddition

/-- The fiberwise linear map `v ↦ β_{π v}(v)` of `TN`. -/
def normMap (v : TangentBundle E N) : TangentBundle E N := ⟨v.proj, A.beta v.proj v.vec⟩

/-- The fiberwise linear map `v ↦ α_{π v}(v)` of `TN`, inverse to `normMap`. -/
def normMapInv (v : TangentBundle E N) : TangentBundle E N := ⟨v.proj, A.alpha v.proj v.vec⟩

/-- `F ∘ F⁻¹ = id`. -/
theorem normMap_normMapInv (v : TangentBundle E N) : A.normMap (A.normMapInv v) = v :=
  TangentBundle.ext_vec rfl (A.beta_alpha v.proj v.vec)

/-- `F⁻¹ ∘ F = id`. -/
theorem normMapInv_normMap (v : TangentBundle E N) : A.normMapInv (A.normMap v) = v :=
  TangentBundle.ext_vec rfl (A.alpha_beta v.proj v.vec)

/-- `normMap` is smooth. -/
theorem smoothMBM_normMap : SmoothMBM (E × E) (E × E) A.normMap := by
  refine smoothMBM_of_coordAt (fun _ ↦ rfl)
    (fun i q ↦ dMB (A.chartLocal i i) ((q.1, q.1), (q.2, 0))) (fun i k ↦ ?_) fun i v hv ↦ ?_
  · have hdom : ∀ q ∈ (tangentChart i i.1).target, ((q.1, q.1) : E × E) ∈ A.chartLocalDom i i :=
      fun q hq ↦ by
        have ha := ((mem_tangentChart_target i i.1 q).1 hq).1
        have h := (A.chartLocal_spec i i (i.1.map_target ha) (i.1.map_target ha)
          (A.self_mem_target _)).1
        rwa [i.1.right_inv ha] at h
    let L : E × E →L[ℝ] (E × E) × (E × E) :=
      ((ContinuousLinearMap.fst ℝ E E).prod (ContinuousLinearMap.fst ℝ E E)).prod
        ((ContinuousLinearMap.snd ℝ E E).prod 0)
    have hd := ContDiffMBOn.comp (g := dMB (A.chartLocal i i)) (tangentChart i i.1).open_target
      ((A.isOpen_chartLocalDom i i).prod isOpen_univ) ((A.smoothMBOn_chartLocal i i (k + 1)).2.2)
      (L.contDiffMBOn k _) fun q hq ↦ ⟨hdom q hq, mem_univ _⟩
    exact ContDiffMBOn.prodMk (tangentChart i i.1).open_target
      (((ContinuousLinearMap.fst ℝ E E).contDiffMBOn k univ).mono (subset_univ _)) hd
  · change tangentCoordChange (chartIdx v.proj) i v.proj (A.beta v.proj v.vec) = _
    rw [A.coordAt_beta i hv]
    rfl

/-- `normMapInv` is smooth. -/
theorem smoothMBM_normMapInv : SmoothMBM (E × E) (E × E) A.normMapInv := by
  refine smoothMBM_of_coordAt (fun _ ↦ rfl)
    (fun i q ↦ dMB (A.invLocal i i) ((q.1, 0), (0, q.2))) (fun i k ↦ ?_) fun i v hv ↦ ?_
  · have hdom : ∀ q ∈ (tangentChart i i.1).target, ((q.1, 0) : E × E) ∈ A.invLocalDom i i :=
      fun q hq ↦ by
        have ha := ((mem_tangentChart_target i i.1 q).1 hq).1
        have hp : i.1.symm q.1 ∈ i.1.source := i.1.map_target ha
        have h := (A.invLocal_spec i i (v := (⟨i.1.symm q.1, 0⟩ : TangentBundle E N)) hp
          (A.zero_mem _) (by rw [A.toFun_zero]; exact hp)).1
        rw [show i.1 (⟨i.1.symm q.1, (0 : E)⟩ : TangentBundle E N).proj = q.1 from
          i.1.right_inv ha] at h
        convert h using 2
        exact (coordAt_zero i hp).symm
    let L : E × E →L[ℝ] (E × E) × (E × E) :=
      ((ContinuousLinearMap.fst ℝ E E).prod 0).prod
        ((0 : E × E →L[ℝ] E).prod (ContinuousLinearMap.snd ℝ E E))
    have hd := ContDiffMBOn.comp (g := dMB (A.invLocal i i)) (tangentChart i i.1).open_target
      ((A.isOpen_invLocalDom i i).prod isOpen_univ) ((A.smoothMBOn_invLocal i i (k + 1)).2.2)
      (L.contDiffMBOn k _) fun q hq ↦ ⟨hdom q hq, mem_univ _⟩
    exact ContDiffMBOn.prodMk (tangentChart i i.1).open_target
      (((ContinuousLinearMap.fst ℝ E E).contDiffMBOn k univ).mono (subset_univ _)) hd
  · change tangentCoordChange (chartIdx v.proj) i v.proj (A.alpha v.proj v.vec) = _
    rw [A.coordAt_alpha i hv]
    rfl

/-- `F = normMap`, `v ↦ α_{π v}⁻¹ v`, as a homeomorphism of `TN`; smooth in both directions. -/
def normEquiv : TangentBundle E N ≃ₜ TangentBundle E N where
  toFun := A.normMap
  invFun := A.normMapInv
  left_inv := A.normMapInv_normMap
  right_inv := A.normMap_normMapInv
  continuous_toFun := continuousOn_univ.1 (A.smoothMBM_normMap 0).1
  continuous_invFun := continuousOn_univ.1 (A.smoothMBM_normMapInv 0).1

/-- **The normalized local addition** [GN26, Remark 3.8.16]: `Σ'(v) = Σ(β_{π v}(v))`,
where `β_y = (T_{0_y}(Σ|_{T_y N}))⁻¹`; equivalently `θ' = θ ∘ normMap`. -/
def normalize : LocalAddition E N where
  toOpenPartialHomeomorph := A.normEquiv.toOpenPartialHomeomorph.trans A.toOpenPartialHomeomorph
  fst_eq v hv := by
    have hv' : A.normMap v ∈ A.toOpenPartialHomeomorph.source := hv.2
    change (A.toOpenPartialHomeomorph (A.normMap v)).1 = v.proj
    exact A.fst_eq _ hv'
  smoothMBMOn := by
    intro k
    have hS : IsOpen (A.normEquiv.toOpenPartialHomeomorph.trans A.toOpenPartialHomeomorph).source :=
      OpenPartialHomeomorph.open_source _
    have h := (A.smoothMBMOn k).comp hS A.toOpenPartialHomeomorph.open_source
      ((SmoothMBMOn.mono_of_isOpen isOpen_univ hS (fun k ↦ A.smoothMBM_normMap k)
        (subset_univ _)) k) fun v hv ↦ hv.2
    exact h
  smoothMBMOn_symm := by
    intro k
    have hT : IsOpen (A.normEquiv.toOpenPartialHomeomorph.trans A.toOpenPartialHomeomorph).target :=
      OpenPartialHomeomorph.open_target _
    have h := ((SmoothMBMOn.mono_of_isOpen isOpen_univ isOpen_univ
      (fun k ↦ A.smoothMBM_normMapInv k) subset_rfl) k).comp hT isOpen_univ
      ((SmoothMBMOn.mono_of_isOpen A.toOpenPartialHomeomorph.open_target hT A.smoothMBMOn_symm
        fun p hp ↦ hp.1) k) (mapsTo_univ _ _)
    exact h
  zero_mem y := by
    refine ⟨mem_univ _, ?_⟩
    change A.normMap ⟨y, 0⟩ ∈ A.toOpenPartialHomeomorph.source
    have h : A.normMap ⟨y, 0⟩ = ⟨y, 0⟩ := TangentBundle.ext_vec rfl (map_zero (A.beta y))
    rw [h]
    exact A.zero_mem y
  snd_zero y := by
    change (A.toOpenPartialHomeomorph (A.normMap ⟨y, 0⟩)).2 = y
    have h : A.normMap ⟨y, 0⟩ = ⟨y, 0⟩ := TangentBundle.ext_vec rfl (map_zero (A.beta y))
    rw [h]
    exact A.snd_zero y

/-- `Σ'(y, v) = Σ(y, β_y v)`. -/
theorem normalize_toFun (v : TangentBundle E N) :
    A.normalize.toFun v = A.toFun ⟨v.proj, A.beta v.proj v.vec⟩ :=
  rfl

/-- **Every local addition can be normalized** [GN26, Remark 3.8.16]:
`A.normalize` is a normalized local addition. -/
theorem isNormalized_normalize : A.normalize.IsNormalized := by
  intro y w
  have hfun : (fun v : E ↦ chartAt E y (A.normalize.toFun ⟨y, v⟩)) =
      A.fibreMap y ∘ A.beta y := rfl
  rw [hfun]
  have h := ContDiffMBOn.hasDirDerivAt_comp (A.isOpen_fibreMapDom y) ((A.smoothMBOn_fibreMap y) 1)
    ((A.beta y).hasDirDerivAt 0 w) (by rw [map_zero]; exact A.zero_mem_fibreMapDom y)
  rw [h.dMB_eq, map_zero]
  exact A.alpha_beta y w

end LocalAddition

end Normalize

end LocallyConvex.Manifolds
