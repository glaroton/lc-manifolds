/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.MappingSpace.ExponentialLaw
public import LocallyConvexManifolds.LocalAddition.Normalize

/-!
# Tangent spaces of manifolds of mappings

For `M` compact, `N` with a local addition `Σ` (normalized, `LocalAddition.IsNormalized`, or
not) and `f ∈ C^ℓ(M, N)`, we prove [GN26, Theorem 4.2.2(d)]: the map `Θ : T_f C^ℓ(M, N) → Γ_f`,
`v ↦ (T_f ε_x (v))_{x ∈ M}`, is an isomorphism of topological vector spaces. The tangent space is
that of an atlas with varying models (`VaryingAtlas.TangentSpace`): at `f`, it is the model `Γ_f`
of the chart `φ_f`, and for a normalized local addition `Θ` turns out to be the identity of `Γ_f`.

## Main results

* `LocalAddition.tangentMapAt_eval`, `LocalAddition.tangentMapAt_evalSm`: `T_f ε_x (v) = v(x)`.
* `LocalAddition.tangentEquivSecCk`, `LocalAddition.coe_tangentEquivSecCk` (and `…Sm`): the
  isomorphism `Θ`, with `Θ(v) = (T_f ε_x (v))_{x ∈ M}`.
* `LocalAddition.mappingAtlasCk_equivalent`, `LocalAddition.mappingAtlasSm_equivalent`: the smooth
  structure does not depend on the local addition.
* `LocalAddition.tangentEquivSecCkOf`, `LocalAddition.coe_tangentEquivSecCkOf` (and `…Sm…`): `Θ`
  for an arbitrary, not necessarily normalized, local addition.

## Implementation notes

* As in `MappingSpace/ExponentialLaw.lean`, no local compactness of the model of `M` is assumed in
  the statements: it holds automatically for nonempty compact `M` (and then the model is
  finite-dimensional, `finiteDimensional_of_compactSpace`).

* **Normalization.** Glöckner–Neeb also assume the local addition normalized for (d): they note that
  by (a) the smooth structure does not depend on the local addition (`mappingAtlasCk_equivalent`)
  and that every local addition can be normalized ([GN26, Remark 3.8.16], `LocalAddition.normalize`
  in `LocalAddition/Normalize.lean`). The computation is
  `T_f ε_x (v) = T_{0}(Σ|_{T_{f(x)} N})(v(x))`, which is `v(x)` by [GN26, (3.55)].
* **Arbitrary local additions.** For a local addition `A` that is not normalized, the tangent
  space `T_f C^ℓ(M, N)` of `A`'s atlas is the model `Γ_f` of `A`'s chart at `f`, and `Θ` is no
  longer the identity. `LocalAddition.tangentEquivSecCkOf` defines `Θ` as the change of tangent
  coordinates, in the union of the (compatible) atlases of `A` and `A.normalize`, from `A`'s chart
  at `f` to `A.normalize`'s chart at `f`; so it is an isomorphism of topological vector spaces by
  construction. `LocalAddition.coe_tangentEquivSecCkOf` identifies it with the intrinsic,
  chart-independent formula `v ↦ (T_f ε_x (v))_{x ∈ M}` (a tangent vector of `N` at `f(x)` is read
  in the preferred chart at `f(x)`). Same for `ℓ = ∞` (`…SecSmOf`).
* Glöckner–Neeb compute with geometric tangent vectors (classes of curves); here tangent vectors
  are vectors in the model of a chart (kinematic tangent vectors in chart coordinates), and the
  computation is a chain rule at the zero section `φ_f(f) = 0`. We do not claim this argument is
  new.
* **Infinite-dimensional subtlety.** In infinite dimensions, different notions of tangent vector
  need not agree. Chart (kinematic) tangent vectors, as here, correspond to classes of `C^1` curves;
  operational tangent vectors (derivations of the algebra of smooth functions at a point) may form a
  different, larger space, for instance when the model has few smooth functions (compare
  [KM97, 28.1 and Lemma 28.4]: on infinite-dimensional Hilbert space there are nonzero
  operational tangent vectors of order 2 and 3, which are not kinematic). Statement (d) concerns the
  kinematic tangent space only.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
* [A. Kriegl, P. W. Michor, *The Convenient Setting of Global Analysis*][KM97]
-/

@[expose] public section

open Set Filter Function TopologicalSpace
open scoped Topology
open LocallyConvex.Analysis

noncomputable section

universe u v

namespace LocallyConvex.Manifolds

section TangentCk

variable {H : Type u} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [IsTopologicalAddGroup H]
  [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [MBManifold H M] [CompactSpace M]
  [T2Space M]
  {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {N : Type v} [TopologicalSpace N] [ChartedSpace E N] [MBManifold E N]
  (A : LocalAddition E N) {ℓ : ℕ}

namespace LocalAddition

/-- The chart at `f` sends `f` to the zero section. -/
theorem chartCk_self (f : CkMap H E ℓ M N) : A.chartCk f f = 0 := by
  ext x
  have h := A.mk_chartCk f f (A.mem_chartCk_source f) x
  rw [A.symm_self] at h
  exact congrArg TangentBundle.vec h

/-- The evaluation `τ ↦ τ(x)` of `C^ℓ` sections along `f`, a continuous linear map. -/
def evalSecCk (f : CkMap H E ℓ M N) (x : M) : SecCk H E ℓ (CkMap.toC f) →L[ℝ] E :=
  ((ContinuousMap.evalCLM ℝ (⟨x, rfl⟩ : ({x} : Set M))).comp
    ⟨Sec.coordL (Sec.singletonIdx (E := E) (f := CkMap.toC f) x),
      Sec.continuous_coordFun _⟩).comp SecCk.toSec

omit [MBManifold H M] [CompactSpace M] in
/-- `evalSecCk f x τ = τ(x)`. -/
theorem evalSecCk_apply (f : CkMap H E ℓ M N) (x : M) (τ : SecCk H E ℓ (CkMap.toC f)) :
    evalSecCk f x τ = τ x :=
  coordAt_chartAt (f x) (τ x)

/-- **The tangent maps of the point evaluations** ([GN26, proof of Theorem 4.2.2(d)]): for
a normalized local addition, `T_f ε_x (v) = v(x)` for every `v` in the tangent space at `f`,
which is the model space `Γ_f` of the chart at `f`. -/
theorem tangentMapAt_eval (hA : A.IsNormalized) (f : CkMap H E ℓ M N) (x : M)
    (v : SecCk H E ℓ (CkMap.toC f)) :
    (VaryingAtlas.tangentMapAt (B := VaryingAtlas.ofChartedSpace E N) isOpen_univ
      ((A.smooth_eval x) 1) (mem_univ f) v : E) = v x := by
  change dMB (chartAt E (f x) ∘ (fun g : CkMap H E ℓ M N ↦ g x) ∘ (A.chartCk f).symm)
    (A.chartCk f f, v) = _
  rw [A.chartCk_self]
  obtain ⟨O, hO, h0O, hG⟩ := A.exists_smoothMBOn_chart_toFun (f x)
  have h0 : (0 : SecCk H E ℓ (CkMap.toC f)) ∈ (A.chartCk f).target :=
    A.chartCk_self f ▸ (A.chartCk f).map_source (A.mem_chartCk_source f)
  have hev : (chartAt E (f x) ∘ (fun g : CkMap H E ℓ M N ↦ g x) ∘ (A.chartCk f).symm) =ᶠ[𝓝 0]
      (fun w : E ↦ chartAt E (f x) (A.toFun ⟨f x, w⟩)) ∘ evalSecCk f x :=
    Filter.eventually_of_mem ((A.chartCk f).open_target.mem_nhds h0) fun τ hτ ↦ by
      simp only [Function.comp_apply, A.chartCk_symm_apply f hτ, evalSecCk_apply]
  rw [dMB_congr_of_eventuallyEq hev]
  have hd := ContDiffMBOn.hasDirDerivAt_comp hO (hG 1) ((evalSecCk f x).hasDirDerivAt 0 v)
    (by rw [map_zero]; exact h0O)
  rw [hd.dMB_eq, map_zero, evalSecCk_apply]
  exact hA (f x) _

/-- **[GN26, Theorem 4.2.2(d)]**, finite `ℓ`: for a normalized local addition, the map
`Θ : T_f C^ℓ(M, N) → Γ_f`, `v ↦ (T_f ε_x (v))_{x ∈ M}`, is an isomorphism of topological vector
spaces. In the atlas `φ_f`, the tangent space at `f` is `Γ_f` itself, and `Θ` is the identity
(`coe_tangentEquivSecCk`). -/
def tangentEquivSecCk (f : CkMap H E ℓ M N) :
    A.mappingAtlasCk.TangentSpace f ≃L[ℝ] SecCk H E ℓ (CkMap.toC f) :=
  ContinuousLinearEquiv.refl ℝ _

/-- `Θ(v) = (T_f ε_x (v))_{x ∈ M}`: the isomorphism `tangentEquivSecCk` is the map of
Theorem 4.2.2(d). -/
theorem coe_tangentEquivSecCk (hA : A.IsNormalized) (f : CkMap H E ℓ M N)
    (v : A.mappingAtlasCk.TangentSpace f) :
    ⇑(A.tangentEquivSecCk f v) = fun x ↦ (VaryingAtlas.tangentMapAt
      (B := VaryingAtlas.ofChartedSpace E N) isOpen_univ ((A.smooth_eval x) 1) (mem_univ f)
        v : E) :=
  funext fun x ↦ (A.tangentMapAt_eval hA f x v).symm

/-- **The smooth structure does not depend on the local addition** ([GN26, proof of
Theorem 4.2.2(d)]): the atlases of `C^ℓ(M, N)` built from two local additions of `N` are
equivalent, since both satisfy the exponential law. -/
theorem mappingAtlasCk_equivalent (A' : LocalAddition E N) :
    (A'.mappingAtlasCk (H := H) (M := M) (ℓ := ℓ)).Equivalent A.mappingAtlasCk :=
  A.equivalent_mappingAtlasCk_of_expLaw _ fun _ _ _ ↦ A'.contMDiffOn_mappingAtlasCk_iff

/-- The atlases of `C^∞(M, N)` built from two local additions of `N` are equivalent. -/
theorem mappingAtlasSm_equivalent (A' : LocalAddition E N) :
    (A'.mappingAtlasSm (H := H) (M := M)).Equivalent A.mappingAtlasSm :=
  A.equivalent_mappingAtlasSm_of_expLaw _ fun _ _ _ ↦ A'.contMDiffOn_mappingAtlasSm_iff

/-! ### The case `ℓ = ∞` -/

/-- The chart of `C^∞(M, N)` at `f` sends `f` to the zero section. -/
theorem chartSm_self (f : SmoothMap H E M N) : A.chartSm f f = 0 := by
  ext x
  have h := congrArg (fun τ : SecCk H E 0 _ ↦ τ x) (A.toCkCLM_chartFunSm f f 0)
  have h0 := congrArg (fun τ : SecCk H E 0 _ ↦ τ x) (A.chartCk_self (SmoothMap.toCk 0 f))
  exact h.trans h0

/-- The inverse of the chart of `C^∞(M, N)` at `f` is `τ ↦ Σ ∘ τ` on `O_f`. -/
theorem chartSm_symm_apply (f : SmoothMap H E M N) {τ : SecSm H E (SmoothMap.toC f)}
    (hτ : τ ∈ (A.chartSm f).target) (x : M) :
    (A.chartSm f).symm τ x = A.toFun ⟨f x, τ x⟩ :=
  (congrArg (fun g : CkMap H E 0 M N ↦ g x) (A.toCk_chartInvFunSm f τ 0)).trans
    (A.chartInvFunCk_apply (SmoothMap.toCk 0 f) (τ := SecSm.toCkCLM 0 τ) hτ x)

/-- The evaluation `τ ↦ τ(x)` of smooth sections along `f`, a continuous linear map. -/
def evalSecSm (f : SmoothMap H E M N) (x : M) : SecSm H E (SmoothMap.toC f) →L[ℝ] E :=
  (evalSecCk (SmoothMap.toCk 0 f) x).comp (SecSm.toCkCLM 0)

omit [MBManifold H M] [CompactSpace M] in
/-- `evalSecSm f x τ = τ(x)`. -/
theorem evalSecSm_apply (f : SmoothMap H E M N) (x : M) (τ : SecSm H E (SmoothMap.toC f)) :
    evalSecSm f x τ = τ x :=
  evalSecCk_apply (SmoothMap.toCk 0 f) x (SecSm.toCkCLM 0 τ)

/-- **The tangent maps of the point evaluations** on `C^∞(M, N)`: for a normalized local
addition, `T_f ε_x (v) = v(x)`. -/
theorem tangentMapAt_evalSm (hA : A.IsNormalized) (f : SmoothMap H E M N) (x : M)
    (v : SecSm H E (SmoothMap.toC f)) :
    (VaryingAtlas.tangentMapAt (B := VaryingAtlas.ofChartedSpace E N) isOpen_univ
      ((A.smooth_evalSm x) 1) (mem_univ f) v : E) = v x := by
  change dMB (chartAt E (f x) ∘ (fun g : SmoothMap H E M N ↦ g x) ∘ (A.chartSm f).symm)
    (A.chartSm f f, v) = _
  rw [A.chartSm_self]
  obtain ⟨O, hO, h0O, hG⟩ := A.exists_smoothMBOn_chart_toFun (f x)
  have h0 : (0 : SecSm H E (SmoothMap.toC f)) ∈ (A.chartSm f).target :=
    A.chartSm_self f ▸ (A.chartSm f).map_source (A.mem_chartSm_source f)
  have hev : (chartAt E (f x) ∘ (fun g : SmoothMap H E M N ↦ g x) ∘ (A.chartSm f).symm) =ᶠ[𝓝 0]
      (fun w : E ↦ chartAt E (f x) (A.toFun ⟨f x, w⟩)) ∘ evalSecSm f x :=
    Filter.eventually_of_mem ((A.chartSm f).open_target.mem_nhds h0) fun τ hτ ↦ by
      simp only [Function.comp_apply, A.chartSm_symm_apply f hτ, evalSecSm_apply]
  rw [dMB_congr_of_eventuallyEq hev]
  have hd := ContDiffMBOn.hasDirDerivAt_comp hO (hG 1) ((evalSecSm f x).hasDirDerivAt 0 v)
    (by rw [map_zero]; exact h0O)
  rw [hd.dMB_eq, map_zero, evalSecSm_apply]
  exact hA (f x) _

/-- **[GN26, Theorem 4.2.2(d)]**, `ℓ = ∞`: `Θ : T_f C^∞(M, N) → Γ_f`,
`v ↦ (T_f ε_x (v))_{x ∈ M}`, is an isomorphism of topological vector spaces (the identity of
`Γ_f`, the model of the chart at `f`, by `coe_tangentEquivSecSm`). -/
def tangentEquivSecSm (f : SmoothMap H E M N) :
    A.mappingAtlasSm.TangentSpace f ≃L[ℝ] SecSm H E (SmoothMap.toC f) :=
  ContinuousLinearEquiv.refl ℝ _

/-- `Θ(v) = (T_f ε_x (v))_{x ∈ M}` on `C^∞(M, N)`. -/
theorem coe_tangentEquivSecSm (hA : A.IsNormalized) (f : SmoothMap H E M N)
    (v : A.mappingAtlasSm.TangentSpace f) :
    ⇑(A.tangentEquivSecSm f v) = fun x ↦ (VaryingAtlas.tangentMapAt
      (B := VaryingAtlas.ofChartedSpace E N) isOpen_univ ((A.smooth_evalSm x) 1) (mem_univ f)
        v : E) :=
  funext fun x ↦ (A.tangentMapAt_evalSm hA f x v).symm

/-! ### Theorem 4.2.2(d) for an arbitrary local addition -/

/-- The atlases of `C^ℓ(M, N)` built from `A` and from its normalization are compatible. -/
theorem compatible_normalize :
    (A.mappingAtlasCk (H := H) (M := M) (ℓ := ℓ)).Compatible A.normalize.mappingAtlasCk :=
  (VaryingAtlas.equivalent_iff_compatible _ _).1 (mappingAtlasCk_equivalent A.normalize A)

/-- The union of the atlases of `C^ℓ(M, N)` built from `A` and from its normalization. -/
def unionAtlasCk : VaryingAtlas (CkMap H E ℓ M N) :=
  (A.mappingAtlasCk (H := H) (M := M) (ℓ := ℓ)).union A.normalize.mappingAtlasCk
    A.compatible_normalize

/-- **[GN26, Theorem 4.2.2(d)]**, finite `ℓ`, for an arbitrary local addition: the map
`Θ : T_f C^ℓ(M, N) → Γ_f`, `v ↦ (T_f ε_x (v))_{x ∈ M}`, is an isomorphism of topological vector
spaces. Here `Θ` is the change of tangent coordinates at `f` from the chart `φ_f` of `A` to the
chart `φ'_f` of the normalized local addition `A.normalize` (the derivative at `0` of the
transition map `φ'_f ∘ φ_f⁻¹`); `coe_tangentEquivSecCkOf` shows that it is the map
`v ↦ (T_f ε_x (v))_x`, which needs no choice of chart. -/
def tangentEquivSecCkOf (f : CkMap H E ℓ M N) :
    A.mappingAtlasCk.TangentSpace f ≃L[ℝ] SecCk H E ℓ (CkMap.toC f) :=
  A.unionAtlasCk.tangentCoordChangeEquiv (.inl f) (.inr f)
    ⟨A.mem_chartCk_source f, A.normalize.mem_chartCk_source f⟩

/-- `Θ(v) = (T_f ε_x (v))_{x ∈ M}`, for an arbitrary local addition. -/
theorem coe_tangentEquivSecCkOf (f : CkMap H E ℓ M N) (v : A.mappingAtlasCk.TangentSpace f) :
    ⇑(A.tangentEquivSecCkOf f v) = fun x ↦ (VaryingAtlas.tangentMapAt
      (B := VaryingAtlas.ofChartedSpace E N) isOpen_univ ((A.smooth_eval x) 1) (mem_univ f)
        v : E) := by
  funext x
  let U := A.unionAtlasCk (H := H) (M := M) (ℓ := ℓ)
  have hU : U.ContMDiffOn (VaryingAtlas.ofChartedSpace E N) 1
      (fun g : CkMap H E ℓ M N ↦ g x) univ := by
    refine ⟨((A.smooth_eval x) 1).1, fun i j ↦ ?_⟩
    cases i with
    | inl g => exact ((A.smooth_eval x) 1).2 g j
    | inr g => exact ((A.normalize.smooth_eval x) 1).2 g j
  have h := VaryingAtlas.dMB_chart_eq_tangentMapAt (A := U) isOpen_univ hU (mem_univ f)
    (i := .inr f) (j := (VaryingAtlas.ofChartedSpace E N).chartAt (f x))
    (A.normalize.mem_chartCk_source f) ((VaryingAtlas.ofChartedSpace E N).mem_chartAt_source _) v
  have hN := A.normalize.tangentMapAt_eval A.isNormalized_normalize f x
    (U.tangentCoordChange (U.chartAt f) (.inr f)
      ⟨U.mem_chartAt_source f, A.normalize.mem_chartCk_source f⟩ v)
  exact hN.symm.trans (h.trans (VaryingAtlas.tangentCoordChange_self _ _
    ((VaryingAtlas.ofChartedSpace E N).mem_chartAt_source (f x)) _))

/-! ### Theorem 4.2.2(d) for an arbitrary local addition, `ℓ = ∞` -/

/-- The atlases of `C^ℓ(M, N)` built from `A` and from its normalization are compatible. -/
theorem compatible_normalizeSm :
    (A.mappingAtlasSm (H := H) (M := M)).Compatible A.normalize.mappingAtlasSm :=
  (VaryingAtlas.equivalent_iff_compatible _ _).1 (mappingAtlasSm_equivalent A.normalize A)

/-- The union of the atlases of `C^ℓ(M, N)` built from `A` and from its normalization. -/
def unionAtlasSm : VaryingAtlas (SmoothMap H E M N) :=
  (A.mappingAtlasSm (H := H) (M := M)).union A.normalize.mappingAtlasSm
    A.compatible_normalizeSm

/-- **[GN26, Theorem 4.2.2(d)]**, `ℓ = ∞`, for an arbitrary local addition: the map
`Θ : T_f C^∞(M, N) → Γ_f`, `v ↦ (T_f ε_x (v))_{x ∈ M}`, is an isomorphism of topological vector
spaces. Here `Θ` is the change of tangent coordinates at `f` from the chart `φ_f` of `A` to the
chart `φ'_f` of the normalized local addition `A.normalize` (the derivative at `0` of the
transition map `φ'_f ∘ φ_f⁻¹`); `coe_tangentEquivSecSmOf` shows that it is the map
`v ↦ (T_f ε_x (v))_x`, which needs no choice of chart. -/
def tangentEquivSecSmOf (f : SmoothMap H E M N) :
    A.mappingAtlasSm.TangentSpace f ≃L[ℝ] SecSm H E (SmoothMap.toC f) :=
  A.unionAtlasSm.tangentCoordChangeEquiv (.inl f) (.inr f)
    ⟨A.mem_chartSm_source f, A.normalize.mem_chartSm_source f⟩

/-- `Θ(v) = (T_f ε_x (v))_{x ∈ M}`, for an arbitrary local addition. -/
theorem coe_tangentEquivSecSmOf (f : SmoothMap H E M N) (v : A.mappingAtlasSm.TangentSpace f) :
    ⇑(A.tangentEquivSecSmOf f v) = fun x ↦ (VaryingAtlas.tangentMapAt
      (B := VaryingAtlas.ofChartedSpace E N) isOpen_univ ((A.smooth_evalSm x) 1) (mem_univ f)
        v : E) := by
  funext x
  let U := A.unionAtlasSm (H := H) (M := M)
  have hU : U.ContMDiffOn (VaryingAtlas.ofChartedSpace E N) 1
      (fun g : SmoothMap H E M N ↦ g x) univ := by
    refine ⟨((A.smooth_evalSm x) 1).1, fun i j ↦ ?_⟩
    cases i with
    | inl g => exact ((A.smooth_evalSm x) 1).2 g j
    | inr g => exact ((A.normalize.smooth_evalSm x) 1).2 g j
  have h := VaryingAtlas.dMB_chart_eq_tangentMapAt (A := U) isOpen_univ hU (mem_univ f)
    (i := .inr f) (j := (VaryingAtlas.ofChartedSpace E N).chartAt (f x))
    (A.normalize.mem_chartSm_source f) ((VaryingAtlas.ofChartedSpace E N).mem_chartAt_source _) v
  have hN := A.normalize.tangentMapAt_evalSm A.isNormalized_normalize f x
    (U.tangentCoordChange (U.chartAt f) (.inr f)
      ⟨U.mem_chartAt_source f, A.normalize.mem_chartSm_source f⟩ v)
  exact hN.symm.trans (h.trans (VaryingAtlas.tangentCoordChange_self _ _
    ((VaryingAtlas.ofChartedSpace E N).mem_chartAt_source (f x)) _))

end LocalAddition

end TangentCk

end LocallyConvex.Manifolds
