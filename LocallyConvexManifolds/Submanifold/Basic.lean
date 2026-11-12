/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.Manifold.ContMDiff

/-!
# Embedded submanifolds

A subset `N` of a manifold `M` modeled on `E` is a submanifold modeled on a closed subspace
`S ⊆ E` ([GN26, Definition 3.1.10]; see also [Lar26, Cap. 2], *subvariedad embebida*) if every
point of `N` lies in a chart `φ` of the maximal atlas with `φ(U ∩ N) = φ(U) ∩ S`. Then `N` is a
manifold modeled on `S` (`IsEmbeddedSubmanifold.mbManifold`) and the inclusion is smooth. The
calculus fact behind the construction is `ContDiffMBOn.codRestrict` ([LCA]): a `C^k` map with
values in a closed subspace `T` is `C^k` as a map into `T` ([GN26, Lemma 1.3.19]).

## Main definitions

* `IsSliceChart`: `φ` is a slice chart for `N` with model `S`.
* `IsEmbeddedSubmanifold`: every point of `N` lies in the domain of a slice chart.
* `sliceChart`: the chart of `N` induced by a slice chart.
* `IsEmbeddedSubmanifold.chartedSpace`: the charted space structure of an embedded submanifold,
  by the induced charts.

## Main results

* `smoothMBOn_sliceChart_transition`: the transition maps between induced charts are smooth.
* `IsEmbeddedSubmanifold.mbManifold`: an embedded submanifold is a manifold modeled on `S`.
* `IsEmbeddedSubmanifold.smoothMBM_val`: the inclusion of an embedded submanifold is smooth.

## Implementation notes

**Subtleties (infinite dimensions).**

* No complement of `S` is required. When `S` is complemented, Glöckner–Neeb call `N` a *split*
  submanifold; in the Banach literature (e.g. Bourbaki) "submanifold" usually means split, and
  non-split ones are called quasi-submanifolds. For locally convex models the splitting
  condition is much less useful ([GN26, Rem. 3.1.11]).
* The slice charts must be taken in the *maximal* atlas (charts compatible with the atlas): for
  `M = E` the atlas only contains the identity.
* The usual criteria (regular values, split immersions) need inverse or implicit function
  theorems, which are not available for general locally convex models.
* Weaker notions are genuinely different in infinite dimensions and are not covered here:
  initial submanifolds ([GN26, Def. 3.3.22]: a universal property for smooth maps into `N`, the
  topology of `N` may be finer than the induced one), immersions ([GN26, Def. 3.3.25(b)]: locally
  a continuous linear map with a continuous linear left inverse), and weak immersions (injective
  differential whose range need not be closed).

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
* [G. Larotonda, *Estructuras geométricas para las variedades de Banach*][Lar26]
* [glaroton, *lc-analysis: Michal–Bastiani calculus on locally convex spaces*][LCA]
-/

@[expose] public section

open Set Filter
open scoped Topology Manifold
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe u v

section Calculus

variable {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

end Calculus

section Submanifold

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]
  (N : Set M) (S : Submodule ℝ E)

/-- `φ` is a slice chart for `N` with model `S`: a chart of the maximal atlas (a chart
compatible with the atlas of `M`) with `φ(U ∩ N) = φ(U) ∩ S`. The maximal atlas is needed: for
instance, when `M = E` the atlas only contains the identity. -/
def IsSliceChart (φ : OpenPartialHomeomorph M E) : Prop :=
  φ ∈ (mbGroupoid E).maximalAtlas M ∧ ∀ q ∈ φ.source, (q ∈ N ↔ φ q ∈ S)

/-- `N` is an embedded submanifold of `M` modeled on the closed subspace `S` of `E`: every point
of `N` lies in a slice chart. -/
structure IsEmbeddedSubmanifold : Prop where
  isClosed : IsClosed (S : Set E)
  exists_sliceChart : ∀ p ∈ N, ∃ φ, IsSliceChart N S φ ∧ p ∈ φ.source

variable {N S}

open scoped Classical in
/-- The chart of `N` induced by a slice chart `φ`: the restriction `U ∩ N → φ(U) ∩ S`. The
point `p₀` is only used as a junk value outside the target. -/
def sliceChart {φ : OpenPartialHomeomorph M E} (hφ : IsSliceChart N S φ) (p₀ : N) :
    OpenPartialHomeomorph N S where
  toFun q := if h : φ q ∈ S then ⟨φ q, h⟩ else 0
  invFun y := if h : φ.symm y ∈ N then ⟨φ.symm y, h⟩ else p₀
  source := Subtype.val ⁻¹' φ.source
  target := Subtype.val ⁻¹' φ.target
  map_source' q hq := by
    rw [dite_eq_left ((hφ.2 q hq).mp q.2)]
    exact φ.map_source hq
  map_target' y hy := by
    have hN : φ.symm y ∈ N := (hφ.2 _ (φ.map_target hy)).mpr (by rw [φ.right_inv hy]; exact y.2)
    rw [dite_eq_left hN]
    exact φ.map_target hy
  left_inv' q hq := by
    have hS : φ q ∈ S := (hφ.2 q hq).mp q.2
    have hN : φ.symm (φ q) ∈ N := by rw [φ.left_inv hq]; exact q.2
    simp only [dite_eq_left hS]
    rw [dite_eq_left hN]
    exact Subtype.ext (φ.left_inv hq)
  right_inv' y hy := by
    have hN : φ.symm y ∈ N := (hφ.2 _ (φ.map_target hy)).mpr (by rw [φ.right_inv hy]; exact y.2)
    have hS : φ (φ.symm y) ∈ S := by rw [φ.right_inv hy]; exact y.2
    simp only [dite_eq_left hN]
    rw [dite_eq_left hS]
    exact Subtype.ext (φ.right_inv hy)
  open_source := φ.open_source.preimage continuous_subtype_val
  open_target := φ.open_target.preimage continuous_subtype_val
  continuousOn_toFun := by
    refine (Topology.IsInducing.subtypeVal.continuousOn_iff).mpr ?_
    refine (φ.continuousOn.comp continuous_subtype_val.continuousOn fun q hq ↦ hq).congr ?_
    intro q hq
    simp only [Function.comp_apply, dite_eq_left ((hφ.2 q hq).mp q.2)]
  continuousOn_invFun := by
    refine (Topology.IsInducing.subtypeVal.continuousOn_iff).mpr ?_
    refine (φ.continuousOn_symm.comp continuous_subtype_val.continuousOn fun y hy ↦ hy).congr ?_
    intro y hy
    have hN : φ.symm y ∈ N := (hφ.2 _ (φ.map_target hy)).mpr (by rw [φ.right_inv hy]; exact y.2)
    simp only [Function.comp_apply, dite_eq_left hN]

open scoped Classical in
omit [MBManifold E M] in
theorem sliceChart_apply_coe {φ : OpenPartialHomeomorph M E} (hφ : IsSliceChart N S φ) (p₀ : N)
    {q : N} (hq : (q : M) ∈ φ.source) : ((sliceChart hφ p₀ q : S) : E) = φ q := by
  change ((if h : φ q ∈ S then (⟨φ q, h⟩ : S) else 0 : S) : E) = φ q
  rw [dite_eq_left ((hφ.2 q hq).mp q.2)]

open scoped Classical in
omit [MBManifold E M] in
theorem sliceChart_symm_apply_coe {φ : OpenPartialHomeomorph M E} (hφ : IsSliceChart N S φ)
    (p₀ : N) {y : S} (hy : (y : E) ∈ φ.target) :
    (((sliceChart hφ p₀).symm y : N) : M) = φ.symm y := by
  have hN : φ.symm y ∈ N := (hφ.2 _ (φ.map_target hy)).mpr (by rw [φ.right_inv hy]; exact y.2)
  change ((if h : φ.symm y ∈ N then (⟨φ.symm y, h⟩ : N) else p₀ : N) : M) = φ.symm y
  rw [dite_eq_left hN]

omit [MBManifold E M] in
/-- The transition maps between induced charts are smooth: they are restrictions to `S` of
transition maps of `M`, with values in `S`. -/
theorem smoothMBOn_sliceChart_transition (hS : IsClosed (S : Set E))
    {φ ψ : OpenPartialHomeomorph M E} (hφ : IsSliceChart N S φ) (hψ : IsSliceChart N S ψ)
    (p₀ p₁ : N) :
    SmoothMBOn ⇑((sliceChart hφ p₀).symm ≫ₕ sliceChart hψ p₁)
      ((sliceChart hφ p₀).symm ≫ₕ sliceChart hψ p₁).source := by
  set e := sliceChart hφ p₀
  set e' := sliceChart hψ p₁
  have hV : IsOpen (e.symm ≫ₕ e').source := (e.symm ≫ₕ e').open_source
  have hsub : ∀ y ∈ (e.symm ≫ₕ e').source,
      (y : E) ∈ φ.target ∩ φ.symm ⁻¹' ψ.source ∧ ((e.symm y : N) : M) = φ.symm y := by
    rintro y ⟨hy, hy'⟩
    have hy₁ : (y : E) ∈ φ.target := hy
    have hc := sliceChart_symm_apply_coe hφ p₀ hy₁
    refine ⟨⟨hy₁, ?_⟩, hc⟩
    have : ((e.symm y : N) : M) ∈ ψ.source := hy'
    rwa [hc] at this
  intro k
  have hh : ContDiffMBOn k ((ψ ∘ φ.symm) ∘ S.subtypeL) (e.symm ≫ₕ e').source :=
    (smoothMBOn_transition_of_mem_maximalAtlas hφ.1 hψ.1 k).comp hV
      (φ.isOpen_inter_preimage_symm ψ.open_source)
      (S.subtypeL.contDiffMBOn k _) fun y hy ↦ (hsub y hy).1
  refine ContDiffMBOn.codRestrict hS hV hh fun y hy ↦ ?_
  rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    sliceChart_apply_coe hψ p₁ (by rw [(hsub y hy).2]; exact (hsub y hy).1.2), (hsub y hy).2]
  rfl

omit [MBManifold E M] in
theorem sliceChart_transition_mem (hS : IsClosed (S : Set E))
    {φ ψ : OpenPartialHomeomorph M E} (hφ : IsSliceChart N S φ) (hψ : IsSliceChart N S ψ)
    (p₀ p₁ : N) :
    (sliceChart hφ p₀).symm ≫ₕ sliceChart hψ p₁ ∈ mbGroupoid S := by
  refine ⟨smoothMBOn_sliceChart_transition hS hφ hψ p₀ p₁, ?_⟩
  have h := smoothMBOn_sliceChart_transition hS hψ hφ p₁ p₀
  rw [OpenPartialHomeomorph.trans_source] at h
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm,
    OpenPartialHomeomorph.trans_target, ← OpenPartialHomeomorph.symm_source,
    OpenPartialHomeomorph.symm_target]
  exact h

/-- The charted space structure of an embedded submanifold, by the induced charts. -/
@[instance_reducible]
def IsEmbeddedSubmanifold.chartedSpace (h : IsEmbeddedSubmanifold N S) : ChartedSpace S N where
  atlas := {e | ∃ (φ : OpenPartialHomeomorph M E) (hφ : IsSliceChart N S φ) (p₀ : N),
    e = sliceChart hφ p₀}
  chartAt p := sliceChart (h.exists_sliceChart p p.2).choose_spec.1 p
  mem_chart_source p := (h.exists_sliceChart p p.2).choose_spec.2
  chart_mem_atlas p := ⟨_, _, p, rfl⟩

omit [MBManifold E M] in
/-- **An embedded submanifold is a manifold** modeled on `S`. -/
theorem IsEmbeddedSubmanifold.mbManifold (h : IsEmbeddedSubmanifold N S) :
    letI := h.chartedSpace; MBManifold S N := by
  let := h.chartedSpace
  exact ⟨by
    rintro _ _ ⟨φ, hφ, p₀, rfl⟩ ⟨ψ, hψ, p₁, rfl⟩
    exact sliceChart_transition_mem h.isClosed hφ hψ p₀ p₁⟩

/-- The inclusion of an embedded submanifold is smooth. -/
theorem IsEmbeddedSubmanifold.smoothMBM_val (h : IsEmbeddedSubmanifold N S) :
    letI := h.chartedSpace; SmoothMBM S E (Subtype.val : N → M) := by
  let := h.chartedSpace
  intro k
  refine ⟨continuous_subtype_val.continuousOn, fun p _ ↦ ?_⟩
  obtain ⟨hφ, hp⟩ := (h.exists_sliceChart p p.2).choose_spec
  set φ := (h.exists_sliceChart p p.2).choose
  set c := chartAt E (p : M)
  change ContDiffMBOn k (c ∘ Subtype.val ∘ (sliceChart hφ p).symm)
    (chartDomain Subtype.val univ (sliceChart hφ p) c)
  have hD : IsOpen (chartDomain Subtype.val univ (sliceChart hφ p) c) :=
    isOpen_chartDomain isOpen_univ continuous_subtype_val.continuousOn _ _
  have hsub : ∀ y ∈ chartDomain Subtype.val univ (sliceChart hφ p) c,
      (y : E) ∈ φ.target ∩ φ.symm ⁻¹' c.source ∧
        (((sliceChart hφ p).symm y : N) : M) = φ.symm y := by
    rintro y ⟨hy, -, hyc⟩
    have hc := sliceChart_symm_apply_coe hφ p (y := y) hy
    refine ⟨⟨hy, ?_⟩, hc⟩
    have : (((sliceChart hφ p).symm y : N) : M) ∈ c.source := hyc
    rwa [hc] at this
  have hh : ContDiffMBOn k ((c ∘ φ.symm) ∘ S.subtypeL)
      (chartDomain Subtype.val univ (sliceChart hφ p) c) :=
    (smoothMBOn_transition_of_mem_maximalAtlas hφ.1
      ((mbGroupoid E).chart_mem_maximalAtlas (p : M)) k).comp hD
      (φ.isOpen_inter_preimage_symm c.open_source) (S.subtypeL.contDiffMBOn k _)
      fun y hy ↦ (hsub y hy).1
  refine ContDiffMBOn.congr_of_isOpen hD (fun y hy ↦ ?_) hh
  simp only [Function.comp_apply, (hsub y hy).2]
  rfl

end Submanifold

end LocallyConvex.Manifolds
