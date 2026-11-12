/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.RoughBoundary.Submanifold
public import LocallyConvexAnalysis.Calculus.DenseInterior.Rules

/-!
# Submanifolds of manifolds with rough boundary modeled on closed subspaces

Let `M` be a `C^r` manifold with rough boundary modeled on `E` and `F ⊆ E` a closed vector
subspace. A chart `e` of `M` is **adapted** to `N ⊆ M` (`IsAdaptedTo`) if `e(U_e ∩ N) = V_e ∩ F`
and `V_e ∩ F` has dense interior relative to `F`. `N` is a **submanifold modeled on `F`**
(`RoughAtlas.IsSubmanifold`) if every point of `N` lies in the domain of an adapted chart (S1) and,
for `r = 0`, adapted charts agree on the boundary points of `N` (S2). Then the charts
`e_N : U_e ∩ N → V_e ∩ F` (`subChart`) form a `C^r` atlas of rough `F`-charts of `N`
(`RoughAtlas.submanifold`) ([GN26, Definition 3.5.14 and Remark 3.5.16, pp. 282–283]).

## Main definitions

* `IsAdaptedTo F e N`: the chart `e` is adapted to `N` and the subspace `F`.
* `subChart F e N`: the chart `e_N : U_e ∩ N → V_e ∩ F` of `N` induced by `e`.
* `RoughAtlas.IsSubmanifold`: `N` is a submanifold modeled on `F`, conditions (S1) and (S2).
* `RoughAtlas.submanifold`: a submanifold modeled on a closed subspace `F`, as a manifold with
  rough boundary modeled on `F`.

## Main results

* `IsLocallyConvexSubset.preimage_clm`: the preimage of a locally convex subset under a
  continuous linear map is locally convex.

## Proof

The targets `V_e ∩ F`, as subsets of `F`, are locally convex (`IsLocallyConvexSubset.preimage_clm`;
[GN26, Remark 3.5.16(b)]) and have dense interior by (S1). The transition maps of the `e_N` are
those of `M` restricted to `F` and corestricted to `F`: they are `C^r` by the chain rule (with the
inclusion `F → E`) and the corestriction lemma for sequentially closed subspaces ([GN26,
Lemma 1.4.16]; [LCA], `contDiffLC_subtype_iff`), which is where closedness of `F` is used.

## Infinite-dimensional subtleties

* The density of the interior of `V_e ∩ F` relative to `F` is a genuine requirement when `V_e` is
  not open [GN26, Remark 3.5.16(d)].
* (S2) is automatic for `r ≥ 1` by the invariance of the boundary ([GN26, Lemma 3.5.6], applied to
  the atlas of `N`); for `r = 0` it is part of the definition.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
  (page numbers refer to arXiv:2602.12362v1)
* [glaroton, *lc-analysis: Michal–Bastiani calculus on locally convex spaces*][LCA]
-/

@[expose] public section

open Set Filter Function
open scoped Topology
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe u

section Subspace

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
/-- The preimage of a locally convex subset under a continuous linear map is locally convex. -/
theorem IsLocallyConvexSubset.preimage_clm {G : Type*} [AddCommGroup G] [Module ℝ G]
    [TopologicalSpace G] (L : G →L[ℝ] E) {U : Set E} (hU : IsLocallyConvexSubset U) :
    IsLocallyConvexSubset (L ⁻¹' U) := by
  intro x hx
  obtain ⟨V, hV, hVU, hVc⟩ := hU (L x) hx
  refine ⟨L ⁻¹' V, ?_, preimage_mono hVU, hVc.linear_preimage (L : G →ₗ[ℝ] E)⟩
  exact (L.continuous.continuousWithinAt.tendsto_nhdsWithin (mapsTo_preimage L U)) hV

end Subspace

/-! ### Submanifolds: Definition 3.5.14 -/

section Submanifold

variable {r : ℕ∞} {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type*} [TopologicalSpace M] (F : Submodule ℝ E)

/-- A chart `e` of `M` is **adapted** to `N ⊆ M` and the subspace `F` [GN26, Definition 3.5.14 (S1),
p. 282]: `e(U_e ∩ N) = V_e ∩ F`, and the interior of `V_e ∩ F` relative to `F` is dense in
`V_e ∩ F`. -/
def IsAdaptedTo (e : PartialHomeomorph M E) (N : Set M) : Prop :=
  e.target ∩ e.symm ⁻¹' N = e.target ∩ F ∧ HasDenseInterior (Subtype.val ⁻¹' e.target : Set F)

open Classical in
/-- The corestriction `x ↦ e x ∈ F` (junk value `0` where `e x ∉ F`). -/
def subChartFun (e : PartialHomeomorph M E) (N : Set M) (x : N) : F :=
  if h : e x ∈ F then ⟨e x, h⟩ else 0

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
theorem subChartFun_of_mem (e : PartialHomeomorph M E) (N : Set M) {x : N} (h : e x ∈ F) :
    subChartFun F e N x = ⟨e x, h⟩ := by
  simp only [subChartFun, h, dite_true]

/-- The chart `e_N : U_e ∩ N → V_e ∩ F` of the submanifold `N` induced by `e`. -/
def subChart (e : PartialHomeomorph M E) (N : Set M) [Nonempty N] : PartialHomeomorph N F where
  toFun := subChartFun F e N
  invFun z := e.restrInv N z
  source := {x | (x : M) ∈ e.source ∧ e x ∈ F}
  target := {z | (z : E) ∈ e.target ∧ e.symm z ∈ N}
  map_source' x hx := by
    rw [subChartFun_of_mem F e N hx.2]
    exact ⟨e.map_source hx.1, by simp only [e.left_inv hx.1]; exact x.2⟩
  map_target' z hz := by
    refine ⟨?_, ?_⟩
    · rw [e.coe_restrInv_of_mem hz.2]; exact e.map_target hz.1
    · rw [e.coe_restrInv_of_mem hz.2, e.right_inv hz.1]; exact z.2
  left_inv' x hx := by
    have h : e.symm (e x) ∈ N := by rw [e.left_inv hx.1]; exact x.2
    rw [subChartFun_of_mem F e N hx.2]
    exact Subtype.ext ((e.coe_restrInv_of_mem h).trans (e.left_inv hx.1))
  right_inv' z hz := by
    have h : e (e.restrInv N z) ∈ F := by
      rw [e.coe_restrInv_of_mem hz.2, e.right_inv hz.1]; exact z.2
    rw [subChartFun_of_mem F e N h]
    exact Subtype.ext (by simp only [e.coe_restrInv_of_mem hz.2, e.right_inv hz.1])
  continuousOn_toFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : ({x : N | (x : M) ∈ e.source ∧ e x ∈ F}).domRestrict (subChartFun F e N) =
        fun x ↦ ⟨e x, x.2.2⟩ := funext fun x ↦ by
      rw [domRestrict_apply, subChartFun_of_mem F e N x.2.2]
    rw [this]
    exact (e.continuousOn.comp_continuous (continuous_subtype_val.comp continuous_subtype_val)
      fun x ↦ x.2.1).subtype_mk _
  continuousOn_invFun := by
    have h := (e.subtypeRestr' N).continuousOn_symm
    refine h.comp continuous_subtype_val.continuousOn fun z hz ↦ ⟨hz.1, hz.2⟩

variable {F} {e : PartialHomeomorph M E} {N : Set M} [Nonempty N]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [Nonempty ↑N] in
theorem IsAdaptedTo.mem (h : IsAdaptedTo F e N) {x : M} (hx : x ∈ e.source) (hxN : x ∈ N) :
    e x ∈ F := by
  have : e x ∈ e.target ∩ e.symm ⁻¹' N :=
    ⟨e.map_source hx, by rw [mem_preimage, e.left_inv hx]; exact hxN⟩
  rw [h.1] at this
  exact this.2

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [Nonempty ↑N] in
theorem IsAdaptedTo.symm_mem (h : IsAdaptedTo F e N) {y : E} (hy : y ∈ e.target)
    (hyF : y ∈ F) : e.symm y ∈ N := by
  have : y ∈ e.target ∩ (F : Set E) := ⟨hy, hyF⟩
  rw [← h.1] at this
  exact this.2

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
theorem IsAdaptedTo.coe_subChart_apply (h : IsAdaptedTo F e N) {x : N} (hx : (x : M) ∈ e.source) :
    (subChart F e N x : E) = e x := by
  change (subChartFun F e N x : E) = e x
  rw [subChartFun_of_mem F e N (h.mem hx x.2)]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
theorem IsAdaptedTo.coe_subChart_symm_apply (h : IsAdaptedTo F e N) {z : F}
    (hz : (z : E) ∈ e.target) : ((subChart F e N).symm z : M) = e.symm z :=
  e.coe_restrInv_of_mem (h.symm_mem hz z.2)

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
theorem IsAdaptedTo.subChart_source (h : IsAdaptedTo F e N) :
    (subChart F e N).source = Subtype.val ⁻¹' e.source := by
  ext x
  exact ⟨fun hx ↦ hx.1, fun hx ↦ ⟨hx, h.mem hx x.2⟩⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
theorem IsAdaptedTo.subChart_target (h : IsAdaptedTo F e N) :
    (subChart F e N).target = Subtype.val ⁻¹' e.target := by
  ext z
  exact ⟨fun hz ↦ hz.1, fun hz ↦ ⟨hz, h.symm_mem hz z.2⟩⟩

namespace RoughAtlas

variable (F) in
/-- **[GN26, Definition 3.5.14, p. 282]**: `N ⊆ M` is a **submanifold modeled on** the
subspace `F`: (S1) every point of `N` lies in the domain of a chart of the atlas adapted to `N`
and `F`, and, for `r = 0`, (S2) adapted charts agree on which points of `N` lie on the boundary
of `V ∩ F` relative to `F` (for `r ≥ 1` this is automatic, Remark 3.5.16(a)). -/
def IsSubmanifold (A : RoughAtlas r E M) (N : Set M) [Nonempty N] : Prop :=
  (∀ x ∈ N, ∃ e ∈ A.atlas, x ∈ e.source ∧ IsAdaptedTo F e N) ∧
  (r = 0 → ∀ e ∈ A.atlas, IsAdaptedTo F e N → ∀ e' ∈ A.atlas, IsAdaptedTo F e' N →
    ∀ x : N, (x : M) ∈ e.source → (x : M) ∈ e'.source →
      (subChart F e N x ∈ interior (Subtype.val ⁻¹' e.target : Set F) ↔
        subChart F e' N x ∈ interior (Subtype.val ⁻¹' e'.target : Set F)))

variable (F) in
/-- **[GN26, Definition 3.5.14, p. 282]**: a submanifold modeled on a closed subspace `F`
is a manifold with rough boundary modeled on `F`, with the charts `e_N` induced by the adapted
charts. -/
def submanifold (A : RoughAtlas r E M) (N : Set M) [Nonempty N] (hF : IsClosed (F : Set E))
    (hN : A.IsSubmanifold F N) : RoughAtlas r F N where
  atlas := {f | ∃ e ∈ A.atlas, IsAdaptedTo F e N ∧ f = subChart F e N}
  isRoughChart := by
    rintro _ ⟨e, he, had, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [had.subChart_source]
      exact continuous_subtype_val.isOpen_preimage _ (A.isRoughChart e he).isOpen_source
    · rw [had.subChart_target]
      exact IsLocallyConvexSubset.preimage_clm F.subtypeL
        (A.isRoughChart e he).isLocallyConvexSubset_target
    · rw [had.subChart_target]
      exact had.2
  exists_mem_source x :=
    let ⟨e, he, hx, had⟩ := hN.1 x x.2
    ⟨_, ⟨e, he, had, rfl⟩, by rw [had.subChart_source]; exact hx⟩
  contDiffLCUpTo_trans := by
    rintro _ ⟨e, he, had, rfl⟩ _ ⟨e', he', had', rfl⟩
    have hTc : IsLocallyConvexSubset (e.target ∩ e.symm ⁻¹' e'.source) :=
      (A.isRoughChart e he).isLocallyConvexSubset_inter_preimage
        (A.isRoughChart e' he').isOpen_source
    have hTd : HasDenseInterior (e.target ∩ e.symm ⁻¹' e'.source) :=
      (A.isRoughChart e he).hasDenseInterior_inter_preimage (A.isRoughChart e' he').isOpen_source
    obtain ⟨O, hO, hOe⟩ := e.exists_isOpen_target_inter (A.isRoughChart e' he').isOpen_source
    have hD : (subChart F e N).target ∩ (subChart F e N).symm ⁻¹' (subChart F e' N).source =
        (Subtype.val ⁻¹' e.target : Set F) ∩ Subtype.val ⁻¹' O := by
      ext z
      rw [had.subChart_target, had'.subChart_source]
      constructor
      · rintro ⟨h1, h2⟩
        rw [mem_preimage, mem_preimage, had.coe_subChart_symm_apply h1] at h2
        have : (z : E) ∈ e.target ∩ e.symm ⁻¹' e'.source := ⟨h1, h2⟩
        rw [hOe] at this
        exact ⟨h1, this.2⟩
      · rintro ⟨h1, h2⟩
        have : (z : E) ∈ e.target ∩ O := ⟨h1, h2⟩
        rw [← hOe] at this
        refine ⟨h1, ?_⟩
        rw [mem_preimage, mem_preimage, had.coe_subChart_symm_apply h1]
        exact this.2
    have hDc : IsLocallyConvexSubset ((Subtype.val ⁻¹' e.target : Set F) ∩ Subtype.val ⁻¹' O) :=
      (IsLocallyConvexSubset.preimage_clm F.subtypeL
        (A.isRoughChart e he).isLocallyConvexSubset_target).inter_isOpen
        (hO.preimage continuous_subtype_val)
    have hDd : HasDenseInterior ((Subtype.val ⁻¹' e.target : Set F) ∩ Subtype.val ⁻¹' O) :=
      had.2.inter_isOpen (hO.preimage continuous_subtype_val)
    have hDT : MapsTo (Subtype.val : F → E)
        ((Subtype.val ⁻¹' e.target : Set F) ∩ Subtype.val ⁻¹' O)
        (e.target ∩ e.symm ⁻¹' e'.source) := fun z hz ↦ by
      have : (z : E) ∈ e.target ∩ O := hz
      rw [← hOe] at this
      exact this
    intro k hk
    rw [hD]
    refine (contDiffLC_subtype_iff hF.isSeqClosed hDc hDd).2 ?_
    have hcomp := ContDiffLC.comp hDd hTc hTd ((A.contDiffLCUpTo_trans e he e' he') k hk)
      (F.subtypeL.contDiffLC k hDd) hDT
    refine hcomp.congr fun z hz ↦ ?_
    have hz1 : (z : E) ∈ e.target := hz.1
    have hzT := hDT hz
    have hsrc : ((subChart F e N).symm z : M) ∈ e'.source := by
      rw [had.coe_subChart_symm_apply hz1]; exact hzT.2
    simp only [comp_apply]
    rw [had'.coe_subChart_apply hsrc, had.coe_subChart_symm_apply hz1]
    rfl
  mem_interior_of_eq_zero := by
    rintro hr _ ⟨e, he, had, rfl⟩ _ ⟨e', he', had', rfl⟩ x hx hint
    rw [had.subChart_source] at hx
    rw [had'.subChart_source] at hx
    rw [had.subChart_target] at hint
    rw [had'.subChart_target]
    exact (hN.2 hr e he had e' he' had' x hx.1 hx.2).1 hint

end RoughAtlas

end Submanifold

end LocallyConvex.Manifolds
