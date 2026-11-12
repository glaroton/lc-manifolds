/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.RoughBoundary.Subspace

/-!
# Graphs of maps into manifolds without boundary

Let `M` be a `C^r` manifold with rough boundary modeled on `E`, `N` a `C^r` manifold without
boundary modeled on `F` (a rough atlas whose charts have open targets), and `f : M → N` a `C^r`
map. Then the graph of `f` is a submanifold of `M × N` modeled on the closed subspace
`E × {0}` of `E × F` (`horizontal E F`), with boundary `{(x, f x) : x ∈ ∂M}`
[GN26, Proposition 3.5.17, pp. 283–284].

## Main definitions

* `roughGraphChart φ ψ f`: for charts `φ` of `M` and `ψ` of `N`, the chart
  `θ(x, y) = (φ x, ψ y - ψ (f x))` of `M × N` on `(U_φ ∩ f⁻¹ U_ψ) × U_ψ`, which is
  `g ∘ (φ × ψ)` for the `C^r` diffeomorphism `g(z, w) = (z, w - h z)`, `h = ψ ∘ f ∘ φ⁻¹`.

## Main results

* `RoughAtlas.isCompatible_roughGraphChart`: `θ` is compatible with the product atlas.
* `isAdaptedTo_roughGraphChart`: `θ` is adapted to the graph and `E × {0}`.
* `RoughAtlas.exists_roughGraphChart`: condition (S1) for the graph, for all `r`.
* `RoughAtlas.isSubmanifold_graph`, `RoughAtlas.graphSubmanifold`,
  `RoughAtlas.boundary_graphSubmanifold`: for `r ≥ 1`, the graph is a submanifold, with the
  asserted boundary.

## Implementation notes

* G–N normalize `φ(x) = 0`, `ψ(f x) = 0` and shrink `U_φ` so that `f(U_φ) ⊆ U_ψ`. We do not
  normalize, and build the shrinking into the source of `θ`. Mathlib has no composition of
  partial homeomorphisms with non-open targets, so `θ` is defined directly.
* The target of `θ` is `(V'_φ × F) ∩ O` for an open `O`, with `V'_φ = φ(U_φ ∩ f⁻¹ U_ψ)`
  (`roughGraphChart_target_eq`); this is where the openness of the targets of the charts of `N` is
  used ([GN26, Example 3.5.18]: for `N = [0, ∞[` and `f(x) = x²` the graph is not a submanifold).
* For `r = 0`, G–N obtain the graph as a submanifold *with prescribed boundary* (3.5.15), since
  condition (S2) has to be checked against all adapted charts of `M × N`. We prove (S1) for all
  `r`, and the submanifold structure and its boundary for `r ≥ 1`, where (S2) is automatic.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
  (page numbers refer to arXiv:2602.12362v1)
-/

@[expose] public section

open Set Function Topology
open LocallyConvex.Analysis

namespace LocallyConvex.Manifolds

universe u

/-! ### The graph and the subspace `E × {0}` -/

section Graph

variable {M N : Type*}

/-- Membership in the graph `univ.graphOn f = {(x, f x) : x ∈ M}`. -/
theorem mem_graphOn_univ_iff {f : M → N} {p : M × N} : p ∈ univ.graphOn f ↔ p.2 = f p.1 := by
  simp [eq_comm]

instance [Nonempty M] (f : M → N) : Nonempty (univ.graphOn f) :=
  ⟨⟨(Classical.arbitrary M, f (Classical.arbitrary M)), by simp⟩⟩

end Graph

section Horizontal

variable {E : Type u} [AddCommGroup E] [Module ℝ E] {F : Type u} [AddCommGroup F] [Module ℝ F]

variable (E F) in
/-- The closed subspace `E × {0}` of `E × F`. -/
def horizontal : Submodule ℝ (E × F) := LinearMap.ker (LinearMap.snd ℝ E F)

@[simp] theorem mem_horizontal {q : E × F} : q ∈ horizontal E F ↔ q.2 = 0 := by
  simp [horizontal]

theorem isClosed_horizontal [TopologicalSpace E] [TopologicalSpace F] [T2Space F] :
    IsClosed (horizontal E F : Set (E × F)) := by
  have : (horizontal E F : Set (E × F)) = {q | q.2 = 0} := by ext; simp
  rw [this]
  exact isClosed_eq continuous_snd continuous_const

/-- `E × {0}` is homeomorphic to `E`, through the first projection. -/
def horizontalEquiv (E F : Type u) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] : horizontal E F ≃ₜ E where
  toFun p := (p : E × F).1
  invFun z := ⟨(z, 0), by simp⟩
  left_inv p := Subtype.ext (Prod.ext rfl (mem_horizontal.mp p.2).symm)
  right_inv _ := rfl
  continuous_toFun := continuous_fst.comp continuous_subtype_val
  continuous_invFun := (continuous_id.prodMk continuous_const).subtype_mk _

@[simp] theorem horizontalEquiv_apply [TopologicalSpace E] [TopologicalSpace F]
    (p : horizontal E F) :
    horizontalEquiv E F p = (p : E × F).1 := rfl

end Horizontal

/-! ### The graph chart -/

section Chart

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  {M : Type*} [TopologicalSpace M] {N : Type*} [TopologicalSpace N]

variable (φ : PartialHomeomorph M E) (ψ : PartialHomeomorph N F) (f : M → N)

/-- The local representative `h = ψ ∘ f ∘ φ⁻¹`. -/
abbrev graphRep (z : E) : F := ψ (f (φ.symm z))

/-- The domain `V'_φ = φ(U_φ ∩ f⁻¹ U_ψ)` of `graphRep`. -/
abbrev graphDom : Set E := φ.target ∩ φ.symm ⁻¹' (f ⁻¹' ψ.source)

variable {f} in
omit [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F] [IsTopologicalAddGroup F] in
theorem continuousOn_graphRep (hf : Continuous f) :
    ContinuousOn (graphRep φ ψ f) (graphDom φ ψ f) :=
  ψ.continuousOn.comp ((hf.comp_continuousOn φ.continuousOn_symm).mono inter_subset_left)
    fun _ hz ↦ hz.2

variable {f} in
/-- **The graph chart** [GN26, proof of Proposition 3.5.17]: `θ = g ∘ (φ × ψ)`,
`θ(x, y) = (φ x, ψ y - ψ (f x))`, on `(U_φ ∩ f⁻¹ U_ψ) × U_ψ`. -/
def roughGraphChart (hf : Continuous f) : PartialHomeomorph (M × N) (E × F) where
  toFun p := (φ p.1, ψ p.2 - ψ (f p.1))
  invFun q := (φ.symm q.1, ψ.symm (q.2 + graphRep φ ψ f q.1))
  source := (φ.source ∩ f ⁻¹' ψ.source) ×ˢ ψ.source
  target := {q | q.1 ∈ graphDom φ ψ f ∧ q.2 + graphRep φ ψ f q.1 ∈ ψ.target}
  map_source' p (hp : p ∈ (φ.source ∩ f ⁻¹' ψ.source) ×ˢ ψ.source) := by
    refine ⟨⟨φ.map_source hp.1.1, ?_⟩, ?_⟩
    · simp only [mem_preimage, φ.left_inv hp.1.1]; exact hp.1.2
    · simp only [graphRep, φ.left_inv hp.1.1, sub_add_cancel]; exact ψ.map_source hp.2
  map_target' q (hq : q ∈ {q : E × F | q.1 ∈ graphDom φ ψ f ∧
      q.2 + graphRep φ ψ f q.1 ∈ ψ.target}) := ⟨⟨φ.map_target hq.1.1, hq.1.2⟩, ψ.map_target hq.2⟩
  left_inv' p (hp : p ∈ (φ.source ∩ f ⁻¹' ψ.source) ×ˢ ψ.source) := by
    simp only [graphRep, φ.left_inv hp.1.1, sub_add_cancel, ψ.left_inv hp.2]
  right_inv' q (hq : q ∈ {q : E × F | q.1 ∈ graphDom φ ψ f ∧
      q.2 + graphRep φ ψ f q.1 ∈ ψ.target}) := by
    simp only
    rw [ψ.right_inv hq.2, φ.right_inv hq.1.1, graphRep, add_sub_cancel_right]
  continuousOn_toFun := by
    show ContinuousOn _ ((φ.source ∩ f ⁻¹' ψ.source) ×ˢ ψ.source)
    refine (φ.continuousOn.comp continuousOn_fst
      fun p (hp : p ∈ (φ.source ∩ f ⁻¹' ψ.source) ×ˢ ψ.source) ↦ hp.1.1).prodMk
      ((ψ.continuousOn.comp continuousOn_snd
        fun p (hp : p ∈ (φ.source ∩ f ⁻¹' ψ.source) ×ˢ ψ.source) ↦ hp.2).sub ?_)
    exact ψ.continuousOn.comp (hf.comp continuous_fst).continuousOn
      fun p (hp : p ∈ (φ.source ∩ f ⁻¹' ψ.source) ×ˢ ψ.source) ↦ hp.1.2
  continuousOn_invFun := by
    show ContinuousOn _ {q : E × F | q.1 ∈ graphDom φ ψ f ∧ q.2 + graphRep φ ψ f q.1 ∈ ψ.target}
    refine (φ.continuousOn_symm.comp continuousOn_fst fun q (hq : q ∈ {q : E × F |
      q.1 ∈ graphDom φ ψ f ∧ q.2 + graphRep φ ψ f q.1 ∈ ψ.target}) ↦ hq.1.1).prodMk ?_
    refine ψ.continuousOn_symm.comp (continuousOn_snd.add ?_) fun q hq ↦ hq.2
    exact (continuousOn_graphRep φ ψ hf).comp continuousOn_fst fun q hq ↦ hq.1

variable {f}

omit [AddCommGroup E] [Module ℝ E] [Module ℝ F] in
@[simp] theorem roughGraphChart_apply (hf : Continuous f) (p : M × N) :
    roughGraphChart φ ψ hf p = (φ p.1, ψ p.2 - ψ (f p.1)) := rfl

omit [AddCommGroup E] [Module ℝ E] [Module ℝ F] in
@[simp] theorem roughGraphChart_symm_apply (hf : Continuous f) (q : E × F) :
    (roughGraphChart φ ψ hf).symm q = (φ.symm q.1, ψ.symm (q.2 + graphRep φ ψ f q.1)) := rfl

omit [AddCommGroup E] [Module ℝ E] [Module ℝ F] in
theorem roughGraphChart_source (hf : Continuous f) :
    (roughGraphChart φ ψ hf).source = (φ.source ∩ f ⁻¹' ψ.source) ×ˢ ψ.source := rfl

omit [AddCommGroup E] [Module ℝ E] [Module ℝ F] in
theorem roughGraphChart_target (hf : Continuous f) :
    (roughGraphChart φ ψ hf).target =
      {q | q.1 ∈ graphDom φ ψ f ∧ q.2 + graphRep φ ψ f q.1 ∈ ψ.target} := rfl

omit [AddCommGroup E] [Module ℝ E] [Module ℝ F] in
/-- The target of `θ` is relatively open in `V'_φ × F` when `ψ` has open target. -/
theorem roughGraphChart_target_eq (hf : Continuous f) (hψ : IsOpen ψ.target) :
    ∃ O : Set (E × F), IsOpen O ∧
      (roughGraphChart φ ψ hf).target = (graphDom φ ψ f ×ˢ univ) ∩ O := by
  have hk : ContinuousOn (fun q : E × F ↦ q.2 + graphRep φ ψ f q.1) (graphDom φ ψ f ×ˢ univ) :=
    continuousOn_snd.add ((continuousOn_graphRep φ ψ hf).comp continuousOn_fst fun q hq ↦ hq.1)
  obtain ⟨O, hO, h⟩ := continuousOn_iff'.mp hk ψ.target hψ
  refine ⟨O, hO, ?_⟩
  ext q
  have hq := Set.ext_iff.mp h q
  simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true] at hq
  simp only [roughGraphChart_target, mem_ofPred_eq, mem_inter_iff, mem_prod, mem_univ, and_true]
  tauto

/-- The graph chart is a rough chart when `φ` and `ψ` are and `ψ` has open target. -/
theorem isRoughChart_roughGraphChart [LocallyConvexSpace ℝ E] [LocallyConvexSpace ℝ F]
    (hf : Continuous f) (hφ : IsRoughChart φ) (hψ : IsRoughChart ψ)
    (hψo : IsOpen ψ.target) : IsRoughChart (roughGraphChart φ ψ hf) := by
  obtain ⟨O, hO, h⟩ := roughGraphChart_target_eq φ ψ hf hψo
  have hs : IsOpen (f ⁻¹' ψ.source) := hψ.isOpen_source.preimage hf
  refine ⟨(hφ.isOpen_source.inter hs).prod hψ.isOpen_source, ?_, ?_⟩
  · rw [h]
    exact ((hφ.isLocallyConvexSubset_inter_preimage hs).prod
      isLocallyConvexSubset_univ).inter_isOpen hO
  · rw [h]
    exact (hφ.hasDenseInterior_inter_preimage hs).prod_univ.inter_isOpen hO

omit [AddCommGroup E] [Module ℝ E] in
/-- A point of the target of `θ` is interior if and only if its first coordinate is interior in
the target of `φ`. -/
theorem mem_interior_roughGraphChart_target_iff (hf : Continuous f) (hψ : IsRoughChart ψ)
    (hψo : IsOpen ψ.target) {q : E × F}
    (hq : q ∈ (roughGraphChart φ ψ hf).target) :
    q ∈ interior (roughGraphChart φ ψ hf).target ↔ q.1 ∈ interior φ.target := by
  obtain ⟨O, hO, h⟩ := roughGraphChart_target_eq φ ψ hf hψo
  rw [h] at hq ⊢
  rw [interior_inter, hO.interior_eq, interior_prod_eq, interior_univ, graphDom,
    φ.interior_target_inter_preimage (hψ.isOpen_source.preimage hf)]
  simp only [mem_inter_iff, mem_prod, mem_univ, and_true] at hq ⊢
  tauto

/-- The target of `θ` meets `E × {0}` in `V'_φ × {0}`. -/
theorem preimage_val_roughGraphChart_target (hf : Continuous f) :
    (Subtype.val ⁻¹' (roughGraphChart φ ψ hf).target : Set (horizontal E F)) =
      horizontalEquiv E F ⁻¹' graphDom φ ψ f := by
  ext p
  have hp : (p : E × F).2 = 0 := mem_horizontal.mp p.2
  simp only [mem_preimage, roughGraphChart_target, mem_ofPred_eq, horizontalEquiv_apply, hp,
    zero_add, and_iff_left_iff_imp]
  exact fun h ↦ ψ.map_source h.2

/-- **The graph chart is adapted** to the graph and to `E × {0}` [GN26, proof of
Proposition 3.5.17]: `θ((U_φ × U_ψ) ∩ graph(f)) = V'_φ × {0}`. -/
theorem isAdaptedTo_roughGraphChart (hf : Continuous f) (hφ : IsRoughChart φ)
    (hψ : IsRoughChart ψ) :
    IsAdaptedTo (horizontal E F) (roughGraphChart φ ψ hf) (univ.graphOn f) := by
  refine ⟨?_, ?_⟩
  · ext q
    simp only [mem_inter_iff, mem_preimage, mem_graphOn_univ_iff, roughGraphChart_symm_apply,
      SetLike.mem_coe,
      mem_horizontal]
    refine and_congr_right fun hq ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · have h' := congrArg ψ h
      rw [ψ.right_inv hq.2] at h'
      exact add_eq_right.mp h'
    · rw [h, zero_add, graphRep, ψ.left_inv hq.1.2]
  · rw [preimage_val_roughGraphChart_target]
    intro p hp
    rw [← (horizontalEquiv E F).preimage_interior, ← (horizontalEquiv E F).preimage_closure]
    exact hφ.hasDenseInterior_inter_preimage (hψ.isOpen_source.preimage hf) hp

end Chart

/-! ### The graph as a submanifold -/

namespace RoughAtlas

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {M : Type*} [TopologicalSpace M] {N : Type*} [TopologicalSpace N] {r : ℕ∞}

variable (E) in
/-- The charts of an ordinary manifold have open targets. -/
theorem isOpen_target_ofChartedSpace [ChartedSpace E M] [MBManifold E M]
    {e : PartialHomeomorph M E} (he : e ∈ (ofChartedSpace r E M).atlas) : IsOpen e.target := by
  obtain ⟨e, -, rfl⟩ := he
  exact e.open_target

variable (A : RoughAtlas r E M) (B : RoughAtlas r F N) (hB : ∀ e ∈ B.atlas, IsOpen e.target)
  {f : M → N} (hf : A.ContMDiff B r f)
include hB hf

/-- **The graph chart is a chart of `M × N`** [GN26, proof of Proposition 3.5.17]: it
is compatible with the product atlas. The transition maps factor through `φ × ψ` and the `C^r`
maps `g(z, w) = (z, w - h z)` and `g⁻¹(z, w) = (z, w + h z)`, `h = ψ ∘ f ∘ φ⁻¹`. -/
theorem isCompatible_roughGraphChart {φ : PartialHomeomorph M E} {ψ : PartialHomeomorph N F}
    (hφ : φ ∈ A.atlas) (hψ : ψ ∈ B.atlas) : (A.prod B).IsCompatible (roughGraphChart φ ψ hf.1) := by
  have hφr := A.isRoughChart φ hφ
  have hψr := B.isRoughChart ψ hψ
  have hθ := isRoughChart_roughGraphChart φ ψ hf.1 hφr hψr (hB ψ hψ)
  have hs : IsOpen (f ⁻¹' ψ.source) := hψr.isOpen_source.preimage hf.1
  have hD := hφr.hasDenseInterior_inter_preimage hs
  have hDl := hφr.isLocallyConvexSubset_inter_preimage hs
  have hSd : HasDenseInterior (graphDom φ ψ f ×ˢ (univ : Set F)) := hD.prod_univ
  have hSl : IsLocallyConvexSubset (graphDom φ ψ f ×ˢ (univ : Set F)) :=
    hDl.prod isLocallyConvexSubset_univ
  have hrep : ContDiffLCUpTo r (graphRep φ ψ f) (graphDom φ ψ f) := hf.2 φ hφ ψ hψ
  have hrep₁ : ContDiffLCUpTo r (fun q : E × F ↦ graphRep φ ψ f q.1)
      (graphDom φ ψ f ×ˢ (univ : Set F)) := by
    intro k hk
    have h := ContDiffLC.comp_clm_of_isOpenMap (ContinuousLinearMap.fst ℝ E F)
      (by rw [ContinuousLinearMap.coe_fst']; exact isOpenMap_fst) hD (hrep k hk)
    rwa [show (ContinuousLinearMap.fst ℝ E F) ⁻¹' graphDom φ ψ f = graphDom φ ψ f ×ˢ univ by
      ext; simp] at h
  have hg : ContDiffLCUpTo r (fun q : E × F ↦ (q.1, q.2 - graphRep φ ψ f q.1))
      (graphDom φ ψ f ×ˢ (univ : Set F)) := fun k hk ↦
    ((contDiffLC_id k hSd).fst hSd).prodMk hSd (((contDiffLC_id k hSd).snd hSd).sub hSd
      (hrep₁ k hk))
  have hg' : ContDiffLCUpTo r (fun q : E × F ↦ (q.1, q.2 + graphRep φ ψ f q.1))
      (graphDom φ ψ f ×ˢ (univ : Set F)) := fun k hk ↦
    ((contDiffLC_id k hSd).fst hSd).prodMk hSd (((contDiffLC_id k hSd).snd hSd).add hSd
      (hrep₁ k hk))
  have hP : φ.prod' ψ ∈ (A.prod B).atlas := mem_image2_of_mem hφ hψ
  have hPr := (A.prod B).isRoughChart _ hP
  refine ⟨hθ, fun c hc ↦ ⟨?_, ?_, ?_⟩⟩
  · -- `c ∘ θ⁻¹ = (c ∘ (φ × ψ)⁻¹) ∘ g⁻¹`
    have hcr := (A.prod B).isRoughChart c hc
    have hU := hθ.hasDenseInterior_inter_preimage hcr.isOpen_source
    have h₁ := (A.prod B).contDiffLCUpTo_trans _ hP c hc
    have h₂ := hg'.mono (V := (roughGraphChart φ ψ hf.1).target ∩
      (roughGraphChart φ ψ hf.1).symm ⁻¹' c.source) (fun q hq ↦ ⟨hq.1.1, mem_univ _⟩) hU
    refine (h₁.comp hU (hPr.isLocallyConvexSubset_inter_preimage hcr.isOpen_source)
      (hPr.hasDenseInterior_inter_preimage hcr.isOpen_source) h₂ ?_).congr ?_
    · intro q hq
      exact ⟨⟨hq.1.1.1, hq.1.2⟩, hq.2⟩
    · intro q _
      rfl
  · -- `θ ∘ c⁻¹ = g ∘ ((φ × ψ) ∘ c⁻¹)`
    have hcr := (A.prod B).isRoughChart c hc
    have hU := hcr.hasDenseInterior_inter_preimage hθ.isOpen_source
    have h₁ := ((A.prod B).contDiffLCUpTo_trans c hc _ hP).mono
      (V := c.target ∩ c.symm ⁻¹' (roughGraphChart φ ψ hf.1).source)
      (fun q hq ↦ ⟨hq.1, hq.2.1.1, hq.2.2⟩) hU
    refine (hg.comp hU hSl hSd h₁ ?_).congr ?_
    · intro q hq
      refine ⟨⟨φ.map_source hq.2.1.1, ?_⟩, mem_univ _⟩
      simp only [comp_apply, PartialHomeomorph.prod'_coe, Prod.map_fst, mem_preimage,
        φ.left_inv hq.2.1.1]
      exact hq.2.1.2
    · intro q hq
      simp only [comp_apply, PartialHomeomorph.prod'_coe, Prod.map_fst, Prod.map_snd,
        roughGraphChart_apply, graphRep, φ.left_inv hq.2.1.1]
  · intro _ x hx
    rw [mem_interior_roughGraphChart_target_iff φ ψ hf.1 hψr (hB ψ hψ)
      ((roughGraphChart φ ψ hf.1).map_source hx.1)]
    have hxP : x ∈ (φ.prod' ψ).source := ⟨hx.1.1.1, hx.1.2⟩
    rw [← (A.prod B).mem_interior_iff hP hc hxP hx.2]
    simp only [roughGraphChart_apply, PartialHomeomorph.prod'_target, PartialHomeomorph.prod'_coe,
      interior_prod_eq, (hB ψ hψ).interior_eq, mem_prod, Prod.map_fst, Prod.map_snd,
      ψ.map_source hx.1.2, and_true]

/-- **[GN26, Proposition 3.5.17], condition (S1)**: every point of the graph of a `C^r`
map `f : M → N` into a manifold without boundary lies in a chart of `M × N` adapted to the graph
and to `E × {0}`. -/
theorem exists_roughGraphChart {p : M × N} (hp : p ∈ univ.graphOn f) :
    ∃ θ ∈ (A.prod B).maximal.atlas, p ∈ θ.source ∧
      IsAdaptedTo (horizontal E F) θ (univ.graphOn f) := by
  obtain ⟨φ, hφ, hx⟩ := A.exists_mem_source p.1
  obtain ⟨ψ, hψ, hy⟩ := B.exists_mem_source (f p.1)
  refine ⟨roughGraphChart φ ψ hf.1, A.isCompatible_roughGraphChart B hB hf hφ hψ, ⟨⟨hx, hy⟩, ?_⟩,
    isAdaptedTo_roughGraphChart φ ψ hf.1 (A.isRoughChart φ hφ) (B.isRoughChart ψ hψ)⟩
  rw [mem_graphOn_univ_iff.mp hp]
  exact hy

/-- **[GN26, Proposition 3.5.17]**: for `r ≥ 1`, the graph of a `C^r` map into a
manifold without boundary is a submanifold of `M × N` modeled on `E × {0}`. -/
theorem isSubmanifold_graph [Nonempty M] (hr : r ≠ 0) :
    (A.prod B).maximal.IsSubmanifold (horizontal E F) (univ.graphOn f) :=
  ⟨fun _ hp ↦ A.exists_roughGraphChart B hB hf hp, fun h ↦ absurd h hr⟩

/-- The graph of a `C^r` map into a manifold without boundary, `r ≥ 1`, as a manifold with rough
boundary modeled on `E × {0}` [GN26, Proposition 3.5.17]. -/
def graphSubmanifold [Nonempty M] (hr : r ≠ 0) : RoughAtlas r (horizontal E F) (univ.graphOn f) :=
  (A.prod B).maximal.submanifold (horizontal E F) (univ.graphOn f) isClosed_horizontal
    (A.isSubmanifold_graph B hB hf hr)

/-- **[GN26, Proposition 3.5.17]**: the boundary of the graph is
`{(x, f x) : x ∈ ∂M}`. -/
theorem boundary_graphSubmanifold [Nonempty M] (hr : r ≠ 0) :
    (A.graphSubmanifold B hB hf hr).boundary =
      {p : univ.graphOn f | (p : M × N).1 ∈ A.boundary} := by
  ext p
  obtain ⟨φ, hφ, hx⟩ := A.exists_mem_source (p : M × N).1
  obtain ⟨ψ, hψ, hy⟩ := B.exists_mem_source (f (p : M × N).1)
  have hφr := A.isRoughChart φ hφ
  have hψr := B.isRoughChart ψ hψ
  have had := isAdaptedTo_roughGraphChart φ ψ hf.1 hφr hψr
  have hθ : roughGraphChart φ ψ hf.1 ∈ (A.prod B).maximal.atlas :=
    A.isCompatible_roughGraphChart B hB hf hφ hψ
  have hpθ : (p : M × N) ∈ (roughGraphChart φ ψ hf.1).source :=
    ⟨⟨hx, hy⟩, by rw [mem_graphOn_univ_iff.mp p.2]; exact hy⟩
  have hmem : subChart (horizontal E F) (roughGraphChart φ ψ hf.1) (univ.graphOn f) ∈
      (A.graphSubmanifold B hB hf hr).atlas := ⟨_, hθ, had, rfl⟩
  rw [(A.graphSubmanifold B hB hf hr).mem_boundary_iff hmem
    (by rw [had.subChart_source]; exact hpθ),
    had.subChart_target, preimage_val_roughGraphChart_target,
    ← (horizontalEquiv E F).preimage_interior]
  change ¬ (horizontalEquiv E F
    (subChart (horizontal E F) (roughGraphChart φ ψ hf.1) (univ.graphOn f) p) ∈
    interior (graphDom φ ψ f)) ↔ (p : M × N).1 ∈ A.boundary
  rw [A.mem_boundary_iff hφ hx, horizontalEquiv_apply, had.coe_subChart_apply hpθ,
    roughGraphChart_apply, graphDom,
    φ.interior_target_inter_preimage (hψr.isOpen_source.preimage hf.1)]
  simp only [mem_inter_iff, mem_preimage, φ.left_inv hx, hy, and_true]

end RoughAtlas

end LocallyConvex.Manifolds
