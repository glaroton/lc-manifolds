/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.RoughBoundary.Basic

/-!
# Open subsets, full submanifolds and corners of manifolds with rough boundary

Reference: H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups* (arXiv:2602.12362v1), §3.5.

## Main definitions

* `PartialHomeomorph.subtypeRestr'`: the restriction of a partial homeomorphism `M → E` to a
  subset `s ⊆ M`, with target `e(U_e ∩ s)`. Mathlib's `OpenPartialHomeomorph.subtypeRestr` needs
  open partial homeomorphisms and open `s`; rough charts have non-open targets.
* `RoughAtlas.restrict`: a nonempty open subset of a manifold with rough boundary (G–N,
  Example 3.5.4, p. 279).
* `RoughAtlas.IsFullSubmanifold`, `RoughAtlas.fullSubmanifold`: full submanifolds, subsets `N`
  such that `e(U_e ∩ N)` is locally convex with dense interior for charts around the points of
  `N` (G–N, Definition 3.5.19, p. 284).
* `quadrant`, `RoughAtlas.IsWithCorners`, `RoughAtlas.IsWithBoundary`: manifolds with corners
  and with boundary in the traditional sense, as manifolds with rough boundary modeled on `ℝ^ι`
  with charts into open subsets of `[0, ∞[^ι` or of a half-space (G–N, Remark 3.5.10, p. 281).

## Main results

* `RoughAtlas.boundary_restrict`: `∂U = U ∩ ∂M`.
* `RoughAtlas.boundary_fullSubmanifold`: `∂N = N ∩ (∂M ∪ (N \ N⁰))` (G–N, (3.24), p. 284), from
  `mem_interior_inter_preimage_iff`. Condition (A3) for `C^0` atlases follows from it, as G–N
  observe.
* `RoughAtlas.quadrantAtlas`, `boundary_quadrantAtlas`, `isWithCorners_quadrantAtlas`: the
  quadrant is a manifold with corners, with boundary the points with a vanishing coordinate.

## See also

Submanifolds modeled on closed subspaces (G–N, Definition 3.5.14) are in
`LocallyConvexManifolds.RoughBoundary.Subspace`.
-/

@[expose] public section

open Set Filter Function
open scoped Topology
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe u

/-! ### Restricting a partial homeomorphism to a subset -/

section Restrict

variable {M E : Type*} [TopologicalSpace M] [TopologicalSpace E]

open Classical in
/-- The inverse of `e` restricted to `s` (junk value outside `e⁻¹(s)`). -/
def _root_.PartialHomeomorph.restrInv (e : PartialHomeomorph M E) (s : Set M) [Nonempty s]
    (y : E) : s :=
  if h : e.symm y ∈ s then ⟨e.symm y, h⟩ else Classical.arbitrary s

theorem _root_.PartialHomeomorph.restrInv_of_mem (e : PartialHomeomorph M E) {s : Set M}
    [Nonempty s] {y : E} (h : e.symm y ∈ s) : e.restrInv s y = ⟨e.symm y, h⟩ := by
  simp only [PartialHomeomorph.restrInv, h, dite_true]

theorem _root_.PartialHomeomorph.coe_restrInv_of_mem (e : PartialHomeomorph M E) {s : Set M}
    [Nonempty s] {y : E} (h : e.symm y ∈ s) : (e.restrInv s y : M) = e.symm y := by
  rw [e.restrInv_of_mem h]

/-- The restriction of a partial homeomorphism `e : M → E` to a nonempty subset `s ⊆ M`, as a
partial homeomorphism `s → E` with source `s ∩ e.source` and target `e(s ∩ e.source)`. -/
def _root_.PartialHomeomorph.subtypeRestr' (e : PartialHomeomorph M E) (s : Set M) [Nonempty s] :
    PartialHomeomorph s E where
  toFun x := e x
  invFun := e.restrInv s
  source := Subtype.val ⁻¹' e.source
  target := e.target ∩ e.symm ⁻¹' s
  map_source' x hx := ⟨e.map_source hx, by
    simp only [mem_preimage, e.left_inv hx]; exact x.2⟩
  map_target' y hy := by
    change (e.restrInv s y : M) ∈ e.source
    rw [e.coe_restrInv_of_mem hy.2]
    exact e.map_target hy.1
  left_inv' x hx := by
    have h : e.symm (e x) ∈ s := by rw [e.left_inv hx]; exact x.2
    exact Subtype.ext ((e.coe_restrInv_of_mem h).trans (e.left_inv hx))
  right_inv' y hy := by
    rw [e.coe_restrInv_of_mem hy.2]
    exact e.right_inv hy.1
  continuousOn_toFun := e.continuousOn.comp continuous_subtype_val.continuousOn fun _ hx ↦ hx
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : (e.target ∩ e.symm ⁻¹' s).domRestrict (e.restrInv s) =
        fun y ↦ ⟨e.symm y, y.2.2⟩ := funext fun y ↦ by
          rw [domRestrict_apply, e.restrInv_of_mem y.2.2]
    rw [this]
    exact ((continuousOn_iff_continuous_domRestrict.1
      (e.continuousOn_symm.mono inter_subset_left))).subtype_mk _

@[simp] theorem _root_.PartialHomeomorph.subtypeRestr'_source (e : PartialHomeomorph M E)
    (s : Set M) [Nonempty s] : (e.subtypeRestr' s).source = Subtype.val ⁻¹' e.source := rfl

@[simp] theorem _root_.PartialHomeomorph.subtypeRestr'_target (e : PartialHomeomorph M E)
    (s : Set M) [Nonempty s] : (e.subtypeRestr' s).target = e.target ∩ e.symm ⁻¹' s := rfl

@[simp] theorem _root_.PartialHomeomorph.subtypeRestr'_apply (e : PartialHomeomorph M E)
    (s : Set M) [Nonempty s] (x : s) : e.subtypeRestr' s x = e x := rfl

theorem _root_.PartialHomeomorph.coe_subtypeRestr'_symm (e : PartialHomeomorph M E) {s : Set M}
    [Nonempty s] {y : E} (h : e.symm y ∈ s) : ((e.subtypeRestr' s).symm y : M) = e.symm y :=
  e.coe_restrInv_of_mem h

/-- Transition maps between restricted charts are restrictions of transition maps. -/
theorem _root_.PartialHomeomorph.subtypeRestr'_trans_eqOn (e e' : PartialHomeomorph M E)
    (s : Set M) [Nonempty s] :
    EqOn (e.subtypeRestr' s ∘ (e'.subtypeRestr' s).symm) (e ∘ e'.symm)
      (e'.target ∩ e'.symm ⁻¹' s) := fun y hy ↦ by
  simp only [comp_apply, PartialHomeomorph.subtypeRestr'_apply, e'.coe_subtypeRestr'_symm hy.2]

/-- The domain of the transition map between restricted charts. -/
theorem _root_.PartialHomeomorph.subtypeRestr'_trans_domain (e e' : PartialHomeomorph M E)
    (s : Set M) [Nonempty s] :
    (e'.subtypeRestr' s).target ∩ (e'.subtypeRestr' s).symm ⁻¹' (e.subtypeRestr' s).source =
      e'.target ∩ e'.symm ⁻¹' (s ∩ e.source) := by
  ext y
  simp only [PartialHomeomorph.subtypeRestr'_target, PartialHomeomorph.subtypeRestr'_source,
    mem_inter_iff, mem_preimage]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    rw [e'.coe_subtypeRestr'_symm h2] at h3
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2⟩, ?_⟩
    rw [e'.coe_subtypeRestr'_symm h2]
    exact h3

end Restrict

/-! ### Open subsets: Example 3.5.4 -/

section Atlas

variable {r : ℕ∞} {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type*} [TopologicalSpace M]

namespace RoughAtlas

/-- **Glöckner–Neeb, Example 3.5.4, p. 279**: a nonempty open subset `U` of a manifold with rough
boundary is a manifold with rough boundary, with the restrictions of the charts. -/
def restrict (A : RoughAtlas r E M) (U : Set M) (hU : IsOpen U) [Nonempty U] :
    RoughAtlas r E U where
  atlas := (fun e ↦ e.subtypeRestr' U) '' A.atlas
  isRoughChart := by
    rintro _ ⟨e, he, rfl⟩
    exact ⟨continuous_subtype_val.isOpen_preimage _ (A.isRoughChart e he).isOpen_source,
      (A.isRoughChart e he).isLocallyConvexSubset_inter_preimage hU,
      (A.isRoughChart e he).hasDenseInterior_inter_preimage hU⟩
  exists_mem_source x :=
    let ⟨e, he, hx⟩ := A.exists_mem_source x
    ⟨_, ⟨e, he, rfl⟩, hx⟩
  contDiffLCUpTo_trans := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    rw [e'.subtypeRestr'_trans_domain e U]
    refine ((A.contDiffLCUpTo_trans e he e' he').mono ?_
      ((A.isRoughChart e he).hasDenseInterior_inter_preimage
        (hU.inter (A.isRoughChart e' he').isOpen_source))).congr
      ((e'.subtypeRestr'_trans_eqOn e U).symm.mono
        fun y (hy : y ∈ e.target ∩ e.symm ⁻¹' (U ∩ e'.source)) ↦
          (⟨hy.1, hy.2.1⟩ : y ∈ e.target ∩ e.symm ⁻¹' U))
    exact fun y hy ↦ ⟨hy.1, hy.2.2⟩
  mem_interior_of_eq_zero := by
    rintro hr _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩ x hx hint
    change e x ∈ interior (e.target ∩ e.symm ⁻¹' U) at hint
    change e' x ∈ interior (e'.target ∩ e'.symm ⁻¹' U)
    rw [e.interior_target_inter_preimage hU] at hint
    rw [e'.interior_target_inter_preimage hU]
    refine ⟨A.mem_interior_of_eq_zero hr e he e' he' x hx hint.1, ?_⟩
    rw [mem_preimage, e'.left_inv hx.2]
    exact x.2

/-- The boundary of an open subset `U` is `U ∩ ∂M`. -/
theorem boundary_restrict (A : RoughAtlas r E M) (U : Set M) (hU : IsOpen U) [Nonempty U] :
    (A.restrict U hU).boundary = Subtype.val ⁻¹' A.boundary := by
  ext x
  obtain ⟨e, he, hx⟩ := A.exists_mem_source x
  rw [(A.restrict U hU).mem_boundary_iff (e := e.subtypeRestr' U) ⟨e, he, rfl⟩ hx, mem_preimage,
    A.mem_boundary_iff he hx]
  change e x ∉ interior (e.target ∩ e.symm ⁻¹' U) ↔ _
  rw [e.interior_target_inter_preimage hU]
  simp only [mem_inter_iff, mem_preimage, e.left_inv hx, Subtype.coe_prop, and_true]

/-! ### Full submanifolds: Definition 3.5.19 -/

/-- `e` is **adapted** to the full submanifold `N`: the image `e(U_e ∩ N)` is locally convex with
dense interior. -/
def IsAdapted (e : PartialHomeomorph M E) (N : Set M) : Prop :=
  IsLocallyConvexSubset (e.target ∩ e.symm ⁻¹' N) ∧ HasDenseInterior (e.target ∩ e.symm ⁻¹' N)

/-- **Glöckner–Neeb, Definition 3.5.19, p. 284**: `N ⊆ M` is a **full submanifold** if every point
of `N` lies in the domain of a chart `e` of the atlas for which `e(U_e ∩ N)` is a locally convex
subset of `E` with dense interior. (For the maximal atlas, pass `A.maximal`.) -/
def IsFullSubmanifold (A : RoughAtlas r E M) (N : Set M) : Prop :=
  ∀ x ∈ N, ∃ e ∈ A.atlas, x ∈ e.source ∧ IsAdapted e N

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
/-- Interior points of `e(U_e ∩ N)` are the images of the points of the interior of `N` that are
mapped into the interior of the target. -/
theorem mem_interior_inter_preimage_iff {e : PartialHomeomorph M E} (he : IsRoughChart e)
    {N : Set M} {x : M} (hx : x ∈ e.source) :
    e x ∈ interior (e.target ∩ e.symm ⁻¹' N) ↔ e x ∈ interior e.target ∧ x ∈ interior N := by
  constructor
  · intro h
    refine ⟨interior_mono inter_subset_left h, ?_⟩
    have hO : IsOpen (e.source ∩ e ⁻¹' interior (e.target ∩ e.symm ⁻¹' N)) :=
      e.continuousOn.isOpen_inter_preimage he.isOpen_source isOpen_interior
    refine interior_maximal (fun z hz ↦ ?_) hO ⟨hx, h⟩
    have h2 := (interior_subset hz.2).2
    rwa [mem_preimage, e.left_inv hz.1] at h2
  · rintro ⟨h1, h2⟩
    obtain ⟨W, hW, hWe⟩ := e.exists_isOpen_target_inter (s := interior N) isOpen_interior
    have hsub : interior e.target ∩ W ⊆ e.target ∩ e.symm ⁻¹' N := fun y hy ↦ by
      have hy' : y ∈ e.target ∩ W := ⟨interior_subset hy.1, hy.2⟩
      rw [← hWe] at hy'
      exact ⟨hy'.1, (interior_subset : interior N ⊆ N) hy'.2⟩
    refine interior_maximal hsub (isOpen_interior.inter hW) ⟨h1, ?_⟩
    have : e x ∈ e.target ∩ e.symm ⁻¹' interior N :=
      ⟨e.map_source hx, by rw [mem_preimage, e.left_inv hx]; exact h2⟩
    rw [hWe] at this
    exact this.2

/-- **Glöckner–Neeb, Definition 3.5.19, p. 284**: a nonempty full submanifold `N` is a manifold
with rough boundary, with the restrictions of the adapted charts. -/
def fullSubmanifold (A : RoughAtlas r E M) (N : Set M) [Nonempty N]
    (hN : A.IsFullSubmanifold N) : RoughAtlas r E N where
  atlas := {f | ∃ e ∈ A.atlas, IsAdapted e N ∧ f = e.subtypeRestr' N}
  isRoughChart := by
    rintro _ ⟨e, he, had, rfl⟩
    exact ⟨continuous_subtype_val.isOpen_preimage _ (A.isRoughChart e he).isOpen_source, had.1,
      had.2⟩
  exists_mem_source x :=
    let ⟨e, he, hx, had⟩ := hN x x.2
    ⟨_, ⟨e, he, had, rfl⟩, hx⟩
  contDiffLCUpTo_trans := by
    rintro _ ⟨e, he, had, rfl⟩ _ ⟨e', he', -, rfl⟩
    rw [e'.subtypeRestr'_trans_domain e N]
    obtain ⟨O, hO, hOe⟩ := e.exists_isOpen_target_inter (A.isRoughChart e' he').isOpen_source
    have hdom : e.target ∩ e.symm ⁻¹' (N ∩ e'.source) = (e.target ∩ e.symm ⁻¹' N) ∩ O := by
      ext y
      constructor
      · rintro ⟨h1, h2, h3⟩
        have : y ∈ e.target ∩ e.symm ⁻¹' e'.source := ⟨h1, h3⟩
        rw [hOe] at this
        exact ⟨⟨h1, h2⟩, this.2⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        have : y ∈ e.target ∩ O := ⟨h1, h3⟩
        rw [← hOe] at this
        exact ⟨h1, h2, this.2⟩
    have hd : HasDenseInterior (e.target ∩ e.symm ⁻¹' (N ∩ e'.source)) := by
      rw [hdom]; exact had.2.inter_isOpen hO
    refine ((A.contDiffLCUpTo_trans e he e' he').mono
      (fun y (hy : y ∈ e.target ∩ e.symm ⁻¹' (N ∩ e'.source)) ↦
        (⟨hy.1, hy.2.2⟩ : y ∈ e.target ∩ e.symm ⁻¹' e'.source)) hd).congr
      ((e'.subtypeRestr'_trans_eqOn e N).symm.mono
        fun y (hy : y ∈ e.target ∩ e.symm ⁻¹' (N ∩ e'.source)) ↦
          (⟨hy.1, hy.2.1⟩ : y ∈ e.target ∩ e.symm ⁻¹' N))
  mem_interior_of_eq_zero := by
    rintro hr _ ⟨e, he, -, rfl⟩ _ ⟨e', he', -, rfl⟩ x hx hint
    change e x ∈ interior (e.target ∩ e.symm ⁻¹' N) at hint
    change e' x ∈ interior (e'.target ∩ e'.symm ⁻¹' N)
    rw [mem_interior_inter_preimage_iff (A.isRoughChart e he) hx.1] at hint
    rw [mem_interior_inter_preimage_iff (A.isRoughChart e' he') hx.2]
    exact ⟨A.mem_interior_of_eq_zero hr e he e' he' x hx hint.1, hint.2⟩

/-- **The boundary of a full submanifold** (Glöckner–Neeb, (3.24), p. 284):
`∂N = N ∩ (∂M ∪ (N \ N⁰))`, where `N⁰` is the interior of `N` in `M`. -/
theorem boundary_fullSubmanifold (A : RoughAtlas r E M) (N : Set M) [Nonempty N]
    (hN : A.IsFullSubmanifold N) :
    (A.fullSubmanifold N hN).boundary = {x : N | (x : M) ∈ A.boundary ∨ (x : M) ∉ interior N} := by
  ext x
  obtain ⟨e, he, hx, had⟩ := hN x x.2
  rw [(A.fullSubmanifold N hN).mem_boundary_iff (e := e.subtypeRestr' N) ⟨e, he, had, rfl⟩ hx]
  change _ ↔ ((x : M) ∈ A.boundary ∨ (x : M) ∉ interior N)
  rw [A.mem_boundary_iff he hx]
  change e x ∉ interior (e.target ∩ e.symm ⁻¹' N) ↔ _
  rw [mem_interior_inter_preimage_iff (A.isRoughChart e he) hx]
  tauto

end RoughAtlas

end Atlas

/-! ### Manifolds with boundary and with corners: Remark 3.5.10 -/

section Corners

variable (ι : Type u) [Finite ι]

/-- The quadrant `[0, ∞[^ι ⊆ ℝ^ι`. -/
def quadrant : Set (ι → ℝ) := Set.pi univ fun _ ↦ Ici 0

theorem interior_quadrant : interior (quadrant ι) = Set.pi univ fun _ ↦ Ioi 0 := by
  rw [quadrant, interior_pi_set finite_univ]
  simp only [interior_Ici]

/-- The closed half-space `{x : ℝ^ι | 0 ≤ x i₀}`, a model of manifolds with boundary
(`ℝ^{n-1} × [0, ∞[`). -/
def coordHalfSpace (i₀ : ι) : Set (ι → ℝ) := {x | 0 ≤ x i₀}

namespace RoughAtlas

variable {r : ℕ∞} {M : Type*} [TopologicalSpace M]

/-- **Glöckner–Neeb, Remark 3.5.10(b), p. 281**: a manifold with rough boundary modeled on `ℝ^ι`
is a **manifold with corners** if its maximal atlas contains charts around every point whose
ranges are open subsets of the quadrant `[0, ∞[^ι`. -/
def IsWithCorners (A : RoughAtlas r (ι → ℝ) M) : Prop :=
  ∀ x, ∃ e ∈ A.maximal.atlas, x ∈ e.source ∧ ∃ W : Set (ι → ℝ), IsOpen W ∧
    e.target = W ∩ quadrant ι

/-- **Glöckner–Neeb, Remark 3.5.10(a), p. 281**: a manifold with rough boundary modeled on `ℝ^ι`
is a **manifold with boundary** if its maximal atlas contains charts around every point whose
ranges are open subsets of the half-space `{x | 0 ≤ x i₀}`. -/
def IsWithBoundary (A : RoughAtlas r (ι → ℝ) M) (i₀ : ι) : Prop :=
  ∀ x, ∃ e ∈ A.maximal.atlas, x ∈ e.source ∧ ∃ W : Set (ι → ℝ), IsOpen W ∧
    e.target = W ∩ coordHalfSpace ι i₀

variable (r)

omit [Finite ι] in
theorem convex_quadrant : Convex ℝ (LocallyConvex.Manifolds.quadrant ι) :=
  convex_pi fun _ _ ↦ convex_Ici 0

theorem hasDenseInterior_quadrant : HasDenseInterior (LocallyConvex.Manifolds.quadrant ι) :=
  (convex_quadrant ι).hasDenseInterior ⟨fun _ ↦ 1, by rw [interior_quadrant]; simp⟩

instance : Nonempty (LocallyConvex.Manifolds.quadrant ι) :=
  ⟨⟨fun _ ↦ 0, by simp [LocallyConvex.Manifolds.quadrant]⟩⟩

/-- The quadrant `[0, ∞[^ι` as a manifold with rough boundary. -/
def quadrantAtlas : RoughAtlas r (ι → ℝ) (LocallyConvex.Manifolds.quadrant ι) :=
  ofSubset r (convex_quadrant ι).isLocallyConvexSubset (hasDenseInterior_quadrant ι)

/-- The boundary of the quadrant consists of the points with some vanishing coordinate. -/
theorem boundary_quadrantAtlas :
    (quadrantAtlas ι r).boundary =
      {x : LocallyConvex.Manifolds.quadrant ι | ∃ i, (x : ι → ℝ) i = 0} := by
  refine (boundary_ofSubset (r := r) (convex_quadrant ι).isLocallyConvexSubset
    (hasDenseInterior_quadrant ι)).trans ?_
  ext ⟨x, hx⟩
  change x ∉ interior (LocallyConvex.Manifolds.quadrant ι) ↔ ∃ i, x i = 0
  simp only [interior_quadrant, Set.mem_pi, mem_univ, mem_Ioi, true_implies, not_forall,
    not_lt]
  exact ⟨fun ⟨i, hi⟩ ↦ ⟨i, le_antisymm hi (hx i (mem_univ i))⟩, fun ⟨i, hi⟩ ↦ ⟨i, hi.le⟩⟩

/-- The quadrant is a manifold with corners. -/
theorem isWithCorners_quadrantAtlas : (quadrantAtlas ι r).IsWithCorners ι := fun _ ↦
  ⟨subsetChart (LocallyConvex.Manifolds.quadrant ι), (quadrantAtlas ι r).subset_maximal rfl,
    by simp, univ, isOpen_univ, by simp⟩

end RoughAtlas

end Corners

end LocallyConvex.Manifolds
