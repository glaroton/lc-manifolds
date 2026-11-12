/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.Manifold.Basic
public import LocallyConvexAnalysis.Calculus.DenseInterior.Basic

/-!
# Manifolds with rough boundary

We follow [GN26, §3.5 "Manifolds with boundary and generalizations", pp. 278–282].

A *rough chart* of a topological space `M` modeled on a locally convex space `E` is a
homeomorphism `φ : U_φ → V_φ` from an open subset of `M` onto a **locally convex subset with
dense interior** `V_φ ⊆ E` [GN26, Definition 3.5.1(a), p. 278]. Closed half-spaces, cubes
`[0, 1]ⁿ`, simplices and closed convex sets with nonempty interior are such subsets; open sets are
a special case. Since the `C^r` calculus of [LCA] (`LocallyConvex.Analysis.ContDiffLC`,
[GN26, §1.4]) works on these sets, `C^r`-compatibility of rough charts makes sense: the overlaps
`ψ(U_φ ∩ U_ψ)` are relatively open in `V_ψ`, hence again locally convex with dense interior
[GN26, Remark 3.5.2, p. 279].

## Design

Mathlib's `ChartedSpace` and `StructureGroupoid` are built on `OpenPartialHomeomorph`, whose
targets are open, so they do not fit. A rough atlas (`RoughAtlas r E M`) is therefore a set of
Mathlib `PartialHomeomorph M E`s (no openness built in) whose sources are open and whose targets
are locally convex with dense interior (`IsRoughChart`), covering `M` (axiom (A1)), with `C^r`
transition maps (axiom (A2)), and with the boundary compatibility axiom (A3) when `r = 0`.
The order of differentiability `r : ℕ∞` covers `r ∈ ℕ₀ ∪ {∞}` as in G–N; `C^r` on a subset means
`ContDiffLC k` for every `k ≤ r` (`ContDiffLCUpTo`). A `C^r` manifold with rough boundary is a
maximal rough atlas (`RoughManifold`); every rough atlas is contained in exactly one maximal
atlas (`RoughAtlas.maximal`, `RoughAtlas.maximal_atlas_eq`), and the boundary and the `C^r`
maps do not change when an atlas is replaced by its maximal atlas (`RoughAtlas.boundary_maximal`,
`RoughAtlas.contMDiff_maximal_iff`), so in practice one works with any atlas.

## Main definitions

* `ContDiffLCUpTo r f U`: `f` is `C^k` on `U` [GN26, Definition 1.4.4] for all `k ≤ r`.
* `IsRoughChart e`: open source, locally convex target with dense interior [GN26, 3.5.1(a)].
* `RoughAtlas r E M`: a `C^r` atlas of rough `E`-charts [GN26, 3.5.1(a)].
* `RoughAtlas.IsCompatible`, `RoughAtlas.maximal`, `RoughAtlas.IsMaximal`, `RoughManifold`:
  maximal atlases, `C^r` manifolds with rough boundary [GN26, 3.5.1(b)].
* `RoughAtlas.boundary`: the formal boundary `∂M` [GN26, 3.5.1(c)].
* `RoughAtlas.ContMDiff A B s f`: `C^s` maps between manifolds with rough boundary
  [GN26, Definition 3.5.11, p. 281].
* `RoughAtlas.ofChartedSpace`: a manifold modeled on `E` (`MBManifold`) as a manifold with rough
  boundary [GN26, Example 3.5.3(a), p. 279].
* `RoughAtlas.prod`: products [GN26, Example 3.5.5, p. 279].
* `RoughAtlas.ofSubset`, `RoughAtlas.ofConvex`: a locally convex subset with dense interior
  (for instance a convex set with nonempty interior), with the single chart given by the
  inclusion [GN26, Example 3.5.3(b), p. 279]; `RoughAtlas.unitInterval`, `RoughAtlas.halfSpace`.

## Main results

* `ContDiffLC.mem_interior_of_rightInvOn`: the analytic core of [GN26, Lemma 3.5.6
  (pp. 279–280)]: a `C^1` map with a `C^1` right inverse sends interior points to interior points.
  `RoughAtlas.mem_interior_iff`: **the boundary is well defined**: interior points in one chart
  are interior points in every chart; for `r ≥ 1` this is Lemma 3.5.6, for `r = 0` it is (A3).
  `RoughAtlas.mem_boundary_iff`: `x ∈ ∂M` if and only if `φ(x) ∉ V_φ⁰` for one (equivalently,
  every) chart `φ` at `x`.
* `RoughAtlas.ContMDiff.comp`: composition of `C^s` maps [GN26, Proposition 3.5.12, p. 281];
  `RoughAtlas.contMDiff_id`, `RoughAtlas.contMDiff_maximal_iff` (chart independence).
* `RoughAtlas.boundary_ofChartedSpace`: ordinary manifolds have empty boundary [GN26, Remark 3.5.7,
  p. 280]. `RoughAtlas.boundary_ofSubset`: the formal boundary of a subset `U` is `U` minus the
  interior of `U` in `E` (Remark 3.5.7); `RoughAtlas.boundary_unitInterval`: the boundary of
  `[0, 1]` is `{0, 1}`. `RoughAtlas.boundary_prod`: `∂(M × N) = ∂M × N ∪ M × ∂N`.

## Infinite-dimensional subtleties

* **Invariance of the boundary needs differentiability and Hahn–Banach.** For `r ≥ 1` the proof of
  Lemma 3.5.6 separates a boundary point `z` of `V_ψ` from the interior of a convex neighborhood
  `W ⊆ V_ψ` of `z` by a continuous functional `λ` (Hahn–Banach, which needs the local convexity
  of the model space and of `V_ψ`), and then differentiates `t ↦ λ(κ(y + t u))` at an interior
  point `y` with `dκ(y) u = z - a`, `a` interior; the chain rule `d(κ ∘ κ⁻¹) = id` provides `u`.
  For `r = 0` the statement is false in infinite dimensions (a closed ball of an
  infinite-dimensional Banach space is homeomorphic to the whole space, [GN26, Remark 3.5.9,
  p. 280]), which is why (A3) is an axiom for `r = 0`. In finite dimensions it would follow from
  Invariance of Domain [GN26, Remark 3.5.8], which is not used here.
* **The rough boundary need not be a submanifold.** `∂M` is just a subset of `M` (corners of
  `[0, 1]²`, the boundary of a closed convex set with nonempty interior); no manifold structure on
  it is claimed or constructed.
* **Dense interior, not just nonempty interior.** [GN26, Example 3.5.3(b)] speaks of locally convex
  subsets "with non-empty interior"; since rough charts take values in sets with dense interior
  (Definition 3.5.1(a)), `RoughAtlas.ofSubset` assumes dense interior. For convex sets the two
  conditions agree (`Convex.hasDenseInterior`), see `RoughAtlas.ofConvex`.
* **No completeness** of the model spaces is assumed anywhere: the calculus of `ContDiffLC` works
  with weak integrals.
* **Hausdorffness.** G–N require `M` to be Hausdorff. As for `MBManifold` in this library, the
  Hausdorff property of `M` is not part of the structure; no result below needs it.

## Departures from Glöckner–Neeb

G–N prove Lemma 3.5.6 by computing `d/dt|_{t=0} λ(κ(y + t u)) = 0` at an interior maximum. Here
only the one-sided difference quotients for `t > 0` are used (they are `≤ 0` and converge to
`λ(dκ(y) u) > 0`), and the direction `v` with `λ(v) > 0` is `z - a` for an interior point `a` of
the convex neighborhood, so the case `E = {0}` needs no separate treatment. The chart-independence
of `C^s` maps is deduced from Proposition 3.5.12 by composing with the identity maps
`(M, A_max) → (M, A)` and `(N, B) → (N, B_max)`. We do not claim this argument is new.

The tangent bundle of a manifold with rough boundary is in `RoughBoundary/TangentBundle.lean`.

## Not done

Open submanifolds (Example 3.5.4),
submanifolds with prescribed boundary (Definition 3.5.14), the comparison of `ContMDiff` with
`ContMDiffMBOn` for `RoughAtlas.ofChartedSpace`, and manifolds with corners (Remark 3.5.10).

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

universe u v w

/-! ### `C^r` maps on locally convex subsets with dense interior, `r ∈ ℕ∞` -/

section UpTo

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {G : Type w} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
  [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G]

/-- `f` is `C^r` on `U`, `r ∈ ℕ₀ ∪ {∞}`, in the sense of [GN26, Definition 1.4.4]:
`ContDiffLC k f U` for every `k ∈ ℕ` with `k ≤ r`. For `r = ∞` this is `SmoothLC f U`. -/
def ContDiffLCUpTo (r : ℕ∞) (f : E → F) (U : Set E) : Prop :=
  ∀ k : ℕ, (k : ℕ∞) ≤ r → ContDiffLC k f U

namespace ContDiffLCUpTo

variable {r s : ℕ∞} {f : E → F} {U V : Set E}

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem continuousOn (hf : ContDiffLCUpTo r f U) : ContinuousOn f U :=
  (hf 0 bot_le).continuousOn

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem contDiffLC_one (hf : ContDiffLCUpTo r f U) (hr : r ≠ 0) : ContDiffLC 1 f U :=
  hf 1 (by simpa using Order.one_le_iff_ne_zero.mpr hr)

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem of_le (hf : ContDiffLCUpTo r f U) (hsr : s ≤ r) : ContDiffLCUpTo s f U :=
  fun k hk ↦ hf k (hk.trans hsr)

omit [LocallyConvexSpace ℝ E] [T2Space E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  [LocallyConvexSpace ℝ F] [T2Space F] in
theorem congr (hf : ContDiffLCUpTo r f U) {g : E → F} (h : EqOn f g U) :
    ContDiffLCUpTo r g U :=
  fun k hk ↦ (hf k hk).congr h

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
theorem mono (hf : ContDiffLCUpTo r f U) (hVU : V ⊆ U) (hV : HasDenseInterior V) :
    ContDiffLCUpTo r f V :=
  fun k hk ↦ (hf k hk).mono hVU hV

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem of_local (h : ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧ ContDiffLCUpTo r f (U ∩ W)) :
    ContDiffLCUpTo r f U :=
  fun k hk ↦ ContDiffLC.of_local fun x hx ↦
    let ⟨W, hW, hxW, hf⟩ := h x hx
    ⟨W, hW, hxW, hf k hk⟩

/-- Chain rule [GN26, Proposition 1.4.10]: only the domain `V` of `g` needs to be
locally convex. -/
theorem comp {g : F → G} {V : Set F} (hd : HasDenseInterior U) (hV : IsLocallyConvexSubset V)
    (hVd : HasDenseInterior V) (hg : ContDiffLCUpTo r g V) (hf : ContDiffLCUpTo r f U)
    (hUV : MapsTo f U V) : ContDiffLCUpTo r (g ∘ f) U :=
  fun k hk ↦ ContDiffLC.comp hd hV hVd (hg k hk) (hf k hk) hUV

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
/-- Maps that are smooth in the sense of Michal–Bastiani on an open set are `C^r` on it. -/
theorem of_smoothMBOn (hU : IsOpen U) (hf : SmoothMBOn f U) : ContDiffLCUpTo r f U :=
  fun k _ ↦ (contDiffLC_iff_contDiffMBOn hU).mpr (hf k)

end ContDiffLCUpTo

theorem contDiffLCUpTo_id (r : ℕ∞) {U : Set E} (hd : HasDenseInterior U) :
    ContDiffLCUpTo r (id : E → E) U :=
  fun k _ ↦ contDiffLC_id k hd

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
    [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] in
/-- Products of `C^r` maps on products of subsets with dense interior. -/
theorem ContDiffLCUpTo.prodMap {E₂ : Type u} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
    {r : ℕ∞} {f : E → F} {g : E₂ → G} {U : Set E} {V : Set E₂} (hU : HasDenseInterior U)
    (hV : HasDenseInterior V) (hf : ContDiffLCUpTo r f U) (hg : ContDiffLCUpTo r g V) :
    ContDiffLCUpTo r (Prod.map f g) (U ×ˢ V) :=
  fun k hk ↦ ContDiffLC.prodMap hU hV (hf k hk) (hg k hk)

/-! ### The analytic core of the invariance of the boundary -/

/-- **[GN26, Lemma 3.5.6 (analytic core), pp. 279–280].** Let `κ : U → U'` be `C^1`
between locally convex subsets with dense interior, with a `C^1` right inverse `μ : U' → U`
(`κ ∘ μ = id` on `U'`). If `y` is an interior point of `U` with `μ (κ y) = y`, then `κ y` is an
interior point of `U'`.

Proof: if `z = κ y` were not interior, a convex neighborhood `C = U' ∩ W` of `z` with nonempty
interior and a functional `λ` separating `z` from the interior of `C` (Hahn–Banach) would give
`λ ≤ λ z` on `C`. With `a` interior in `C` and `v = z - a`, the chain rule for `κ ∘ μ = id`
yields `u` with `dκ(y) u = v`, and the difference quotients of `t ↦ λ(κ(y + t u))` at `0⁺` are
`≤ 0` but converge to `λ v > 0`. -/
theorem ContDiffLC.mem_interior_of_rightInvOn {κ : E → F} {μ : F → E} {U : Set E} {U' : Set F}
    (hU : IsLocallyConvexSubset U) (hUd : HasDenseInterior U) (hU' : IsLocallyConvexSubset U')
    (hU'd : HasDenseInterior U') (hκ : ContDiffLC 1 κ U) (hμ : ContDiffLC 1 μ U')
    (hκU : MapsTo κ U U') (hμU : MapsTo μ U' U) (hinv : ∀ z ∈ U', κ (μ z) = z) {y : E}
    (hy : y ∈ interior U) (hμκ : μ (κ y) = y) : κ y ∈ interior U' := by
  by_contra hz
  have hzU' : κ y ∈ U' := hκU (interior_subset hy)
  obtain ⟨W, hW, hzW, -, hC, a, ha⟩ := hU'.exists_isOpen_convex_interior hU'd hzU' univ_mem
  have hzC : κ y ∉ interior (U' ∩ W) := fun h ↦ hz (interior_mono inter_subset_left h)
  obtain ⟨l, hl⟩ := geometric_hahn_banach_open_point hC.interior isOpen_interior hzC
  have hle : ∀ b ∈ U' ∩ W, l b ≤ l (κ y) := by
    intro b hb
    have hcl : U' ∩ W ⊆ closure (interior (U' ∩ W)) := hC.hasDenseInterior ⟨a, ha⟩
    exact closure_minimal (fun c hc ↦ (hl c hc).le) (isClosed_le l.continuous continuous_const)
      (hcl hb)
  set v := κ y - a with hv
  have hlv : 0 < l v := by rw [hv, map_sub]; linarith [hl a ha]
  -- the chain rule for `κ ∘ μ = id` at `κ y`
  set w := dLC μ U' (κ y, v)
  have hchain := ContDiffLC.dLC_comp hU'd hU hUd hκ hμ hμU hzU' v
  have hid : dLC (κ ∘ μ) U' = dLC id U' :=
    dLC_congr fun z hz ↦ hinv z (interior_subset hz)
  have hidv : dLC (id : F → F) U' (κ y, v) = v := by
    refine (ContDiffLC.of_hasDirDerivAt (k := 0) (D := Prod.snd) hU'd continuousOn_id
      (fun x _ h ↦ ?_) continuousOn_snd).2 ⟨hzU', mem_univ _⟩
    simpa using (ContinuousLinearMap.id ℝ F).hasDirDerivAt x h
  rw [hid, hidv, hμκ, dLC_of_mem_interior κ (p := (y, w)) hy] at hchain
  have hdir : HasDirDerivAt κ y w v := hchain ▸ hκ.hasDirDerivAt hy w
  -- along `t ↦ y + t w`, `t > 0` small, `κ` stays in `U' ∩ W`
  have hline : Tendsto (fun t : ℝ ↦ y + t • w) (𝓝 0) (𝓝 y) := by
    have : Continuous fun t : ℝ ↦ y + t • w := by fun_prop
    simpa using this.tendsto 0
  have hκc : ContinuousAt κ y :=
    hκ.continuousOn.continuousAt (mem_interior_iff_mem_nhds.mp hy)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), y + t • w ∈ U ∧ κ (y + t • w) ∈ W ∧ 0 < t := by
    have h1 := hline.eventually (mem_interior_iff_mem_nhds.mp hy)
    have h2 := (hκc.tendsto.comp hline).eventually (hW.mem_nhds hzW)
    filter_upwards [nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2, self_mem_nhdsWithin]
      with t ht1 ht2 ht3
    exact ⟨ht1, ht2, ht3⟩
  have hT : Tendsto (fun t : ℝ ↦ l (t⁻¹ • (κ (y + t • w) - κ y))) (𝓝[>] 0) (𝓝 (l v)) :=
    ((l.continuous.tendsto v).comp hdir).mono_left
      (nhdsWithin_mono _ fun t (ht : 0 < t) ↦ ht.ne')
  have hnp : l v ≤ 0 := by
    refine le_of_tendsto hT ?_
    filter_upwards [hev] with t ⟨ht1, ht2, ht3⟩
    rw [map_smul, map_sub, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht3.le)
      (sub_nonpos.mpr (hle _ ⟨hκU ht1, ht2⟩))
  linarith

end UpTo

/-! ### Rough charts -/

/-- [GN26, Definition 3.5.1(a), p. 278]: a *rough chart* is a homeomorphism from an open
subset of `M` onto a locally convex subset of `E` with dense interior. -/
structure IsRoughChart {M : Type*} [TopologicalSpace M] {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] (e : PartialHomeomorph M E) : Prop where
  isOpen_source : IsOpen e.source
  isLocallyConvexSubset_target : IsLocallyConvexSubset e.target
  hasDenseInterior_target : HasDenseInterior e.target

section PartialHomeomorph

variable {M E : Type*} [TopologicalSpace M] [TopologicalSpace E]

/-- The preimage under a partial homeomorphism of an open set of `M` is relatively open in the
target. -/
theorem _root_.PartialHomeomorph.exists_isOpen_target_inter (e : PartialHomeomorph M E)
    {s : Set M} (hs : IsOpen s) :
    ∃ W : Set E, IsOpen W ∧ e.target ∩ e.symm ⁻¹' s = e.target ∩ W := by
  obtain ⟨W, hW, h⟩ := continuousOn_iff'.mp e.continuousOn_symm s hs
  exact ⟨W, hW, by rw [inter_comm, h, inter_comm]⟩

/-- The transition map `e' ∘ e⁻¹` maps its domain onto the domain of `e ∘ e'⁻¹`. -/
theorem _root_.PartialHomeomorph.mapsTo_trans (e e' : PartialHomeomorph M E) :
    MapsTo (e' ∘ e.symm) (e.target ∩ e.symm ⁻¹' e'.source)
      (e'.target ∩ e'.symm ⁻¹' e.source) := by
  intro y hy
  refine ⟨e'.map_source hy.2, ?_⟩
  simp only [mem_preimage, comp_apply, e'.left_inv hy.2]
  exact e.map_target hy.1

/-- The interior of the image of an open set under a partial homeomorphism. -/
theorem _root_.PartialHomeomorph.interior_target_inter_preimage (e : PartialHomeomorph M E)
    {s : Set M} (hs : IsOpen s) :
    interior (e.target ∩ e.symm ⁻¹' s) = interior e.target ∩ e.symm ⁻¹' s := by
  obtain ⟨W, hW, h⟩ := e.exists_isOpen_target_inter hs
  rw [h, interior_inter, hW.interior_eq]
  ext y
  refine and_congr_right fun hy ↦ ?_
  have hy' : y ∈ e.target := interior_subset hy
  constructor
  · intro hyW
    exact (h.symm ▸ (⟨hy', hyW⟩ : y ∈ e.target ∩ W) : y ∈ e.target ∩ e.symm ⁻¹' s).2
  · intro hys
    exact (h ▸ (⟨hy', hys⟩ : y ∈ e.target ∩ e.symm ⁻¹' s) : y ∈ e.target ∩ W).2

/-- The chart of a nonempty subset `U ⊆ E`: the inclusion `U → E`, a partial homeomorphism
with source `univ` and target `U`. -/
def subsetChart (U : Set E) [Nonempty U] : PartialHomeomorph U E :=
  Topology.IsEmbedding.subtypeVal.toPartialHomeomorph Subtype.val

@[simp] theorem subsetChart_source (U : Set E) [Nonempty U] : (subsetChart U).source = univ :=
  rfl

@[simp] theorem subsetChart_target (U : Set E) [Nonempty U] : (subsetChart U).target = U := by
  simp [subsetChart]

@[simp] theorem subsetChart_apply (U : Set E) [Nonempty U] (x : U) : subsetChart U x = x := rfl

end PartialHomeomorph

section Charts

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {M : Type*} [TopologicalSpace M] {N : Type*} [TopologicalSpace N]
  {X : Type*} [TopologicalSpace X]

namespace IsRoughChart

variable {e : PartialHomeomorph M E}

/-- [GN26, Remark 3.5.2, p. 279]: images of open subsets under rough charts are locally
convex. -/
theorem isLocallyConvexSubset_inter_preimage [LocallyConvexSpace ℝ E] (he : IsRoughChart e)
    {s : Set M} (hs : IsOpen s) : IsLocallyConvexSubset (e.target ∩ e.symm ⁻¹' s) := by
  obtain ⟨W, hW, h⟩ := e.exists_isOpen_target_inter hs
  rw [h]
  exact he.isLocallyConvexSubset_target.inter_isOpen hW

/-- [GN26, Remark 3.5.2, p. 279]: images of open subsets under rough charts have dense
interior. -/
theorem hasDenseInterior_inter_preimage (he : IsRoughChart e) {s : Set M} (hs : IsOpen s) :
    HasDenseInterior (e.target ∩ e.symm ⁻¹' s) := by
  obtain ⟨W, hW, h⟩ := e.exists_isOpen_target_inter hs
  rw [h]
  exact he.hasDenseInterior_target.inter_isOpen hW

end IsRoughChart

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]

/-- `C^r` on the image of an open set `t` under a partial homeomorphism is a local property
on `t`. -/
theorem _root_.PartialHomeomorph.contDiffLCUpTo_of_local (e : PartialHomeomorph M E) {r : ℕ∞}
    {f : E → F} {t : Set M}
    (h : ∀ x ∈ e.source ∩ t, ∃ s, IsOpen s ∧ x ∈ s ∧
      ContDiffLCUpTo r f (e.target ∩ e.symm ⁻¹' (t ∩ s))) :
    ContDiffLCUpTo r f (e.target ∩ e.symm ⁻¹' t) := by
  refine ContDiffLCUpTo.of_local fun y hy ↦ ?_
  obtain ⟨s, hs, hxs, hf⟩ := h (e.symm y) ⟨e.map_target hy.1, hy.2⟩
  obtain ⟨W, hW, hWe⟩ := e.exists_isOpen_target_inter hs
  have hyW : y ∈ e.target ∩ W := hWe ▸ (⟨hy.1, hxs⟩ : y ∈ e.target ∩ e.symm ⁻¹' s)
  refine ⟨W, hW, hyW.2, ?_⟩
  have heq : e.target ∩ e.symm ⁻¹' t ∩ W = e.target ∩ e.symm ⁻¹' (t ∩ s) := by
    ext z
    constructor
    · rintro ⟨⟨hz1, hz2⟩, hz3⟩
      have : z ∈ e.target ∩ e.symm ⁻¹' s := hWe.symm ▸ (⟨hz1, hz3⟩ : z ∈ e.target ∩ W)
      exact ⟨hz1, hz2, this.2⟩
    · rintro ⟨hz1, hz2, hz3⟩
      have : z ∈ e.target ∩ W := hWe ▸ (⟨hz1, hz3⟩ : z ∈ e.target ∩ e.symm ⁻¹' s)
      exact ⟨⟨hz1, hz2⟩, this.2⟩
  rw [heq]
  exact hf

variable [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {G : Type w} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
  [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G]

namespace IsRoughChart

/-- **Factoring a local representative through an intermediate chart** (the computation in the
proof of [GN26, Proposition 3.5.12, p. 281]): on the part of the domain where `f` lands
in the chart `κ`, `ψ ∘ (g ∘ f) ∘ φ⁻¹ = (ψ ∘ g ∘ κ⁻¹) ∘ (κ ∘ f ∘ φ⁻¹)` is `C^r` if both factors
are. -/
theorem contDiffLCUpTo_comp {φ : PartialHomeomorph M E} {κ : PartialHomeomorph N F}
    {ψ : PartialHomeomorph X G} (hφ : IsRoughChart φ) (hκ : IsRoughChart κ)
    (hψ : IsOpen ψ.source) {f : M → N} {g : N → X} (hf : Continuous f) (hg : Continuous g)
    {r : ℕ∞} (h₁ : ContDiffLCUpTo r (κ ∘ f ∘ φ.symm) (φ.target ∩ φ.symm ⁻¹' (f ⁻¹' κ.source)))
    (h₂ : ContDiffLCUpTo r (ψ ∘ g ∘ κ.symm) (κ.target ∩ κ.symm ⁻¹' (g ⁻¹' ψ.source))) :
    ContDiffLCUpTo r (ψ ∘ (g ∘ f) ∘ φ.symm)
      (φ.target ∩ φ.symm ⁻¹' ((g ∘ f) ⁻¹' ψ.source ∩ f ⁻¹' κ.source)) := by
  have hopen : IsOpen ((g ∘ f) ⁻¹' ψ.source ∩ f ⁻¹' κ.source) :=
    (hψ.preimage (hg.comp hf)).inter (hκ.isOpen_source.preimage hf)
  have hD := hφ.hasDenseInterior_inter_preimage hopen
  have hsub : φ.target ∩ φ.symm ⁻¹' ((g ∘ f) ⁻¹' ψ.source ∩ f ⁻¹' κ.source) ⊆
      φ.target ∩ φ.symm ⁻¹' (f ⁻¹' κ.source) := fun y hy ↦ ⟨hy.1, hy.2.2⟩
  have hmaps : MapsTo (κ ∘ f ∘ φ.symm)
      (φ.target ∩ φ.symm ⁻¹' ((g ∘ f) ⁻¹' ψ.source ∩ f ⁻¹' κ.source))
      (κ.target ∩ κ.symm ⁻¹' (g ⁻¹' ψ.source)) := by
    intro y hy
    refine ⟨κ.map_source hy.2.2, ?_⟩
    simp only [mem_preimage, comp_apply, κ.left_inv hy.2.2]
    exact hy.2.1
  refine (h₂.comp hD (hκ.isLocallyConvexSubset_inter_preimage (hψ.preimage hg))
    (hκ.hasDenseInterior_inter_preimage (hψ.preimage hg)) (h₁.mono hsub hD) hmaps).congr
    fun y hy ↦ ?_
  simp only [comp_apply, κ.left_inv hy.2.2]

/-- **[GN26, Lemma 3.5.6, pp. 279–280], for two charts.** If the transition maps between
two rough charts are `C^1`, a point of the common domain is mapped to an interior point of the
target by one chart if and only if it is so by the other. -/
theorem mem_interior_of_trans {e e' : PartialHomeomorph M E} (he : IsRoughChart e)
    (he' : IsRoughChart e') (h : ContDiffLC 1 (e' ∘ e.symm) (e.target ∩ e.symm ⁻¹' e'.source))
    (h' : ContDiffLC 1 (e ∘ e'.symm) (e'.target ∩ e'.symm ⁻¹' e.source)) {x : M}
    (hx : x ∈ e.source) (hx' : x ∈ e'.source) (hint : e x ∈ interior e.target) :
    e' x ∈ interior e'.target := by
  have hU := he.isLocallyConvexSubset_inter_preimage he'.isOpen_source
  have hUd := he.hasDenseInterior_inter_preimage he'.isOpen_source
  have hU' := he'.isLocallyConvexSubset_inter_preimage he.isOpen_source
  have hU'd := he'.hasDenseInterior_inter_preimage he.isOpen_source
  have hy : e x ∈ interior (e.target ∩ e.symm ⁻¹' e'.source) := by
    rw [e.interior_target_inter_preimage he'.isOpen_source]
    exact ⟨hint, by simpa [mem_preimage, e.left_inv hx] using hx'⟩
  have hinv : ∀ z ∈ e'.target ∩ e'.symm ⁻¹' e.source, (e' ∘ e.symm) ((e ∘ e'.symm) z) = z := by
    intro z hz
    simp only [comp_apply, e.left_inv hz.2, e'.right_inv hz.1]
  have hμκ : (e ∘ e'.symm) ((e' ∘ e.symm) (e x)) = e x := by
    simp only [comp_apply, e.left_inv hx, e'.left_inv hx']
  have := ContDiffLC.mem_interior_of_rightInvOn hU hUd hU' hU'd h h' (e.mapsTo_trans e')
    (e'.mapsTo_trans e) hinv hy hμκ
  rw [e'.interior_target_inter_preimage he.isOpen_source] at this
  simpa [comp_apply, e.left_inv hx] using this.1

end IsRoughChart

end Charts

/-! ### Rough atlases and manifolds with rough boundary -/

section Atlas

variable (r : ℕ∞) (E : Type u) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  (M : Type*) [TopologicalSpace M]

/-- **[GN26, Definition 3.5.1(a), p. 278]**: a `C^r` atlas of rough `E`-charts of `M`,
`r ∈ ℕ₀ ∪ {∞}`. The charts are rough charts (open sources, locally convex targets with dense
interior), they cover `M` (A1), the transition maps `e' ∘ e⁻¹ : e(U_e ∩ U_{e'}) → E` are `C^r`
(A2), and, for `r = 0`, interior points correspond to interior points (A3). For `r ≥ 1`, (A3)
is automatic (`RoughAtlas.mem_interior_iff`, [GN26, Lemma 3.5.6]). -/
structure RoughAtlas where
  /-- The charts. -/
  atlas : Set (PartialHomeomorph M E)
  /-- The charts are rough charts. -/
  isRoughChart : ∀ e ∈ atlas, IsRoughChart e
  /-- (A1): the chart domains cover `M`. -/
  exists_mem_source : ∀ x, ∃ e ∈ atlas, x ∈ e.source
  /-- (A2): the transition maps are `C^r`. -/
  contDiffLCUpTo_trans : ∀ e ∈ atlas, ∀ e' ∈ atlas,
    ContDiffLCUpTo r (e' ∘ e.symm) (e.target ∩ e.symm ⁻¹' e'.source)
  /-- (A3), for `r = 0`: interior points correspond to interior points. -/
  mem_interior_of_eq_zero : r = 0 → ∀ e ∈ atlas, ∀ e' ∈ atlas, ∀ x ∈ e.source ∩ e'.source,
    e x ∈ interior e.target → e' x ∈ interior e'.target

namespace RoughAtlas

variable {r E M}
variable {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {G : Type w} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
  [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G]
  {N : Type*} [TopologicalSpace N] {X : Type*} [TopologicalSpace X]

/-- **The boundary is well defined** [GN26, Lemma 3.5.6, pp. 279–280]: for two charts
`e`, `e'` at `x`, `e x` is an interior point of `e.target` if and only if `e' x` is an interior
point of `e'.target`. For `r ≥ 1` this follows from the invertibility of the differentials of the
transition maps and Hahn–Banach; for `r = 0` it is axiom (A3). -/
theorem mem_interior_iff (A : RoughAtlas r E M) {e e' : PartialHomeomorph M E} (he : e ∈ A.atlas)
    (he' : e' ∈ A.atlas) {x : M} (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    e x ∈ interior e.target ↔ e' x ∈ interior e'.target := by
  rcases eq_or_ne r 0 with hr | hr
  · exact ⟨A.mem_interior_of_eq_zero hr e he e' he' x ⟨hx, hx'⟩,
      A.mem_interior_of_eq_zero hr e' he' e he x ⟨hx', hx⟩⟩
  · have h := (A.contDiffLCUpTo_trans e he e' he').contDiffLC_one hr
    have h' := (A.contDiffLCUpTo_trans e' he' e he).contDiffLC_one hr
    exact ⟨(A.isRoughChart e he).mem_interior_of_trans (A.isRoughChart e' he') h h' hx hx',
      (A.isRoughChart e' he').mem_interior_of_trans (A.isRoughChart e he) h' h hx' hx⟩

/-- **[GN26, Definition 3.5.1(c), p. 278]**: the (formal) boundary `∂M`, the set of
points mapped to the topological boundary `V_e \ V_e⁰` of the target by some chart. -/
def boundary (A : RoughAtlas r E M) : Set M :=
  {x | ∃ e ∈ A.atlas, x ∈ e.source ∧ e x ∉ interior e.target}

/-- `x ∈ ∂M` can be tested in any chart at `x` [GN26, Lemma 3.5.6]. -/
theorem mem_boundary_iff (A : RoughAtlas r E M) {e : PartialHomeomorph M E} (he : e ∈ A.atlas)
    {x : M} (hx : x ∈ e.source) : x ∈ A.boundary ↔ e x ∉ interior e.target := by
  constructor
  · rintro ⟨e', he', hx', hb⟩
    exact fun h ↦ hb ((A.mem_interior_iff he he' hx hx').mp h)
  · exact fun h ↦ ⟨e, he, hx, h⟩

/-! #### Maximal atlases -/

/-- A rough chart is *compatible* with the atlas `A` if all the transition maps between it and the
charts of `A` are `C^r` and, for `r = 0`, interior points correspond ([GN26, Remark 3.1.5] adapted
to rough charts). -/
def IsCompatible (A : RoughAtlas r E M) (e : PartialHomeomorph M E) : Prop :=
  IsRoughChart e ∧ ∀ c ∈ A.atlas,
    ContDiffLCUpTo r (c ∘ e.symm) (e.target ∩ e.symm ⁻¹' c.source) ∧
    ContDiffLCUpTo r (e ∘ c.symm) (c.target ∩ c.symm ⁻¹' e.source) ∧
    (r = 0 → ∀ x ∈ e.source ∩ c.source, (e x ∈ interior e.target ↔ c x ∈ interior c.target))

theorem isCompatible_of_mem (A : RoughAtlas r E M) {e : PartialHomeomorph M E}
    (he : e ∈ A.atlas) : A.IsCompatible e :=
  ⟨A.isRoughChart e he, fun c hc ↦ ⟨A.contDiffLCUpTo_trans e he c hc,
    A.contDiffLCUpTo_trans c hc e he, fun _ _ hx ↦ A.mem_interior_iff he hc hx.1 hx.2⟩⟩

/-- The transition map between two charts compatible with `A` is `C^r`: it factors locally
through the charts of `A`. -/
theorem contDiffLCUpTo_trans_of_isCompatible (A : RoughAtlas r E M) {e e' : PartialHomeomorph M E}
    (he : A.IsCompatible e) (he' : A.IsCompatible e') :
    ContDiffLCUpTo r (e' ∘ e.symm) (e.target ∩ e.symm ⁻¹' e'.source) := by
  refine e.contDiffLCUpTo_of_local fun x hx ↦ ?_
  obtain ⟨c, hc, hxc⟩ := A.exists_mem_source x
  refine ⟨c.source, (A.isRoughChart c hc).isOpen_source, hxc, ?_⟩
  exact he.1.contDiffLCUpTo_comp (A.isRoughChart c hc) he'.1.isOpen_source continuous_id
    continuous_id ((he.2 c hc).1) ((he'.2 c hc).2.1)

/-- **The maximal atlas** containing `A` ([GN26, Remark 3.1.5], for rough charts): all
rough charts compatible with `A`. -/
def maximal (A : RoughAtlas r E M) : RoughAtlas r E M where
  atlas := {e | A.IsCompatible e}
  isRoughChart _ he := he.1
  exists_mem_source x :=
    let ⟨e, he, hx⟩ := A.exists_mem_source x
    ⟨e, A.isCompatible_of_mem he, hx⟩
  contDiffLCUpTo_trans _ he _ he' := A.contDiffLCUpTo_trans_of_isCompatible he he'
  mem_interior_of_eq_zero hr e he e' he' x hx hint := by
    obtain ⟨c, hc, hxc⟩ := A.exists_mem_source x
    exact ((he'.2 c hc).2.2 hr x ⟨hx.2, hxc⟩).mpr (((he.2 c hc).2.2 hr x ⟨hx.1, hxc⟩).mp hint)

theorem subset_maximal (A : RoughAtlas r E M) : A.atlas ⊆ A.maximal.atlas :=
  fun _ he ↦ A.isCompatible_of_mem he

/-- A rough atlas is *maximal* if it contains every compatible rough chart. -/
def IsMaximal (A : RoughAtlas r E M) : Prop :=
  ∀ e, A.IsCompatible e → e ∈ A.atlas

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
theorem IsCompatible.mono {A B : RoughAtlas r E M} (hAB : A.atlas ⊆ B.atlas)
    {e : PartialHomeomorph M E} (he : B.IsCompatible e) : A.IsCompatible e :=
  ⟨he.1, fun c hc ↦ he.2 c (hAB hc)⟩

theorem maximal_isMaximal (A : RoughAtlas r E M) : A.maximal.IsMaximal :=
  fun _ he ↦ he.mono A.subset_maximal

/-- The maximal atlas of `A` is the only maximal atlas containing `A`. -/
theorem maximal_atlas_eq {A B : RoughAtlas r E M} (hAB : A.atlas ⊆ B.atlas) (hB : B.IsMaximal) :
    A.maximal.atlas = B.atlas := by
  ext e
  constructor
  · intro he
    refine hB e ⟨he.1, fun c hc ↦ ?_⟩
    have hc' : A.IsCompatible c := (B.isCompatible_of_mem hc).mono hAB
    exact ⟨A.contDiffLCUpTo_trans_of_isCompatible he hc',
      A.contDiffLCUpTo_trans_of_isCompatible hc' he,
      fun _ x hx ↦ A.maximal.mem_interior_iff he hc' hx.1 hx.2⟩
  · intro he
    exact (B.isCompatible_of_mem he).mono hAB

/-- The boundary does not depend on the atlas within a maximal atlas. -/
theorem boundary_maximal (A : RoughAtlas r E M) : A.maximal.boundary = A.boundary := by
  ext x
  obtain ⟨c, hc, hxc⟩ := A.exists_mem_source x
  rw [A.mem_boundary_iff hc hxc, A.maximal.mem_boundary_iff (A.subset_maximal hc) hxc]

/-! #### `C^s` maps -/

/-- **[GN26, Definition 3.5.11, p. 281]**: `f : M → N` is `C^s` if it is continuous and
all its local representatives `e' ∘ f ∘ e⁻¹ : e(f⁻¹(U_{e'}) ∩ U_e) → F` are `C^s`. The domains
are relatively open in the targets of the charts, hence locally convex with dense interior. -/
def ContMDiff {r' : ℕ∞} (A : RoughAtlas r E M) (B : RoughAtlas r' F N) (s : ℕ∞) (f : M → N) :
    Prop :=
  Continuous f ∧ ∀ e ∈ A.atlas, ∀ e' ∈ B.atlas,
    ContDiffLCUpTo s (e' ∘ f ∘ e.symm) (e.target ∩ e.symm ⁻¹' (f ⁻¹' e'.source))

variable {r' r'' : ℕ∞}

/-- **[GN26, Proposition 3.5.12, p. 281]**: compositions of `C^s` maps between manifolds
with rough boundary are `C^s`. -/
theorem ContMDiff.comp {A : RoughAtlas r E M} {B : RoughAtlas r' F N} {C : RoughAtlas r'' G X}
    {s : ℕ∞} {f : M → N} {g : N → X} (hg : B.ContMDiff C s g) (hf : A.ContMDiff B s f) :
    A.ContMDiff C s (g ∘ f) := by
  refine ⟨hg.1.comp hf.1, fun φ hφ ψ hψ ↦ ?_⟩
  refine φ.contDiffLCUpTo_of_local fun x _ ↦ ?_
  obtain ⟨κ, hκ, hxκ⟩ := B.exists_mem_source (f x)
  refine ⟨f ⁻¹' κ.source, (B.isRoughChart κ hκ).isOpen_source.preimage hf.1, hxκ, ?_⟩
  exact (A.isRoughChart φ hφ).contDiffLCUpTo_comp (B.isRoughChart κ hκ)
    (C.isRoughChart ψ hψ).isOpen_source hf.1 hg.1 (hf.2 φ hφ κ hκ) (hg.2 κ hκ ψ hψ)

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
/-- The identity is `C^s` for `s ≤ r`. -/
theorem contMDiff_id (A : RoughAtlas r E M) {s : ℕ∞} (hs : s ≤ r) : A.ContMDiff A s id :=
  ⟨continuous_id, fun e he e' he' ↦ (A.contDiffLCUpTo_trans e he e' he').of_le hs⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem ContMDiff.of_le {A : RoughAtlas r E M} {B : RoughAtlas r' F N} {s s' : ℕ∞} {f : M → N}
    (hf : A.ContMDiff B s f) (hs : s' ≤ s) : A.ContMDiff B s' f :=
  ⟨hf.1, fun e he e' he' ↦ (hf.2 e he e' he').of_le hs⟩

/-- `C^s` maps for the maximal atlases restrict to `C^s` maps for the given atlases. -/
theorem ContMDiff.of_maximal {A : RoughAtlas r E M} {B : RoughAtlas r' F N} {s : ℕ∞} {f : M → N}
    (hf : A.maximal.ContMDiff B.maximal s f) : A.ContMDiff B s f :=
  ⟨hf.1, fun e he e' he' ↦ hf.2 e (A.subset_maximal he) e' (B.subset_maximal he')⟩

/-- **Chart independence**: for `s ≤ r` and `s ≤ r'`, a map is `C^s` for given atlases if and only
if it is `C^s` for the maximal atlases. Hence `C^s` maps only depend on the manifolds with rough
boundary, as in [GN26, Definition 3.5.11]. -/
theorem contMDiff_maximal_iff {A : RoughAtlas r E M} {B : RoughAtlas r' F N} {s : ℕ∞}
    (hsr : s ≤ r) (hsr' : s ≤ r') {f : M → N} :
    A.maximal.ContMDiff B.maximal s f ↔ A.ContMDiff B s f := by
  refine ⟨ContMDiff.of_maximal, fun hf ↦ ?_⟩
  have h₁ : A.maximal.ContMDiff A s id :=
    ⟨continuous_id, fun _ he c hc ↦ ((he.2 c hc).1).of_le hsr⟩
  have h₂ : B.ContMDiff B.maximal s id :=
    ⟨continuous_id, fun c hc _ he ↦ ((he.2 c hc).2.1).of_le hsr'⟩
  exact h₂.comp (hf.comp h₁)

end RoughAtlas

/-- **[GN26, Definition 3.5.1(b), p. 278]**: a `C^r` manifold with rough boundary modeled
on `E`, a maximal `C^r` atlas of rough `E`-charts. Every rough atlas `A` defines one,
`A.toRoughManifold`. -/
structure RoughManifold extends RoughAtlas r E M where
  isMaximal : toRoughAtlas.IsMaximal

/-- The manifold with rough boundary defined by a rough atlas: its maximal atlas. -/
def RoughAtlas.toRoughManifold {r E M} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
    [TopologicalSpace M] (A : RoughAtlas r E M) : RoughManifold r E M :=
  ⟨A.maximal, A.maximal_isMaximal⟩

end Atlas

/-! ### Products of partial homeomorphisms -/

section Prod

variable {M N E F : Type*} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace E]
  [TopologicalSpace F]

/-- The product of two partial homeomorphisms (Mathlib only has it for open partial
homeomorphisms, `OpenPartialHomeomorph.prod`). -/
def _root_.PartialHomeomorph.prod' (e : PartialHomeomorph M E) (e' : PartialHomeomorph N F) :
    PartialHomeomorph (M × N) (E × F) where
  toPartialEquiv := e.toPartialEquiv.prod e'.toPartialEquiv
  continuousOn_toFun := e.continuousOn.prodMap e'.continuousOn
  continuousOn_invFun := e.continuousOn_symm.prodMap e'.continuousOn_symm

@[simp] theorem _root_.PartialHomeomorph.prod'_source (e : PartialHomeomorph M E)
    (e' : PartialHomeomorph N F) : (e.prod' e').source = e.source ×ˢ e'.source := rfl

@[simp] theorem _root_.PartialHomeomorph.prod'_target (e : PartialHomeomorph M E)
    (e' : PartialHomeomorph N F) : (e.prod' e').target = e.target ×ˢ e'.target := rfl

@[simp] theorem _root_.PartialHomeomorph.prod'_coe (e : PartialHomeomorph M E)
    (e' : PartialHomeomorph N F) : (e.prod' e' : M × N → E × F) = Prod.map e e' := rfl

@[simp] theorem _root_.PartialHomeomorph.prod'_coe_symm (e : PartialHomeomorph M E)
    (e' : PartialHomeomorph N F) :
    ((e.prod' e').symm : E × F → M × N) = Prod.map e.symm e'.symm := rfl

variable [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

theorem IsRoughChart.prod {e : PartialHomeomorph M E} {e' : PartialHomeomorph N F}
    (he : IsRoughChart e) (he' : IsRoughChart e') : IsRoughChart (e.prod' e') :=
  ⟨he.isOpen_source.prod he'.isOpen_source,
    he.isLocallyConvexSubset_target.prod he'.isLocallyConvexSubset_target,
    he.hasDenseInterior_target.prod he'.hasDenseInterior_target⟩

end Prod

/-! ### Examples -/

section Examples

variable {r : ℕ∞} {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {M : Type*} [TopologicalSpace M] {N : Type*} [TopologicalSpace N]

namespace RoughAtlas

/-! #### Ordinary manifolds -/

variable (r E M) in
/-- **[GN26, Example 3.5.3(a), p. 279]**: a smooth manifold modeled on `E`
(`MBManifold E M`) is a `C^r` manifold with rough boundary, for every `r`, through the charts of
its atlas. -/
def ofChartedSpace [ChartedSpace E M] [MBManifold E M] : RoughAtlas r E M where
  atlas := OpenPartialHomeomorph.toPartialHomeomorph '' _root_.atlas E M
  isRoughChart := by
    rintro _ ⟨e, -, rfl⟩
    exact ⟨e.open_source, e.open_target.isLocallyConvexSubset, e.open_target.hasDenseInterior⟩
  exists_mem_source x := ⟨_, ⟨chartAt E x, chart_mem_atlas E x, rfl⟩, mem_chart_source E x⟩
  contDiffLCUpTo_trans := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    have h : SmoothMBOn (e.symm.trans e') (e.symm.trans e').source :=
      (HasGroupoid.compatible (G := mbGroupoid E) he he').1
    rw [OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source] at h
    exact ContDiffLCUpTo.of_smoothMBOn
      (e.isOpen_inter_preimage_symm e'.open_source) h
  mem_interior_of_eq_zero := by
    rintro - _ ⟨e, -, rfl⟩ _ ⟨e', -, rfl⟩ x hx -
    change e' x ∈ interior e'.target
    rw [e'.open_target.interior_eq]
    exact e'.map_source hx.2

/-- Ordinary manifolds have empty boundary [GN26, Remark 3.5.7, p. 280]. -/
theorem boundary_ofChartedSpace [ChartedSpace E M] [MBManifold E M] :
    (ofChartedSpace r E M).boundary = ∅ := by
  refine eq_empty_iff_forall_notMem.mpr fun x hx ↦ ?_
  obtain ⟨_, ⟨e, -, rfl⟩, hx, hb⟩ := hx
  exact hb (by
    change e x ∈ interior e.target
    rw [e.open_target.interior_eq]
    exact e.map_source hx)

/-! #### Products -/

/-- **[GN26, Example 3.5.5, p. 279]**: the product of manifolds with rough boundary, with
the charts `φ₁ × φ₂`. -/
def prod (A : RoughAtlas r E M) (B : RoughAtlas r F N) : RoughAtlas r (E × F) (M × N) where
  atlas := image2 PartialHomeomorph.prod' A.atlas B.atlas
  isRoughChart := by
    rintro _ ⟨e, he, e', he', rfl⟩
    exact (A.isRoughChart e he).prod (B.isRoughChart e' he')
  exists_mem_source x :=
    let ⟨e, he, hx⟩ := A.exists_mem_source x.1
    let ⟨e', he', hx'⟩ := B.exists_mem_source x.2
    ⟨e.prod' e', mem_image2_of_mem he he', hx, hx'⟩
  contDiffLCUpTo_trans := by
    rintro _ ⟨e₁, he₁, e₂, he₂, rfl⟩ _ ⟨c₁, hc₁, c₂, hc₂, rfl⟩
    have hset : (e₁.prod' e₂).target ∩ (e₁.prod' e₂).symm ⁻¹' (c₁.prod' c₂).source =
        (e₁.target ∩ e₁.symm ⁻¹' c₁.source) ×ˢ (e₂.target ∩ e₂.symm ⁻¹' c₂.source) := by
      ext p
      simp only [PartialHomeomorph.prod'_target, PartialHomeomorph.prod'_source,
        PartialHomeomorph.prod'_coe_symm, mem_inter_iff, mem_prod, mem_preimage, Prod.map_fst,
        Prod.map_snd]
      tauto
    rw [hset]
    exact ContDiffLCUpTo.prodMap
      ((A.isRoughChart e₁ he₁).hasDenseInterior_inter_preimage
        (A.isRoughChart c₁ hc₁).isOpen_source)
      ((B.isRoughChart e₂ he₂).hasDenseInterior_inter_preimage
        (B.isRoughChart c₂ hc₂).isOpen_source)
      (A.contDiffLCUpTo_trans e₁ he₁ c₁ hc₁) (B.contDiffLCUpTo_trans e₂ he₂ c₂ hc₂)
  mem_interior_of_eq_zero := by
    rintro hr _ ⟨e₁, he₁, e₂, he₂, rfl⟩ _ ⟨c₁, hc₁, c₂, hc₂, rfl⟩ x ⟨hx, hx'⟩ hint
    simp only [PartialHomeomorph.prod'_target, PartialHomeomorph.prod'_coe, interior_prod_eq,
      mem_prod, Prod.map_fst, Prod.map_snd] at hint ⊢
    exact ⟨A.mem_interior_of_eq_zero hr e₁ he₁ c₁ hc₁ x.1 ⟨hx.1, hx'.1⟩ hint.1,
      B.mem_interior_of_eq_zero hr e₂ he₂ c₂ hc₂ x.2 ⟨hx.2, hx'.2⟩ hint.2⟩

/-- The boundary of a product: `∂(M × N) = (∂M × N) ∪ (M × ∂N)`. -/
theorem boundary_prod (A : RoughAtlas r E M) (B : RoughAtlas r F N) :
    (A.prod B).boundary = A.boundary ×ˢ univ ∪ univ ×ˢ B.boundary := by
  ext x
  obtain ⟨e, he, hx⟩ := A.exists_mem_source x.1
  obtain ⟨e', he', hx'⟩ := B.exists_mem_source x.2
  rw [(A.prod B).mem_boundary_iff (mem_image2_of_mem he he') (show x ∈ (e.prod' e').source from
    ⟨hx, hx'⟩)]
  simp only [PartialHomeomorph.prod'_target, PartialHomeomorph.prod'_coe, interior_prod_eq,
    mem_prod, Prod.map_fst, Prod.map_snd, mem_union, mem_univ, and_true, true_and,
    A.mem_boundary_iff he hx, B.mem_boundary_iff he' hx']
  tauto

/-! #### Subsets of the model space -/

variable (r) in
/-- **[GN26, Example 3.5.3(b), p. 279]**: a nonempty locally convex subset `U ⊆ E` with
dense interior is a `C^r` manifold with rough boundary, with the single chart `U ↪ E`. G–N state
it for nonempty interior; dense interior is what makes the inclusion a rough chart
(Definition 3.5.1(a)), and it follows from nonempty interior for convex `U` (`ofConvex`). -/
def ofSubset {U : Set E} (hU : IsLocallyConvexSubset U) (hd : HasDenseInterior U) [Nonempty U] :
    RoughAtlas r E U where
  atlas := {subsetChart U}
  isRoughChart := by
    rintro _ rfl
    exact ⟨by simp, by simpa using hU, by simpa using hd⟩
  exists_mem_source x := ⟨_, rfl, by simp⟩
  contDiffLCUpTo_trans := by
    rintro _ rfl _ rfl
    refine (contDiffLCUpTo_id r (hd.inter_isOpen (W := univ) isOpen_univ)).mono ?_ ?_ |>.congr ?_
    · simp
    · simpa using hd
    · intro y hy
      simp only [subsetChart_target, subsetChart_source, preimage_univ, inter_univ] at hy
      simp only [id, comp_apply]
      exact Topology.IsEmbedding.toPartialHomeomorph_right_inv _ _ (by simpa using hy) |>.symm
  mem_interior_of_eq_zero := by
    rintro - _ rfl _ rfl x - h
    exact h

/-- The formal boundary of a subset `U` is the set of points of `U` that are not interior points
of `U` in `E` [GN26, Remark 3.5.7, p. 280]. -/
theorem boundary_ofSubset {U : Set E} (hU : IsLocallyConvexSubset U) (hd : HasDenseInterior U)
    [Nonempty U] : (ofSubset r hU hd).boundary = {x : U | (x : E) ∉ interior U} := by
  ext x
  rw [(ofSubset r hU hd).mem_boundary_iff (e := subsetChart U) rfl (by simp)]
  simp

variable (r) in
/-- A convex subset with nonempty interior is a `C^r` manifold with rough boundary
[GN26, Example 3.5.3(b), p. 279]. -/
def ofConvex {U : Set E} (hU : Convex ℝ U) (hne : (interior U).Nonempty) : RoughAtlas r E U :=
  haveI : Nonempty U := ⟨⟨_, interior_subset hne.some_mem⟩⟩
  ofSubset r hU.isLocallyConvexSubset (hU.hasDenseInterior hne)

variable (r) in
/-- A closed half-space `{x | 0 ≤ λ x}`, `λ ≠ 0` a continuous functional, is a `C^r` manifold
with rough boundary. -/
def halfSpace (l : StrongDual ℝ E) (hl : l ≠ 0) : RoughAtlas r E {x : E | 0 ≤ l x} :=
  ofConvex r (convex_halfSpace_ge l.isLinear 0) (by
    obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hl
    replace hx : l x ≠ 0 := by simpa using hx
    refine ⟨(l x)⁻¹ • x, ?_⟩
    have hopen : IsOpen {y : E | 0 < l y} := isOpen_lt continuous_const l.continuous
    have hsub : {y : E | 0 < l y} ⊆ {y : E | 0 ≤ l y} := fun y (hy : 0 < l y) ↦ hy.le
    refine interior_maximal hsub hopen ?_
    change 0 < l ((l x)⁻¹ • x)
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hx]
    exact one_pos)

variable (r) in
/-- The unit interval `[0, 1]` is a `C^r` manifold with rough boundary. -/
def unitInterval : RoughAtlas r ℝ (Icc (0 : ℝ) 1) :=
  ofConvex r (convex_Icc 0 1) (by
    rw [interior_Icc]
    exact ⟨1 / 2, by norm_num, by norm_num⟩)

/-- The boundary of `[0, 1]` is `{0, 1}`. -/
theorem boundary_unitInterval :
    (unitInterval r).boundary = {x : Icc (0 : ℝ) 1 | (x : ℝ) = 0 ∨ (x : ℝ) = 1} := by
  have := boundary_ofSubset (r := r) (convex_Icc (0 : ℝ) 1).isLocallyConvexSubset
    ((convex_Icc (0 : ℝ) 1).hasDenseInterior (by
      rw [interior_Icc]; exact ⟨1 / 2, by norm_num, by norm_num⟩))
  refine this.trans ?_
  ext ⟨x, hx0, hx1⟩
  simp only [interior_Icc, mem_Ioo, not_and_or, not_lt]
  constructor
  · rintro (h | h)
    · exact Or.inl (le_antisymm h hx0)
    · exact Or.inr (le_antisymm hx1 h)
  · rintro (h | h)
    · exact Or.inl h.le
    · exact Or.inr h.ge

end RoughAtlas

end Examples

end LocallyConvex.Manifolds
