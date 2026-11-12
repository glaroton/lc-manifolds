/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.RoughBoundary.Basic
public import LocallyConvexManifolds.Tangent.Bundle

/-!
# The tangent bundle of a manifold with rough boundary

Reference: H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups* (arXiv:2602.12362v1),
3.5.22, p. 285, which transfers Definitions 3.3.3–3.3.11, Lemma 3.3.8 and Proposition 3.3.12
(pp. 256–260) to manifolds with rough boundary.

Let `A` be a `C^r` atlas of rough charts of `M` modeled on `E` (`RoughAtlas r E M`), `r ≥ 1`.
The tangent bundle `TM` is glued from the products `V_φ × E`, `φ ∈ A`, along the maps
`T(ψ ∘ φ⁻¹) : (y, w) ↦ (ψ (φ⁻¹ y), d(ψ ∘ φ⁻¹)(y, w))`, where `d = dLC` is the differential on a
locally convex subset with dense interior (G–N, Definition 1.4.4). As for the tangent bundle of an
ordinary manifold in this library (`Tangent/Bundle.lean`), we build it from a `FiberBundleCore`
indexed by the charts of `A` whose coordinate changes are the differentials of the transition
maps (`RoughAtlas.tangentBundleCore`); the base sets are the chart domains, which are open in `M`.
The tangent charts `Tφ : TU_φ → V_φ × E` (G–N, (3.9), p. 257) take values in the locally convex
subsets `V_φ × E ⊆ E × E` with dense interior, and they form a rough `C^{r-1}` atlas of `TM`
(`RoughAtlas.tangentAtlas`).

## Main definitions

* `RoughAtlas.chartAt A x`: a chart of `A` at `x`, chosen once and for all; the fiber of `TM` over
  `x` is `E`, read in this chart.
* `RoughAtlas.tangentCoordChange A i j x`: `d(j ∘ i⁻¹)(i x, ·)`, the change of tangent coordinates.
* `RoughAtlas.tangentBundleCore A hr`, `RoughAtlas.TangentBundle A hr`: the tangent bundle `TM`,
  a topological fiber bundle over `M` with fiber `E` (`hr : r ≠ 0`).
* `RoughAtlas.tangentChart A hr i`: the tangent chart `Tφ`, `(x, v) ↦ (φ x, v read in φ)`, with
  target `φ.target ×ˢ univ`.
* `RoughAtlas.tangentAtlas A hr : RoughAtlas (r - 1) (E × E) (A.TangentBundle hr)`.
* `RoughAtlas.tangentMap A hr B hr' f : A.TangentBundle hr → B.TangentBundle hr'`: the tangent map
  `Tf` (G–N, Definition 3.3.11, p. 259).

## Main results

* `RoughAtlas.tangentCoordChange_self`, `RoughAtlas.tangentCoordChange_comp`: the cocycle
  conditions; `RoughAtlas.exists_clm_tangentCoordChange`: the coordinate changes are continuous
  linear **also at boundary points**, and invertible (`RoughAtlas.tangentCoordChange_inv`), so
  the topological vector space structure of the fibers does not depend on the chart.
* `RoughAtlas.tangentChart_trans_eqOn`: the transition maps of the tangent atlas are
  `T(ψ ∘ φ⁻¹) : (y, w) ↦ (ψ (φ⁻¹ y), d(ψ ∘ φ⁻¹)(y, w))` (G–N, Lemma 3.3.8(a), p. 258).
* `ContDiffLCUpTo.tangent`: `Tg = (g ∘ pr₁, dg)` is `C^{s-1}` on `D × E` if `g` is `C^s` on `D`
  (G–N, Definition 3.3.3, p. 256, on locally convex subsets with dense interior).
* `RoughAtlas.boundary_tangentAtlas`: `∂(TM) = π⁻¹(∂M)` (G–N, 3.5.22, p. 285:
  `(V_φ × E)⁰ = V_φ⁰ × E`; compare Lemma 3.5.23, p. 285).
* `RoughAtlas.contMDiff_proj`: the bundle projection is `C^{r-1}` (G–N, Lemma 3.3.8(e), p. 258).
* `RoughAtlas.dLC_localRep_change`: the differentials of the local representatives of a `C^1` map
  transform by the tangent coordinate changes, so the tangent map is chart independent.
* `RoughAtlas.tangentChart_tangentMap`: in tangent charts, `Tf` is `T(ψ ∘ f ∘ φ⁻¹)` (G–N,
  Definition 3.3.11(b), p. 259); `RoughAtlas.continuous_tangentMap`,
  `RoughAtlas.contMDiff_tangentMap`: `Tf` is continuous, and `C^{s-1}` if `f` is `C^s`,
  `s ≥ 1`; `RoughAtlas.tangentMap_comp`: the chain rule `T(g ∘ f) = Tg ∘ Tf` (G–N,
  Proposition 3.3.12, p. 259); `RoughAtlas.tangentMap_id`: `T(id) = id` (G–N, Remark 3.3.13,
  p. 260).

## Infinite-dimensional subtleties

* **Linearity at the boundary.** At a boundary point `x`, `d(ψ ∘ φ⁻¹)(φ x, ·)` is not a derivative
  at an interior point but the continuous extension of the differential from the interior. It is
  still continuous linear (G–N, Lemma 1.4.7; `ContDiffLC.exists_clm`), and invertible by the chain
  rule (G–N, Proposition 1.4.10; `ContDiffLC.dLC_comp`), which is what makes the fibers over
  boundary points topological vector spaces, isomorphic to `E` through every chart. Both facts
  need the domains of the transition maps to be locally convex with dense interior, which they are
  (G–N, Remark 3.5.2).
* **No inward/outward distinction.** The fiber over a boundary point is all of `E`, not a cone
  of inward vectors, as in G–N, 3.5.22 (`T_p M ≅ E` for all `p ∈ M`).
* **Order of differentiability.** `r - 1` is truncated subtraction in `ℕ∞`, with `⊤ - 1 = ⊤`;
  the hypothesis `r ≠ 0` is needed for the coordinate changes to exist.
* **No completeness** of `E` is assumed, as everywhere in the rough-boundary files.

## Implementation notes

The tangent bundle depends on the atlas `A` (through the index set of the fiber bundle core and
the chosen charts `A.chartAt x`), not only on the maximal atlas; comparing the tangent bundles of
two compatible atlases is not done here.

## Departures from Glöckner–Neeb

G–N define `TM` as a set of equivalence classes of triples `(φ, x, v)` with the final topology
(Definitions 3.3.5 and 3.3.7). Here, as for ordinary manifolds in this library, `TM` is the total
space of a `FiberBundleCore`; the fiber over `x` is `E`, read in the chart `A.chartAt x`. The
well-definedness of the tangent map (which G–N obtain by inserting charts and using Lemma 3.3.8(a)
and the chain rule (3.6)) is `RoughAtlas.dLC_localRep_change`, which is proved by computing the
differential of `ψ' ∘ f ∘ φ⁻¹` in two ways with the chain rule on a common domain with dense
interior (`dLC_comp_of_eqOn`). We do not claim this argument is new.

## Not done

The comparison with the tangent bundle of an ordinary manifold (`TangentBundle E M`) for
`RoughAtlas.ofChartedSpace`: it needs a comparison of `RoughAtlas.ContMDiff` with
`ContMDiffMBOn`, which is not available yet. The coordinate changes agree
(`RoughAtlas.tangentCoordChange_ofChartedSpace`).
-/

@[expose] public section

open Set Filter Function Bundle
open scoped Topology
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe u v w

/-! ### Calculus lemmas -/

section Calculus

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {G : Type w} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
  [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G]

/-- The differential of a map that is the identity on a set with dense interior is the identity
at every point of the set, including the boundary points. -/
theorem dLC_eq_snd_of_eqOn_id {f : E → E} {U : Set E} (hd : HasDenseInterior U)
    (hf : EqOn f id U) {p : E × E} (hp : p.1 ∈ U) : dLC f U p = p.2 := by
  rw [dLC_congr (hf.mono interior_subset)]
  refine (ContDiffLC.of_hasDirDerivAt (k := 0) (D := Prod.snd) hd continuousOn_id
    (fun x _ h ↦ ?_) continuousOn_snd).2 ⟨hp, mem_univ _⟩
  simpa using (ContinuousLinearMap.id ℝ E).hasDirDerivAt x h

/-- **The chain rule on a common subdomain.** If `g ∘ f = h` on a set `W` with dense interior
contained in the domains `U` of `f` and `U'` of `h`, then `dh(x, v) = dg(f x, df(x, v))` for
`x ∈ W`, where each differential is taken on the domain of the corresponding map. -/
theorem dLC_comp_of_eqOn {f : E → F} {g : F → G} {h : E → G} {U U' W : Set E} {V : Set F}
    (hW : HasDenseInterior W) (hWU : W ⊆ U) (hWU' : W ⊆ U') (hV : IsLocallyConvexSubset V)
    (hVd : HasDenseInterior V) (hf : ContDiffLC 1 f U) (hg : ContDiffLC 1 g V)
    (hh : ContDiffLC 1 h U') (hmaps : MapsTo f W V) (heq : EqOn (g ∘ f) h W) {x : E}
    (hx : x ∈ W) (v : E) : dLC h U' (x, v) = dLC g V (f x, dLC f U (x, v)) := by
  rw [← hh.dLC_mono hWU' hW ⟨hx, mem_univ v⟩, ← hf.dLC_mono hWU hW ⟨hx, mem_univ v⟩,
    ← dLC_congr (heq.mono interior_subset)]
  exact ContDiffLC.dLC_comp hW hV hVd hg (hf.mono hWU hW) hmaps hx v

/-- `k ≤ s - 1` in `ℕ∞` with `s ≠ 0` means `k + 1 ≤ s`. -/
theorem _root_.ENat.natCast_succ_le_of_le_sub_one {k : ℕ} {s : ℕ∞} (hs : s ≠ 0)
    (hk : (k : ℕ∞) ≤ s - 1) : ((k + 1 : ℕ) : ℕ∞) ≤ s := by
  induction s using ENat.recTopCoe with
  | top => exact le_top
  | coe n =>
    have hn : n ≠ 0 := by exact_mod_cast hs
    have hk' : k ≤ n - 1 := by exact_mod_cast hk
    exact_mod_cast (by omega : k + 1 ≤ n)

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
/-- Precomposition with the first projection `D × E → D`. -/
theorem ContDiffLCUpTo.comp_fst {s : ℕ∞} {g : E → F} {D : Set E} (hD : HasDenseInterior D)
    (hg : ContDiffLCUpTo s g D) : ContDiffLCUpTo s (fun q : E × E ↦ g q.1) (D ×ˢ univ) := by
  intro k hk
  have := ContDiffLC.comp_clm_of_isOpenMap (ContinuousLinearMap.fst ℝ E E)
    (by rw [ContinuousLinearMap.coe_fst']; exact isOpenMap_fst) hD (hg k hk)
  have hpre : (ContinuousLinearMap.fst ℝ E E) ⁻¹' D = D ×ˢ univ := by ext; simp
  rw [hpre] at this
  exact this

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
/-- **Glöckner–Neeb, Definition 3.3.3, p. 256**, on a set with dense interior (3.5.22, p. 285):
if `g` is `C^s` on `D`, `s ≥ 1`, then `Tg : (y, w) ↦ (g y, dg(y, w))` is `C^{s-1}` on
`D × E`. -/
theorem ContDiffLCUpTo.tangent {s : ℕ∞} (hs : s ≠ 0) {g : E → F} {D : Set E}
    (hD : HasDenseInterior D) (hg : ContDiffLCUpTo s g D) :
    ContDiffLCUpTo (s - 1) (fun q : E × E ↦ (g q.1, dLC g D q)) (D ×ˢ univ) := by
  intro k hk
  have hgk : ContDiffLC (k + 1) g D := hg (k + 1) (ENat.natCast_succ_le_of_le_sub_one hs hk)
  exact ContDiffLC.prodMk hD.prod_univ ((hg.comp_fst hD) k (hk.trans tsub_le_self))
    hgk.contDiffLC_dLC

end Calculus

/-! ### The tangent bundle -/

namespace RoughAtlas

variable {r : ℕ∞} {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type*} [TopologicalSpace M] (A : RoughAtlas r E M)

/-- A chart of `A` at `x`, chosen once and for all. -/
def chartAt (x : M) : A.atlas :=
  ⟨(A.exists_mem_source x).choose, (A.exists_mem_source x).choose_spec.1⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
theorem mem_chartAt_source (x : M) : x ∈ (A.chartAt x).1.source :=
  (A.exists_mem_source x).choose_spec.2

/-- The change of tangent coordinates from the chart `i` to the chart `j` at `x`:
`d(j ∘ i⁻¹)(i x, v)`, the differential being taken on the locally convex subset
`i(U_i ∩ U_j)` with dense interior. At boundary points it is the continuous extension of the
differential from the interior. -/
def tangentCoordChange (i j : A.atlas) (x : M) (v : E) : E :=
  dLC (j.1 ∘ i.1.symm) (i.1.target ∩ i.1.symm ⁻¹' j.1.source) (i.1 x, v)

theorem tangentCoordChange_self (i : A.atlas) {x : M} (hx : x ∈ i.1.source) (v : E) :
    A.tangentCoordChange i i x v = v := by
  have hd : HasDenseInterior (i.1.target ∩ i.1.symm ⁻¹' i.1.source) := by
    refine fun y hy ↦ ?_
    have h : i.1.target ∩ i.1.symm ⁻¹' i.1.source = i.1.target :=
      inter_eq_left.mpr fun y hy ↦ i.1.map_target hy
    rw [h] at hy ⊢
    exact (A.isRoughChart i.1 i.2).hasDenseInterior_target hy
  exact dLC_eq_snd_of_eqOn_id hd (fun y hy ↦ i.1.right_inv hy.1)
    ⟨i.1.map_source hx, by simpa [i.1.left_inv hx] using hx⟩

variable {A}

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
theorem contDiffLC_one_trans (hr : r ≠ 0) (i j : A.atlas) :
    ContDiffLC 1 (j.1 ∘ i.1.symm) (i.1.target ∩ i.1.symm ⁻¹' j.1.source) :=
  (A.contDiffLCUpTo_trans i.1 i.2 j.1 j.2).contDiffLC_one hr

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] in
theorem isLocallyConvexSubset_trans (i j : A.atlas) :
    IsLocallyConvexSubset (i.1.target ∩ i.1.symm ⁻¹' j.1.source) :=
  (A.isRoughChart i.1 i.2).isLocallyConvexSubset_inter_preimage
    (A.isRoughChart j.1 j.2).isOpen_source

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
theorem hasDenseInterior_trans (i j : A.atlas) :
    HasDenseInterior (i.1.target ∩ i.1.symm ⁻¹' j.1.source) :=
  (A.isRoughChart i.1 i.2).hasDenseInterior_inter_preimage (A.isRoughChart j.1 j.2).isOpen_source

/-- The cocycle condition for the changes of tangent coordinates: the chain rule
(G–N, Proposition 1.4.10) on `i(U_i ∩ U_j ∩ U_k)`. -/
theorem tangentCoordChange_comp (hr : r ≠ 0) (i j k : A.atlas) {x : M}
    (hx : x ∈ i.1.source ∩ j.1.source ∩ k.1.source) (v : E) :
    A.tangentCoordChange j k x (A.tangentCoordChange i j x v) = A.tangentCoordChange i k x v := by
  obtain ⟨⟨hi, hj⟩, hk⟩ := hx
  have hW : HasDenseInterior (i.1.target ∩ i.1.symm ⁻¹' (j.1.source ∩ k.1.source)) :=
    (A.isRoughChart i.1 i.2).hasDenseInterior_inter_preimage
      ((A.isRoughChart j.1 j.2).isOpen_source.inter (A.isRoughChart k.1 k.2).isOpen_source)
  have h := dLC_comp_of_eqOn (W := i.1.target ∩ i.1.symm ⁻¹' (j.1.source ∩ k.1.source))
    (U := i.1.target ∩ i.1.symm ⁻¹' j.1.source) (U' := i.1.target ∩ i.1.symm ⁻¹' k.1.source) hW
    (fun y hy ↦ ⟨hy.1, hy.2.1⟩) (fun y hy ↦ ⟨hy.1, hy.2.2⟩)
    (isLocallyConvexSubset_trans j k) (hasDenseInterior_trans j k) (contDiffLC_one_trans hr i j)
    (contDiffLC_one_trans hr j k) (contDiffLC_one_trans hr i k)
    (fun y hy ↦ ⟨j.1.map_source hy.2.1, by simpa [j.1.left_inv hy.2.1] using hy.2.2⟩)
    (fun y hy ↦ by simp [j.1.left_inv hy.2.1])
    (x := i.1 x) ⟨i.1.map_source hi, by simpa [i.1.left_inv hi] using ⟨hj, hk⟩⟩ v
  simp only [comp_apply, i.1.left_inv hi] at h
  exact h.symm

/-- **Linearity at the boundary**: for `x ∈ U_i ∩ U_j`, also when `x ∈ ∂M`, the change of tangent
coordinates is a continuous linear map (G–N, Lemma 1.4.7). -/
theorem exists_clm_tangentCoordChange (hr : r ≠ 0) (i j : A.atlas) {x : M}
    (hx : x ∈ i.1.source ∩ j.1.source) :
    ∃ L : E →L[ℝ] E, ∀ v, L v = A.tangentCoordChange i j x v :=
  (contDiffLC_one_trans hr i j).exists_clm (hasDenseInterior_trans i j)
    ⟨i.1.map_source hx.1, by simpa [i.1.left_inv hx.1] using hx.2⟩

/-- The changes of tangent coordinates are invertible, also at boundary points. -/
theorem tangentCoordChange_inv (hr : r ≠ 0) (i j : A.atlas) {x : M}
    (hx : x ∈ i.1.source ∩ j.1.source) (v : E) :
    A.tangentCoordChange j i x (A.tangentCoordChange i j x v) = v := by
  rw [tangentCoordChange_comp hr i j i ⟨hx, hx.1⟩, tangentCoordChange_self A i hx.1]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
theorem continuousOn_tangentCoordChange (hr : r ≠ 0) (i j : A.atlas) :
    ContinuousOn (fun p : M × E ↦ A.tangentCoordChange i j p.1 p.2)
      ((i.1.source ∩ j.1.source) ×ˢ univ) := by
  have hfst : ContinuousOn (fun p : M × E ↦ i.1 p.1) ((i.1.source ∩ j.1.source) ×ˢ univ) :=
    i.1.continuousOn.comp continuousOn_fst fun p hp ↦ hp.1.1
  refine (contDiffLC_one_trans hr i j).continuousOn_dLC.comp (hfst.prodMk continuousOn_snd) ?_
  rintro ⟨x, v⟩ ⟨⟨hi, hj⟩, -⟩
  exact ⟨⟨i.1.map_source hi, by simpa [i.1.left_inv hi] using hj⟩, mem_univ _⟩

variable (A) in
/-- The tangent bundle of a manifold with rough boundary as a fiber bundle core: indexed by the
charts of `A`, over the chart domains, with coordinate changes the differentials of the
transition maps (G–N, 3.5.22 and Definition 3.3.7). -/
def tangentBundleCore (hr : r ≠ 0) : FiberBundleCore A.atlas M E where
  baseSet i := i.1.source
  isOpen_baseSet i := (A.isRoughChart i.1 i.2).isOpen_source
  indexAt := A.chartAt
  mem_baseSet_at := A.mem_chartAt_source
  coordChange := A.tangentCoordChange
  coordChange_self i _ hx v := A.tangentCoordChange_self i hx v
  continuousOn_coordChange := continuousOn_tangentCoordChange hr
  coordChange_comp i j k _ hx v := tangentCoordChange_comp hr i j k hx v

variable (A) in
/-- The tangent bundle `TM` of a `C^r` manifold with rough boundary, `r ≥ 1`. The fiber over `x`
is `E`, read in the chart `A.chartAt x`. -/
abbrev TangentBundle (hr : r ≠ 0) : Type _ := (A.tangentBundleCore hr).TotalSpace

instance (hr : r ≠ 0) (x : M) : AddCommGroup ((A.tangentBundleCore hr).Fiber x) :=
  inferInstanceAs (AddCommGroup E)

instance (hr : r ≠ 0) (x : M) : Module ℝ ((A.tangentBundleCore hr).Fiber x) :=
  inferInstanceAs (Module ℝ E)

/-! #### Tangent charts and the tangent atlas -/

variable (A) in
/-- **The tangent chart** `Tφ : TU_φ → V_φ × E` of a chart `φ = i` (G–N, (3.9), p. 257):
`(x, v) ↦ (φ x, v read in φ)`. It is the local trivialization over `U_φ` followed by `φ × id`;
its target is `V_φ × E` (`tangentChart_target`). -/
def tangentChart (hr : r ≠ 0) (i : A.atlas) : PartialHomeomorph (A.TangentBundle hr) (E × E) where
  toPartialEquiv := ((A.tangentBundleCore hr).localTriv i).toPartialEquiv.trans
    (i.1.prod' (PartialHomeomorph.refl E)).toPartialEquiv
  continuousOn_toFun :=
    (i.1.prod' (PartialHomeomorph.refl E)).continuousOn.comp
      (((A.tangentBundleCore hr).localTriv i).toOpenPartialHomeomorph.continuousOn.mono
        inter_subset_left) fun _ hp ↦ hp.2
  continuousOn_invFun :=
    ((A.tangentBundleCore hr).localTriv i).toOpenPartialHomeomorph.continuousOn_symm.comp
      ((i.1.prod' (PartialHomeomorph.refl E)).continuousOn_symm.mono inter_subset_left)
      fun _ hq ↦ hq.2

theorem tangentChart_apply (hr : r ≠ 0) (i : A.atlas) (p : A.TangentBundle hr) :
    A.tangentChart hr i p = (i.1 p.1, A.tangentCoordChange (A.chartAt p.1) i p.1 p.2) :=
  rfl

theorem tangentChart_symm_apply (hr : r ≠ 0) (i : A.atlas) (q : E × E) :
    (A.tangentChart hr i).symm q =
      ⟨i.1.symm q.1, A.tangentCoordChange i (A.chartAt (i.1.symm q.1)) (i.1.symm q.1) q.2⟩ :=
  rfl

theorem tangentChart_source (hr : r ≠ 0) (i : A.atlas) :
    (A.tangentChart hr i).source = TotalSpace.proj ⁻¹' i.1.source := by
  ext p
  change p ∈ ((A.tangentBundleCore hr).localTriv i).source ∩ _ ↔ _
  simp only [FiberBundleCore.mem_localTriv_source, mem_inter_iff, mem_preimage]
  constructor
  · exact fun h ↦ h.1
  · exact fun h ↦ ⟨h, h, mem_univ _⟩

theorem tangentChart_target (hr : r ≠ 0) (i : A.atlas) :
    (A.tangentChart hr i).target = i.1.target ×ˢ univ := by
  ext q
  change q ∈ (i.1.target ×ˢ univ) ∩ _ ↔ _
  simp only [mem_inter_iff, mem_preimage]
  constructor
  · exact fun h ↦ h.1
  · intro h
    refine ⟨h, ?_⟩
    change (i.1.symm q.1, q.2) ∈ ((A.tangentBundleCore hr).localTriv i).target
    rw [FiberBundleCore.mem_localTriv_target]
    exact i.1.map_target h.1

/-- The tangent charts are rough charts: their targets `V_φ × E` are locally convex with dense
interior (G–N, 3.5.22, p. 285). -/
theorem isRoughChart_tangentChart (hr : r ≠ 0) (i : A.atlas) :
    IsRoughChart (A.tangentChart hr i) := by
  have hi := A.isRoughChart i.1 i.2
  refine ⟨?_, ?_, ?_⟩
  · rw [tangentChart_source]
    exact hi.isOpen_source.preimage (FiberBundleCore.continuous_proj _)
  · rw [tangentChart_target]
    exact hi.isLocallyConvexSubset_target.prod isLocallyConvexSubset_univ
  · rw [tangentChart_target]
    exact hi.hasDenseInterior_target.prod_univ

theorem tangentChart_trans_domain (hr : r ≠ 0) (i j : A.atlas) :
    (A.tangentChart hr i).target ∩ (A.tangentChart hr i).symm ⁻¹' (A.tangentChart hr j).source =
      (i.1.target ∩ i.1.symm ⁻¹' j.1.source) ×ˢ univ := by
  ext q
  simp only [tangentChart_target, tangentChart_source, mem_inter_iff, mem_prod, mem_univ,
    and_true, mem_preimage, tangentChart_symm_apply]

/-- **Glöckner–Neeb, Lemma 3.3.8(a), p. 258**: the transition maps of the tangent atlas are
`T(ψ ∘ φ⁻¹) : (y, w) ↦ (ψ (φ⁻¹ y), d(ψ ∘ φ⁻¹)(y, w))`. -/
theorem tangentChart_trans_eqOn (hr : r ≠ 0) (i j : A.atlas) :
    EqOn (A.tangentChart hr j ∘ (A.tangentChart hr i).symm)
      (fun q ↦ ((j.1 ∘ i.1.symm) q.1,
        dLC (j.1 ∘ i.1.symm) (i.1.target ∩ i.1.symm ⁻¹' j.1.source) q))
      ((i.1.target ∩ i.1.symm ⁻¹' j.1.source) ×ˢ univ) := by
  rintro ⟨y, w⟩ ⟨⟨hy, hyj⟩, -⟩
  have hx : i.1.symm y ∈ i.1.source := i.1.map_target hy
  rw [comp_apply, tangentChart_symm_apply, tangentChart_apply]
  refine Prod.ext rfl ?_
  change A.tangentCoordChange _ j _ (A.tangentCoordChange i _ _ w) = _
  rw [tangentCoordChange_comp hr i _ j ⟨⟨hx, A.mem_chartAt_source _⟩, hyj⟩, tangentCoordChange,
    i.1.right_inv hy]

variable (A) in
/-- **The tangent bundle of a manifold with rough boundary** (G–N, 3.5.22, p. 285, and
Definition 3.3.7 and Lemma 3.3.8(d), pp. 257–258): for `r ≥ 1`, the tangent charts form a rough
`C^{r-1}` atlas of `TM` modeled on `E × E`. The transition maps are `T(ψ ∘ φ⁻¹)`
(`tangentChart_trans_eqOn`), which are `C^{r-1}` (`ContDiffLCUpTo.tangent`); since
`(V_φ × E)⁰ = V_φ⁰ × E`, axiom (A3) for `r = 1` follows from (A3) or Lemma 3.5.6 for `M`. -/
def tangentAtlas (hr : r ≠ 0) : RoughAtlas (r - 1) (E × E) (A.TangentBundle hr) where
  atlas := range (A.tangentChart hr)
  isRoughChart := by
    rintro _ ⟨i, rfl⟩
    exact isRoughChart_tangentChart hr i
  exists_mem_source p :=
    ⟨_, ⟨A.chartAt p.1, rfl⟩, by rw [tangentChart_source]; exact A.mem_chartAt_source p.1⟩
  contDiffLCUpTo_trans := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    rw [tangentChart_trans_domain]
    exact ((A.contDiffLCUpTo_trans i.1 i.2 j.1 j.2).tangent hr (hasDenseInterior_trans i j)).congr
      (tangentChart_trans_eqOn hr i j).symm
  mem_interior_of_eq_zero := by
    rintro - _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ p ⟨hpi, hpj⟩ hint
    rw [tangentChart_source] at hpi hpj
    rw [tangentChart_target, interior_prod_eq, interior_univ] at hint ⊢
    exact ⟨(A.mem_interior_iff i.2 j.2 hpi hpj).mp hint.1, mem_univ _⟩

theorem tangentChart_mem_tangentAtlas (hr : r ≠ 0) (i : A.atlas) :
    A.tangentChart hr i ∈ (A.tangentAtlas hr).atlas :=
  ⟨i, rfl⟩

/-- **The boundary of the tangent bundle** is `π⁻¹(∂M)` (G–N, 3.5.22, p. 285: since
`(V_φ × E)⁰ = V_φ⁰ × E`; compare Lemma 3.5.23, p. 285). -/
theorem boundary_tangentAtlas (hr : r ≠ 0) :
    (A.tangentAtlas hr).boundary = TotalSpace.proj ⁻¹' A.boundary := by
  ext p
  have hp : p ∈ (A.tangentChart hr (A.chartAt p.1)).source := by
    rw [tangentChart_source]; exact A.mem_chartAt_source p.1
  rw [(A.tangentAtlas hr).mem_boundary_iff (tangentChart_mem_tangentAtlas hr _) hp, mem_preimage,
    A.mem_boundary_iff (A.chartAt p.1).2 (A.mem_chartAt_source p.1), tangentChart_target,
    interior_prod_eq, interior_univ, tangentChart_apply]
  simp

/-- The bundle projection `TM → M` is `C^{r-1}` (G–N, Lemma 3.3.8(e), p. 258). -/
theorem contMDiff_proj (hr : r ≠ 0) :
    (A.tangentAtlas hr).ContMDiff A (r - 1) TotalSpace.proj := by
  refine ⟨FiberBundleCore.continuous_proj _, ?_⟩
  rintro _ ⟨i, rfl⟩ e he
  have hdom : (A.tangentChart hr i).target ∩
      (A.tangentChart hr i).symm ⁻¹' (TotalSpace.proj ⁻¹' e.source) =
      (i.1.target ∩ i.1.symm ⁻¹' e.source) ×ˢ univ := by
    ext q
    simp only [tangentChart_target, mem_inter_iff, mem_prod, mem_univ, and_true, mem_preimage,
      tangentChart_symm_apply]
  rw [hdom]
  exact (((A.contDiffLCUpTo_trans i.1 i.2 e he).of_le tsub_le_self).comp_fst
    ((A.isRoughChart i.1 i.2).hasDenseInterior_inter_preimage
      (A.isRoughChart e he).isOpen_source)).congr fun _ _ ↦ rfl

/-! #### Tangent maps -/

section TangentMap

variable {r' r'' : ℕ∞} {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {G : Type w} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
  [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G]
  {N : Type*} [TopologicalSpace N] {X : Type*} [TopologicalSpace X]
  {B : RoughAtlas r' F N} {C : RoughAtlas r'' G X}

variable (A B) in
/-- **The tangent map** `Tf : TM → TN` (G–N, Definition 3.3.11, p. 259, and 3.5.22, p. 285):
`Tf(x, v) = (f x, d(ψ ∘ f ∘ φ⁻¹)(φ x, v))`, where `φ = A.chartAt x` and `ψ = B.chartAt (f x)` are
the charts in which the fibers are read. The definition makes sense for every map; it is
meaningful for `C^1` maps, for which it does not depend on the charts (`dLC_localRep_change`,
`tangentChart_tangentMap`). -/
def tangentMap (hr : r ≠ 0) (hr' : r' ≠ 0) (f : M → N) :
    A.TangentBundle hr → B.TangentBundle hr' := fun p ↦
  ⟨f p.1, dLC ((B.chartAt (f p.1)).1 ∘ f ∘ (A.chartAt p.1).1.symm)
    ((A.chartAt p.1).1.target ∩ (A.chartAt p.1).1.symm ⁻¹' (f ⁻¹' (B.chartAt (f p.1)).1.source))
    ((A.chartAt p.1).1 p.1, p.2)⟩

/-- `π_N ∘ Tf = f ∘ π_M` (G–N, Definition 3.3.11(a)). -/
@[simp] theorem proj_tangentMap (hr : r ≠ 0) (hr' : r' ≠ 0) (f : M → N) (p : A.TangentBundle hr) :
    (A.tangentMap B hr hr' f p).proj = f p.proj :=
  rfl

/-- **Chart independence of the tangent map** (the well-definedness in G–N, Definition 3.3.11,
p. 259): for a `C^s` map `f`, `s ≥ 1`, charts `φ, φ'` at `x` and `ψ, ψ'` at `f x`, the
differentials of the local representatives transform by the changes of tangent coordinates:
`d(ψ' ∘ f ∘ φ'⁻¹)(φ' x, d(φ' ∘ φ⁻¹)(φ x, v)) = d(ψ' ∘ ψ⁻¹)(ψ (f x), d(ψ ∘ f ∘ φ⁻¹)(φ x, v))`.
Both sides are the differential of `ψ' ∘ f ∘ φ⁻¹` at `φ x`, by the chain rule on a common domain
with dense interior; this also holds at boundary points. -/
theorem dLC_localRep_change (hr : r ≠ 0) (hr' : r' ≠ 0) {s : ℕ∞} (hs : s ≠ 0) {f : M → N}
    (hf : A.ContMDiff B s f) (φ φ' : A.atlas) (ψ ψ' : B.atlas) {x : M}
    (hx : x ∈ φ.1.source ∩ φ'.1.source) (hfx : f x ∈ ψ.1.source ∩ ψ'.1.source) (v : E) :
    dLC (ψ'.1 ∘ f ∘ φ'.1.symm) (φ'.1.target ∩ φ'.1.symm ⁻¹' (f ⁻¹' ψ'.1.source))
        (φ'.1 x, A.tangentCoordChange φ φ' x v) =
      B.tangentCoordChange ψ ψ' (f x)
        (dLC (ψ.1 ∘ f ∘ φ.1.symm) (φ.1.target ∩ φ.1.symm ⁻¹' (f ⁻¹' ψ.1.source)) (φ.1 x, v)) := by
  have hWo : IsOpen (φ'.1.source ∩ f ⁻¹' (ψ.1.source ∩ ψ'.1.source)) :=
    (A.isRoughChart φ'.1 φ'.2).isOpen_source.inter (((B.isRoughChart ψ.1 ψ.2).isOpen_source.inter
      (B.isRoughChart ψ'.1 ψ'.2).isOpen_source).preimage hf.1)
  have hW := (A.isRoughChart φ.1 φ.2).hasDenseInterior_inter_preimage hWo
  have hxW : φ.1 x ∈ φ.1.target ∩ φ.1.symm ⁻¹' (φ'.1.source ∩ f ⁻¹' (ψ.1.source ∩ ψ'.1.source)) :=
    ⟨φ.1.map_source hx.1, by simpa [φ.1.left_inv hx.1] using ⟨hx.2, hfx⟩⟩
  have hloc : ∀ (φ : A.atlas) (ψ : B.atlas), ContDiffLC 1 (ψ.1 ∘ f ∘ φ.1.symm)
      (φ.1.target ∩ φ.1.symm ⁻¹' (f ⁻¹' ψ.1.source)) :=
    fun φ ψ ↦ (hf.2 φ.1 φ.2 ψ.1 ψ.2).contDiffLC_one hs
  have hψ' : IsOpen (f ⁻¹' ψ'.1.source) := (B.isRoughChart ψ'.1 ψ'.2).isOpen_source.preimage hf.1
  have h1 := dLC_comp_of_eqOn
    (W := φ.1.target ∩ φ.1.symm ⁻¹' (φ'.1.source ∩ f ⁻¹' (ψ.1.source ∩ ψ'.1.source)))
    (U := φ.1.target ∩ φ.1.symm ⁻¹' φ'.1.source)
    (U' := φ.1.target ∩ φ.1.symm ⁻¹' (f ⁻¹' ψ'.1.source))
    (V := φ'.1.target ∩ φ'.1.symm ⁻¹' (f ⁻¹' ψ'.1.source)) hW
    (fun y hy ↦ ⟨hy.1, hy.2.1⟩) (fun y hy ↦ ⟨hy.1, hy.2.2.2⟩)
    ((A.isRoughChart φ'.1 φ'.2).isLocallyConvexSubset_inter_preimage hψ')
    ((A.isRoughChart φ'.1 φ'.2).hasDenseInterior_inter_preimage hψ')
    (contDiffLC_one_trans hr φ φ') (hloc φ' ψ') (hloc φ ψ')
    (fun y hy ↦ ⟨φ'.1.map_source hy.2.1, by simpa [φ'.1.left_inv hy.2.1] using hy.2.2.2⟩)
    (fun y hy ↦ by simp [φ'.1.left_inv hy.2.1]) hxW v
  have h2 := dLC_comp_of_eqOn
    (W := φ.1.target ∩ φ.1.symm ⁻¹' (φ'.1.source ∩ f ⁻¹' (ψ.1.source ∩ ψ'.1.source)))
    (U := φ.1.target ∩ φ.1.symm ⁻¹' (f ⁻¹' ψ.1.source))
    (U' := φ.1.target ∩ φ.1.symm ⁻¹' (f ⁻¹' ψ'.1.source))
    (V := ψ.1.target ∩ ψ.1.symm ⁻¹' ψ'.1.source) hW
    (fun y hy ↦ ⟨hy.1, hy.2.2.1⟩) (fun y hy ↦ ⟨hy.1, hy.2.2.2⟩)
    (isLocallyConvexSubset_trans ψ ψ') (hasDenseInterior_trans ψ ψ')
    (hloc φ ψ) (contDiffLC_one_trans hr' ψ ψ') (hloc φ ψ')
    (fun y hy ↦ ⟨ψ.1.map_source hy.2.2.1, by simpa [ψ.1.left_inv hy.2.2.1] using hy.2.2.2⟩)
    (fun y hy ↦ by simp [ψ.1.left_inv hy.2.2.1]) hxW v
  simp only [comp_apply, φ.1.left_inv hx.1] at h1 h2
  rw [tangentCoordChange, tangentCoordChange, ← h1, h2]

/-- The tangent map read in the fiber coordinates of arbitrary charts `i` at `x` and `j` at
`f x`: it is `d(j ∘ f ∘ i⁻¹)`. -/
theorem tangentCoordChange_tangentMap (hr : r ≠ 0) (hr' : r' ≠ 0) {s : ℕ∞} (hs : s ≠ 0)
    {f : M → N} (hf : A.ContMDiff B s f) (i : A.atlas) (j : B.atlas) {x : M}
    (hx : x ∈ i.1.source) (hfx : f x ∈ j.1.source) (v : E) :
    B.tangentCoordChange (B.chartAt (f x)) j (f x) (A.tangentMap B hr hr' f ⟨x, v⟩).2 =
      dLC (j.1 ∘ f ∘ i.1.symm) (i.1.target ∩ i.1.symm ⁻¹' (f ⁻¹' j.1.source))
        (i.1 x, A.tangentCoordChange (A.chartAt x) i x v) :=
  (dLC_localRep_change hr hr' hs hf (A.chartAt x) i (B.chartAt (f x)) j
    ⟨A.mem_chartAt_source x, hx⟩ ⟨B.mem_chartAt_source (f x), hfx⟩ v).symm

/-- **Glöckner–Neeb, Definition 3.3.11(b), p. 259**: in the tangent charts `Tφ` and `Tψ`, the
tangent map is `T(ψ ∘ f ∘ φ⁻¹)`. -/
theorem tangentChart_tangentMap (hr : r ≠ 0) (hr' : r' ≠ 0) {s : ℕ∞} (hs : s ≠ 0) {f : M → N}
    (hf : A.ContMDiff B s f) (i : A.atlas) (j : B.atlas) :
    EqOn (B.tangentChart hr' j ∘ A.tangentMap B hr hr' f ∘ (A.tangentChart hr i).symm)
      (fun q ↦ ((j.1 ∘ f ∘ i.1.symm) q.1,
        dLC (j.1 ∘ f ∘ i.1.symm) (i.1.target ∩ i.1.symm ⁻¹' (f ⁻¹' j.1.source)) q))
      ((i.1.target ∩ i.1.symm ⁻¹' (f ⁻¹' j.1.source)) ×ˢ univ) := by
  rintro ⟨y, w⟩ ⟨⟨hy, hyj⟩, -⟩
  have hx : i.1.symm y ∈ i.1.source := i.1.map_target hy
  rw [comp_apply, comp_apply, tangentChart_symm_apply, tangentChart_apply]
  refine Prod.ext rfl ?_
  change B.tangentCoordChange (B.chartAt (f (i.1.symm y))) j (f (i.1.symm y))
    (A.tangentMap B hr hr' f ⟨i.1.symm y,
      A.tangentCoordChange i (A.chartAt (i.1.symm y)) (i.1.symm y) w⟩).2 =
    dLC (j.1 ∘ f ∘ i.1.symm) (i.1.target ∩ i.1.symm ⁻¹' (f ⁻¹' j.1.source)) (y, w)
  refine (tangentCoordChange_tangentMap hr hr' hs hf i j hx hyj _).trans ?_
  rw [tangentCoordChange_inv hr i _ ⟨hx, A.mem_chartAt_source _⟩, i.1.right_inv hy]

/-- The tangent map of a `C^s` map, `s ≥ 1`, is continuous. -/
theorem continuous_tangentMap (hr : r ≠ 0) (hr' : r' ≠ 0) {s : ℕ∞} (hs : s ≠ 0) {f : M → N}
    (hf : A.ContMDiff B s f) : Continuous (A.tangentMap B hr hr' f) := by
  refine continuous_iff_continuousAt.mpr fun p ↦ ?_
  set i := A.chartAt p.1
  set j := B.chartAt (f p.1)
  have hi : p.1 ∈ i.1.source := A.mem_chartAt_source p.1
  have hj : f p.1 ∈ j.1.source := B.mem_chartAt_source (f p.1)
  set O : Set (M × E) := (i.1.source ∩ f ⁻¹' j.1.source) ×ˢ univ
  have hO : IsOpen O := ((A.isRoughChart i.1 i.2).isOpen_source.inter
    ((B.isRoughChart j.1 j.2).isOpen_source.preimage hf.1)).prod isOpen_univ
  set e := (A.tangentBundleCore hr).localTriv i
  set e' := (B.tangentBundleCore hr').localTriv j
  have hformula : EqOn (e' ∘ (A.tangentMap B hr hr' f ∘ e.toPartialEquiv.symm))
      (fun q ↦ (f q.1, dLC (j.1 ∘ f ∘ i.1.symm) (i.1.target ∩ i.1.symm ⁻¹' (f ⁻¹' j.1.source))
        (i.1 q.1, q.2))) O := by
    rintro ⟨b, w⟩ ⟨⟨hb, hbj⟩, -⟩
    refine Prod.ext rfl ?_
    change B.tangentCoordChange (B.chartAt (f b)) j (f b)
      (A.tangentMap B hr hr' f ⟨b, A.tangentCoordChange i (A.chartAt b) b w⟩).2 =
      dLC (j.1 ∘ f ∘ i.1.symm) (i.1.target ∩ i.1.symm ⁻¹' (f ⁻¹' j.1.source)) (i.1 b, w)
    refine (tangentCoordChange_tangentMap hr hr' hs hf i j hb hbj _).trans ?_
    rw [tangentCoordChange_inv hr i _ ⟨hb, A.mem_chartAt_source _⟩]
  have hcont : ContinuousOn (fun q : M × E ↦ (f q.1, dLC (j.1 ∘ f ∘ i.1.symm)
      (i.1.target ∩ i.1.symm ⁻¹' (f ⁻¹' j.1.source)) (i.1 q.1, q.2))) O := by
    refine (hf.1.comp continuous_fst).continuousOn.prodMk ?_
    refine ((hf.2 i.1 i.2 j.1 j.2).contDiffLC_one hs).continuousOn_dLC.comp
      ((i.1.continuousOn.comp (s := O) continuousOn_fst fun q (hq : q ∈ O) ↦ hq.1.1).prodMk
        continuousOn_snd) ?_
    rintro ⟨b, w⟩ ⟨⟨hb, hbj⟩, -⟩
    exact ⟨⟨i.1.map_source hb, by simpa [i.1.left_inv hb] using hbj⟩, mem_univ _⟩
  have hp : e p ∈ O := ⟨⟨hi, hj⟩, mem_univ _⟩
  refine e.continuousAt_of_comp_right hi ?_
  refine e'.continuousAt_of_comp_left ?_ hj ?_
  · exact (hf.1.comp continuous_fst).continuousAt
  · exact (hcont.congr hformula).continuousAt (hO.mem_nhds hp)

/-- **Glöckner–Neeb, Definition 3.3.11, p. 259** (with 3.5.22, p. 285): the tangent map of a
`C^s` map between manifolds with rough boundary, `s ≥ 1`, is `C^{s-1}`. -/
theorem contMDiff_tangentMap (hr : r ≠ 0) (hr' : r' ≠ 0) {s : ℕ∞} (hs : s ≠ 0) {f : M → N}
    (hf : A.ContMDiff B s f) :
    (A.tangentAtlas hr).ContMDiff (B.tangentAtlas hr') (s - 1) (A.tangentMap B hr hr' f) := by
  refine ⟨continuous_tangentMap hr hr' hs hf, ?_⟩
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  have hdom : (A.tangentChart hr i).target ∩ (A.tangentChart hr i).symm ⁻¹'
      (A.tangentMap B hr hr' f ⁻¹' (B.tangentChart hr' j).source) =
      (i.1.target ∩ i.1.symm ⁻¹' (f ⁻¹' j.1.source)) ×ˢ univ := by
    ext q
    simp only [tangentChart_target, tangentChart_source, mem_inter_iff, mem_prod, mem_univ,
      and_true, mem_preimage, tangentChart_symm_apply, proj_tangentMap]
  rw [hdom]
  exact ((hf.2 i.1 i.2 j.1 j.2).tangent hs ((A.isRoughChart i.1 i.2).hasDenseInterior_inter_preimage
    ((B.isRoughChart j.1 j.2).isOpen_source.preimage hf.1))).congr
    (tangentChart_tangentMap hr hr' hs hf i j).symm

/-- `T(id) = id` (G–N, Remark 3.3.13, p. 260). -/
theorem tangentMap_id (hr : r ≠ 0) : A.tangentMap A hr hr id = id := by
  funext p
  have hi := A.mem_chartAt_source p.1
  have hd : HasDenseInterior ((A.chartAt p.1).1.target ∩
      (A.chartAt p.1).1.symm ⁻¹' (id ⁻¹' (A.chartAt p.1).1.source)) :=
    (A.isRoughChart _ (A.chartAt p.1).2).hasDenseInterior_inter_preimage
      (A.isRoughChart _ (A.chartAt p.1).2).isOpen_source
  change (⟨p.1, _⟩ : A.TangentBundle hr) = ⟨p.1, p.2⟩
  congr 1
  exact dLC_eq_snd_of_eqOn_id hd (fun y hy ↦ (A.chartAt p.1).1.right_inv hy.1)
    ⟨(A.chartAt p.1).1.map_source hi, by simpa [(A.chartAt p.1).1.left_inv hi] using hi⟩

/-- **The chain rule** `T(g ∘ f) = Tg ∘ Tf` (G–N, Proposition 3.3.12, p. 259, with 3.5.22,
p. 285) for `C^1` maps between manifolds with rough boundary. -/
theorem tangentMap_comp (hr : r ≠ 0) (hr' : r' ≠ 0) (hr'' : r'' ≠ 0) {s s' : ℕ∞} (hs : s ≠ 0)
    (hs' : s' ≠ 0) {f : M → N} {g : N → X} (hf : A.ContMDiff B s f) (hg : B.ContMDiff C s' g) :
    A.tangentMap C hr hr'' (g ∘ f) = B.tangentMap C hr' hr'' g ∘ A.tangentMap B hr hr' f := by
  funext p
  set φ := A.chartAt p.1
  set ψ := B.chartAt (f p.1)
  set χ := C.chartAt (g (f p.1))
  have hx : p.1 ∈ φ.1.source := A.mem_chartAt_source p.1
  have hfx : f p.1 ∈ ψ.1.source := B.mem_chartAt_source (f p.1)
  have hgfx : g (f p.1) ∈ χ.1.source := C.mem_chartAt_source (g (f p.1))
  have h1 : (1 : ℕ∞) ≤ s := Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr hs)
  have h1' : (1 : ℕ∞) ≤ s' := Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr hs')
  have hgf := (hg.of_le h1').comp (hf.of_le h1)
  have hWo : IsOpen (f ⁻¹' ψ.1.source ∩ (g ∘ f) ⁻¹' χ.1.source) :=
    ((B.isRoughChart ψ.1 ψ.2).isOpen_source.preimage hf.1).inter
      ((C.isRoughChart χ.1 χ.2).isOpen_source.preimage hgf.1)
  have hgo : IsOpen (g ⁻¹' χ.1.source) := (C.isRoughChart χ.1 χ.2).isOpen_source.preimage hg.1
  have h := dLC_comp_of_eqOn
    (W := φ.1.target ∩ φ.1.symm ⁻¹' (f ⁻¹' ψ.1.source ∩ (g ∘ f) ⁻¹' χ.1.source))
    (U := φ.1.target ∩ φ.1.symm ⁻¹' (f ⁻¹' ψ.1.source))
    (U' := φ.1.target ∩ φ.1.symm ⁻¹' ((g ∘ f) ⁻¹' χ.1.source))
    (V := ψ.1.target ∩ ψ.1.symm ⁻¹' (g ⁻¹' χ.1.source))
    ((A.isRoughChart φ.1 φ.2).hasDenseInterior_inter_preimage hWo)
    (fun y hy ↦ ⟨hy.1, hy.2.1⟩) (fun y hy ↦ ⟨hy.1, hy.2.2⟩)
    ((B.isRoughChart ψ.1 ψ.2).isLocallyConvexSubset_inter_preimage hgo)
    ((B.isRoughChart ψ.1 ψ.2).hasDenseInterior_inter_preimage hgo)
    ((hf.2 φ.1 φ.2 ψ.1 ψ.2).contDiffLC_one hs) ((hg.2 ψ.1 ψ.2 χ.1 χ.2).contDiffLC_one hs')
    ((hgf.2 φ.1 φ.2 χ.1 χ.2).contDiffLC_one one_ne_zero)
    (fun y hy ↦ ⟨ψ.1.map_source hy.2.1, by simpa [ψ.1.left_inv hy.2.1] using hy.2.2⟩)
    (fun y hy ↦ by simp [ψ.1.left_inv hy.2.1])
    (x := φ.1 p.1) ⟨φ.1.map_source hx, by simpa [φ.1.left_inv hx] using ⟨hfx, hgfx⟩⟩ p.2
  simp only [comp_apply, φ.1.left_inv hx] at h
  change (⟨g (f p.1), _⟩ : C.TangentBundle hr'') = ⟨g (f p.1), _⟩
  congr 1

end TangentMap

/-! #### Ordinary manifolds -/

/-- For an ordinary manifold (`RoughAtlas.ofChartedSpace`), the changes of tangent coordinates
are those of the tangent bundle `TangentBundle E M` (`LocallyConvex.Manifolds.tangentCoordChange`):
on open domains `dLC` is the Michal–Bastiani differential. -/
theorem tangentCoordChange_ofChartedSpace [ChartedSpace E M] [MBManifold E M]
    (i j : _root_.atlas E M)
    {x : M} (hx : x ∈ i.1.source ∩ j.1.source) (v : E) :
    (ofChartedSpace r E M).tangentCoordChange ⟨i.1.toPartialHomeomorph, mem_image_of_mem _ i.2⟩
      ⟨j.1.toPartialHomeomorph, mem_image_of_mem _ j.2⟩ x v =
      LocallyConvex.Manifolds.tangentCoordChange i j x v :=
  dLC_of_isOpen _ (isOpen_transition_domain i j)
    ⟨⟨i.1.map_source hx.1, by simpa [i.1.left_inv hx.1] using hx.2⟩, mem_univ _⟩

end RoughAtlas

end LocallyConvex.Manifolds
