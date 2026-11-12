/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.Tangent.Iterated

/-!
# The chart topology of `C^ℓ(M, N)` and the tangent map

The chart topology `CkMap.chartTopology` describes the compact-open `C^ℓ` topology of `C^ℓ(M, N)`
through local representatives on open subsets of compact sets in charts; for a locally compact model
of `M` it is the topology of `C^ℓ(M, N)` (the jet topology `CkMap.jetTopology`,
`CkMap.chartTopology_eq_jetTopology`). This file proves, for a locally compact model of `M`, that
the chart topology satisfies the recursion of [GN26, Lemma 4.1.6]: it is the compact-open topology
for `ℓ = 0`, and for `ℓ + 1` it is initial with respect to `f ↦ f ∈ C(M, N)` and
`f ↦ Tf ∈ C^ℓ(TM, TN)`. With `MBMfld.gnTopology_succ`, this gives the agreement of the chart
topology with [GN26, Definition 4.1.2] (`chartTopology_eq_gnTopology`,
`MappingSpace/TopologyGN.lean`).

## Main results

* `exists_eq_tangentChart`: the charts of `TM` are the `tangentChart i c`.
* `continuous_toC_of_rep`: for a locally compact model, continuity into `C(M, N)` follows from
  that of the local representatives.
* `continuous_of_tangentCk`, `continuous_tangentCk`: a map into `C^(ℓ+1)(M, N)` is continuous if
  its compositions with `f ↦ f ∈ C(M, N)` and with `T` are, and `T` is continuous (chart
  topologies).
* `chartTopology_zero`, `chartTopology_succ`: the recursion of [GN26, Lemma 4.1.6] for the chart
  topology.

## Implementation notes

* In the charts `tangentChart j j`, `tangentChart i i` the local representative of `Tg` is
  `(y, w) ↦ (rep g(y), d(rep g)(y, w))` (`tangentIdx_rep_apply`), so `d(rep g)` is a component of a
  local representative of `Tg`, over products `V × int K` with `K` compact; in general tangent
  charts it is `(F, dF)` pulled back along a smooth map and composed with a smooth map, continuous
  by `ContDiffMBMap.contDiffMBOn_compLeftOn`. Glöckner–Neeb prove [GN26, Lemma 4.1.6] directly from
  their [GN26, Definition 4.1.2]; here the chart description comes first. We do not claim these
  arguments are new.
* The model of `M` is assumed locally compact: the chart topology is meant for such models (see
  `MappingSpace/Ck.lean`), and the localizations above use compact neighborhoods. For arbitrary
  models, the analogous recursion is proved for the jet topology, the topology of `C^ℓ(M, N)`,
  in `MappingSpace/TopologyJet.lean`.
* All statements about topologies of `C^ℓ(X, Y)` in this file are about the chart topology, which
  is not the instance; it is named explicitly in them (inside the proofs it is made a local
  instance).

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function TopologicalSpace
open scoped Topology
open LocallyConvex.Analysis

noncomputable section

universe u v

namespace LocallyConvex.Manifolds

/-! ### The charts of the tangent bundle -/

section TangentAtlas

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

/-- The charts of the tangent bundle are the charts `tangentChart i c`, for a chart `i` of `M`
(the trivialization) and a chart `c` of `M` (the base coordinates). -/
theorem exists_eq_tangentChart {e : OpenPartialHomeomorph (TangentBundle E M) (E × E)}
    (he : e ∈ atlas (E × E) (TangentBundle E M)) :
    ∃ (i : atlas E M) (c : OpenPartialHomeomorph M E), c ∈ atlas E M ∧ e = tangentChart i c := by
  obtain ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, _, ⟨c, hc, r, hr, rfl⟩, rfl⟩ := he
  obtain rfl : r = OpenPartialHomeomorph.refl E := chartedSpaceSelf_atlas.1 hr
  exact ⟨i, c, hc, rfl⟩

end TangentAtlas

/-! ### Continuity criteria for maps into `C^ℓ(X, Y)` -/

section Criteria

variable {X : MBMfld.{u, u}} {Y : MBMfld.{u, v}} {ℓ : ℕ}

/-- The `0`-th differential of a local representative depends continuously on the map, for the
compact-open topology of `C(X, Y)`. -/
theorem continuousOn_iteratedD_zero_rep {P : Type*} [tP : TopologicalSpace P]
    {ψ : P → CkMap X.Model Y.Model ℓ X.Carrier Y.Carrier}
    (h₀ : Continuous fun p ↦ CkMap.toC (ψ p))
    (a : CkMap.ChartIdx X.Model Y.Model X.Carrier Y.Carrier) :
    ContinuousOn (fun p ↦ ContDiffMBMap.iteratedD 0 (Nat.zero_le ℓ) (a.rep (ψ p)))
      (ψ ⁻¹' a.dom) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let σ : C(a.V × (Fin 0 → X.Model), X.Carrier) :=
    ⟨fun z ↦ a.j.1.symm z.1, a.j.1.continuousOn_symm.comp_continuous
      (continuous_subtype_val.comp continuous_fst) fun z ↦ a.L_subset (a.V_subset z.1.2)⟩
  have hmem : ∀ s : ψ ⁻¹' a.dom, ∀ z, (CkMap.toC (ψ s)).comp σ z ∈ a.i.1.source :=
    fun s z ↦ s.2 (mem_image_of_mem _ (a.V_subset z.1.2))
  have hc : Continuous fun s : ψ ⁻¹' a.dom ↦
      (⟨(CkMap.toC (ψ s)).comp σ, hmem s⟩ :
        {g : C(a.V × (Fin 0 → X.Model), Y.Carrier) // ∀ z, g z ∈ a.i.1.source}) :=
    (((ContinuousMap.continuous_precomp σ).comp h₀).comp continuous_subtype_val).subtype_mk _
  refine ((continuous_compOn a.i.1 a.i.1.continuousOn).comp hc).congr fun s ↦ ?_
  ext z
  change a.i.1 (ψ s (a.j.1.symm z.1)) = a.rep (ψ s) z.1
  rw [a.rep_apply s.2 z.1.2]

/-- The set of `γ ∈ C^ℓ(V, F)` with `γ(L) ⊆ O`, for `L ⊆ V` compact and `O` open, is open. -/
theorem isOpen_setOf_mapsTo_contDiffMBMap {Z F : Type u} [AddCommGroup Z] [Module ℝ Z]
    [TopologicalSpace Z] [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z] [LocallyConvexSpace ℝ Z]
    [T2Space Z] [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] {V : Opens Z} {L : Set Z}
    (hL : IsCompact L) (hLV : L ⊆ V) {O : Set F} (hO : IsOpen O) :
    IsOpen {γ : ContDiffMBMap F ℓ V | ∀ y ∈ L, γ y ∈ O} := by
  have : CompactSpace L := isCompact_iff_compactSpace.mp hL
  let σ : L → V × (Fin 0 → Z) := fun y ↦ (⟨y, hLV y.2⟩, Fin.elim0)
  have hσ : Continuous σ := by fun_prop
  have h := (ContinuousMap.isOpen_setOfPred_mapsTo (isCompact_range hσ) hO).preimage
    (ContDiffMBMap.continuous_iteratedD (F := F) (U := V) (k := ℓ) 0 (Nat.zero_le ℓ))
  convert h using 1
  ext γ
  constructor
  · rintro hγ _ ⟨y, rfl⟩
    exact hγ y y.2
  · intro hγ y hy
    exact hγ ⟨⟨y, hy⟩, rfl⟩

/-- **The compact-open part of the chart topology is determined by the local representatives**
(for a locally compact model): if the sets `ψ⁻¹(dom a)` are open and the local representatives
`p ↦ rep_a(ψ p)` are continuous on them, then `p ↦ ψ p ∈ C(X, Y)` is continuous. -/
theorem continuous_toC_of_rep [LocallyCompactSpace X.Model] {P : Type*} [TopologicalSpace P]
    {ψ : P → CkMap X.Model Y.Model ℓ X.Carrier Y.Carrier}
    (hdom : ∀ a : CkMap.ChartIdx X.Model Y.Model X.Carrier Y.Carrier, IsOpen (ψ ⁻¹' a.dom))
    (hrep : ∀ a : CkMap.ChartIdx X.Model Y.Model X.Carrier Y.Carrier,
      ContinuousOn (fun p ↦ a.rep (ψ p)) (ψ ⁻¹' a.dom)) :
    Continuous fun p ↦ CkMap.toC (ψ p) := by
  refine ContinuousMap.continuous_compactOpen.2 fun K hK U hU ↦ isOpen_iff_forall_mem_open.2
    fun p₀ hp₀ ↦ ?_
  set g₀ := CkMap.toC (ψ p₀)
  -- around each point of `K`, a chart index whose domain contains `ψ p₀` and is mapped into `U`
  have hloc : ∀ x ∈ K, ∃ a : CkMap.ChartIdx X.Model Y.Model X.Carrier Y.Carrier,
      ∃ L : Set X.Model, IsCompact L ∧ L ⊆ a.V ∧ (a.j.1.source ∩ a.j.1 ⁻¹' interior L) ∈ 𝓝 x ∧
        ψ p₀ ∈ a.dom ∧ ∀ y ∈ L, a.rep (ψ p₀) y ∈ a.i.1.target ∩ a.i.1.symm ⁻¹' U := by
    intro x hx
    let j : atlas X.Model X.Carrier := ⟨chartAt X.Model x, chart_mem_atlas X.Model x⟩
    let i : atlas Y.Model Y.Carrier := ⟨chartAt Y.Model (g₀ x), chart_mem_atlas Y.Model _⟩
    set Q := j.1.target ∩ j.1.symm ⁻¹' (g₀ ⁻¹' (U ∩ i.1.source))
    have hQ : IsOpen Q := j.1.isOpen_inter_preimage_symm
      ((hU.inter i.1.open_source).preimage g₀.continuous)
    have hxQ : j.1 x ∈ Q := ⟨j.1.map_source (mem_chart_source X.Model x), by
      rw [mem_preimage, j.1.left_inv (mem_chart_source X.Model x)]
      exact ⟨hp₀ hx, mem_chart_source Y.Model _⟩⟩
    obtain ⟨L, hLn, hLQ, hLc⟩ := local_compact_nhds (hQ.mem_nhds hxQ)
    obtain ⟨V, hV, hLV, hVQ, hVc⟩ := exists_open_between_and_isCompact_closure hLc hQ hLQ
    let a : CkMap.ChartIdx X.Model Y.Model X.Carrier Y.Carrier :=
      ⟨j, i, closure V, hVc, fun y hy ↦ (hVQ hy).1, ⟨V, hV⟩, subset_closure⟩
    have hdom₀ : ψ p₀ ∈ a.dom := by
      rintro _ ⟨y, hy, rfl⟩
      exact (hVQ hy).2.2
    refine ⟨a, L, hLc, hLV, ?_, hdom₀, fun y hy ↦ ?_⟩
    · refine Filter.inter_mem (j.1.open_source.mem_nhds (mem_chart_source X.Model x)) ?_
      exact j.1.continuousAt (mem_chart_source X.Model x) (interior_mem_nhds.2 hLn)
    · rw [a.rep_apply hdom₀ (hLV hy)]
      have hs : g₀ (j.1.symm y) ∈ i.1.source := (hLQ hy).2.2
      refine ⟨i.1.map_source hs, ?_⟩
      change i.1.symm (i.1 (g₀ (j.1.symm y))) ∈ U
      rw [i.1.left_inv hs]
      exact (hLQ hy).2.1
  choose a L hLc hLV hLn hdom₀ hrep₀ using hloc
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' (fun x hx ↦ (a x hx).j.1.source ∩ (a x hx).j.1 ⁻¹'
    interior (L x hx)) fun x hx ↦ hLn x hx
  set W := ⋂ x ∈ t, (ψ ⁻¹' (a x.1 x.2).dom ∩ (fun p ↦ (a x.1 x.2).rep (ψ p)) ⁻¹'
    {γ | ∀ y ∈ L x.1 x.2, γ y ∈ (a x.1 x.2).i.1.target ∩ (a x.1 x.2).i.1.symm ⁻¹' U})
  refine ⟨W, fun p hp k hk ↦ ?_, isOpen_biInter_finset fun x _ ↦
    (hrep _).isOpen_inter_preimage (hdom _) (isOpen_setOf_mapsTo_contDiffMBMap (hLc x.1 x.2)
      (hLV x.1 x.2) ((a x.1 x.2).i.1.isOpen_inter_preimage_symm hU)), mem_iInter₂.2 fun x _ ↦
    ⟨hdom₀ x.1 x.2, hrep₀ x.1 x.2⟩⟩
  obtain ⟨x, hxt, hkx⟩ := mem_iUnion₂.1 (ht hk)
  have hpx := mem_iInter₂.1 hp x hxt
  have hy := interior_subset hkx.2
  have h := hpx.2 _ hy
  rw [(a x.1 x.2).rep_apply hpx.1 (hLV x.1 x.2 hy), (a x.1 x.2).j.1.left_inv hkx.1] at h
  have hs : ψ p k ∈ (a x.1 x.2).i.1.source := by
    have := hpx.1 (mem_image_of_mem _ (show (a x.1 x.2).j.1 k ∈ (a x.1 x.2).L from
      (a x.1 x.2).V_subset (hLV x.1 x.2 hy)))
    rwa [(a x.1 x.2).j.1.left_inv hkx.1] at this
  have h2 := h.2
  change (a x.1 x.2).i.1.symm ((a x.1 x.2).i.1 (ψ p k)) ∈ U at h2
  rw [(a x.1 x.2).i.1.left_inv hs] at h2
  exact h2

end Criteria

/-! ### The tangent map and the local representatives -/

section OneStep

variable {X : MBMfld.{u, u}} {Y : MBMfld.{u, v}} {ℓ : ℕ}

/- In this section `C^ℓ(X, Y)` carries the chart topology `CkMap.chartTopology` (not the instance,
which is the jet topology); the statements name it explicitly. -/
attribute [local instance 2000] CkMap.chartTopology

/-- The chart `tangentChart j j` of the tangent bundle, as an element of its atlas. -/
def tangentAtlasIdx {Z : MBMfld.{u, v}} (j : atlas Z.Model Z.Carrier) :
    atlas (MBMfld.tangent Z).Model (MBMfld.tangent Z).Carrier :=
  ⟨tangentChart j j.1, tangentChart_self_mem_atlas j⟩

/-- `C^(ℓ+1)` maps are `C^1`. -/
theorem CkMap.contMDiffMB_one (g : CkMap X.Model Y.Model (ℓ + 1) X.Carrier Y.Carrier) :
    ContMDiffMB X.Model Y.Model 1 g :=
  ⟨g.2.1, fun x hx ↦ (g.2.2 x hx).of_le (by omega)⟩

/-- The chart index of `C^ℓ(TX, TY)` built from a chart index `a` of `C^(ℓ+1)(X, Y)` and a compact
set `K` of directions: the charts `tangentChart j j`, `tangentChart i i`, the compact set `L × K`
and the open set `V × int K`. -/
def tangentIdx (a : CkMap.ChartIdx X.Model Y.Model X.Carrier Y.Carrier) {K : Set X.Model}
    (hK : IsCompact K) :
    CkMap.ChartIdx (MBMfld.tangent X).Model (MBMfld.tangent Y).Model (MBMfld.tangent X).Carrier
      (MBMfld.tangent Y).Carrier where
  j := tangentAtlasIdx a.j
  i := tangentAtlasIdx a.i
  L := a.L ×ˢ K
  isCompact_L := a.isCompact_L.prod hK
  L_subset q hq := (mem_tangentChart_target a.j a.j.1 q).2
    ⟨a.L_subset hq.1, a.j.1.map_target (a.L_subset hq.1)⟩
  V := ⟨(a.V : Set X.Model) ×ˢ interior K, a.V.isOpen.prod isOpen_interior⟩
  V_subset _ hq := ⟨a.V_subset hq.1, interior_subset hq.2⟩

/-- If `g` sends `j⁻¹(L)` into the source of `i`, then `Tg` sends the corresponding part of `TX`
into the source of the tangent chart. -/
theorem tangentCk_mem_dom {a : CkMap.ChartIdx X.Model Y.Model X.Carrier Y.Carrier}
    {K : Set X.Model} (hK : IsCompact K) {g : CkMap X.Model Y.Model (ℓ + 1) X.Carrier Y.Carrier}
    (hg : g ∈ a.dom) : MBMfld.tangentCk g ∈ (tangentIdx a hK).dom := by
  rintro _ ⟨q, hq, rfl⟩
  change tangentMap X.Model Y.Model g ((tangentChart a.j a.j.1).symm q) ∈
    (tangentChart a.i a.i.1).source
  rw [mem_tangentChart_self_source]
  exact hg (mem_image_of_mem _ hq.1)

/-- **The local representatives of `Tg`**: in the charts `tangentChart j j`, `tangentChart i i`,
`Tg` reads `(y, w) ↦ (i(g(j⁻¹ y)), d(rep g)(y, w))`. -/
theorem tangentIdx_rep_apply {a : CkMap.ChartIdx X.Model Y.Model X.Carrier Y.Carrier}
    {K : Set X.Model} (hK : IsCompact K) {g : CkMap X.Model Y.Model (ℓ + 1) X.Carrier Y.Carrier}
    (hg : g ∈ a.dom) {q : X.Model × X.Model} (hq : q ∈ (tangentIdx a hK).V) :
    (tangentIdx a hK).rep (MBMfld.tangentCk g) q =
      (a.i.1 (g (a.j.1.symm q.1)), dMB (a.rep g) q) := by
  rw [(tangentIdx a hK).rep_apply (tangentCk_mem_dom hK hg) hq]
  have hy : q.1 ∈ a.j.1.target := a.L_subset (a.V_subset hq.1)
  have hfy : g (a.j.1.symm q.1) ∈ a.i.1.source := hg (mem_image_of_mem _ (a.V_subset hq.1))
  have h := tangentMap_chart (CkMap.contMDiffMB_one g) a.j a.i hy hfy q.2
  change tangentChart a.i a.i.1 (tangentMap X.Model Y.Model g
    ((tangentChart a.j a.j.1).symm (q.1, q.2))) = _
  rw [h]
  refine Prod.ext rfl ?_
  change dMB (a.i.1 ∘ g ∘ a.j.1.symm) (q.1, q.2) = dMB (a.rep g) (q.1, q.2)
  refine dMB_congr_of_eventuallyEq (Filter.eventually_of_mem (a.V.isOpen.mem_nhds hq.1)
    fun y hy ↦ ?_) q.2
  exact (a.rep_apply hg hy).symm

/-- **A continuity criterion through the tangent map** (one half of the analogue of
[GN26, Lemma 4.1.6], for the chart topology): if `p ↦ ψ p ∈ C(X, Y)` and
`p ↦ Tψ(p) ∈ C^ℓ(TX, TY)` are continuous, then `ψ : P → C^(ℓ+1)(X, Y)` is continuous. The model of
`X` is assumed locally compact. -/
theorem continuous_of_tangentCk [LocallyCompactSpace X.Model] {P : Type*} [tP : TopologicalSpace P]
    {ψ : P → CkMap X.Model Y.Model (ℓ + 1) X.Carrier Y.Carrier}
    (h₀ : Continuous fun p ↦ CkMap.toC (ψ p))
    (h₁ : Continuous[_, CkMap.chartTopology (MBMfld.tangent X).Model (MBMfld.tangent Y).Model ℓ
      (MBMfld.tangent X).Carrier (MBMfld.tangent Y).Carrier] fun p ↦ MBMfld.tangentCk (ψ p)) :
    Continuous[_, CkMap.chartTopology X.Model Y.Model (ℓ + 1) X.Carrier Y.Carrier] ψ := by
  refine CkMap.continuous_of_rep h₀ fun a ↦ ?_
  rw [continuousOn_iff_continuous_domRestrict]
  refine ContDiffMBMap.continuous_of_continuous_dMap
    (continuousOn_iff_continuous_domRestrict.1 (continuousOn_iteratedD_zero_rep h₀ a)) ?_
  let V' : {K : Set X.Model // IsCompact K} → Opens (X.Model × X.Model) :=
    fun K ↦ (tangentIdx a K.2).V
  have hVU : ∀ K, V' K ≤ Opens.prodUniv a.V := fun K q hq ↦ hq.1
  have hcov : (Opens.prodUniv a.V : Set (X.Model × X.Model)) ⊆ ⋃ K, (V' K : Set _) := by
    intro q hq
    obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds q.2
    exact mem_iUnion.2 ⟨⟨K, hKc⟩, hq, mem_interior_iff_mem_nhds.2 hKn⟩
  refine (ContDiffMBMap.isEmbedding_restrictCover V' hVU hcov).continuous_iff.2
    (continuous_pi fun K ↦ ?_)
  have hrep := (tangentIdx a K.2).continuousOn_rep.comp_continuous
    (h₁.comp continuous_subtype_val) fun s : ψ ⁻¹' a.dom ↦ tangentCk_mem_dom K.2 s.2
  refine ((ContDiffMBMap.compLeftCLM (ContinuousLinearMap.snd ℝ Y.Model Y.Model)).continuous.comp
    hrep).congr fun s ↦ ?_
  ext q
  change ContinuousLinearMap.snd ℝ Y.Model Y.Model ((tangentIdx a K.2).rep
    (MBMfld.tangentCk (ψ s)) q) = ContDiffMBMap.restrictCLM (hVU K) (ContDiffMBMap.dMap
      (a.rep (ψ s))) q
  by_cases hq : q ∈ V' K
  · rw [tangentIdx_rep_apply K.2 s.2 hq, ContDiffMBMap.restrictCLM_apply _ _ hq,
      ContDiffMBMap.dMap_apply _ hq.1]
    rfl
  · rw [ContDiffMBMap.apply_of_notMem _ hq, ContDiffMBMap.apply_of_notMem _ hq, map_zero]

/-- The tangent charts `tangentChart i c` and `tangentChart i i` have the same inverse up to the
change of base coordinates `c → i`. -/
theorem tangentChart_symm_eq {Z : MBMfld.{u, v}} (i : atlas Z.Model Z.Carrier)
    (c : OpenPartialHomeomorph Z.Carrier Z.Model) {y : Z.Model} (hy : c.symm y ∈ i.1.source)
    (w : Z.Model) :
    (tangentChart i c).symm (y, w) = (tangentChart i i.1).symm (i.1 (c.symm y), w) := by
  refine TangentBundle.ext_vec ?_ ?_
  · change c.symm y = i.1.symm (i.1 (c.symm y))
    rw [i.1.left_inv hy]
  · change tangentCoordChange i ⟨chartAt Z.Model (c.symm y), chart_mem_atlas Z.Model _⟩
      (c.symm y) w = tangentCoordChange i ⟨chartAt Z.Model (i.1.symm (i.1 (c.symm y))),
        chart_mem_atlas Z.Model _⟩ (i.1.symm (i.1 (c.symm y))) w
    rw [i.1.left_inv hy]

/-- **The tangent map is continuous** for the chart topologies (the other half of the analogue
of [GN26, Lemma 4.1.6]): `T : C^(ℓ+1)(X, Y) → C^ℓ(TX, TY)`. In tangent charts, the local
representatives of `Tg` are obtained from those of `g` by `F ↦ (F, dF)`, a pullback along a smooth
map, and a superposition by a smooth map; the model of `X` is assumed locally compact. -/
theorem continuous_tangentCk [LocallyCompactSpace X.Model] :
    Continuous[CkMap.chartTopology X.Model Y.Model (ℓ + 1) X.Carrier Y.Carrier,
      CkMap.chartTopology (MBMfld.tangent X).Model (MBMfld.tangent Y).Model ℓ
        (MBMfld.tangent X).Carrier (MBMfld.tangent Y).Carrier]
      (MBMfld.tangentCk : CkMap X.Model Y.Model (ℓ + 1) X.Carrier Y.Carrier → _) := by
  -- the domains of the local representatives of `Tg` are open
  have hdom : ∀ a' : CkMap.ChartIdx (MBMfld.tangent X).Model (MBMfld.tangent Y).Model
      (MBMfld.tangent X).Carrier (MBMfld.tangent Y).Carrier,
      ∃ (i₁ : atlas X.Model X.Carrier) (c₁ : OpenPartialHomeomorph X.Carrier X.Model)
        (i₂ : atlas Y.Model Y.Carrier) (c₂ : OpenPartialHomeomorph Y.Carrier Y.Model),
        c₁ ∈ atlas X.Model X.Carrier ∧ c₂ ∈ atlas Y.Model Y.Carrier ∧
        a'.j.1 = tangentChart i₁ c₁ ∧ a'.i.1 = tangentChart i₂ c₂ := fun a' ↦ by
    obtain ⟨i₁, c₁, hc₁, h₁⟩ := exists_eq_tangentChart a'.j.2
    obtain ⟨i₂, c₂, hc₂, h₂⟩ := exists_eq_tangentChart a'.i.2
    exact ⟨i₁, c₁, i₂, c₂, hc₁, hc₂, h₁, h₂⟩
  have hdomiff : ∀ a' : CkMap.ChartIdx (MBMfld.tangent X).Model (MBMfld.tangent Y).Model
      (MBMfld.tangent X).Carrier (MBMfld.tangent Y).Carrier,
      ∀ (i₁ : atlas X.Model X.Carrier) (c₁ : OpenPartialHomeomorph X.Carrier X.Model)
        (i₂ : atlas Y.Model Y.Carrier) (c₂ : OpenPartialHomeomorph Y.Carrier Y.Model),
        a'.j.1 = tangentChart i₁ c₁ → a'.i.1 = tangentChart i₂ c₂ →
        ∀ g : CkMap X.Model Y.Model (ℓ + 1) X.Carrier Y.Carrier, MBMfld.tangentCk g ∈ a'.dom ↔
          MapsTo g (c₁.symm '' (Prod.fst '' a'.L)) (i₂.1.source ∩ c₂.source) := by
    intro a' i₁ c₁ i₂ c₂ h₁ h₂ g
    constructor
    · rintro hg _ ⟨y, ⟨q, hq, rfl⟩, rfl⟩
      have := hg (mem_image_of_mem _ hq)
      rw [h₂, mem_tangentChart_source] at this
      rw [h₁] at this
      exact this
    · rintro hg _ ⟨q, hq, rfl⟩
      rw [h₂, mem_tangentChart_source, h₁]
      exact hg (mem_image_of_mem _ (mem_image_of_mem _ hq))
  have hdomopen : ∀ a' : CkMap.ChartIdx (MBMfld.tangent X).Model (MBMfld.tangent Y).Model
      (MBMfld.tangent X).Carrier (MBMfld.tangent Y).Carrier,
      IsOpen (MBMfld.tangentCk (X := X) (Y := Y) (ℓ := ℓ) ⁻¹' a'.dom) := by
    intro a'
    obtain ⟨i₁, c₁, i₂, c₂, -, -, h₁, h₂⟩ := hdom a'
    have hS : IsCompact (c₁.symm '' (Prod.fst '' a'.L)) := by
      refine (a'.isCompact_L.image continuous_fst).image_of_continuousOn
        (c₁.continuousOn_symm.mono ?_)
      rintro _ ⟨q, hq, rfl⟩
      have := a'.L_subset hq
      rw [h₁, mem_tangentChart_target] at this
      exact this.1
    have h := (ContinuousMap.isOpen_setOfPred_mapsTo hS (i₂.1.open_source.inter
      c₂.open_source)).preimage (CkMap.continuous_toC_chartTopology (H := X.Model)
        (E := Y.Model) (ℓ := ℓ + 1) (M := X.Carrier) (N := Y.Carrier))
    convert h using 1
    ext g
    exact hdomiff a' i₁ c₁ i₂ c₂ h₁ h₂ g
  have hrep : ∀ a' : CkMap.ChartIdx (MBMfld.tangent X).Model (MBMfld.tangent Y).Model
      (MBMfld.tangent X).Carrier (MBMfld.tangent Y).Carrier,
      ContinuousOn (fun g ↦ a'.rep (MBMfld.tangentCk (X := X) (Y := Y) (ℓ := ℓ) g))
        (MBMfld.tangentCk ⁻¹' a'.dom) := by
    intro a'
    obtain ⟨i₁, c₁, i₂, c₂, hc₁, hc₂, h₁, h₂⟩ := hdom a'
    refine fun g₀ hg₀ ↦ ContinuousAt.continuousWithinAt ?_
    set S := c₁.symm '' (Prod.fst '' a'.L)
    have hLt : ∀ q ∈ a'.L, q.1 ∈ c₁.target ∧ c₁.symm q.1 ∈ i₁.1.source := fun q hq ↦ by
      have := a'.L_subset hq
      rwa [h₁, mem_tangentChart_target] at this
    have hSc : IsCompact S := (a'.isCompact_L.image continuous_fst).image_of_continuousOn
      (c₁.continuousOn_symm.mono fun _ ⟨q, hq, e⟩ ↦ e ▸ (hLt q hq).1)
    have hSi : S ⊆ i₁.1.source := fun _ ⟨_, ⟨q, hq, e⟩, e'⟩ ↦ e' ▸ e ▸ (hLt q hq).2
    have hS₀ := (hdomiff a' i₁ c₁ i₂ c₂ h₁ h₂ g₀).1 hg₀
    set Lb := i₁.1 '' S
    have hLbc : IsCompact Lb := hSc.image_of_continuousOn (i₁.1.continuousOn.mono hSi)
    set Q := i₁.1.target ∩ i₁.1.symm ⁻¹' (g₀ ⁻¹' (i₂.1.source ∩ c₂.source))
    have hQ : IsOpen Q := i₁.1.isOpen_inter_preimage_symm
      ((i₂.1.open_source.inter c₂.open_source).preimage (CkMap.toC g₀).continuous)
    have hLbQ : Lb ⊆ Q := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨i₁.1.map_source (hSi hx), ?_⟩
      rw [mem_preimage, i₁.1.left_inv (hSi hx)]
      exact hS₀ hx
    obtain ⟨Vb, hVb, hLbV, hVQ, hVc⟩ := exists_open_between_and_isCompact_closure hLbc hQ hLbQ
    let Vbo : Opens X.Model := ⟨Vb, hVb⟩
    let b : CkMap.ChartIdx X.Model Y.Model X.Carrier Y.Carrier :=
      ⟨i₁, i₂, closure Vb, hVc, fun y hy ↦ (hVQ hy).1, Vbo, subset_closure⟩
    have hg₀b : g₀ ∈ b.dom := by
      rintro _ ⟨y, hy, rfl⟩
      exact (hVQ hy).2.1
    -- the pullback `α(y, w) = (i₁(c₁⁻¹ y), w)`
    let α : X.Model × X.Model → X.Model × X.Model := fun q ↦ (i₁.1 (c₁.symm q.1), q.2)
    have hαL : ∀ q ∈ a'.V, (α q).1 ∈ Lb := fun q hq ↦
      mem_image_of_mem _ (mem_image_of_mem _ (mem_image_of_mem _ (a'.V_subset hq)))
    have hα : ContDiffMBOn ℓ α a'.V := by
      have hτ := (smoothMBOn_transition hc₁ i₁.2 ℓ).comp_clm
        (ContinuousLinearMap.fst ℝ X.Model X.Model)
        (c₁.isOpen_inter_preimage_symm i₁.1.open_source)
      refine ContDiffMBOn.prodMk a'.V.isOpen (hτ.mono fun q hq ↦ hLt q (a'.V_subset hq))
        (((ContinuousLinearMap.snd ℝ X.Model X.Model).contDiffMBOn ℓ univ).mono (subset_univ _))
    have hαmaps : MapsTo α a'.V (Opens.prodUniv Vbo) := fun q hq ↦ hLbV (hαL q hq)
    let Pm : ContDiffMBMap Y.Model (ℓ + 1) Vbo →L[ℝ]
        ContDiffMBMap (Y.Model × Y.Model) ℓ a'.V :=
      (ContDiffMBMap.compRightOfContDiffCLM hα hαmaps).comp ContDiffMBMap.graphDataCLM
    have hP : ∀ (F' : ContDiffMBMap Y.Model (ℓ + 1) Vbo), ∀ q ∈ a'.V,
        Pm F' q = (F' (α q).1, dMB F' (α q)) := fun F' q hq ↦ by
      change ContDiffMBMap.compRightOfContDiff hα hαmaps (ContDiffMBMap.graphDataCLM F') q = _
      rw [ContDiffMBMap.compRightOfContDiff_apply _ _ _ hq,
        ContDiffMBMap.graphDataCLM_apply _ (hLbV (hαL q hq))]
    -- the superposition by `(z, v) ↦ (c₂(i₂⁻¹ z), v)`
    set O := (i₂.1.target ∩ i₂.1.symm ⁻¹' c₂.source) ×ˢ (univ : Set Y.Model)
    have hO : IsOpen O := (i₂.1.isOpen_inter_preimage_symm c₂.open_source).prod isOpen_univ
    let hf : Y.Model × Y.Model → Y.Model × Y.Model := fun z ↦ (c₂ (i₂.1.symm z.1), z.2)
    have hsm : SmoothMBOn hf O := fun k ↦ by
      have hτ := (smoothMBOn_transition i₂.2 hc₂ k).comp_clm
        (ContinuousLinearMap.fst ℝ Y.Model Y.Model)
        (i₂.1.isOpen_inter_preimage_symm c₂.open_source)
      refine ContDiffMBOn.prodMk hO (hτ.mono fun z hz ↦ hz.1)
        (((ContinuousLinearMap.snd ℝ Y.Model Y.Model).contDiffMBOn k univ).mono (subset_univ _))
    set W := {F' : ContDiffMBMap Y.Model (ℓ + 1) Vbo |
      ∀ z ∈ Lb, F' z ∈ i₂.1.target ∩ i₂.1.symm ⁻¹' c₂.source}
    have hW : IsOpen W := isOpen_setOf_mapsTo_contDiffMBMap hLbc hLbV
      (i₂.1.isOpen_inter_preimage_symm c₂.open_source)
    have hWmaps : ∀ F' ∈ W, MapsTo (Pm F') a'.V O := fun F' hF' q hq ↦ by
      rw [hP F' q hq]
      exact ⟨hF' _ (hαL q hq), mem_univ _⟩
    have hΦ := (ContDiffMBMap.contDiffMBOn_compLeftOn ℓ (U := a'.V) hO hsm (k := 0) hW
      (Pm.contDiffMBOn 0 _) hWmaps).continuousOn
    have hrepW : ∀ g ∈ b.dom, MBMfld.tangentCk g ∈ a'.dom → b.rep g ∈ W := fun g hgb hga z hz ↦ by
      obtain ⟨x, hx, rfl⟩ := hz
      have hgx := (hdomiff a' i₁ c₁ i₂ c₂ h₁ h₂ g).1 hga hx
      rw [b.rep_apply hgb (hLbV ⟨x, hx, rfl⟩), i₁.1.left_inv (hSi hx)]
      refine ⟨i₂.1.map_source hgx.1, ?_⟩
      change i₂.1.symm (i₂.1 (g x)) ∈ c₂.source
      rw [i₂.1.left_inv hgx.1]
      exact hgx.2
    have hcont : ContinuousAt (fun g ↦ ContDiffMBMap.compLeftOn hf O (Pm (b.rep g))) g₀ :=
      ContinuousAt.comp (f := b.rep) (hΦ.continuousAt (hW.mem_nhds (hrepW g₀ hg₀b hg₀)))
        (b.continuousOn_rep.continuousAt (b.isOpen_dom_chartTopology.mem_nhds hg₀b))
    refine hcont.congr (Filter.eventually_of_mem
      ((b.isOpen_dom_chartTopology.inter (hdomopen a')).mem_nhds ⟨hg₀b, hg₀⟩) fun g hg ↦ ?_)
    refine ContDiffMBMap.ext fun q ↦ ?_
    by_cases hq : q ∈ a'.V
    · have hq1 := hLt q (a'.V_subset hq)
      have hgq := (hdomiff a' i₁ c₁ i₂ c₂ h₁ h₂ g).1 hg.2
        (mem_image_of_mem _ (mem_image_of_mem _ (a'.V_subset hq)))
      have hτq : i₁.1 (c₁.symm q.1) ∈ i₁.1.target := i₁.1.map_source hq1.2
      have hfy : g (i₁.1.symm (i₁.1 (c₁.symm q.1))) ∈ i₂.1.source := by
        rw [i₁.1.left_inv hq1.2]; exact hgq.1
      have key := tangentMap_chart (CkMap.contMDiffMB_one g) i₁ i₂ hτq hfy q.2
      rw [ContDiffMBMap.compLeftOn_apply hO (hsm ℓ) (hWmaps _ (hrepW g hg.1 hg.2)) hq,
        hP _ q hq, a'.rep_apply hg.2 hq]
      have hαV : (α q).1 ∈ Vb := hLbV (hαL q hq)
      rw [b.rep_apply hg.1 hαV]
      have hd : dMB (b.rep g) (α q) = dMB (i₂.1 ∘ g ∘ i₁.1.symm) (α q) :=
        dMB_congr_of_eventuallyEq (Filter.eventually_of_mem (hVb.mem_nhds hαV)
          fun y hy ↦ b.rep_apply hg.1 hy) q.2
      rw [hd]
      have e : (tangentChart i₁ c₁).symm q =
          (tangentChart i₁ i₁.1).symm (i₁.1 (c₁.symm q.1), q.2) :=
        tangentChart_symm_eq i₁ c₁ hq1.2 q.2
      rw [h₂, h₁, e]
      refine Prod.ext ?_ ?_
      · change c₂ (i₂.1.symm (i₂.1 (g (i₁.1.symm (i₁.1 (c₁.symm q.1)))))) =
          c₂ (g (i₁.1.symm (i₁.1 (c₁.symm q.1))))
        rw [i₂.1.left_inv hfy]
      · exact (congrArg Prod.snd key).symm
    · rw [ContDiffMBMap.apply_of_notMem _ hq, ContDiffMBMap.apply_of_notMem _ hq]
  refine CkMap.continuous_of_rep (continuous_toC_of_rep hdomopen hrep) hrep

/-- **The chart topology satisfies [GN26, Lemma 4.1.6]** (in the form used in its proof):
the chart topology of `C^(ℓ+1)(X, Y)` is initial with respect to `f ↦ f ∈ C(X, Y)` and
`f ↦ Tf ∈ C^ℓ(TX, TY)`, the latter with the chart topology, if the model of `X` is locally
compact. -/
theorem chartTopology_succ [LocallyCompactSpace X.Model] :
    CkMap.chartTopology X.Model Y.Model (ℓ + 1) X.Carrier Y.Carrier =
      TopologicalSpace.induced CkMap.toC inferInstance ⊓
        TopologicalSpace.induced MBMfld.tangentCk (CkMap.chartTopology (MBMfld.tangent X).Model
          (MBMfld.tangent Y).Model ℓ (MBMfld.tangent X).Carrier (MBMfld.tangent Y).Carrier) := by
  refine le_antisymm (le_inf (continuous_iff_le_induced.1 CkMap.continuous_toC_chartTopology)
    (continuous_iff_le_induced.1 continuous_tangentCk)) ?_
  let τ : TopologicalSpace (CkMap X.Model Y.Model (ℓ + 1) X.Carrier Y.Carrier) :=
    TopologicalSpace.induced CkMap.toC inferInstance ⊓
      TopologicalSpace.induced MBMfld.tangentCk inferInstance
  have h := continuous_of_tangentCk (tP := τ) (ψ := id)
    (continuous_iff_le_induced.2 inf_le_left) (continuous_iff_le_induced.2 inf_le_right)
  simpa [induced_id] using continuous_iff_le_induced.1 h

/-- **The chart topology of `C^0(X, Y)` is the compact-open topology.** -/
theorem chartTopology_zero :
    CkMap.chartTopology X.Model Y.Model 0 X.Carrier Y.Carrier =
      TopologicalSpace.induced CkMap.toC inferInstance := by
  refine le_antisymm (continuous_iff_le_induced.1 CkMap.continuous_toC_chartTopology) ?_
  let τ : TopologicalSpace (CkMap X.Model Y.Model 0 X.Carrier Y.Carrier) :=
    TopologicalSpace.induced CkMap.toC inferInstance
  have h₀ : Continuous[τ, _] fun g : CkMap X.Model Y.Model 0 X.Carrier Y.Carrier ↦ CkMap.toC g :=
    continuous_induced_dom
  change τ ≤ TopologicalSpace.induced CkMap.toC inferInstance ⊓ TopologicalSpace.generateFrom _
  refine le_inf le_rfl (le_generateFrom ?_)
  rintro _ ⟨a, O, hO, rfl⟩
  have hc0 := continuousOn_iteratedD_zero_rep (tP := τ) (ψ := id) h₀ a
  have hc : @ContinuousOn _ _ τ _ a.rep a.dom := fun x hx ↦ by
    have h := hc0 x hx
    unfold ContinuousWithinAt at h ⊢
    rw [ContDiffMBMap.isEmbedding_toPi.tendsto_nhds_iff, tendsto_pi_nhds]
    intro j
    obtain rfl : j = 0 := Fin.fin_one_eq_zero j
    exact h
  exact hc.isOpen_inter_preimage (a.isOpen_domC.preimage h₀) hO

end OneStep

end LocallyConvex.Manifolds
