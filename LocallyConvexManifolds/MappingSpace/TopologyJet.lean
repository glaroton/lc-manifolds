/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.MappingSpace.TopologyGN

/-!
# The compact-open `C^ℓ` topology through jets on compact sets in charts

The topology of `C^ℓ(M, N)` (the instance `CkMap.instTopologicalSpace`, `MappingSpace/Ck.lean`) is
the jet topology `CkMap.jetTopology`, which works for every Hausdorff locally convex model and every
manifold `M`, compact or not. This file compares it with [GN26, Definition 4.1.2] (p. 339). The
chart topology `CkMap.chartTopology` (local representatives on *open* subsets of compact sets in
charts) agrees with it for a locally compact model (`CkMap.chartTopology_eq_jetTopology`,
`MappingSpace/Ck.lean`); if the model `H` of `M` is not locally compact (for instance
infinite-dimensional), compact sets have empty interior and the chart topology collapses to the
compact-open `C^0` topology.

**The jet topology** (`CkMap.jetTopology`, defined in `MappingSpace/Ck.lean`). For charts `j` of
`M`, `i` of `N`, a compact set `K` in the target of `j` (no interior is required) and `m ≤ ℓ`, the
`m`-jet of `g` on `K` is `d^(m)(i ∘ g ∘ j⁻¹)|_{K × H^m} ∈ C(K × H^m, E)`, defined on the open set of
maps `g` with `g(j⁻¹(K)) ⊆ i.source`. The jet topology is the coarsest topology finer than the
compact-open topology of `C(M, N)` that makes all the jets continuous (compact-open topology on
`C(K × H^m, E)`). A subbasis consists of the open sets of `C(M, N)` and the sets
`{g : g(j⁻¹(K)) ⊆ i.source, d^(m)(i ∘ g ∘ j⁻¹)|_{K × H^m} ∈ O}`. This is the weak (compact-open)
`C^r` topology of [Hir76, Chapter 2, §1, pp. 34–35], with the uniform bounds on the derivatives over
`K` replaced by the compact-open topology of `C(K × H^m, E)`, as in the compact-open `C^k` topology
of [GN26, Definition 1.7.10] (p. 90), for maps on open sets.

The jets and the jet topologies are defined in `MappingSpace/Ck.lean`: `jetOn m f S`, the `m`-jet
`d^(m) f|_{S × H^m}` of `f : H → E` on any set `S ⊆ H`; `CkMap.CompactIdx`, `CkMap.CompactIdx.jet`:
charts `j`, `i`, a compact set `K` and the jets of `i ∘ g ∘ j⁻¹` on `K`;
`CkMap.jetTopology H E ℓ M N`, `SmoothMap.jetTopologySm H E M N`: the jet topologies of
`C^ℓ(M, N)` and `C^∞(M, N)`, the instances; `CkMap.continuous_jetTopology_iff`.

## Main definitions

* `CompactLocalizable Z`: every compact set is covered by finitely many compact sets inside
  prescribed neighborhoods of its points; true for Hausdorff (`R₁`) and for locally compact `Z`.

## Main results

* `MBMfld.gnTopology_le_jetTopology`: the topology of [GN26, Definition 4.1.2] is always finer than
  the jet topology; `MBMfld.jetTopology_le_gnTopology`: the converse, when the iterated tangent
  bundles of `M` are compact-localizable.
* `MBMfld.jetTopology_eq_gnTopology`, `MBMfld.jetTopologySm_eq_gnTopologySm`: **the jet topology is
  the compact-open `C^ℓ` topology of [GN26, Definition 4.1.2]**, `ℓ ∈ ℕ ∪ {∞}`, for every Hausdorff
  manifold `M` (their manifolds are Hausdorff, [GN26, Definition 3.1.4], p. 242), compact or not,
  modeled on any Hausdorff locally convex space;
  `MBMfld.jetTopology_eq_gnTopology_of_locallyCompactSpace`: the same for a locally compact model,
  without the Hausdorff hypothesis. This is **[GN26, Theorem 4.2.2(b)]**, in that generality: the
  topology of `C^ℓ(M, N)` (for compact `M`, the topology underlying the atlases
  `LocalAddition.mappingAtlasCk`, `LocalAddition.mappingAtlasSm`) is the topology of
  [GN26, Definition 4.1.2]. For unbundled `M`, `N`, with `N` in any universe, these are
  `CkMap.topology_eq_gnTopology`, `SmoothMap.topology_eq_gnTopologySm` and their variants
  (`MappingSpace/TopologyULift.lean`).
* `MBMfld.jetTopology_eq_chartTopology`: for a locally compact model, the jet topology is the
  chart topology (`CkMap.chartTopology_eq_jetTopology` for bundled manifolds).

## Implementation notes

* **The comparison with [GN26, Definition 4.1.2]** is by induction on the order, through the tangent
  map as in the proof of [GN26, Lemma 4.1.6] (p. 340): in the charts `tangentChart j j`,
  `tangentChart i i` the local representative of `Tg` is `(y, w) ↦ (F y, dF(y, w))`,
  `F = i ∘ g ∘ j⁻¹` (`tangentJetIdx_jet`), and the jets of `dF` and those of `F` determine each
  other by `d^(m+1)F(x, v₀, v) = d^(m)(dF)((x, v₀), (v, 0))` ([GN26, (1.36)], p. 42; `jetOn_succ`)
  and the formula for `d^(m)(dF)` (`jetOn_dMB`), the identities behind the proof of
  [GN26, Lemma 4.1.12] (pp. 342–344). Only the charts `tangentChart j j` are used at each step,
  which is why the induction is run for families of chart pairs that cover `M × N` (compare
  [GN26, Lemma 4.1.17], p. 346: any atlas gives the topology). We do not claim these arguments are
  new.
* **Infinite-dimensional subtleties.** The compact sets `K` have empty interior when `H` is not
  locally compact, so jets are taken on `K × H^m` itself, not on open sets; continuity on the
  non-compact set `K × H` of the jets of `dF` is reduced to compact subsets
  (`continuousOn_jetOn_of_isCompact`). Recovering the compact-open topology of `C(T^n M, T^n N)`
  from compact sets inside charts needs every compact subset of `T^n M` to be a finite union of
  compact sets inside charts (`CompactLocalizable`): this holds for Hausdorff `M`
  (`IsCompact.finite_compact_cover`; Glöckner–Neeb use the corresponding [GN26, Lemma A.6.11],
  p. 873, for Hausdorff spaces) and for a locally compact model; for non-Hausdorff manifolds with
  infinite-dimensional models we only prove that [GN26, Definition 4.1.2] is finer than the jet
  topology. `t2Space_tangentBundle`: tangent bundles of Hausdorff manifolds are Hausdorff.
* The jet topology is the instance `CkMap.instTopologicalSpace` (and `SmoothMap.jetTopologySm` is
  `SmoothMap.instTopologicalSpace`), so every statement about the topology of `C^ℓ(M, N)` holds for
  arbitrary models. The manifold structure of `C^ℓ(M, N)` for compact `M` (`MappingSpace/Ck.lean`)
  is a manifold structure for this topology.
* The induction runs over `MBMfld.{u, v}`, so here `N` lives in `Type (max u v)`, `u` the universe
  of `M` and of the models; `MappingSpace/TopologyULift.lean` transports the results to `N` in any
  universe along `ULift`.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
* [M. W. Hirsch, *Differential Topology*][Hir76]
-/

@[expose] public section

open Set Filter Function TopologicalSpace
open scoped Topology
open LocallyConvex.Analysis

noncomputable section

universe u v w

namespace LocallyConvex.Manifolds

/-! ### Jets on subsets of a locally convex space -/

section Jets

variable {H : Type u} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H]
  {E : Type v} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- The reindexing `((x, a), (v, w)) ↦ (x, a, v₁, …, vₘ)` of the first term of the jets of `dγ`. -/
def jetDA (T : Set (H × H)) (m : ℕ) :
    C(T × (Fin m → H × H), (Prod.fst '' T : Set H) × (Fin (m + 1) → H)) :=
  ⟨fun p ↦ (⟨p.1.1.1, mem_image_of_mem _ p.1.2⟩, Fin.cons p.1.1.2 fun l ↦ (p.2 l).1), by
    fun_prop⟩

/-- The reindexing `((x, a), (v, w)) ↦ (x, v₁, …, wᵢ, …, vₘ)` of the other terms of the jets of
`dγ`. -/
def jetDB (T : Set (H × H)) (m : ℕ) (i : Fin m) :
    C(T × (Fin m → H × H), (Prod.fst '' T : Set H) × (Fin m → H)) :=
  ⟨fun p ↦ (⟨p.1.1.1, mem_image_of_mem _ p.1.2⟩, update (fun l ↦ (p.2 l).1) i (p.2 i).2), by
    fun_prop⟩

/-- **The jets of `dγ`** in terms of those of `γ`: on a set `T ⊆ U × H`,
`d^(m)(dγ) = d^(m+1)γ ∘ A + ∑ᵢ d^(m)γ ∘ Bᵢ` (`ContDiffMBOn.iteratedDMB_dMB`). -/
theorem jetOn_dMB [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H]
    [T2Space H] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    [T2Space E] {k m : ℕ} {γ : H → E} {U : Set H} (hU : IsOpen U)
    (hγ : ContDiffMBOn (k + 1) γ U) {T : Set (H × H)} (hT : Prod.fst '' T ⊆ U) (hm : m ≤ k) :
    jetOn m (dMB γ) T = (jetOn (m + 1) γ (Prod.fst '' T)).comp (jetDA T m) +
      ∑ i : Fin m, (jetOn m γ (Prod.fst '' T)).comp (jetDB T m i) := by
  have hTU : T ⊆ U ×ˢ univ := fun q hq ↦ ⟨hT (mem_image_of_mem _ hq), mem_univ _⟩
  ext p
  simp only [ContinuousMap.add_apply, ContinuousMap.sum_apply, ContinuousMap.comp_apply]
  rw [jetOn_apply hγ.2.2 hTU hm, jetOn_apply hγ hT (by omega)]
  simp only [jetOn_apply hγ hT (show m ≤ k + 1 by omega)]
  exact hγ.iteratedDMB_dMB hU m hm p.1.1.1 (hT (mem_image_of_mem _ p.1.2)) p.1.1.2 _ _

/-- The reindexing `(x, v₀, …, vₘ) ↦ ((x, v₀), (v₁, 0), …, (vₘ, 0))`. -/
def jetSucc (S : Set H) (m : ℕ) :
    C(S × (Fin (m + 1) → H), (S ×ˢ (univ : Set H) : Set (H × H)) × (Fin m → H × H)) :=
  ⟨fun p ↦ (⟨((p.1 : H), p.2 0), p.1.2, mem_univ _⟩, fun i ↦ (p.2 i.succ, 0)), by fun_prop⟩

/-- **The jets of order `m + 1` of `γ` from those of order `m` of `dγ`** ([GN26, (1.36)]). -/
theorem jetOn_succ {k m : ℕ} {γ : H → E} {U S : Set H} (hγ : ContDiffMBOn (k + 1) γ U)
    (hSU : S ⊆ U) (hm : m ≤ k) :
    jetOn (m + 1) γ S = (jetOn m (dMB γ) (S ×ˢ univ)).comp (jetSucc S m) := by
  ext p
  rw [ContinuousMap.comp_apply, jetOn_apply hγ hSU (by omega),
    jetOn_apply hγ.2.2 (prod_mono hSU subset_rfl) hm]
  exact iteratedDMB_succ_eq_dMB m γ _ _

end Jets

/-! ### Localizing compact sets -/

section Localizable

/-- A space in which **compact sets can be localized**: every compact set `C` is covered by
finitely many compact sets, each inside a prescribed neighborhood of one of its points. This holds
in locally compact spaces and in `R₁` (for instance Hausdorff) spaces; it is what is needed to
describe the compact-open topology by compact sets inside charts. -/
def CompactLocalizable (Z : Type*) [TopologicalSpace Z] : Prop :=
  ∀ C : Set Z, IsCompact C → ∀ W : Z → Set Z, (∀ z ∈ C, W z ∈ 𝓝 z) →
    ∃ (t : Finset Z) (L : Z → Set Z), (∀ z ∈ t, z ∈ C ∧ IsCompact (L z) ∧ L z ⊆ W z) ∧
      C ⊆ ⋃ z ∈ t, L z

/-- Locally compact spaces are compact-localizable. -/
theorem CompactLocalizable.of_locallyCompactSpace (Z : Type*) [TopologicalSpace Z]
    [LocallyCompactSpace Z] : CompactLocalizable Z := by
  intro C hC W hW
  have h : ∀ z ∈ C, ∃ L, L ∈ 𝓝 z ∧ L ⊆ W z ∧ IsCompact L := fun z hz ↦ local_compact_nhds (hW z hz)
  choose! L hLn hLW hLc using h
  obtain ⟨t, htC, ht⟩ := hC.elim_nhds_subcover L hLn
  exact ⟨t, L, fun z hz ↦ ⟨htC z hz, hLc z (htC z hz), hLW z (htC z hz)⟩, ht⟩

/-- `R₁` (for instance Hausdorff) spaces are compact-localizable
(`IsCompact.finite_compact_cover`). -/
theorem CompactLocalizable.of_r1Space (Z : Type*) [TopologicalSpace Z] [R1Space Z] :
    CompactLocalizable Z := by
  intro C hC W hW
  obtain ⟨t, htC, ht⟩ := hC.elim_nhds_subcover (fun z ↦ interior (W z))
    fun z hz ↦ interior_mem_nhds.2 (hW z hz)
  obtain ⟨L, hLc, hLW, hCL⟩ := hC.finite_compact_cover t (fun z ↦ interior (W z))
    (fun _ _ ↦ isOpen_interior) ht
  exact ⟨t, L, fun z hz ↦ ⟨htC z hz, hLc z, (hLW z).trans interior_subset⟩, hCL.le⟩

end Localizable

/-! ### Jets in charts and the jet topology of `C^ℓ(M, N)` -/

section JetTopology

variable {H : Type u} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [IsTopologicalAddGroup H]
  [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {ℓ : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [MBManifold H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [MBManifold E N]

/-- In a compact space, the maps with values in an open set form an open set. -/
theorem ContinuousMap.isOpen_setOf_forall_mem {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace X] {O : Set Y} (hO : IsOpen O) :
    IsOpen {γ : C(X, Y) | ∀ x, γ x ∈ O} := by
  simpa [MapsTo] using ContinuousMap.isOpen_setOfPred_mapsTo (K := univ) isCompact_univ hO

/-- **The compact-open part of the jet topology is determined by the `0`-jets** in a family `A`
of pairs of charts covering `M × N`, if compact subsets of `M` can be localized
(`CompactLocalizable`, for instance `M` Hausdorff or its model locally compact). -/
theorem CkMap.continuous_toC_of_jet (hloc : CompactLocalizable M)
    {A : Set (atlas H M × atlas E N)}
    (hA : ∀ x y, ∃ c ∈ A, x ∈ c.1.1.source ∧ y ∈ c.2.1.source)
    {P : Type*} [TopologicalSpace P] {ψ : P → CkMap H E ℓ M N}
    (hdom : ∀ a : CkMap.CompactIdx H E M N, (a.j, a.i) ∈ A → IsOpen (ψ ⁻¹' a.dom))
    (hjet : ∀ a : CkMap.CompactIdx H E M N, (a.j, a.i) ∈ A →
      ContinuousOn (fun p ↦ a.jet 0 (ψ p)) (ψ ⁻¹' a.dom)) :
    Continuous fun p ↦ CkMap.toC (ψ p) := by
  refine ContinuousMap.continuous_compactOpen.2 fun K hK U hU ↦ isOpen_iff_forall_mem_open.2
    fun p₀ hp₀ ↦ ?_
  set g₀ := CkMap.toC (ψ p₀)
  choose c hcA hc₁ hc₂ using fun x ↦ hA x (g₀ x)
  set W : M → Set M := fun x ↦ (c x).1.1.source ∩ g₀ ⁻¹' (U ∩ (c x).2.1.source)
  have hW : ∀ x ∈ K, W x ∈ 𝓝 x := fun x hx ↦
    ((c x).1.1.open_source.inter ((hU.inter (c x).2.1.open_source).preimage
      g₀.continuous)).mem_nhds ⟨hc₁ x, hp₀ hx, hc₂ x⟩
  obtain ⟨t, L, hL, hKL⟩ := hloc K hK W hW
  have hLs : ∀ z ∈ t, L z ⊆ (c z).1.1.source := fun z hz ↦ (hL z hz).2.2.trans inter_subset_left
  let a : t → CkMap.CompactIdx H E M N := fun z ↦
    ⟨(c z).1, (c z).2, (c z).1.1 '' L z,
      (hL z z.2).2.1.image_of_continuousOn ((c z).1.1.continuousOn.mono (hLs z z.2)),
      fun _ ⟨x, hx, e⟩ ↦ e ▸ (c z).1.1.map_source (hLs z z.2 hx)⟩
  have hsymm : ∀ z : t, (a z).j.1.symm '' (a z).K = L z := fun z ↦ by
    change (c z).1.1.symm '' ((c z).1.1 '' L z) = L z
    exact (c z).1.1.symm_image_image_of_subset_source (hLs z z.2)
  set O : t → Set E := fun z ↦ (c z).2.1.target ∩ (c z).2.1.symm ⁻¹' U
  have hO : ∀ z, IsOpen (O z) := fun z ↦ (c z).2.1.isOpen_inter_preimage_symm hU
  have hcpt : ∀ z : t, CompactSpace ((a z).K × (Fin 0 → H)) := fun z ↦ by
    have := isCompact_iff_compactSpace.mp (a z).isCompact_K
    infer_instance
  have hdom₀ : ∀ z : t, ψ p₀ ∈ (a z).dom := fun z ↦ by
    change MapsTo g₀ _ _
    rw [hsymm z]
    exact fun x hx ↦ ((hL z z.2).2.2 hx).2.2
  refine ⟨⋂ z : t, (ψ ⁻¹' (a z).dom ∩ (fun p ↦ (a z).jet 0 (ψ p)) ⁻¹' {γ | ∀ y, γ y ∈ O z}),
    fun p hp k hk ↦ ?_, isOpen_iInter_of_finite fun z ↦ ?_, mem_iInter.2 fun z ↦ ⟨hdom₀ z, ?_⟩⟩
  · obtain ⟨z, hz, hkz⟩ := mem_iUnion₂.1 (hKL hk)
    have hp' := mem_iInter.1 hp ⟨z, hz⟩
    have hks : k ∈ (c z).1.1.source := hLs z hz hkz
    have hy := hp'.2 (⟨(c z).1.1 k, mem_image_of_mem _ hkz⟩, Fin.elim0)
    rw [(a ⟨z, hz⟩).jet_apply hp'.1 (Nat.zero_le ℓ)] at hy
    change (c z).2.1 (ψ p ((c z).1.1.symm ((c z).1.1 k))) ∈ O ⟨z, hz⟩ at hy
    rw [(c z).1.1.left_inv hks] at hy
    have hsrc : ψ p k ∈ (c z).2.1.source := by
      have h1 := hp'.1
      change MapsTo (ψ p) _ _ at h1
      rw [hsymm ⟨z, hz⟩] at h1
      exact h1 hkz
    have h2 := hy.2
    rw [mem_preimage, (c z).2.1.left_inv hsrc] at h2
    exact h2
  · have := hcpt z
    exact (hjet (a z) (hcA z)).isOpen_inter_preimage (hdom (a z) (hcA z))
      (ContinuousMap.isOpen_setOf_forall_mem (hO z))
  · intro y
    rw [mem_ofPred_eq, (a z).jet_apply (hdom₀ z) (Nat.zero_le ℓ)]
    obtain ⟨x, hx, hxe⟩ := y.1.2
    have hxs : x ∈ (c z).1.1.source := hLs z z.2 hx
    have hgx := ((hL z z.2).2.2 hx).2
    change (c z).2.1 (g₀ ((c z).1.1.symm (y.1 : H))) ∈ O z
    rw [← hxe, (c z).1.1.left_inv hxs]
    refine ⟨(c z).2.1.map_source hgx.2, ?_⟩
    rw [mem_preimage, (c z).2.1.left_inv hgx.2]
    exact hgx.1

end JetTopology

/-! ### Hausdorff tangent bundles -/

section T2

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

/-- **The tangent bundle of a Hausdorff manifold is Hausdorff**: points in different fibers are
separated by the projection, points in one fiber by a chart. -/
instance t2Space_tangentBundle [T2Space M] : T2Space (TangentBundle E M) := by
  refine t2Space_iff_disjoint_nhds.2 fun v w hvw ↦ ?_
  by_cases h : v.proj = w.proj
  · obtain ⟨i, c, -, he⟩ := exists_eq_tangentChart (chart_mem_atlas (E × E) v)
    set e := chartAt (E × E) v
    have hv : v ∈ e.source := mem_chart_source _ v
    have hw : w ∈ e.source := by
      have he' : e = tangentChart i c := he
      rw [he', mem_tangentChart_source] at hv ⊢
      rwa [← h]
    have hne : e v ≠ e w := fun heq ↦ hvw (e.injOn hv hw heq)
    exact (e.continuousAt hv).disjoint (disjoint_nhds_nhds.2 hne) (e.continuousAt hw)
  · have hc := (tangentBundleCore E M).continuous_proj
    exact (hc.continuousAt (x := v)).disjoint (disjoint_nhds_nhds.2 h) (hc.continuousAt (x := w))

end T2

/-- The iterated tangent bundles of a Hausdorff manifold are Hausdorff. -/
theorem MBMfld.t2Space_iter (n : ℕ) :
    ∀ (X : MBMfld.{u, v}) [T2Space X.Carrier], T2Space (MBMfld.iter n X).Carrier := by
  induction n with
  | zero => intro X _; exact ‹_›
  | succ n ih => intro X _; exact ih (MBMfld.tangent X)

/-- The iterated tangent bundles of a Hausdorff manifold are compact-localizable. -/
theorem MBMfld.compactLocalizable_iter_of_t2Space (X : MBMfld.{u, v}) [T2Space X.Carrier] (n : ℕ) :
    CompactLocalizable (MBMfld.iter n X).Carrier := by
  have := MBMfld.t2Space_iter n X
  exact CompactLocalizable.of_r1Space _

/-- The iterated tangent bundles of a manifold with a locally compact model are
compact-localizable. -/
theorem MBMfld.compactLocalizable_iter_of_locallyCompactSpace (X : MBMfld.{u, v})
    [LocallyCompactSpace X.Model] (n : ℕ) : CompactLocalizable (MBMfld.iter n X).Carrier := by
  have := MBMfld.locallyCompactSpace_iter n X
  have := ChartedSpace.locallyCompactSpace (MBMfld.iter n X).Model (MBMfld.iter n X).Carrier
  exact CompactLocalizable.of_locallyCompactSpace _

/-! ### Jets of the tangent map -/

section TangentJets

variable {X : MBMfld.{u, u}} {Y : MBMfld.{u, v}}

/-- The chart pairs `(tangentChart j j, tangentChart i i)` of `TX × TY` built from a family `A` of
chart pairs of `X × Y`. -/
def tangentFamily (A : Set (atlas X.Model X.Carrier × atlas Y.Model Y.Carrier)) :
    Set (atlas (MBMfld.tangent X).Model (MBMfld.tangent X).Carrier ×
      atlas (MBMfld.tangent Y).Model (MBMfld.tangent Y).Carrier) :=
  (fun c ↦ (tangentAtlasIdx c.1, tangentAtlasIdx c.2)) '' A

/-- If `A` covers `X × Y`, the family `tangentFamily A` covers `TX × TY`. -/
theorem tangentFamily_covering {A : Set (atlas X.Model X.Carrier × atlas Y.Model Y.Carrier)}
    (hA : ∀ x y, ∃ c ∈ A, x ∈ c.1.1.source ∧ y ∈ c.2.1.source) :
    ∀ v w, ∃ c ∈ tangentFamily A, v ∈ c.1.1.source ∧ w ∈ c.2.1.source := fun v w ↦ by
  obtain ⟨c, hc, h₁, h₂⟩ := hA v.proj w.proj
  exact ⟨_, ⟨c, hc, rfl⟩, (mem_tangentChart_self_source _ _).2 h₁,
    (mem_tangentChart_self_source _ _).2 h₂⟩

/-- The jet index of `TX × TY` with the charts `tangentChart j j`, `tangentChart i i` and a compact
set `K'` in the target of `tangentChart j j`. -/
def tangentJetIdx (j : atlas X.Model X.Carrier) (i : atlas Y.Model Y.Carrier)
    (K' : Set (X.Model × X.Model)) (hK' : IsCompact K') (hsub : K' ⊆ (tangentChart j j.1).target) :
    CkMap.CompactIdx (MBMfld.tangent X).Model (MBMfld.tangent Y).Model
      (MBMfld.tangent X).Carrier (MBMfld.tangent Y).Carrier :=
  ⟨tangentAtlasIdx j, tangentAtlasIdx i, K', hK', hsub⟩

/-- The jet index of `X × Y` under `tangentJetIdx j i K'`: the charts `j`, `i` and the compact set
`pr₁(K')`. -/
def baseJetIdx (j : atlas X.Model X.Carrier) (i : atlas Y.Model Y.Carrier)
    (K' : Set (X.Model × X.Model)) (hK' : IsCompact K') (hsub : K' ⊆ (tangentChart j j.1).target) :
    CkMap.CompactIdx X.Model Y.Model X.Carrier Y.Carrier :=
  ⟨j, i, Prod.fst '' K', hK'.image continuous_fst, fun _ ⟨q, hq, e⟩ ↦
    e ▸ ((mem_tangentChart_target j j.1 q).1 (hsub hq)).1⟩

/-- Every jet index of `TX × TY` in the family `tangentFamily A` is a `tangentJetIdx`. -/
theorem exists_eq_tangentJetIdx {A : Set (atlas X.Model X.Carrier × atlas Y.Model Y.Carrier)}
    {a' : CkMap.CompactIdx (MBMfld.tangent X).Model (MBMfld.tangent Y).Model
      (MBMfld.tangent X).Carrier (MBMfld.tangent Y).Carrier}
    (ha' : (a'.j, a'.i) ∈ tangentFamily A) :
    ∃ c ∈ A, ∃ (K' : Set (X.Model × X.Model)) (hK' : IsCompact K')
      (hsub : K' ⊆ (tangentChart c.1 c.1.1).target), a' = tangentJetIdx c.1 c.2 K' hK' hsub := by
  obtain ⟨⟨j, i⟩, hc, e⟩ := ha'
  obtain ⟨j', i', K', hK', hsub⟩ := a'
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact ⟨(j, i), hc, K', hK', hsub, rfl⟩

variable {j : atlas X.Model X.Carrier} {i : atlas Y.Model Y.Carrier}
  {K' : Set (X.Model × X.Model)} {hK' : IsCompact K'} {hsub : K' ⊆ (tangentChart j j.1).target}
  {ℓ : ℕ}

/-- `Tg` sends the part of `TX` over `K'` into the chart `tangentChart i i` if and only if `g`
sends the part of `X` over `pr₁(K')` into the chart `i`. -/
theorem tangentCk_mem_tangentJetIdx_dom
    {g : CkMap X.Model Y.Model (ℓ + 1) X.Carrier Y.Carrier} :
    MBMfld.tangentCk g ∈ (tangentJetIdx j i K' hK' hsub).dom ↔
      g ∈ (baseJetIdx j i K' hK' hsub).dom := by
  constructor
  · rintro hg _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    have : tangentMap X.Model Y.Model g ((tangentChart j j.1).symm q) ∈
        (tangentChart i i.1).source := hg (mem_image_of_mem _ hq)
    rwa [mem_tangentChart_self_source] at this
  · rintro hg _ ⟨q, hq, rfl⟩
    change tangentMap X.Model Y.Model g ((tangentChart j j.1).symm q) ∈
      (tangentChart i i.1).source
    rw [mem_tangentChart_self_source]
    exact hg ⟨q.1, mem_image_of_mem _ hq, rfl⟩

/-- The reindexing `((y, w), (v, v')) ↦ (y, v)` of the jets of `g ∘ pr₁`. -/
def jetFst (K' : Set (X.Model × X.Model)) (m : ℕ) :
    C(K' × (Fin m → X.Model × X.Model), (Prod.fst '' K' : Set X.Model) × (Fin m → X.Model)) :=
  ⟨fun p ↦ (⟨p.1.1.1, mem_image_of_mem _ p.1.2⟩, fun l ↦ (p.2 l).1), by fun_prop⟩

/-- **The jets of `Tg` in the charts `tangentChart j j`, `tangentChart i i`**: on `K'`, the
local representative of `Tg` is `(y, w) ↦ (F y, dF(y, w))` with `F = i ∘ g ∘ j⁻¹`, so its `m`-jet
is the pair of the `m`-jet of `F ∘ pr₁` and the `m`-jet of `dF`. -/
theorem tangentJetIdx_jet {g : CkMap X.Model Y.Model (ℓ + 1) X.Carrier Y.Carrier}
    (hg : g ∈ (baseJetIdx j i K' hK' hsub).dom) {m : ℕ} (hm : m ≤ ℓ) :
    (tangentJetIdx j i K' hK' hsub).jet m (MBMfld.tangentCk g) =
      (((baseJetIdx j i K' hK' hsub).jet m g).comp (jetFst K' m)).prodMk
        (jetOn m (dMB (i.1 ∘ g ∘ j.1.symm)) K') := by
  set b := baseJetIdx j i K' hK' hsub
  set D := chartDomain g univ j.1 i.1
  have hD : IsOpen D := b.isOpen_chartDomain g
  have hψ : ContDiffMBOn (ℓ + 1) (i.1 ∘ g ∘ j.1.symm) D := b.contDiffMBOn_rep g
  have hK'D : K' ⊆ D ×ˢ univ := fun q hq ↦
    ⟨b.subset_chartDomain hg (mem_image_of_mem _ hq), mem_univ _⟩
  have hDU : IsOpen (D ×ˢ (univ : Set X.Model)) := hD.prod isOpen_univ
  have h₁ : ContDiffMBOn m (fun q : X.Model × X.Model ↦ (i.1 ∘ g ∘ j.1.symm) q.1) (D ×ˢ univ) :=
    ((hψ.of_le (by omega)).comp_clm (ContinuousLinearMap.fst ℝ X.Model X.Model) hD).mono
      fun q hq ↦ hq.1
  have h₂ : ContDiffMBOn m (dMB (i.1 ∘ g ∘ j.1.symm)) (D ×ˢ univ) := hψ.2.2.of_le hm
  refine ContinuousMap.ext fun p ↦ ?_
  rw [(tangentJetIdx j i K' hK' hsub).jet_apply (tangentCk_mem_tangentJetIdx_dom.2 hg) hm]
  have hev : ((tangentChart i i.1) ∘ tangentMap X.Model Y.Model g ∘ (tangentChart j j.1).symm)
      =ᶠ[𝓝 (p.1 : X.Model × X.Model)]
        fun q ↦ ((i.1 ∘ g ∘ j.1.symm) q.1, dMB (i.1 ∘ g ∘ j.1.symm) q) :=
    Filter.eventually_of_mem (hDU.mem_nhds (hK'D p.1.2)) fun q hq ↦
      tangentMap_chart (CkMap.contMDiffMB_one g) j i hq.1.1 hq.1.2.2 q.2
  change iteratedDMB m ((tangentChart i i.1) ∘ tangentMap X.Model Y.Model g ∘
    (tangentChart j j.1).symm) ((p.1 : X.Model × X.Model), p.2) = _
  rw [iteratedDMB_congr_of_eventuallyEq m hev,
    iteratedDMB_prodMk hDU h₁ h₂ m le_rfl _ (hK'D p.1.2)]
  refine Prod.ext ?_ ?_
  · change iteratedDMB m ((i.1 ∘ g ∘ j.1.symm) ∘ ⇑(LinearMap.fst ℝ X.Model X.Model)) _ = _
    rw [iteratedDMB_comp_linearMap]
    exact (b.jet_apply hg (m := m) (by omega) (jetFst K' m p)).symm
  · exact (jetOn_apply hψ.2.2 hK'D hm _).symm

end TangentJets

/-! ### The induction on the order -/

section Induction

variable {P : Type*} [TopologicalSpace P]

/-- The jets of a family `ψ` of `C^ℓ` maps of order `≤ m`, in the chart pairs of `A`, are
continuous where defined. -/
def JetFam {X : MBMfld.{u, u}} {Y : MBMfld.{u, v}}
    (A : Set (atlas X.Model X.Carrier × atlas Y.Model Y.Carrier))
    (m : ℕ) {ℓ : ℕ} (ψ : P → CkMap X.Model Y.Model ℓ X.Carrier Y.Carrier) : Prop :=
  ∀ a : CkMap.CompactIdx X.Model Y.Model X.Carrier Y.Carrier, (a.j, a.i) ∈ A → ∀ m' ≤ m,
    ContinuousOn (fun p ↦ a.jet m' (ψ p)) (ψ ⁻¹' a.dom)

variable {X : MBMfld.{u, u}} {Y : MBMfld.{u, v}}

omit [TopologicalSpace P] in
/-- Preimages of the domains of `tangentJetIdx` under `T ∘ ψ`. -/
theorem preimage_tangentJetIdx_dom {ℓ : ℕ}
    {ψ : P → CkMap X.Model Y.Model (ℓ + 1) X.Carrier Y.Carrier}
    {j : atlas X.Model X.Carrier} {i : atlas Y.Model Y.Carrier}
    {K' : Set (X.Model × X.Model)} {hK' : IsCompact K'} {hsub : K' ⊆ (tangentChart j j.1).target} :
    (fun p ↦ MBMfld.tangentCk (ψ p)) ⁻¹' (tangentJetIdx j i K' hK' hsub).dom =
      ψ ⁻¹' (baseJetIdx j i K' hK' hsub).dom :=
  Set.ext fun _ ↦ tangentCk_mem_tangentJetIdx_dom

/-- `T^0 g = g`, for continuity. -/
theorem continuous_toC_of_iterMapC_zero {ℓ : ℕ}
    {ψ : P → CkMap X.Model Y.Model ℓ X.Carrier Y.Carrier}
    (h : Continuous fun p ↦ MBMfld.iterMapC (Nat.zero_le ℓ) (ψ p)) :
    Continuous fun p ↦ CkMap.toC (ψ p) :=
  h

/-- `T^0 g = g`, for continuity. -/
theorem continuous_iterMapC_zero_of_toC {ℓ : ℕ}
    {ψ : P → CkMap X.Model Y.Model ℓ X.Carrier Y.Carrier}
    (h : Continuous fun p ↦ CkMap.toC (ψ p)) {hn : 0 ≤ ℓ} :
    Continuous fun p ↦ MBMfld.iterMapC hn (ψ p) :=
  h

/-- **Jets of `Tg` from jets of `g`**: if the jets of order `≤ m + 1` of `ψ` are continuous, so are
the jets of order `≤ m` of `T ∘ ψ`, in the tangent charts. -/
theorem jetFam_tangent_of_jetFam {A : Set (atlas X.Model X.Carrier × atlas Y.Model Y.Carrier)}
    {m ℓ : ℕ} (hm : m ≤ ℓ) {ψ : P → CkMap X.Model Y.Model (ℓ + 1) X.Carrier Y.Carrier}
    (h : JetFam A (m + 1) ψ) : JetFam (tangentFamily A) m fun p ↦ MBMfld.tangentCk (ψ p) := by
  intro a' ha' m' hm'
  obtain ⟨⟨j, i⟩, hc, K', hK', hsub, rfl⟩ := exists_eq_tangentJetIdx ha'
  set b := baseJetIdx j i K' hK' hsub
  have hb : (b.j, b.i) ∈ A := hc
  rw [preimage_tangentJetIdx_dom]
  have hc₁ := (ContinuousMap.continuous_precomp (jetFst K' m')).comp_continuousOn
    (h b hb m' (by omega))
  have hc₂ := ((ContinuousMap.continuous_precomp (jetDA K' m')).comp_continuousOn
    (h b hb (m' + 1) (by omega))).add (continuousOn_finsetSum Finset.univ fun l _ ↦
      (ContinuousMap.continuous_precomp (jetDB K' m' l)).comp_continuousOn (h b hb m' (by omega)))
  refine (ContinuousMap.continuous_prodMk_pair.comp_continuousOn (hc₁.prodMk hc₂)).congr
    fun p hp ↦ ?_
  simp only [Function.comp_apply]
  rw [tangentJetIdx_jet hp (by omega)]
  congr 1
  exact jetOn_dMB (b.isOpen_chartDomain (ψ p)) (b.contDiffMBOn_rep (ψ p))
    (b.subset_chartDomain hp) (by omega)

/-- **Jets of `g` from jets of `Tg`**: if `ψ` is continuous into `C(X, Y)` and the jets of order
`≤ m` of `T ∘ ψ` are continuous in the tangent charts, the jets of order `≤ m + 1` of `ψ` are
continuous. -/
theorem jetFam_of_jetFam_tangent {A : Set (atlas X.Model X.Carrier × atlas Y.Model Y.Carrier)}
    {m ℓ : ℕ} (hm : m ≤ ℓ) {ψ : P → CkMap X.Model Y.Model (ℓ + 1) X.Carrier Y.Carrier}
    (h₀ : Continuous fun p ↦ CkMap.toC (ψ p))
    (h : JetFam (tangentFamily A) m fun p ↦ MBMfld.tangentCk (ψ p)) : JetFam A (m + 1) ψ := by
  intro a ha m'' hm''
  rcases m'' with _ | m'
  · exact a.continuousOn_jet_zero h₀
  refine ContinuousOn.congr (f := fun p ↦ (jetOn m' (dMB (a.i.1 ∘ ψ p ∘ a.j.1.symm))
      (a.K ×ˢ univ)).comp (jetSucc a.K m')) ?_ fun p hp ↦
    jetOn_succ (a.contDiffMBOn_rep (ψ p)) (a.subset_chartDomain hp) (by omega)
  refine (ContinuousMap.continuous_precomp _).comp_continuousOn ?_
  refine continuousOn_jetOn_of_isCompact (k := ℓ) (by omega) (fun p hp ↦ ⟨_,
    prod_mono (a.subset_chartDomain hp) subset_rfl, (a.contDiffMBOn_rep (ψ p)).2.2⟩)
    fun K'' hK''a hK'' ↦ ?_
  have hsub : K'' ⊆ (tangentChart a.j a.j.1).target := fun q hq ↦
    (mem_tangentChart_target a.j a.j.1 q).2
      ⟨a.K_subset (hK''a hq).1, a.j.1.map_target (a.K_subset (hK''a hq).1)⟩
  have hab : ∀ p ∈ ψ ⁻¹' a.dom, p ∈ ψ ⁻¹' (baseJetIdx a.j a.i K'' hK'' hsub).dom :=
    fun p hp ↦ MapsTo.mono_left hp (image_mono fun _ ⟨q, hq, e⟩ ↦ e ▸ (hK''a hq).1)
  have hc := h (tangentJetIdx a.j a.i K'' hK'' hsub) ⟨(a.j, a.i), ha, rfl⟩ m' (by omega)
  rw [preimage_tangentJetIdx_dom] at hc
  refine (((ContinuousMap.continuous_postcomp (ContinuousMap.snd)).comp_continuousOn hc).mono
    hab).congr fun p hp ↦ ?_
  simp only [Function.comp_apply]
  rw [tangentJetIdx_jet (hab p hp) (by omega)]
  rfl

/-- **The iterated tangent maps determine the jets** (one half of the comparison with
[GN26, Definition 4.1.2]): if `p ↦ T^n(ψ p) ∈ C(T^n X, T^n Y)` is continuous for `n ≤ m`,
then the jets of order `≤ m` of `ψ` are continuous in all chart pairs. No hypothesis on `X` is
needed. -/
theorem jetFam_of_iterCont (m : ℕ) : ∀ {X : MBMfld.{u, u}} {Y : MBMfld.{u, v}} {ℓ : ℕ}, m ≤ ℓ →
    ∀ (A : Set (atlas X.Model X.Carrier × atlas Y.Model Y.Carrier))
      (ψ : P → CkMap X.Model Y.Model ℓ X.Carrier Y.Carrier),
      (∀ n (hn : n ≤ ℓ), n ≤ m → Continuous fun p ↦ MBMfld.iterMapC hn (ψ p)) → JetFam A m ψ := by
  induction m with
  | zero =>
    intro X Y ℓ _ A ψ h a _ m' hm'
    obtain rfl : m' = 0 := by omega
    exact a.continuousOn_jet_zero (continuous_toC_of_iterMapC_zero (h 0 (Nat.zero_le ℓ) le_rfl))
  | succ m ih =>
    intro X Y ℓ hm A ψ h
    obtain ⟨ℓ, rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
    refine jetFam_of_jetFam_tangent (by omega)
      (continuous_toC_of_iterMapC_zero (h 0 (Nat.zero_le _) (Nat.zero_le _)))
      (ih (by omega) (tangentFamily A) _ fun n hn hnm ↦ h (n + 1) (by omega) (by omega))

/-- **The jets determine the iterated tangent maps** (the other half): if `ψ` is continuous into
`C(X, Y)` and its jets of order `≤ m` are continuous in a family of chart pairs covering `X × Y`,
then `p ↦ T^n(ψ p)` is continuous for `n ≤ m`, provided the iterated tangent bundles of `X` are
compact-localizable (`X` Hausdorff, or its model locally compact). -/
theorem iterCont_of_jetFam (m : ℕ) : ∀ {X : MBMfld.{u, u}} {Y : MBMfld.{u, v}} {ℓ : ℕ}, m ≤ ℓ →
    (∀ n, CompactLocalizable (MBMfld.iter n X).Carrier) →
    ∀ (A : Set (atlas X.Model X.Carrier × atlas Y.Model Y.Carrier)),
      (∀ x y, ∃ c ∈ A, x ∈ c.1.1.source ∧ y ∈ c.2.1.source) →
    ∀ (ψ : P → CkMap X.Model Y.Model ℓ X.Carrier Y.Carrier),
      (Continuous fun p ↦ CkMap.toC (ψ p)) → JetFam A m ψ →
        ∀ n (hn : n ≤ ℓ), n ≤ m → Continuous fun p ↦ MBMfld.iterMapC hn (ψ p) := by
  induction m with
  | zero =>
    intro X Y ℓ _ _ A _ ψ h₀ _ n hn hnm
    obtain rfl : n = 0 := by omega
    exact continuous_iterMapC_zero_of_toC h₀
  | succ m ih =>
    intro X Y ℓ hm hloc A hA ψ h₀ hjet
    obtain ⟨ℓ, rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
    have hT := jetFam_tangent_of_jetFam (by omega) hjet
    have hdom : ∀ a' : CkMap.CompactIdx (MBMfld.tangent X).Model (MBMfld.tangent Y).Model
        (MBMfld.tangent X).Carrier (MBMfld.tangent Y).Carrier, (a'.j, a'.i) ∈ tangentFamily A →
        IsOpen ((fun p ↦ MBMfld.tangentCk (ψ p)) ⁻¹' a'.dom) := by
      intro a' ha'
      obtain ⟨c, -, K', hK', hsub, rfl⟩ := exists_eq_tangentJetIdx ha'
      rw [preimage_tangentJetIdx_dom]
      exact (baseJetIdx c.1 c.2 _ _ hsub).isOpen_domC.preimage h₀
    have hloc1 : CompactLocalizable (MBMfld.tangent X).Carrier := hloc 1
    have h₀' := CkMap.continuous_toC_of_jet (M := (MBMfld.tangent X).Carrier) hloc1
      (tangentFamily_covering hA) hdom
      fun a' ha' ↦ hT a' ha' 0 (Nat.zero_le _)
    have hT' := ih (X := MBMfld.tangent X) (Y := MBMfld.tangent Y) (by omega)
      (fun n ↦ hloc (n + 1)) _ (tangentFamily_covering hA) _ h₀' hT
    intro n hn hnm
    rcases n with _ | n
    · exact continuous_iterMapC_zero_of_toC h₀
    · exact hT' n (by omega) (by omega)

end Induction

/-! ### Comparison with [GN26, Definition 4.1.2], and with the chart topology -/

section Comparison

/-- The chart pairs `(chartAt x, chartAt y)` cover `X × Y`. -/
theorem univ_covering (X : MBMfld.{u, w}) (Y : MBMfld.{u, v}) :
    ∀ x y, ∃ c ∈ (univ : Set (atlas X.Model X.Carrier × atlas Y.Model Y.Carrier)),
      x ∈ c.1.1.source ∧ y ∈ c.2.1.source := fun x y ↦
  ⟨(⟨chartAt X.Model x, chart_mem_atlas _ x⟩, ⟨chartAt Y.Model y, chart_mem_atlas _ y⟩), trivial,
    mem_chart_source _ x, mem_chart_source _ y⟩

/-- **The jet topology is coarser than the compact-open `C^ℓ` topology of [GN26,
Definition 4.1.2]**, with no hypothesis on the manifolds. -/
theorem MBMfld.gnTopology_le_jetTopology (ℓ : ℕ) (X : MBMfld.{u, u}) (Y : MBMfld.{u, v}) :
    MBMfld.gnTopology ℓ X Y ≤ CkMap.jetTopology X.Model Y.Model ℓ X.Carrier Y.Carrier := by
  let _ : TopologicalSpace (CkMap X.Model Y.Model ℓ X.Carrier Y.Carrier) := MBMfld.gnTopology ℓ X Y
  have hiter : ∀ n (hn : n ≤ ℓ), n ≤ ℓ → Continuous fun g : CkMap X.Model Y.Model ℓ X.Carrier
      Y.Carrier ↦ MBMfld.iterMapC hn (id g) :=
    fun n hn _ ↦ continuous_iInf_dom (i := ⟨n, Nat.lt_succ_of_le hn⟩) continuous_induced_dom
  refine continuous_id_iff_le.1 (CkMap.continuous_jetTopology_iff.2 ⟨?_, fun a m hm ↦ ?_⟩)
  · exact continuous_toC_of_iterMapC_zero (hiter 0 (Nat.zero_le ℓ) (Nat.zero_le ℓ))
  · exact jetFam_of_iterCont ℓ le_rfl univ id hiter a trivial m hm

/-- **The compact-open `C^ℓ` topology of [GN26, Definition 4.1.2], is coarser than the jet
topology** if the iterated tangent bundles of `X` are compact-localizable. -/
theorem MBMfld.jetTopology_le_gnTopology (ℓ : ℕ) (X : MBMfld.{u, u}) (Y : MBMfld.{u, v})
    (hloc : ∀ n, CompactLocalizable (MBMfld.iter n X).Carrier) :
    CkMap.jetTopology X.Model Y.Model ℓ X.Carrier Y.Carrier ≤ MBMfld.gnTopology ℓ X Y := by
  let _ : TopologicalSpace (CkMap X.Model Y.Model ℓ X.Carrier Y.Carrier) :=
    CkMap.jetTopology X.Model Y.Model ℓ X.Carrier Y.Carrier
  obtain ⟨h₀, hj⟩ := CkMap.continuous_jetTopology_iff.1
    (continuous_id (X := CkMap X.Model Y.Model ℓ X.Carrier Y.Carrier))
  have hc := iterCont_of_jetFam ℓ le_rfl hloc univ (univ_covering X Y) id h₀
    fun a _ m hm ↦ hj a m hm
  refine continuous_id_iff_le.1 (continuous_iInf_rng.2 fun j ↦ continuous_induced_rng.2 ?_)
  exact hc j (Nat.lt_succ_iff.1 j.2) (Nat.lt_succ_iff.1 j.2)

/-- **The jet topology is the compact-open `C^ℓ` topology of [GN26, Definition 4.1.2]**,
for compact-localizable iterated tangent bundles of `X`. -/
theorem MBMfld.jetTopology_eq_gnTopology_of_compactLocalizable (ℓ : ℕ) (X : MBMfld.{u, u})
    (Y : MBMfld.{u, v})
    (hloc : ∀ n, CompactLocalizable (MBMfld.iter n X).Carrier) :
    CkMap.jetTopology X.Model Y.Model ℓ X.Carrier Y.Carrier = MBMfld.gnTopology ℓ X Y :=
  le_antisymm (MBMfld.jetTopology_le_gnTopology ℓ X Y hloc) (MBMfld.gnTopology_le_jetTopology ℓ X Y)

/-- **The jet topology is the compact-open `C^ℓ` topology of [GN26, Definition 4.1.2]**,
for a Hausdorff manifold `X` modeled on any Hausdorff locally convex space. -/
theorem MBMfld.jetTopology_eq_gnTopology (ℓ : ℕ) (X : MBMfld.{u, u}) (Y : MBMfld.{u, v})
    [T2Space X.Carrier] :
    CkMap.jetTopology X.Model Y.Model ℓ X.Carrier Y.Carrier = MBMfld.gnTopology ℓ X Y :=
  MBMfld.jetTopology_eq_gnTopology_of_compactLocalizable ℓ X Y
    (MBMfld.compactLocalizable_iter_of_t2Space X)

/-- The jet topology is the compact-open `C^ℓ` topology of [GN26, Definition 4.1.2], for a
locally compact model of `X` (no Hausdorff hypothesis on `X`). -/
theorem MBMfld.jetTopology_eq_gnTopology_of_locallyCompactSpace (ℓ : ℕ) (X : MBMfld.{u, u})
    (Y : MBMfld.{u, v})
    [LocallyCompactSpace X.Model] :
    CkMap.jetTopology X.Model Y.Model ℓ X.Carrier Y.Carrier = MBMfld.gnTopology ℓ X Y :=
  MBMfld.jetTopology_eq_gnTopology_of_compactLocalizable ℓ X Y
    (MBMfld.compactLocalizable_iter_of_locallyCompactSpace X)

/-- **For a locally compact model of `X`, the jet topology is the chart topology**
`CkMap.chartTopology` (local representatives on open subsets of compact sets); this is
`CkMap.chartTopology_eq_jetTopology` for bundled manifolds. -/
theorem MBMfld.jetTopology_eq_chartTopology (ℓ : ℕ) (X : MBMfld.{u, u}) (Y : MBMfld.{u, v})
    [LocallyCompactSpace X.Model] :
    CkMap.jetTopology X.Model Y.Model ℓ X.Carrier Y.Carrier =
      CkMap.chartTopology X.Model Y.Model ℓ X.Carrier Y.Carrier :=
  CkMap.chartTopology_eq_jetTopology.symm

/-- **The jet topology of `C^∞(X, Y)` is the compact-open `C^∞` topology of [GN26,
Definition 4.1.2]**, for a Hausdorff manifold `X` modeled on any Hausdorff locally convex space. -/
theorem MBMfld.jetTopologySm_eq_gnTopologySm (X : MBMfld.{u, u}) (Y : MBMfld.{u, v})
    [T2Space X.Carrier] :
    SmoothMap.jetTopologySm X.Model Y.Model X.Carrier Y.Carrier = MBMfld.gnTopologySm X Y := by
  rw [MBMfld.gnTopologySm_eq]
  exact iInf_congr fun ℓ ↦ congrArg (TopologicalSpace.induced (SmoothMap.toCk ℓ))
    (MBMfld.jetTopology_eq_gnTopology ℓ X Y)

/-- The jet topology of `C^∞(X, Y)` is the compact-open `C^∞` topology of [GN26,
Definition 4.1.2], for a locally compact model of `X`. -/
theorem MBMfld.jetTopologySm_eq_gnTopologySm_of_locallyCompactSpace (X : MBMfld.{u, u})
    (Y : MBMfld.{u, v}) [LocallyCompactSpace X.Model] :
    SmoothMap.jetTopologySm X.Model Y.Model X.Carrier Y.Carrier = MBMfld.gnTopologySm X Y := by
  rw [MBMfld.gnTopologySm_eq]
  exact iInf_congr fun ℓ ↦ congrArg (TopologicalSpace.induced (SmoothMap.toCk ℓ))
    (MBMfld.jetTopology_eq_gnTopology_of_locallyCompactSpace ℓ X Y)

end Comparison

end LocallyConvex.Manifolds
