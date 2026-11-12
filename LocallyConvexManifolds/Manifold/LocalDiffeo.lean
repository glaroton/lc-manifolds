/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.MappingSpace.Basic
public import LocallyConvexManifolds.Analytic.Basic
public import Mathlib.Topology.IsLocalHomeomorph

/-!
# Local diffeomorphisms injective on a compact or σ-compact set

We prove [GN26, Proposition 3.8.18, Corollary 3.8.19, Proposition 3.8.20 and Corollary 3.8.21]
(appendix "Alternative constructions" to §3.8, pp. 328–330): a local diffeomorphism (or local
homeomorphism) that is injective on a compact set `K`, or that restricts to an embedding with closed
image on a σ-compact set `A` of a locally compact situation, is a diffeomorphism (homeomorphism)
from an open neighborhood of `K` (of `A`) onto an open set.

## Main results

* `exists_isOpen_injOn_of_isCompact` (Proposition 3.8.18): a continuous map into a Hausdorff space,
  injective on a compact `K` and locally injective at the points of `K`, is injective on an open
  neighborhood of `K`.
* `IsLocalHomeomorph.exists_openPartialHomeomorph_of_isCompact`: the topological consequence for
  local homeomorphisms (the remark after Proposition 3.8.18).
* `ContMDiffMBOn.of_local`: being `C^k` is a local property.
* `exists_contMDiffMB_diffeo_of_isCompact`, `exists_smoothMBM_diffeo_of_isCompact`,
  `exists_realAnalyticMOn_diffeo_of_isCompact` (Corollary 3.8.19, for `C^k`, `k ∈ ℕ`, smooth and
  real analytic maps).
* `exists_isOpen_injOn_of_isSigmaCompact` (Proposition 3.8.20): `f : X → Y` continuous into a
  Hausdorff weakly locally compact space, `A ⊆ X` σ-compact with `f(A)` closed and `f|_A` an
  embedding, `f` locally injective at the points of `A`: then `f` is injective on an open
  neighborhood of `A`. The core statement `exists_isOpen_injOn_of_isSigmaCompact_image` only uses
  that `f(A)` is σ-compact, `f|_A` injective and `A ∩ f⁻¹(C)` compact for compact `C`.
* `exists_openPartialHomeomorph_of_isSigmaCompact`: the consequence for maps that are local
  homeomorphisms near `A`, carrying along any property of the local inverses.
* `exists_contMDiffMB_diffeo_of_isSigmaCompact`, `exists_smoothMBM_diffeo_of_isSigmaCompact`,
  `exists_realAnalyticMOn_diffeo_of_isSigmaCompact` (Corollary 3.8.21, for `C^k`, smooth and real
  analytic maps); `locallyCompactSpace_of_finiteDimensional`: finite-dimensional manifolds satisfy
  the local compactness hypothesis.
* `realAnalyticMOn_of_local`: real analyticity of maps between real analytic manifolds is a local
  property.

## Implementation notes

* Glöckner–Neeb prove Proposition 3.8.18 with nets and the Wallace lemma. Here the set
  `{(x, y) : f x = f y → x = y}` is shown to be a neighborhood of `K × K`, and the Wallace lemma
  is `IsCompact.nhdsSet_prod_eq` (`𝓝ˢ (K ×ˢ K) = 𝓝ˢ K ×ˢ 𝓝ˢ K`). The Hausdorff property of the
  domain, assumed there, is not needed. We do not claim this argument is new.
* Proposition 3.8.20 is proved by Glöckner–Neeb with Lemma A.5.5 (compact sets `Lⱼ` covering
  `f(A)` with open neighborhoods `Oⱼ` such that `Oᵢ ∩ Oⱼ ≠ ∅` only for `|i - j| ≤ 1`). We avoid
  that lemma: from a compact exhaustion `∅ = C₀ ⊆ C₁ ⊆ ⋯` of a neighborhood of `f(A)` with
  `Cₙ ⊆ int Cₙ₊₁` (`IsSigmaCompact.exists_compact_exhaustion`) the "annuli"
  `Oⱼ = int Cⱼ₊₁ \ Cⱼ₋₁` already have this property, and `U = ⋃ⱼ f⁻¹(Oⱼ) ∩ Vⱼ ∩ Vⱼ₊₁` works,
  where `Vⱼ` is an open neighborhood of the compact set `A ∩ f⁻¹(Cⱼ₊₁)` on which `f` is injective
  (Proposition 3.8.18). The domain need not be Hausdorff, and "locally compact" is only used in
  the weak form `WeaklyLocallyCompactSpace` (every point has a compact neighborhood) together with
  the Hausdorff property of `Y`. We do not claim this argument is new.
* The statement of Corollary 3.8.21 in the manuscript concludes `K ⊆ U`; this is a misprint for
  `A ⊆ U`. Its hypothesis "finite-dimensional" is only used through local compactness of `N`; we
  assume `WeaklyLocallyCompactSpace N`, which holds for finite-dimensional models
  (`locallyCompactSpace_of_finiteDimensional`). Of `f` only continuity is used, together with
  the local diffeomorphisms near the points of `A`.
* A local `C^k`-diffeomorphism is given by local inverses: every point lies in the source of a
  partial homeomorphism that agrees with `f` on its source and is `C^k` in both directions.
* Manifolds with rough boundary are not treated.
* The statements producing a partial homeomorphism assume the domain nonempty: a partial
  homeomorphism `M → N` needs an inverse `N → M`, which does not exist when `M = ∅ ≠ N`.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
  (page numbers refer to arXiv:2602.12362v1)
-/

@[expose] public section

open Set Filter Function
open scoped Topology
open Topology (IsEmbedding IsClosedEmbedding)
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

/-! ### Injectivity near a compact set -/

section Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **[GN26, Proposition 3.8.18].** A continuous map into a Hausdorff space that is
injective on a compact set `K` and locally injective at the points of `K` is injective on an open
neighborhood of `K`. -/
theorem exists_isOpen_injOn_of_isCompact [T2Space Y] {f : X → Y} (hf : Continuous f)
    {K : Set X} (hK : IsCompact K) (hinj : InjOn f K)
    (hloc : ∀ x ∈ K, ∃ W ∈ 𝓝 x, InjOn f W) : ∃ U, IsOpen U ∧ K ⊆ U ∧ InjOn f U := by
  set D : Set (X × X) := {p | f p.1 = f p.2 → p.1 = p.2}
  have hD : D ∈ 𝓝ˢ (K ×ˢ K) := by
    rw [mem_nhdsSet_iff_forall]
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    by_cases hxy : x = y
    · subst hxy
      obtain ⟨W, hW, hWi⟩ := hloc x hx
      exact mem_of_superset (prod_mem_nhds hW hW) fun p hp hfp ↦ hWi hp.1 hp.2 hfp
    · have hfxy : f x ≠ f y := fun h ↦ hxy (hinj hx hy h)
      obtain ⟨u, v, hu, hv, hxu, hyv, huv⟩ := t2_separation hfxy
      refine mem_of_superset (prod_mem_nhds ((hu.preimage hf).mem_nhds hxu)
        ((hv.preimage hf).mem_nhds hyv)) fun p hp hfp ↦ ?_
      exact absurd (huv.ne_of_mem hp.1 hp.2 hfp) not_false
  rw [hK.nhdsSet_prod_eq hK, Filter.mem_prod_iff] at hD
  obtain ⟨A, hA, B, hB, hAB⟩ := hD
  refine ⟨interior (A ∩ B), isOpen_interior,
    subset_interior_iff_mem_nhdsSet.2 (inter_mem hA hB), fun a ha b hb hab ↦ ?_⟩
  exact hAB (show (a, b) ∈ A ×ˢ B from ⟨(interior_subset ha).1, (interior_subset hb).2⟩) hab

/-- A local homeomorphism into a Hausdorff space that is injective on a compact set `K` restricts
to a homeomorphism from an open neighborhood of `K` onto an open set [GN26, remark
after Proposition 3.8.18]. -/
theorem IsLocalHomeomorph.exists_openPartialHomeomorph_of_isCompact [T2Space Y] [Nonempty X]
    {f : X → Y} (hf : IsLocalHomeomorph f) {K : Set X} (hK : IsCompact K) (hinj : InjOn f K) :
    ∃ Φ : OpenPartialHomeomorph X Y, K ⊆ Φ.source ∧ ⇑Φ = f := by
  obtain ⟨U, hU, hKU, hUi⟩ := exists_isOpen_injOn_of_isCompact hf.continuous hK hinj
    fun x _ ↦ by
      obtain ⟨W, hW, hxW, hWi⟩ := hf.isLocallyInjective x
      exact ⟨W, hW.mem_nhds hxW, hWi⟩
  have hopen : IsOpenMap (U.domRestrict f) := hf.isOpenMap.comp hU.isOpenMap_subtype_val
  refine ⟨OpenPartialHomeomorph.ofContinuousOpenRestrict (hUi.toPartialEquiv f U)
    hf.continuous.continuousOn hopen hU, hKU, rfl⟩

/-! ### Injectivity near a σ-compact set -/

/-- A σ-compact subset `s` of a weakly locally compact space has a compact exhaustion
`∅ = C₀ ⊆ C₁ ⊆ ⋯` with `Cₙ ⊆ int Cₙ₊₁` and `s ⊆ ⋃ Cₙ`. -/
theorem IsSigmaCompact.exists_compact_exhaustion [WeaklyLocallyCompactSpace Y] {s : Set Y}
    (hs : IsSigmaCompact s) :
    ∃ C : ℕ → Set Y, C 0 = ∅ ∧ (∀ n, IsCompact (C n)) ∧ (∀ n, C n ⊆ interior (C (n + 1))) ∧
      s ⊆ ⋃ n, C n := by
  obtain ⟨B, hB, hBs⟩ := hs
  let D : ℕ → {K : Set Y // IsCompact K} := fun n ↦ Nat.rec ⟨∅, isCompact_empty⟩
    (fun n K ↦ ⟨(exists_compact_superset (K.2.union (hB n))).choose,
      (exists_compact_superset (K.2.union (hB n))).choose_spec.1⟩) n
  have hsucc : ∀ n, (D n).1 ∪ B n ⊆ interior (D (n + 1)).1 := fun n ↦
    (exists_compact_superset ((D n).2.union (hB n))).choose_spec.2
  refine ⟨fun n ↦ (D n).1, rfl, fun n ↦ (D n).2, fun n ↦ subset_union_left.trans (hsucc n), ?_⟩
  rw [← hBs]
  exact iUnion_subset fun n ↦ (subset_union_right.trans (hsucc n)).trans interior_subset |>.trans
    (subset_iUnion (fun n ↦ (D n).1) (n + 1))

/-- **Injectivity near a σ-compact set**, in the form used for [GN26, Proposition 3.8.20]:
let `f : X → Y` be continuous into a Hausdorff weakly locally compact space, `A ⊆ X` a set on
which `f` is injective, such that `f(A)` is σ-compact and `A ∩ f⁻¹(C)` is compact for every
compact `C ⊆ Y`, and assume that `f` is injective on a neighborhood of each point of `A`. Then
`f` is injective on an open neighborhood of `A`. -/
theorem exists_isOpen_injOn_of_isSigmaCompact_image [T2Space Y] [WeaklyLocallyCompactSpace Y]
    {f : X → Y} (hf : Continuous f) {A : Set X} (hσ : IsSigmaCompact (f '' A))
    (hinj : InjOn f A) (hprop : ∀ C, IsCompact C → IsCompact (A ∩ f ⁻¹' C))
    (hloc : ∀ x ∈ A, ∃ W ∈ 𝓝 x, InjOn f W) : ∃ U, IsOpen U ∧ A ⊆ U ∧ InjOn f U := by
  obtain ⟨C, hC0, hCc, hCi, hAC⟩ := IsSigmaCompact.exists_compact_exhaustion hσ
  have hmono : Monotone C := monotone_nat_of_le_succ fun n ↦ (hCi n).trans interior_subset
  -- the "annuli" `Oⱼ = int Cⱼ₊₁ \ Cⱼ₋₁`
  set O : ℕ → Set Y := fun j ↦ interior (C (j + 1)) \ C (j - 1)
  have hO : ∀ j, IsOpen (O j) := fun j ↦ isOpen_interior.sdiff (hCc _).isClosed
  have hOcov : ∀ y ∈ f '' A, ∃ j, y ∈ O j := by
    intro y hy
    have hex : ∃ n, y ∈ C n := mem_iUnion.1 (hAC hy)
    classical
    refine ⟨Nat.find hex, hCi _ (Nat.find_spec hex), fun hy' ↦ ?_⟩
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · have := Nat.find_spec hex
      rw [h0, hC0] at this
      exact this
    · exact Nat.find_min hex (Nat.sub_lt hpos one_pos) hy'
  have hOdisj : ∀ i j, i + 2 ≤ j → Disjoint (O i) (O j) := by
    intro i j hij
    refine Set.disjoint_left.2 fun y hyi hyj ↦ hyj.2 ?_
    exact hmono (by omega) (interior_subset hyi.1)
  -- injective open neighborhoods `Vⱼ` of the compact sets `A ∩ f⁻¹(Cⱼ₊₁)`
  have hV : ∀ j, ∃ V, IsOpen V ∧ A ∩ f ⁻¹' C (j + 1) ⊆ V ∧ InjOn f V := fun j ↦
    exists_isOpen_injOn_of_isCompact hf (hprop _ (hCc _)) (hinj.mono inter_subset_left)
      fun x hx ↦ hloc x hx.1
  choose V hVo hAV hVi using hV
  set P : ℕ → Set X := fun j ↦ f ⁻¹' O j ∩ V j ∩ V (j + 1)
  refine ⟨⋃ j, P j, isOpen_iUnion fun j ↦ (((hO j).preimage hf).inter (hVo j)).inter (hVo _),
    fun a ha ↦ ?_, ?_⟩
  · obtain ⟨j, hj⟩ := hOcov (f a) (mem_image_of_mem f ha)
    have h1 : f a ∈ C (j + 1) := interior_subset hj.1
    exact mem_iUnion.2 ⟨j, ⟨hj, hAV j ⟨ha, h1⟩⟩, hAV (j + 1) ⟨ha, hmono (Nat.le_succ _) h1⟩⟩
  · -- two points with the same image lie in pieces with indices at distance at most `1`
    have key : ∀ i j, i ≤ j → ∀ x ∈ P i, ∀ y ∈ P j, f x = f y → x = y := by
      intro i j hij x hx y hy hxy
      have hj : j = i ∨ j = i + 1 := by
        by_contra hne
        exact Set.disjoint_left.1 (hOdisj i j (by omega)) hx.1.1 (hxy ▸ hy.1.1)
      rcases hj with rfl | rfl
      · exact hVi _ hx.1.2 hy.1.2 hxy
      · exact hVi _ hx.2 hy.1.2 hxy
    intro x hx y hy hxy
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    obtain ⟨j, hj⟩ := mem_iUnion.1 hy
    rcases le_total i j with h | h
    · exact key i j h x hi y hj hxy
    · exact (key j i h y hj x hi hxy.symm).symm

/-- **[GN26, Proposition 3.8.20].** Let `f : X → Y` be continuous into a Hausdorff weakly
locally compact space and `A ⊆ X` a σ-compact set such that `f(A)` is closed and `f|_A` is a
topological embedding. If `f` is injective on a neighborhood of each point of `A`, then `f` is
injective on an open neighborhood of `A`. -/
theorem exists_isOpen_injOn_of_isSigmaCompact [T2Space Y] [WeaklyLocallyCompactSpace Y]
    {f : X → Y} (hf : Continuous f) {A : Set X} (hA : IsSigmaCompact A)
    (hclosed : IsClosed (f '' A)) (hemb : IsEmbedding (A.domRestrict f))
    (hloc : ∀ x ∈ A, ∃ W ∈ 𝓝 x, InjOn f W) : ∃ U, IsOpen U ∧ A ⊆ U ∧ InjOn f U := by
  have hce : IsClosedEmbedding (A.domRestrict f) :=
    ⟨hemb, by rw [range_domRestrict]; exact hclosed⟩
  refine exists_isOpen_injOn_of_isSigmaCompact_image hf (hA.image hf)
    (fun x hx y hy hxy ↦ congrArg Subtype.val
      (hemb.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)) (fun K hK ↦ ?_) hloc
  have h := (hce.isProperMap.isCompact_preimage hK).image continuous_subtype_val
  convert h using 1
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_image, Subtype.exists, exists_and_right,
    exists_eq_right]
  exact ⟨fun h ↦ ⟨h.1, h.2⟩, fun ⟨h1, h2⟩ ↦ ⟨h1, h2⟩⟩


/-- The restriction of a map that is a local homeomorphism near each point of an open set `U`
and injective on `U` is a homeomorphism of `U` onto an open set. -/
theorem exists_openPartialHomeomorph_of_injOn [Nonempty X] {f : X → Y} (hf : Continuous f)
    {U : Set X} (hU : IsOpen U) (hUi : InjOn f U)
    (hloc : ∀ x ∈ U, ∃ e : OpenPartialHomeomorph X Y, x ∈ e.source ∧ EqOn f e e.source) :
    ∃ Φ : OpenPartialHomeomorph X Y, Φ.source = U ∧ ⇑Φ = f := by
  have hopen : IsOpenMap (U.domRestrict f) := by
    intro V hV
    rw [isOpen_iff_forall_mem_open]
    rintro _ ⟨⟨x, hxU⟩, hxV, rfl⟩
    obtain ⟨e, hxe, heq⟩ := hloc x hxU
    obtain ⟨V', hV'o, hV'⟩ := isOpen_induced_iff.1 hV
    set W := V' ∩ U ∩ e.source
    have hW : IsOpen W := (hV'o.inter hU).inter e.open_source
    refine ⟨e '' W, ?_, e.isOpen_image_of_subset_source hW inter_subset_right, ?_⟩
    · rintro _ ⟨z, ⟨⟨hzV', hzU⟩, hze⟩, rfl⟩
      refine ⟨⟨z, hzU⟩, ?_, heq hze⟩
      rw [← hV']
      exact hzV'
    · refine ⟨x, ⟨⟨?_, hxU⟩, hxe⟩, (heq hxe).symm⟩
      have : (⟨x, hxU⟩ : U) ∈ Subtype.val ⁻¹' V' := by rw [hV']; exact hxV
      exact this
  exact ⟨OpenPartialHomeomorph.ofContinuousOpenRestrict (hUi.toPartialEquiv f U)
    hf.continuousOn hopen hU, rfl, rfl⟩

/-- **[GN26, Proposition 3.8.20], for local homeomorphisms near `A`.** Let `f : X → Y` be
continuous into a Hausdorff weakly locally compact space, `A ⊆ X` a σ-compact set with `f(A)`
closed and `f|_A` a topological embedding, and assume that near each point of `A`, `f` agrees with
a partial homeomorphism `e` having a property `P`. Then `f` restricts to a homeomorphism `Φ` from
an open neighborhood of `A` onto an open set, and near each point of the source of `Φ`, `f` agrees
with a partial homeomorphism having the property `P`. -/
theorem exists_openPartialHomeomorph_of_isSigmaCompact [T2Space Y] [WeaklyLocallyCompactSpace Y]
    [Nonempty X] {f : X → Y} (hf : Continuous f) {A : Set X} (hA : IsSigmaCompact A)
    (hclosed : IsClosed (f '' A)) (hemb : IsEmbedding (A.domRestrict f))
    (P : OpenPartialHomeomorph X Y → Prop)
    (hloc : ∀ x ∈ A, ∃ e : OpenPartialHomeomorph X Y, x ∈ e.source ∧ EqOn f e e.source ∧ P e) :
    ∃ Φ : OpenPartialHomeomorph X Y, A ⊆ Φ.source ∧ ⇑Φ = f ∧
      ∀ x ∈ Φ.source, ∃ e : OpenPartialHomeomorph X Y, x ∈ e.source ∧ EqOn f e e.source ∧ P e := by
  choose e he heq hP using hloc
  obtain ⟨U, hU, hAU, hUi⟩ := exists_isOpen_injOn_of_isSigmaCompact hf hA hclosed hemb
    fun x hx ↦ ⟨(e x hx).source, (e x hx).open_source.mem_nhds (he x hx),
      ((e x hx).injOn).congr fun y hy ↦ (heq x hx hy).symm⟩
  set S := ⋃ (a : X) (ha : a ∈ A), (e a ha).source
  have hS : IsOpen S := isOpen_iUnion fun a ↦ isOpen_iUnion fun ha ↦ (e a ha).open_source
  have hdata : ∀ x ∈ U ∩ S, ∃ (a : X) (ha : a ∈ A), x ∈ (e a ha).source := fun x hx ↦ by
    simpa [S] using hx.2
  obtain ⟨Φ, hΦs, hΦ⟩ := exists_openPartialHomeomorph_of_injOn hf (hU.inter hS)
    (hUi.mono inter_subset_left) fun x hx ↦
      let ⟨a, ha, hxa⟩ := hdata x hx; ⟨e a ha, hxa, heq a ha⟩
  refine ⟨Φ, fun a ha ↦ hΦs ▸ ⟨hAU ha, mem_iUnion₂.2 ⟨a, ha, he a ha⟩⟩, hΦ, fun x hx ↦ ?_⟩
  rw [hΦs] at hx
  obtain ⟨a, ha, hxa⟩ := hdata x hx
  exact ⟨e a ha, hxa, heq a ha, hP a ha⟩

end Topology

/-! ### Local diffeomorphisms -/

section Smooth

universe u

variable {E F : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N] [MBManifold F N]

/-- Being `C^k` is a local property. -/
theorem ContMDiffMBOn.of_local {k : ℕ} {f : M → N} {U : Set M} (hU : IsOpen U)
    (h : ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧ ContMDiffMBOn (E := E) (F := F) k f W) :
    ContMDiffMBOn (E := E) (F := F) k f U := by
  have hcont : ContinuousOn f U := fun x hx ↦ by
    obtain ⟨W, hW, hxW, hf⟩ := h x hx
    exact (hf.1.continuousAt (hW.mem_nhds hxW)).continuousWithinAt
  refine ⟨hcont, fun x hx ↦ ?_⟩
  set c := chartAt E x
  set c' := chartAt F (f x)
  refine ContDiffMBOn.of_local (isOpen_chartDomain hU hcont c c') fun y hy ↦ ?_
  obtain ⟨W, hW, hzW, hf⟩ := h (c.symm y) hy.2.1
  refine ⟨chartDomain f W c c', isOpen_chartDomain hW hf.1 c c', ⟨hy.1, hzW, hy.2.2⟩, ?_⟩
  exact (hf.contDiffMBOn_chart hW (chart_mem_atlas E x) (chart_mem_atlas F (f x))).mono
    inter_subset_right

/-- A partial homeomorphism that agrees near each point of its source with a `C^k` partial
homeomorphism is `C^k` on its source. -/
theorem OpenPartialHomeomorph.contMDiffMBOn_of_local {k : ℕ} (Φ : OpenPartialHomeomorph M N)
    (h : ∀ x ∈ Φ.source, ∃ e : OpenPartialHomeomorph M N, x ∈ e.source ∧ EqOn Φ e e.source ∧
      ContMDiffMBOn (E := E) (F := F) k e e.source) :
    ContMDiffMBOn (E := E) (F := F) k Φ Φ.source := by
  refine ContMDiffMBOn.of_local Φ.open_source fun x hx ↦ ?_
  obtain ⟨e, hxe, heq, he⟩ := h x hx
  refine ⟨e.source, e.open_source, hxe, he.congr_of_isOpen e.open_source fun z hz ↦ ?_⟩
  exact (heq hz).symm

/-- A partial homeomorphism whose inverse agrees near each point of its target with the `C^k`
inverse of a partial homeomorphism has a `C^k` inverse. -/
theorem OpenPartialHomeomorph.contMDiffMBOn_symm_of_local {k : ℕ} (Φ : OpenPartialHomeomorph M N)
    (h : ∀ x ∈ Φ.source, ∃ e : OpenPartialHomeomorph M N, x ∈ e.source ∧ EqOn Φ e e.source ∧
      ContMDiffMBOn (E := F) (F := E) k e.symm e.target) :
    ContMDiffMBOn (E := F) (F := E) k Φ.symm Φ.target := by
  refine ContMDiffMBOn.of_local Φ.open_target fun y hy ↦ ?_
  have hx : Φ.symm y ∈ Φ.source := Φ.map_target hy
  obtain ⟨e, hxe, heq, he⟩ := h _ hx
  have hey : e (Φ.symm y) = y := by rw [← heq hxe, Φ.right_inv hy]
  set O := Φ.target ∩ (e.target ∩ e.symm ⁻¹' Φ.source)
  have hO : IsOpen O := Φ.open_target.inter (e.isOpen_inter_preimage_symm Φ.open_source)
  have hyO : y ∈ O := by
    refine ⟨hy, ?_, ?_⟩
    · rw [← hey]; exact e.map_source hxe
    · rw [mem_preimage, ← hey, e.left_inv hxe]; exact hx
  have heO : ContMDiffMBOn (E := F) (F := E) k e.symm O :=
    he.comp hO e.open_target (smoothMBMOn_id hO k) fun z hz ↦ hz.2.1
  refine ⟨O, hO, hyO, heO.congr_of_isOpen hO fun z hz ↦ ?_⟩
  have hzs : e.symm z ∈ e.source := e.map_target hz.2.1
  have hΦ : Φ (e.symm z) = z := by rw [heq hzs, e.right_inv hz.2.1]
  rw [← hΦ, Φ.left_inv hz.2.2]
  simp only [hΦ]

/-- **[GN26, Corollary 3.8.19]** (`C^k` maps, `k ∈ ℕ`). A local `C^k`-diffeomorphism
`f : M → N` into a Hausdorff manifold that is injective on a compact set `K` restricts to a
`C^k`-diffeomorphism from an open neighborhood of `K` onto an open subset of `N`. -/
theorem exists_contMDiffMB_diffeo_of_isCompact [T2Space N] [Nonempty M] {k : ℕ} {f : M → N}
    (hf : ∀ x, ∃ e : OpenPartialHomeomorph M N, x ∈ e.source ∧ EqOn f e e.source ∧
      ContMDiffMBOn (E := E) (F := F) k e e.source ∧
      ContMDiffMBOn (E := F) (F := E) k e.symm e.target)
    {K : Set M} (hK : IsCompact K) (hinj : InjOn f K) :
    ∃ Φ : OpenPartialHomeomorph M N, K ⊆ Φ.source ∧ ⇑Φ = f ∧
      ContMDiffMBOn (E := E) (F := F) k Φ Φ.source ∧
      ContMDiffMBOn (E := F) (F := E) k Φ.symm Φ.target := by
  have hloc : IsLocalHomeomorph f := IsLocalHomeomorph.mk f fun x ↦
    let ⟨e, hx, heq, _⟩ := hf x; ⟨e, hx, heq⟩
  obtain ⟨Φ, hKΦ, hΦ⟩ := IsLocalHomeomorph.exists_openPartialHomeomorph_of_isCompact hloc hK hinj
  refine ⟨Φ, hKΦ, hΦ, OpenPartialHomeomorph.contMDiffMBOn_of_local Φ fun x _ ↦ ?_,
    OpenPartialHomeomorph.contMDiffMBOn_symm_of_local Φ fun x _ ↦ ?_⟩
  · obtain ⟨e, hx, heq, he, -⟩ := hf x
    exact ⟨e, hx, by rw [hΦ]; exact heq, he⟩
  · obtain ⟨e, hx, heq, -, he⟩ := hf x
    exact ⟨e, hx, by rw [hΦ]; exact heq, he⟩

/-- **[GN26, Corollary 3.8.19]** (smooth maps). A local diffeomorphism `f : M → N` into a
Hausdorff manifold that is injective on a compact set `K` restricts to a diffeomorphism from an
open neighborhood of `K` onto an open subset of `N`. -/
theorem exists_smoothMBM_diffeo_of_isCompact [T2Space N] [Nonempty M] {f : M → N}
    (hf : ∀ x, ∃ e : OpenPartialHomeomorph M N, x ∈ e.source ∧ EqOn f e e.source ∧
      SmoothMBMOn E F e e.source ∧ SmoothMBMOn F E e.symm e.target)
    {K : Set M} (hK : IsCompact K) (hinj : InjOn f K) :
    ∃ Φ : OpenPartialHomeomorph M N, K ⊆ Φ.source ∧ ⇑Φ = f ∧
      SmoothMBMOn E F Φ Φ.source ∧ SmoothMBMOn F E Φ.symm Φ.target := by
  have hloc : IsLocalHomeomorph f := IsLocalHomeomorph.mk f fun x ↦
    let ⟨e, hx, heq, _⟩ := hf x; ⟨e, hx, heq⟩
  obtain ⟨Φ, hKΦ, hΦ⟩ := IsLocalHomeomorph.exists_openPartialHomeomorph_of_isCompact hloc hK hinj
  refine ⟨Φ, hKΦ, hΦ, fun k ↦ OpenPartialHomeomorph.contMDiffMBOn_of_local Φ fun x _ ↦ ?_,
    fun k ↦ OpenPartialHomeomorph.contMDiffMBOn_symm_of_local Φ fun x _ ↦ ?_⟩
  · obtain ⟨e, hx, heq, he, -⟩ := hf x
    exact ⟨e, hx, by rw [hΦ]; exact heq, he k⟩
  · obtain ⟨e, hx, heq, -, he⟩ := hf x
    exact ⟨e, hx, by rw [hΦ]; exact heq, he k⟩


omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [LocallyConvexSpace ℝ F] [MBManifold E M] [MBManifold F N] in
/-- A manifold modeled on a finite-dimensional (Hausdorff) space is locally compact; this is how
the finite-dimensionality hypothesis of [GN26, Corollary 3.8.21], enters below (through
`WeaklyLocallyCompactSpace N`). -/
theorem locallyCompactSpace_of_finiteDimensional [FiniteDimensional ℝ F] :
    LocallyCompactSpace N := by
  let e := (Module.finBasis ℝ F).equivFun.toContinuousLinearEquiv
  have : LocallyCompactSpace F := e.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  exact ChartedSpace.locallyCompactSpace F N

/-- **[GN26, Corollary 3.8.21]** (`C^k` maps, `k ∈ ℕ`). Let `f : M → N` be continuous
into a Hausdorff, weakly locally compact manifold (e.g. a finite-dimensional one), `A ⊆ M` a
σ-compact set with `f(A)` closed and `f|_A` a topological embedding, and assume that near each
point of `A`, `f` agrees with a `C^k`-diffeomorphism between open sets. Then `f` restricts to a
`C^k`-diffeomorphism from an open neighborhood of `A` onto an open subset of `N`. -/
theorem exists_contMDiffMB_diffeo_of_isSigmaCompact [T2Space N] [WeaklyLocallyCompactSpace N]
    [Nonempty M] {k : ℕ} {f : M → N} (hf : Continuous f) {A : Set M} (hA : IsSigmaCompact A)
    (hclosed : IsClosed (f '' A)) (hemb : IsEmbedding (A.domRestrict f))
    (hloc : ∀ x ∈ A, ∃ e : OpenPartialHomeomorph M N, x ∈ e.source ∧ EqOn f e e.source ∧
      ContMDiffMBOn (E := E) (F := F) k e e.source ∧
      ContMDiffMBOn (E := F) (F := E) k e.symm e.target) :
    ∃ Φ : OpenPartialHomeomorph M N, A ⊆ Φ.source ∧ ⇑Φ = f ∧
      ContMDiffMBOn (E := E) (F := F) k Φ Φ.source ∧
      ContMDiffMBOn (E := F) (F := E) k Φ.symm Φ.target := by
  obtain ⟨Φ, hAΦ, hΦ, hdata⟩ := exists_openPartialHomeomorph_of_isSigmaCompact hf hA hclosed hemb
    (fun e ↦ ContMDiffMBOn (E := E) (F := F) k e e.source ∧
      ContMDiffMBOn (E := F) (F := E) k e.symm e.target) hloc
  refine ⟨Φ, hAΦ, hΦ, OpenPartialHomeomorph.contMDiffMBOn_of_local Φ fun x hx ↦ ?_,
    OpenPartialHomeomorph.contMDiffMBOn_symm_of_local Φ fun x hx ↦ ?_⟩
  · obtain ⟨e, hx, heq, he, -⟩ := hdata x hx
    exact ⟨e, hx, by rw [hΦ]; exact heq, he⟩
  · obtain ⟨e, hx, heq, -, he⟩ := hdata x hx
    exact ⟨e, hx, by rw [hΦ]; exact heq, he⟩

/-- **[GN26, Corollary 3.8.21]** (smooth maps); see
`exists_contMDiffMB_diffeo_of_isSigmaCompact`. -/
theorem exists_smoothMBM_diffeo_of_isSigmaCompact [T2Space N] [WeaklyLocallyCompactSpace N]
    [Nonempty M] {f : M → N} (hf : Continuous f) {A : Set M} (hA : IsSigmaCompact A)
    (hclosed : IsClosed (f '' A)) (hemb : IsEmbedding (A.domRestrict f))
    (hloc : ∀ x ∈ A, ∃ e : OpenPartialHomeomorph M N, x ∈ e.source ∧ EqOn f e e.source ∧
      SmoothMBMOn E F e e.source ∧ SmoothMBMOn F E e.symm e.target) :
    ∃ Φ : OpenPartialHomeomorph M N, A ⊆ Φ.source ∧ ⇑Φ = f ∧
      SmoothMBMOn E F Φ Φ.source ∧ SmoothMBMOn F E Φ.symm Φ.target := by
  obtain ⟨Φ, hAΦ, hΦ, hdata⟩ := exists_openPartialHomeomorph_of_isSigmaCompact hf hA hclosed hemb
    (fun e ↦ SmoothMBMOn E F e e.source ∧ SmoothMBMOn F E e.symm e.target) hloc
  refine ⟨Φ, hAΦ, hΦ, fun k ↦ OpenPartialHomeomorph.contMDiffMBOn_of_local Φ fun x hx ↦ ?_,
    fun k ↦ OpenPartialHomeomorph.contMDiffMBOn_symm_of_local Φ fun x hx ↦ ?_⟩
  · obtain ⟨e, hx, heq, he, -⟩ := hdata x hx
    exact ⟨e, hx, by rw [hΦ]; exact heq, he k⟩
  · obtain ⟨e, hx, heq, -, he⟩ := hdata x hx
    exact ⟨e, hx, by rw [hΦ]; exact heq, he k⟩

end Smooth

/-! ### Real analytic local diffeomorphisms -/

section Analytic

universe u

variable {E F : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [RealAnalyticManifold E M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N] [RealAnalyticManifold F N]

/-- **Real analyticity is local**: a map which near each point of an open set agrees with a
real analytic map is real analytic. -/
theorem realAnalyticMOn_of_local {f : M → N} {U : Set M} (hU : IsOpen U)
    (h : ∀ z ∈ U, ∃ W, IsOpen W ∧ z ∈ W ∧ ∃ V g, IsOpen V ∧ W ⊆ V ∧
      RealAnalyticMOn (E := E) (F := F) g V ∧ EqOn f g W) :
    RealAnalyticMOn (E := E) (F := F) f U := by
  have hcont : ContinuousOn f U := fun z hz ↦ by
    obtain ⟨W, hW, hzW, V, g, -, hWV, hg, heq⟩ := h z hz
    exact (((hg.1.mono hWV).congr fun y hy ↦ heq hy).continuousAt
      (hW.mem_nhds hzW)).continuousWithinAt
  refine ⟨hcont, fun x _ ↦ ?_⟩
  set c := chartAt E x
  set c' := chartAt F (f x)
  refine RealAnalyticOn.of_local (isOpen_chartDomain hU hcont c c') fun y hy ↦ ?_
  obtain ⟨W, hW, hpW, V, g, hV, hWV, hg, heq⟩ := h (c.symm y) hy.2.1
  have hfW : ContinuousOn f W := (hg.1.mono hWV).congr fun z hz ↦ heq hz
  refine ⟨chartDomain f W c c', isOpen_chartDomain hW hfW c c', ⟨hy.1, hpW, hy.2.2⟩, ?_⟩
  have hga := hg.realAnalyticOn_chart hV ((realAnalyticGroupoid E).chart_mem_maximalAtlas x)
    ((realAnalyticGroupoid F).chart_mem_maximalAtlas (f x))
  refine realAnalyticOn_congr (fun z hz ↦ ?_)
    (hga.mono fun z hz ↦ ⟨hz.2.1, hWV hz.2.2.1, ?_⟩)
  · simp only [comp_apply, heq hz.2.2.1]
    rfl
  · have := hz.2.2.2
    simp only [mem_preimage] at this ⊢
    rwa [← heq hz.2.2.1]

/-- A partial homeomorphism that agrees near each point of its source with a real analytic
partial homeomorphism is real analytic on its source. -/
theorem OpenPartialHomeomorph.realAnalyticMOn_of_local (Φ : OpenPartialHomeomorph M N)
    (h : ∀ x ∈ Φ.source, ∃ e : OpenPartialHomeomorph M N, x ∈ e.source ∧ EqOn Φ e e.source ∧
      RealAnalyticMOn (E := E) (F := F) e e.source) :
    RealAnalyticMOn (E := E) (F := F) Φ Φ.source :=
  LocallyConvex.Manifolds.realAnalyticMOn_of_local Φ.open_source fun x hx ↦
    let ⟨e, hxe, heq, he⟩ := h x hx
    ⟨e.source, e.open_source, hxe, e.source, e, e.open_source, subset_rfl, he, heq⟩

/-- A partial homeomorphism whose inverse agrees near each point of its target with the real
analytic inverse of a partial homeomorphism has a real analytic inverse. -/
theorem OpenPartialHomeomorph.realAnalyticMOn_symm_of_local (Φ : OpenPartialHomeomorph M N)
    (h : ∀ x ∈ Φ.source, ∃ e : OpenPartialHomeomorph M N, x ∈ e.source ∧ EqOn Φ e e.source ∧
      RealAnalyticMOn (E := F) (F := E) e.symm e.target) :
    RealAnalyticMOn (E := F) (F := E) Φ.symm Φ.target := by
  refine LocallyConvex.Manifolds.realAnalyticMOn_of_local Φ.open_target fun y hy ↦ ?_
  have hx : Φ.symm y ∈ Φ.source := Φ.map_target hy
  obtain ⟨e, hxe, heq, he⟩ := h _ hx
  have hey : e (Φ.symm y) = y := by rw [← heq hxe, Φ.right_inv hy]
  set O := Φ.target ∩ (e.target ∩ e.symm ⁻¹' Φ.source)
  have hO : IsOpen O := Φ.open_target.inter (e.isOpen_inter_preimage_symm Φ.open_source)
  have hyO : y ∈ O := by
    refine ⟨hy, ?_, ?_⟩
    · rw [← hey]; exact e.map_source hxe
    · rw [mem_preimage, ← hey, e.left_inv hxe]; exact hx
  refine ⟨O, hO, hyO, e.target, e.symm, e.open_target, fun z hz ↦ hz.2.1, he, fun z hz ↦ ?_⟩
  have hzs : e.symm z ∈ e.source := e.map_target hz.2.1
  have hΦ : Φ (e.symm z) = z := by rw [heq hzs, e.right_inv hz.2.1]
  rw [← hΦ, Φ.left_inv hz.2.2]
  simp only [hΦ]

/-- **[GN26, Corollary 3.8.19]** (real analytic maps, `r = ω`). A local real analytic
diffeomorphism `f : M → N` into a Hausdorff manifold that is injective on a compact set `K`
restricts to a real analytic diffeomorphism from an open neighborhood of `K` onto an open subset
of `N`. -/
theorem exists_realAnalyticMOn_diffeo_of_isCompact [T2Space N] [Nonempty M] {f : M → N}
    (hf : ∀ x, ∃ e : OpenPartialHomeomorph M N, x ∈ e.source ∧ EqOn f e e.source ∧
      RealAnalyticMOn (E := E) (F := F) e e.source ∧
      RealAnalyticMOn (E := F) (F := E) e.symm e.target)
    {K : Set M} (hK : IsCompact K) (hinj : InjOn f K) :
    ∃ Φ : OpenPartialHomeomorph M N, K ⊆ Φ.source ∧ ⇑Φ = f ∧
      RealAnalyticMOn (E := E) (F := F) Φ Φ.source ∧
      RealAnalyticMOn (E := F) (F := E) Φ.symm Φ.target := by
  have hloc : IsLocalHomeomorph f := IsLocalHomeomorph.mk f fun x ↦
    let ⟨e, hx, heq, _⟩ := hf x; ⟨e, hx, heq⟩
  obtain ⟨Φ, hKΦ, hΦ⟩ := IsLocalHomeomorph.exists_openPartialHomeomorph_of_isCompact hloc hK hinj
  refine ⟨Φ, hKΦ, hΦ, OpenPartialHomeomorph.realAnalyticMOn_of_local Φ fun x _ ↦ ?_,
    OpenPartialHomeomorph.realAnalyticMOn_symm_of_local Φ fun x _ ↦ ?_⟩
  · obtain ⟨e, hx, heq, he, -⟩ := hf x
    exact ⟨e, hx, by rw [hΦ]; exact heq, he⟩
  · obtain ⟨e, hx, heq, -, he⟩ := hf x
    exact ⟨e, hx, by rw [hΦ]; exact heq, he⟩

/-- **[GN26, Corollary 3.8.21]** (real analytic maps, `r = ω`). Let `f : M → N` be
continuous into a Hausdorff, weakly locally compact real analytic manifold (e.g. a
finite-dimensional one), `A ⊆ M` a σ-compact set with `f(A)` closed and `f|_A` a topological
embedding, and assume that near each point of `A`, `f` agrees with a real analytic
diffeomorphism between open sets. Then `f` restricts to a real analytic diffeomorphism from an
open neighborhood of `A` onto an open subset of `N`. -/
theorem exists_realAnalyticMOn_diffeo_of_isSigmaCompact [T2Space N] [WeaklyLocallyCompactSpace N]
    [Nonempty M] {f : M → N} (hf : Continuous f) {A : Set M} (hA : IsSigmaCompact A)
    (hclosed : IsClosed (f '' A)) (hemb : IsEmbedding (A.domRestrict f))
    (hloc : ∀ x ∈ A, ∃ e : OpenPartialHomeomorph M N, x ∈ e.source ∧ EqOn f e e.source ∧
      RealAnalyticMOn (E := E) (F := F) e e.source ∧
      RealAnalyticMOn (E := F) (F := E) e.symm e.target) :
    ∃ Φ : OpenPartialHomeomorph M N, A ⊆ Φ.source ∧ ⇑Φ = f ∧
      RealAnalyticMOn (E := E) (F := F) Φ Φ.source ∧
      RealAnalyticMOn (E := F) (F := E) Φ.symm Φ.target := by
  obtain ⟨Φ, hAΦ, hΦ, hdata⟩ := exists_openPartialHomeomorph_of_isSigmaCompact hf hA hclosed hemb
    (fun e ↦ RealAnalyticMOn (E := E) (F := F) e e.source ∧
      RealAnalyticMOn (E := F) (F := E) e.symm e.target) hloc
  refine ⟨Φ, hAΦ, hΦ, OpenPartialHomeomorph.realAnalyticMOn_of_local Φ fun x hx ↦ ?_,
    OpenPartialHomeomorph.realAnalyticMOn_symm_of_local Φ fun x hx ↦ ?_⟩
  · obtain ⟨e, hx, heq, he, -⟩ := hdata x hx
    exact ⟨e, hx, by rw [hΦ]; exact heq, he⟩
  · obtain ⟨e, hx, heq, -, he⟩ := hdata x hx
    exact ⟨e, hx, by rw [hΦ]; exact heq, he⟩

end Analytic

end LocallyConvex.Manifolds
