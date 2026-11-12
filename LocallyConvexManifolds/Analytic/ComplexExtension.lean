/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.Analytic.Basic
public import LocallyConvexAnalysis.Analytic.Identity
public import Mathlib.Topology.Compactness.Paracompact

/-!
# Complex analytic extensions to complexifications

We prove H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups* (arXiv:2602.12362),
Proposition 2.2.19: if `M*` is a paracompact complexification of the real analytic manifold `M`
in which `M` is closed, every real analytic map from `M` to a complex analytic manifold extends to
a complex analytic map on an open neighborhood of `M` in `M*`. The proof follows GN: local
extensions in charts (GN, Proposition 2.2.12, `RealAnalyticOn.exists_complexAnalytic_extension`),
their agreement near `M` by the identity theorem (GN, Theorem 2.1.16(c),
`ComplexAnalyticOn.eqOn_of_eqOn_real`), and a gluing lemma for paracompact spaces (GN,
Lemma A.5.10).

## Main results

* `exists_glue_of_paracompact`: GN, Lemma A.5.10.
* `complexAnalyticMOn_of_mem_maximalAtlas`, `complexAnalyticMOn_symm_of_mem_maximalAtlas`,
  `complexAnalyticMOn_of_local`: charts are complex analytic, and complex analyticity of maps
  between complex analytic manifolds is local.
* `IsComplexification.exists_local_extension`, `IsComplexification.eventuallyEq_of_extension`:
  the two local steps.
* `IsComplexification.exists_complexAnalytic_extension`: GN, Proposition 2.2.19.

## Implementation notes

* In `IsComplexification` the inclusion `M ⊆ M*` is an injective map `ι`; "`M` closed in `M*`"
  becomes `IsClosed (range ι)`. The topology of `M` never enters: the extension is glued on
  `M*`. Paracompactness is Mathlib's `ParacompactSpace`, together with `T2Space` (GN's
  paracompact spaces are Hausdorff, Definition A.5.2); regularity, used for closed
  neighborhoods, follows. We also assume `M` nonempty, to have an index for the gluing lemma.
* In Lemma A.5.10 the maps `g_i` are total maps `Z → Y` and need not be continuous; the
  conclusion only records that the glued map agrees near each point with some `g_i`, which is
  what the proof of Proposition 2.2.19 uses.
* The identity theorem is applied on convex open neighborhoods in `E_ℂ`, which exist since
  `E_ℂ` is locally convex; no local connectedness of `M*` beyond this is needed.
-/

@[expose] public section

open Set Filter Function
open scoped Topology
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

/-! ### Gluing near a closed subset of a paracompact space (GN, Lemma A.5.10) -/

section Glue

variable {Y Z ι : Type*} [TopologicalSpace Z]

/-- **Glöckner–Neeb, Lemma A.5.10.** Let `Z` be paracompact Hausdorff, `A ⊆ Z` closed, and
`(V_i)` open sets covering `A`, with maps `g_i` such that `g_i` and `g_j` agree near each point
of `A ∩ V_i ∩ V_j`. Then there are an open `U ⊇ A` and a map `G` which near each point of `U`
agrees with some `g_i` on an open subset of `V_i`. -/
theorem exists_glue_of_paracompact [ParacompactSpace Z] [T2Space Z] [Nonempty ι]
    {A : Set Z} (hA : IsClosed A) {V : ι → Set Z} (hV : ∀ i, IsOpen (V i))
    (hAV : A ⊆ ⋃ i, V i) (g : ι → Z → Y)
    (hg : ∀ i j, ∀ a ∈ A, a ∈ V i → a ∈ V j → ∃ O, IsOpen O ∧ a ∈ O ∧ EqOn (g i) (g j) O) :
    ∃ U, IsOpen U ∧ A ⊆ U ∧ ∃ G : Z → Y, ∀ x ∈ U, ∃ i, ∃ W, IsOpen W ∧ x ∈ W ∧
      W ⊆ U ∩ V i ∧ EqOn G (g i) W := by
  classical
  -- an index for each point of `A`, and a closed neighborhood inside `V_i`
  let ιz : Z → ι := fun z ↦
    if hz : z ∈ A then (mem_iUnion.1 (hAV hz)).choose else Classical.arbitrary ι
  have hιz : ∀ z ∈ A, z ∈ V (ιz z) := fun z hz ↦ by
    simp only [ιz, dite_eq_left hz]; exact (mem_iUnion.1 (hAV hz)).choose_spec
  have hQ : ∀ z, ∃ Q : Set Z, IsClosed Q ∧ (z ∈ A → Q ∈ 𝓝 z ∧ Q ⊆ V (ιz z)) := fun z ↦ by
    by_cases hz : z ∈ A
    · obtain ⟨Q, hQn, hQc, hQV⟩ := exists_mem_nhds_isClosed_subset
        ((hV _).mem_nhds (hιz z hz))
      exact ⟨Q, hQc, fun _ ↦ ⟨hQn, hQV⟩⟩
    · exact ⟨univ, isClosed_univ, fun h ↦ absurd h hz⟩
  choose Q hQc hQ using hQ
  let u : Z → Set Z := fun z ↦ if z ∈ A then interior (Q z) else Aᶜ
  have huo : ∀ z, IsOpen (u z) := fun z ↦ by
    by_cases hz : z ∈ A
    · simp only [u, ite_eq_left hz]; exact isOpen_interior
    · simp only [u, ite_eq_right hz]; exact hA.isOpen_compl
  have huc : ⋃ z, u z = univ := eq_univ_of_forall fun z ↦ mem_iUnion.2 ⟨z, by
    by_cases hz : z ∈ A
    · simp only [u, ite_eq_left hz]; exact mem_interior_iff_mem_nhds.2 (hQ z hz).1
    · simp only [u, ite_eq_right hz]; exact hz⟩
  obtain ⟨W, hWo, hWc, hWlf, hWu⟩ := precise_refinement u huo huc
  have hWA : ∀ j, j ∉ A → W j ⊆ Aᶜ := fun j hj ↦ by
    have := hWu j; simp only [u, ite_eq_right hj] at this; exact this
  have hWV : ∀ j ∈ A, closure (W j) ⊆ V (ιz j) := fun j hj ↦ by
    have h1 := hWu j
    simp only [u, ite_eq_left hj] at h1
    exact (closure_minimal (h1.trans interior_subset) (hQc j)).trans (hQ j hj).2
  -- the data at a point of `A`
  have hja : ∀ a, ∃ j, a ∈ A → j ∈ A ∧ a ∈ W j := fun a ↦ by
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hWc ▸ mem_univ a)
    refine ⟨j, fun ha ↦ ⟨?_, hj⟩⟩
    by_contra hjA
    exact hWA j hjA hj ha
  choose ja hja using hja
  choose N hN hNf using hWlf
  have hO : ∀ a j k, ∃ O : Set Z, IsOpen O ∧ a ∈ O ∧ (a ∈ A → j ∈ A → k ∈ A →
      a ∈ closure (W j) → a ∈ closure (W k) → EqOn (g (ιz j)) (g (ιz k)) O) := by
    intro a j k
    by_cases h : a ∈ A ∧ j ∈ A ∧ k ∈ A ∧ a ∈ closure (W j) ∧ a ∈ closure (W k)
    · obtain ⟨ha, hj, hk, haj, hak⟩ := h
      obtain ⟨O, hO, haO, hEq⟩ := hg _ _ a ha (hWV j hj haj) (hWV k hk hak)
      exact ⟨O, hO, haO, fun _ _ _ _ _ ↦ hEq⟩
    · refine ⟨univ, isOpen_univ, mem_univ a, fun ha hj hk haj hak ↦ ?_⟩
      exact absurd ⟨ha, hj, hk, haj, hak⟩ h
  choose O hOo haO hOeq using hO
  let S : Z → Set Z := fun a ↦ {j | (W j ∩ N a).Nonempty}
  let Φ : Z → Set Z := fun a ↦ {j | j ∈ A ∧ j ∈ S a ∧ a ∈ closure (W j)}
  let Ψ : Z → Set Z := fun a ↦ {j | j ∈ A ∧ j ∈ S a ∧ a ∉ closure (W j)}
  have hΦf : ∀ a, (Φ a).Finite := fun a ↦ (hNf a).subset fun j hj ↦ hj.2.1
  have hΨf : ∀ a, (Ψ a).Finite := fun a ↦ (hNf a).subset fun j hj ↦ hj.2.1
  let U' : Z → Set Z := fun a ↦ interior (N a) ∩ (⋂ j ∈ Ψ a, (closure (W j))ᶜ) ∩
    (⋂ p ∈ Φ a ×ˢ Φ a, O a p.1 p.2) ∩ W (ja a)
  have hU'o : ∀ a, IsOpen (U' a) := fun a ↦
    ((isOpen_interior.inter ((hΨf a).isOpen_biInter fun j _ ↦ isClosed_closure.isOpen_compl)).inter
      (((hΦf a).prod (hΦf a)).isOpen_biInter fun p _ ↦ hOo a p.1 p.2)).inter (hWo _)
  have haU' : ∀ a ∈ A, a ∈ U' a := fun a ha ↦
    ⟨⟨⟨mem_interior_iff_mem_nhds.2 (hN a), mem_iInter₂.2 fun j hj ↦ hj.2.2⟩,
      mem_iInter₂.2 fun p _ ↦ haO a p.1 p.2⟩, (hja a ha).2⟩
  -- the index of `U' a` belongs to `Φ a`, and so does the index of any `U' b` meeting it
  have hjΦ : ∀ a ∈ A, ∀ b ∈ A, ∀ z ∈ U' a, z ∈ U' b → ja b ∈ Φ a := by
    intro a ha b hb z hza hzb
    have hzW : z ∈ W (ja b) := hzb.2
    have hS : ja b ∈ S a := ⟨z, hzW, interior_subset hza.1.1.1⟩
    refine ⟨(hja b hb).1, hS, ?_⟩
    by_contra hcl
    exact (mem_iInter₂.1 hza.1.1.2 (ja b) ⟨(hja b hb).1, hS, hcl⟩) (subset_closure hzW)
  set U := ⋃ a ∈ A, U' a
  have hUo : IsOpen U := isOpen_biUnion fun a _ ↦ hU'o a
  let G : Z → Y := fun z ↦
    if h : ∃ a ∈ A, z ∈ U' a then g (ιz (ja h.choose)) z else g (Classical.arbitrary ι) z
  refine ⟨U, hUo, fun a ha ↦ mem_biUnion ha (haU' a ha), G, fun x hx ↦ ?_⟩
  obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 hx
  refine ⟨ιz (ja a), U' a, hU'o a, hxa, fun z hz ↦ ⟨mem_biUnion ha hz,
    hWV _ (hja a ha).1 (subset_closure hz.2)⟩, fun z hz ↦ ?_⟩
  have h : ∃ a ∈ A, z ∈ U' a := ⟨a, ha, hz⟩
  simp only [G, dite_eq_left h]
  obtain ⟨hbA, hzb⟩ := h.choose_spec
  have h1 := hjΦ a ha _ hbA z hz hzb
  have h2 := hjΦ a ha a ha z hz hz
  have hzO : z ∈ O a (ja a) (ja h.choose) := mem_iInter₂.1 hz.1.2 (ja a, ja h.choose) ⟨h2, h1⟩
  exact (hOeq a (ja a) (ja h.choose) ha h2.1 h1.1 h2.2.2 h1.2.2 hzO).symm

end Glue

/-! ### Complex analytic maps: charts and locality -/

section ComplexCharts

universe u

attribute [local instance] continuousSMul_real_of_complex

variable {G F : Type u}
  [AddCommGroup G] [Module ℝ G] [Module ℂ G] [IsScalarTower ℝ ℂ G] [TopologicalSpace G]
  [IsTopologicalAddGroup G] [ContinuousSMul ℂ G] [LocallyConvexSpace ℝ G] [T2Space G]
  [AddCommGroup F] [Module ℝ F] [Module ℂ F] [IsScalarTower ℝ ℂ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {P : Type*} [TopologicalSpace P] [ChartedSpace G P] [ComplexAnalyticManifold G P]
  {L : Type*} [TopologicalSpace L] [ChartedSpace F L] [ComplexAnalyticManifold F L]

/-- Charts of the maximal atlas of a complex analytic manifold are complex analytic. -/
theorem complexAnalyticMOn_of_mem_maximalAtlas {e : OpenPartialHomeomorph P G}
    (he : e ∈ (complexAnalyticGroupoid G).maximalAtlas P) :
    ComplexAnalyticMOn (E := G) (F := G) e e.source := by
  refine ⟨e.continuousOn, fun x _ ↦ ?_⟩
  have h := complexAnalyticOn_transition
    ((complexAnalyticGroupoid G).chart_mem_maximalAtlas x) he
  exact h.mono ((chartAt G x).isOpen_inter_preimage_symm e.open_source)
    (isOpen_chartDomain e.open_source e.continuousOn _ _) fun y hy ↦ ⟨hy.1, hy.2.1⟩

/-- Inverses of charts of the maximal atlas are complex analytic. -/
theorem complexAnalyticMOn_symm_of_mem_maximalAtlas {e : OpenPartialHomeomorph P G}
    (he : e ∈ (complexAnalyticGroupoid G).maximalAtlas P) :
    ComplexAnalyticMOn (E := G) (F := G) e.symm e.target := by
  refine ⟨e.continuousOn_symm, fun y _ ↦ ?_⟩
  have h := complexAnalyticOn_transition he
    ((complexAnalyticGroupoid G).chart_mem_maximalAtlas (e.symm y))
  exact h.mono (e.isOpen_inter_preimage_symm (chartAt G (e.symm y)).open_source)
    (isOpen_chartDomain e.open_target e.continuousOn_symm _ _) fun z hz ↦ ⟨hz.2.1, hz.2.2⟩

/-- Restriction of complex analytic maps to smaller open sets. -/
theorem ComplexAnalyticMOn.mono_of_isOpen {f : P → L} {U V : Set P} (hU : IsOpen U)
    (hV : IsOpen V) (hf : ComplexAnalyticMOn (E := G) (F := F) f U) (hVU : V ⊆ U) :
    ComplexAnalyticMOn (E := G) (F := F) f V :=
  hf.comp hV hU (complexAnalyticMOn_id hV) hVU

/-- **Complex analyticity is local**: a map which near each point of an open set agrees with a
complex analytic map is complex analytic. -/
theorem complexAnalyticMOn_of_local {f : P → L} {U : Set P} (hU : IsOpen U)
    (h : ∀ z ∈ U, ∃ W, IsOpen W ∧ z ∈ W ∧ ∃ V g, IsOpen V ∧ W ⊆ V ∧
      ComplexAnalyticMOn (E := G) (F := F) g V ∧ EqOn f g W) :
    ComplexAnalyticMOn (E := G) (F := F) f U := by
  have hloc : ∀ z ∈ U, ∃ W, IsOpen W ∧ z ∈ W ∧ ContinuousOn f W := fun z hz ↦ by
    obtain ⟨W, hW, hzW, V, g, -, hWV, hg, heq⟩ := h z hz
    exact ⟨W, hW, hzW, (hg.1.mono hWV).congr fun y hy ↦ heq hy⟩
  have hcont : ContinuousOn f U := fun z hz ↦ by
    obtain ⟨W, hW, hzW, hfW⟩ := hloc z hz
    exact (hfW.continuousAt (hW.mem_nhds hzW)).continuousWithinAt
  refine ⟨hcont, fun x _ ↦ ?_⟩
  set c := chartAt G x
  set c' := chartAt F (f x)
  refine ComplexAnalyticOn.of_local (isOpen_chartDomain hU hcont c c') fun y hy ↦ ?_
  obtain ⟨W, hW, hpW, V, g, hV, hWV, hg, heq⟩ := h (c.symm y) hy.2.1
  have hfW : ContinuousOn f W := (hg.1.mono hWV).congr fun z hz ↦ heq hz
  have hD := isOpen_chartDomain hW hfW c c'
  refine ⟨chartDomain f W c c', hD, ⟨hy.1, hpW, hy.2.2⟩, ?_⟩
  have hga := hg.complexAnalyticOn_chart hV ((complexAnalyticGroupoid G).chart_mem_maximalAtlas x)
    ((complexAnalyticGroupoid F).chart_mem_maximalAtlas (f x))
  have hD' := (isOpen_chartDomain hU hcont c c').inter hD
  refine (hga.mono (isOpen_chartDomain hV hg.1 c c') hD' fun z hz ↦ ⟨hz.2.1, hWV hz.2.2.1, ?_⟩)
    |>.congr hD' fun z hz ↦ ?_
  · have := hz.2.2.2
    simp only [mem_preimage] at this ⊢
    rwa [← heq hz.2.2.1]
  · simp only [comp_apply, heq hz.2.2.1]
    rfl

end ComplexCharts

/-! ### Extension to complexifications (GN, Proposition 2.2.19) -/

section Extension

universe u

attribute [local instance] continuousSMul_real_of_complex

open Complexification

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {F : Type u}
  [AddCommGroup F] [Module ℝ F] [Module ℂ F] [IsScalarTower ℝ ℂ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [RealAnalyticManifold E M]
  {Mc : Type*} [TopologicalSpace Mc] [ChartedSpace (Complexification E) Mc]
  [ComplexAnalyticManifold (Complexification E) Mc]
  {L : Type*} [TopologicalSpace L] [ChartedSpace F L] [ComplexAnalyticManifold F L]
  {ι : M → Mc}

/-- Local complex analytic extensions (the first step of the proof of GN, Proposition 2.2.19):
around `ι x`, a real analytic `f : M → L` has a complex analytic extension. -/
theorem IsComplexification.exists_local_extension (hc : IsComplexification E M Mc ι)
    {f : M → L} (hf : RealAnalyticMOn (E := E) (F := F) f univ) (x : M) :
    ∃ V : Set Mc, IsOpen V ∧ ι x ∈ V ∧ ∃ g : Mc → L,
      ComplexAnalyticMOn (E := Complexification E) (F := F) g V ∧
      ∀ m, ι m ∈ V → g (ι m) = f m := by
  have := ComplexAnalyticManifold.realAnalyticManifold F L
  obtain ⟨φ, hφ, ψ, hψ, hxψ, hsrc, -, hφι, -⟩ := hc.exists_chart x
  set κ := chartAt F (f x)
  set D := chartDomain f univ ψ κ
  have hD : IsOpen D := isOpen_chartDomain isOpen_univ hf.1 ψ κ
  have hh : RealAnalyticOn (κ ∘ f ∘ ψ.symm) D := hf.realAnalyticOn_chart isOpen_univ hψ
    ((realAnalyticGroupoid F).chart_mem_maximalAtlas (f x))
  obtain ⟨W, hW, h, hh', hext⟩ := hh.exists_complexAnalytic_extension
  set W' : Set (Complexification E) := (W ∩ h ⁻¹' κ.target) ∩ (re ⁻¹' D ∪ im ⁻¹' {0}ᶜ)
  have hW' : IsOpen W' :=
    ((hh'.smoothMBOn hW 0).continuousOn.isOpen_inter_preimage hW κ.open_target).inter
      ((hD.preimage continuous_re).union (isOpen_compl_singleton.preimage continuous_im))
  have hreal : ∀ y ∈ D, ofReal y ∈ W' := fun y hy ↦ by
    refine ⟨⟨(hext y hy).1, ?_⟩, Or.inl (by simpa using hy)⟩
    simp only [mem_preimage, (hext y hy).2, comp_apply]
    exact κ.map_source hy.2.2
  set V := φ.source ∩ φ ⁻¹' W'
  have hV : IsOpen V := φ.isOpen_inter_preimage hW'
  have hxD : ψ x ∈ D := ⟨ψ.map_source hxψ, by
    simp only [mem_preimage, ψ.left_inv hxψ]; exact ⟨mem_univ _, mem_chart_source F (f x)⟩⟩
  have hxV : ι x ∈ V := by
    have hxφ : ι x ∈ φ.source := by rw [hsrc] at hxψ; exact hxψ
    exact ⟨hxφ, by simp only [mem_preimage, hφι x hxψ]; exact hreal _ hxD⟩
  refine ⟨V, hV, hxV, κ.symm ∘ h ∘ φ, ?_, fun m hm ↦ ?_⟩
  · have h1 : ComplexAnalyticMOn (E := Complexification E) (F := Complexification E) φ V :=
      (complexAnalyticMOn_of_mem_maximalAtlas hφ).mono_of_isOpen φ.open_source hV
        inter_subset_left
    have h2 : ComplexAnalyticMOn (E := Complexification E) (F := F) h W' :=
      (complexAnalyticMOn_iff_complexAnalyticOn hW').2
        (hh'.mono hW hW' fun z hz ↦ hz.1.1)
    have h3 := complexAnalyticMOn_symm_of_mem_maximalAtlas
      ((complexAnalyticGroupoid F).chart_mem_maximalAtlas (M := L) (f x))
    have h12 := h2.comp hV hW' h1 fun z hz ↦ hz.2
    exact h3.comp hV κ.open_target h12 fun z hz ↦ hz.2.1.2
  · have hmψ : m ∈ ψ.source := by rw [hsrc]; exact hm.1
    have hmW := hm.2
    simp only [mem_preimage, hφι m hmψ] at hmW
    have hmD : ψ m ∈ D := by
      rcases hmW.2 with h' | h'
      · simpa using h'
      · simp at h'
    have hmκ : f m ∈ κ.source := by
      have := hmD.2.2; simp only [mem_preimage, ψ.left_inv hmψ] at this; exact this
    simp only [comp_apply, hφι m hmψ, (hext _ hmD).2, ψ.left_inv hmψ]
    exact κ.left_inv hmκ

omit [RealAnalyticManifold E M] in
/-- Local uniqueness of complex analytic extensions (the identity theorem step of the proof of
GN, Proposition 2.2.19): two complex analytic maps on open sets `V₁`, `V₂` of `M*` which agree
with `f` on the points of `M` agree near each point `ι m ∈ V₁ ∩ V₂`. -/
theorem IsComplexification.eventuallyEq_of_extension (hc : IsComplexification E M Mc ι)
    {f : M → L} {V₁ V₂ : Set Mc} (hV₁ : IsOpen V₁) (hV₂ : IsOpen V₂) {g₁ g₂ : Mc → L}
    (hg₁ : ComplexAnalyticMOn (E := Complexification E) (F := F) g₁ V₁)
    (hg₂ : ComplexAnalyticMOn (E := Complexification E) (F := F) g₂ V₂)
    (hf₁ : ∀ m, ι m ∈ V₁ → g₁ (ι m) = f m) (hf₂ : ∀ m, ι m ∈ V₂ → g₂ (ι m) = f m) {m : M}
    (hm₁ : ι m ∈ V₁) (hm₂ : ι m ∈ V₂) : ∃ O, IsOpen O ∧ ι m ∈ O ∧ EqOn g₁ g₂ O := by
  obtain ⟨φ, hφ, ψ, -, hmψ, hsrc, -, hφι, hrange⟩ := hc.exists_chart m
  set κ := chartAt F (f m)
  set T := ((V₁ ∩ g₁ ⁻¹' κ.source) ∩ (V₂ ∩ g₂ ⁻¹' κ.source)) ∩ φ.source
  have hT : IsOpen T := ((hg₁.1.isOpen_inter_preimage hV₁ κ.open_source).inter
    (hg₂.1.isOpen_inter_preimage hV₂ κ.open_source)).inter φ.open_source
  have hmφ : ι m ∈ φ.source := by rw [hsrc] at hmψ; exact hmψ
  have hκm : f m ∈ κ.source := mem_chart_source F (f m)
  have hmT : ι m ∈ T := ⟨⟨⟨hm₁, by rw [mem_preimage, hf₁ m hm₁]; exact hκm⟩,
    ⟨hm₂, by rw [mem_preimage, hf₂ m hm₂]; exact hκm⟩⟩, hmφ⟩
  set R := φ.target ∩ φ.symm ⁻¹' T
  have hR : IsOpen R := φ.isOpen_inter_preimage_symm hT
  have hmR : φ (ι m) ∈ R := ⟨φ.map_source hmφ, by rw [mem_preimage, φ.left_inv hmφ]; exact hmT⟩
  obtain ⟨S, hSn, hSc, hSR⟩ := (locallyConvexSpace_iff_exists_convex_subset ℝ
    (Complexification E)).1 inferInstance _ R (hR.mem_nhds hmR)
  set B := interior S
  have hB : IsOpen B := isOpen_interior
  have hmB : φ (ι m) ∈ B := mem_interior_iff_mem_nhds.2 hSn
  have hBR : B ⊆ R := interior_subset.trans hSR
  have hrep : ∀ {g : Mc → L} {V : Set Mc}, IsOpen V →
      ComplexAnalyticMOn (E := Complexification E) (F := F) g V →
      (∀ z ∈ T, z ∈ V ∧ g z ∈ κ.source) → ComplexAnalyticOn (κ ∘ g ∘ φ.symm) B := by
    intro g V hV hg hTV
    refine (hg.complexAnalyticOn_chart hV hφ
      ((complexAnalyticGroupoid F).chart_mem_maximalAtlas (M := L) (f m))).mono
      (isOpen_chartDomain hV hg.1 φ κ) hB fun z hz ↦ ?_
    obtain ⟨hzt, hzT⟩ := hBR hz
    exact ⟨hzt, (hTV _ hzT).1, (hTV _ hzT).2⟩
  have h₁ := hrep hV₁ hg₁ fun z hz ↦ hz.1.1
  have h₂ := hrep hV₂ hg₂ fun z hz ↦ hz.1.2
  set H : Submodule ℝ (Complexification E) := LinearMap.range (ofRealₗ (E := E))
  have hH : ∀ w : Complexification E, ∃ a ∈ H, ∃ b ∈ H, w = a + Complex.I • b := fun w ↦
    ⟨_, ⟨re w, rfl⟩, _, ⟨im w, rfl⟩, (mk_eq_add_I_smul (re w) (im w)).symm ▸ rfl⟩
  have heq := ComplexAnalyticOn.eqOn_of_eqOn_real hB hSc.interior.isPreconnected h₁ h₂ H hH
    hmB fun h hh hxh ↦ by
      obtain ⟨h', rfl⟩ := hh
      have hreal : φ (ι m) + ofRealₗ h' = ofReal (ψ m + h') := by
        rw [hφι m hmψ, map_add]; rfl
      obtain ⟨hzt, hzT⟩ := hBR hxh
      have hz : φ.symm (φ (ι m) + ofRealₗ h') ∈ φ.source ∩ range ι := by
        rw [hrange]
        refine ⟨φ.map_target hzt, ?_⟩
        rw [mem_preimage, φ.right_inv hzt, hreal]
        exact mem_range_self _
      obtain ⟨m', hm'⟩ := hz.2
      simp only [comp_apply, ← hm', hf₁ m' (hm' ▸ hzT.1.1.1), hf₂ m' (hm' ▸ hzT.1.2.1)]
  refine ⟨φ.source ∩ φ ⁻¹' B, φ.isOpen_inter_preimage hB, ⟨hmφ, hmB⟩, fun z hz ↦ ?_⟩
  have hzT : z ∈ T := by
    have := (hBR hz.2).2; rwa [mem_preimage, φ.left_inv hz.1] at this
  have := heq hz.2
  simp only [comp_apply, φ.left_inv hz.1] at this
  rw [← κ.left_inv hzT.1.1.2, this, κ.left_inv hzT.1.2.2]

/-- **Glöckner–Neeb, Proposition 2.2.19.** Let `M*` be a complexification of the real analytic
manifold `M` (`ι : M → M*`), with `ι(M)` closed in `M*` and `M*` paracompact Hausdorff. Every real
analytic map `f : M → L` into a complex analytic manifold extends to a complex analytic map on an
open neighborhood of `ι(M)`: there are `U ⊇ ι(M)` open and `g` complex analytic on `U` with
`g ∘ ι = f`. -/
theorem IsComplexification.exists_complexAnalytic_extension [ParacompactSpace Mc] [T2Space Mc]
    [Nonempty M] (hc : IsComplexification E M Mc ι) (hcl : IsClosed (range ι)) {f : M → L}
    (hf : RealAnalyticMOn (E := E) (F := F) f univ) :
    ∃ U : Set Mc, IsOpen U ∧ range ι ⊆ U ∧ ∃ g : Mc → L,
      ComplexAnalyticMOn (E := Complexification E) (F := F) g U ∧ ∀ x, g (ι x) = f x := by
  choose V hV hxV g hg hgf using hc.exists_local_extension hf
  obtain ⟨U, hU, hAU, G, hG⟩ := exists_glue_of_paracompact hcl hV
    (fun z ⟨x, hx⟩ ↦ mem_iUnion.2 ⟨x, hx ▸ hxV x⟩) g fun i j a ⟨m, hm⟩ hai haj ↦ by
      subst hm
      exact hc.eventuallyEq_of_extension (hV i) (hV j) (hg i) (hg j) (hgf i) (hgf j) hai haj
  refine ⟨U, hU, hAU, G, complexAnalyticMOn_of_local hU fun z hz ↦ ?_, fun x ↦ ?_⟩
  · obtain ⟨i, W, hW, hzW, hWU, hEq⟩ := hG z hz
    exact ⟨W, hW, hzW, V i, g i, hV i, fun y hy ↦ (hWU hy).2, hg i, hEq⟩
  · obtain ⟨i, W, -, hxW, hWU, hEq⟩ := hG (ι x) (hAU (mem_range_self x))
    rw [hEq hxW, hgf i x (hWU hxW).2]

end Extension

end LocallyConvex.Manifolds
