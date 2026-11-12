/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.Manifold.Ckl
public import LocallyConvexManifolds.MappingSpace.Ck

/-!
# The exponential law for manifolds of mappings

Let `M` be a compact manifold modeled on `H`, `N` a manifold with a local addition, and
`ℓ ∈ ℕ ∪ {∞}`. We prove the exponential law of [GN26, Theorem 4.2.2(a)], for the atlases
`LocalAddition.mappingAtlasCk` and `LocalAddition.mappingAtlasSm` of `C^ℓ(M, N)`: for every space
`L` with an atlas with varying models `B` (a manifold of the library through
`VaryingAtlas.ofChartedSpace`, or a manifold of mappings), a map `g : L → C^ℓ(M, N)` is `C^k` if
and only if `g^∧ : L × M → N`, `(x, y) ↦ g(x)(y)`, is `C^{k,ℓ}`. Applied to the identity, the law
characterizes the smooth structure.

## Main results

* `LocalAddition.contMDiffOn_mappingAtlasCk_iff`: the exponential law for finite `ℓ`;
  `LocalAddition.contMDiffOn_mappingAtlasSm_iff`: for `ℓ = ∞` (`g^∧` is `C^{k,ℓ}` for all `ℓ`).
* `LocalAddition.equivalent_mappingAtlasCk_of_expLaw`,
  `LocalAddition.equivalent_mappingAtlasSm_of_expLaw`: **uniqueness**, an atlas on `C^ℓ(M, N)`
  satisfying the exponential law defines the same smooth structure (`VaryingAtlas.Equivalent`).
* `LocalAddition.contMDiffMB₂_eval`, `LocalAddition.contMDiffMB₂_evalSm`:
  **[GN26, Theorem 4.2.2(c)]**, the evaluation map `ε : C^ℓ(M, N) × M → N` is `C^{k,ℓ}` for every
  `k` (the law applied to the identity); `LocalAddition.smooth_eval`, `LocalAddition.smooth_evalSm`:
  the point evaluations `ε_x` are smooth.
* `LocalAddition.continuous_of_contMDiffMB₂`: if `g^∧` is `C^{k,ℓ}`, `g` is continuous for the
  compact-open `C^ℓ` topology. `LocalAddition.smooth_toCk`: `C^∞(M, N) → C^ℓ(M, N)` is smooth.

## Implementation notes

* **The proof.** If `g` is `C^k`, then near `(x₀, y₀)` the local representative of `g^∧` is
  `(a, b) ↦ c(Σ(τ(a)(b)))` with `τ = φ_f ∘ g` (`f = g(x₀)`), the composition of the smooth map
  `LocalAddition.invLocal` with the evaluation of `τ`; as a function of `a`, it is a superposition
  operator applied to a `C^k` curve in `C^ℓ(V, E × E)`, hence `C^k`
  (`ContDiffMBMap.contDiffMBOn_compLeftOn`), and uncurrying ([GN26, Theorem 1.7.30]) gives
  `C^{k,ℓ}`. Conversely, the local representatives of `φ_f ∘ g` are superposition operators by
  `LocalAddition.chartLocal` applied to the curried local representatives of `g^∧`, over a finite
  cover of `M` by compact sets on which `g(x)` stays in single charts of `N` for `x` near `x₁`.
  Glöckner–Neeb argue through the exponential law for sections ([GN26, Proposition 4.1.34]) and the
  smoothness of the evaluation map ([GN26, Proposition 4.1.32]). We do not claim these arguments are
  new. * **Local compactness.** If `M` is nonempty and compact, its model `H` is locally compact
  (`locallyCompactSpace_of_compactSpace`), hence finite-dimensional by Riesz's theorem
  (`finiteDimensional_of_compactSpace`): `M` is modeled on some `ℝⁿ`, and only the target `N` may be
  infinite-dimensional. The proofs use only the local compactness of `H` (for uncurrying,
  [GN26, Theorem 1.7.30(a)], and for superposition operators); it is derived inside the proofs,
  after disposing of the trivial case `M = ∅` (where `C^ℓ(M, N)` and `Γ_f` are points), so that the
  public statements carry only Glöckner–Neeb's hypotheses on `M` (compact, Hausdorff).
  Inside the proofs, it is used for uncurrying, for the chart independence of `C^{k,ℓ}` maps and
  for the superposition operators.
* **Uniqueness.** It is stated for atlases on `C^ℓ(M, N)` indexed by a type in the universe of
  `C^ℓ(M, N)` (as is the canonical atlas), and assumes the exponential law only for atlases `B` on
  `C^ℓ(M, N)` itself, which is all that its proof uses (the law is applied to the identity in both
  directions).
* Manifolds with rough boundary (for `L` or `M`), which Glöckner–Neeb allow, are out of scope.
* **[GN26, Theorem 4.2.2(b)].** The topology of `C^ℓ(M, N)` underlying the atlas is the compact-open
  `C^ℓ` topology `CkMap.instTopologicalSpace`, the jet topology (the charts are partial
  homeomorphisms for it); for compact `M` it is the chart topology
  (`CkMap.topology_eq_chartTopology_of_compactSpace`), in which `continuous_of_contMDiffMB₂` is
  proved. Its agreement with the topology of [GN26, Definition 4.1.2], defined through the
  iterated tangent maps `T^j g`, is `CkMap.topology_eq_gnTopology`
  (`MappingSpace/TopologyULift.lean`).

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

section ExpLawCk

variable {H : Type u} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [IsTopologicalAddGroup H]
  [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [MBManifold H M] [CompactSpace M]
  [T2Space M]
  {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {N : Type v} [TopologicalSpace N] [ChartedSpace E N] [MBManifold E N]
  (A : LocalAddition E N) {ℓ : ℕ}
  {L : Type*} [TopologicalSpace L] {B : VaryingAtlas.{u, _, _} L}

namespace LocalAddition

/-- **Exponential law, first half** ([GN26, Theorem 4.2.2(a)]): if `g : L → C^ℓ(M, N)` is
`C^k`, then `g^∧ : L × M → N`, `(x, y) ↦ g(x)(y)`, is `C^{k,ℓ}`. -/
theorem contMDiffMB₂_of_contMDiffOn {k : ℕ} {g : L → CkMap H E ℓ M N}
    (hg : B.ContMDiffOn A.mappingAtlasCk k g univ) :
    ContMDiffMB₂ H E B k ℓ (fun p ↦ g p.1 p.2) := by
  intro x₀ y₀
  have : Nonempty M := ⟨y₀⟩
  have := locallyCompactSpace_of_compactSpace (H := H) M
  obtain ⟨i, hi⟩ := B.exists_mem_source x₀
  set f := g x₀
  let e' : atlas H M := ⟨chartAt H y₀, chart_mem_atlas H y₀⟩
  let c : atlas E N := ⟨chartAt E (f y₀), chart_mem_atlas E (f y₀)⟩
  set φ := B.chart i
  have hgc : Continuous g := continuousOn_univ.1 hg.1
  set D₁ := chartDomain g univ φ (A.chartCk f)
  have hD₁ : IsOpen D₁ := isOpen_chartDomain isOpen_univ hg.1 φ (A.chartCk f)
  have hx₀D₁ : φ x₀ ∈ D₁ := by
    refine ⟨φ.map_source hi, mem_univ _, ?_⟩
    rw [mem_preimage, φ.left_inv hi]
    exact A.mem_chartCk_source f
  set R := A.chartCk f ∘ g ∘ φ.symm
  have hR : ContDiffMBOn k R D₁ := hg.2 i f
  set V₀ := chartDomOpens (CkMap.toC f) e' c
  have hy₀ : e'.1 y₀ ∈ V₀ := chartAt_mem_chartDomOpens (CkMap.toC f) y₀
  -- the set of `(a, b)` with `g(φ⁻¹ a)(e'⁻¹ b)` in the source of `c` is open
  have hev : Continuous fun p : L × M ↦ g p.1 p.2 :=
    continuous_eval.comp ((CkMap.continuous_toC.comp hgc).prodMap continuous_id)
  have hG : ContinuousOn (fun p : B.model i × H ↦ g (φ.symm p.1) (e'.1.symm p.2))
      (D₁ ×ˢ (V₀ : Set H)) :=
    hev.comp_continuousOn ((φ.continuousOn_symm.comp continuousOn_fst
      fun (p : B.model i × H) (hp : p ∈ D₁ ×ˢ (V₀ : Set H)) ↦ hp.1.1).prodMk
      (e'.1.continuousOn_symm.comp continuousOn_snd
        fun (p : B.model i × H) (hp : p ∈ D₁ ×ˢ (V₀ : Set H)) ↦ (mem_chartDomOpens.1 hp.2).1))
  have hQ := hG.isOpen_inter_preimage (hD₁.prod V₀.isOpen) c.1.open_source
  have hmem : (φ x₀, e'.1 y₀) ∈ (D₁ ×ˢ (V₀ : Set H)) ∩
      (fun p : B.model i × H ↦ g (φ.symm p.1) (e'.1.symm p.2)) ⁻¹' c.1.source := by
    refine ⟨⟨hx₀D₁, hy₀⟩, ?_⟩
    simp only [mem_preimage, φ.left_inv hi, e'.1.left_inv (_root_.mem_chart_source H y₀)]
    exact _root_.mem_chart_source E (f y₀)
  obtain ⟨U, V, hU, hV, ha, hb, hUV⟩ := isOpen_prod_iff.1 hQ _ _ hmem
  have hUV' : ∀ a ∈ U, ∀ b ∈ V, (a, b) ∈ (D₁ ×ˢ (V₀ : Set H)) ∩
      (fun p : B.model i × H ↦ g (φ.symm p.1) (e'.1.symm p.2)) ⁻¹' c.1.source :=
    fun a ha' b hb' ↦ hUV (mk_mem_prod ha' hb')
  have hUD : U ⊆ D₁ := fun a ha' ↦ (hUV' a ha' _ hb).1.1
  have hVD : V ⊆ V₀ := fun b hb' ↦ (hUV' _ ha b hb').1.2
  have hbox : IsChartBox (fun p : L × M ↦ g p.1 p.2) φ e'.1 c.1 U V :=
    ⟨hU, hV, fun a ha' ↦ (hUD ha').1, fun b hb' ↦ (mem_chartDomOpens.1 (hVD hb')).1,
      fun a ha' b hb' ↦ (hUV' a ha' b hb').2⟩
  let Vo : Opens H := ⟨V, hV⟩
  have hVV₀ : Vo ≤ V₀ := hVD
  let c_f : ContDiffMBMap E ℓ Vo := ContDiffMBMap.restrictCLM hVV₀ (CkMap.localRep f e' c)
  let Lm : SecCk H E ℓ (CkMap.toC f) →L[ℝ] ContDiffMBMap (E × E) ℓ Vo :=
    ContDiffMBMap.prodMkCLM.comp ((ContinuousLinearMap.inr ℝ _ _).comp
      ((ContDiffMBMap.restrictCLM hVV₀).comp (SecCk.coordCLM (e', c))))
  let c₀ : ContDiffMBMap (E × E) ℓ Vo := ContDiffMBMap.prodMkCLM (c_f, 0)
  have hΛ : ∀ τ, ∀ b ∈ V, (c₀ + Lm τ) b =
      (c.1 (f (e'.1.symm b)), localCoord (CkMap.toC f) e' c τ b) := fun τ b hb₀ ↦ by
    have hb' : b ∈ Vo := hb₀
    have h1 : c_f b = c.1 (f (e'.1.symm b)) := by
      simp only [c_f, ContDiffMBMap.restrictCLM_apply _ _ hb',
        CkMap.localRep_apply _ _ _ (hVV₀ hb')]
    have h2 := ContDiffMBMap.restrictCLM_apply hVV₀ (SecCk.coordFun (e', c) τ) hb'
    simp only [c₀, Lm, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      ContDiffMBMap.coe_add, Pi.add_apply]
    change (c_f b, (0 : ContDiffMBMap E ℓ Vo) b) +
      ((0 : ContDiffMBMap E ℓ Vo) b, ContDiffMBMap.restrictCLM hVV₀ (SecCk.coordFun (e', c) τ) b)
        = _
    rw [h1, h2, SecCk.coordFun_apply _ _ (hVV₀ hb')]
    simp
  have hspec : ∀ a ∈ U, ∀ b ∈ V,
      ((c.1 (f (e'.1.symm b)), localCoord (CkMap.toC f) e' c (R a) b) : E × E) ∈
        A.invLocalDom c c ∧
      A.invLocal c c (c.1 (f (e'.1.symm b)), localCoord (CkMap.toC f) e' c (R a) b) =
        c.1 (g (φ.symm a) (e'.1.symm b)) := fun a ha' b hb' ↦ by
    have hsrc : g (φ.symm a) ∈ (A.chartCk f).source := (hUD ha').2.2
    have htgt : R a ∈ (A.chartCk f).target := (A.chartCk f).map_source hsrc
    have hval : A.toFun ⟨f (e'.1.symm b), R a (e'.1.symm b)⟩ = g (φ.symm a) (e'.1.symm b) := by
      rw [← A.chartCk_symm_apply f htgt]
      change (A.chartCk f).symm ((A.chartCk f) (g (φ.symm a))) _ = _
      rw [(A.chartCk f).left_inv hsrc]
    have h := A.invLocal_spec c c (v := ⟨f (e'.1.symm b), R a (e'.1.symm b)⟩)
      (mem_chartDomOpens.1 (hVD hb')).2 (htgt _) (hval ▸ (hUV' a ha' b hb').2)
    rw [hval] at h
    exact h
  have hmaps : ∀ a ∈ U, MapsTo (c₀ + Lm (R a)) Vo (A.invLocalDom c c) := fun a ha' b hb' ↦ by
    rw [hΛ _ b hb']
    exact (hspec a ha' b hb').1
  have hcomp : ContDiffMBOn k (fun a ↦ c₀ + Lm (R a)) U :=
    ContDiffMBOn.comp (g := fun τ ↦ c₀ + Lm τ) hU isOpen_univ
      (contDiffMBOn_const_add_clm c₀ Lm k univ) (hR.mono hUD) (mapsTo_univ _ _)
  have hΨ := ContDiffMBMap.contDiffMBOn_compLeftOn ℓ (U := Vo) (A.isOpen_invLocalDom c c)
    (A.smoothMBOn_invLocal c c) hU hcomp hmaps
  refine ⟨i, e'.1, e'.2, c.1, c.2, U, V, hi, _root_.mem_chart_source H y₀, ha, hb, hbox,
    (contDiffMBOn₂_of_curry hU hΨ).congr hU hV fun p hp ↦ ?_⟩
  rw [ContDiffMBMap.compLeftOn_apply (A.isOpen_invLocalDom c c) (A.smoothMBOn_invLocal c c ℓ)
    (hmaps p.1 hp.1) hp.2, hΛ _ p.2 hp.2, (hspec p.1 hp.1 p.2 hp.2).2]
  rfl

omit [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  [MBManifold H M] [CompactSpace M] [T2Space M]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E N] in
/-- If `g^∧` is continuous, then `g` is continuous as a map into `C(M, N)`. -/
theorem continuous_toC_of_continuous_uncurry {g : L → CkMap H E ℓ M N}
    (hg : Continuous fun p : L × M ↦ g p.1 p.2) : Continuous fun x ↦ CkMap.toC (g x) :=
  (ContinuousMap.curry ⟨fun p : L × M ↦ g p.1 p.2, hg⟩).continuous.congr fun _ ↦ rfl

/-- If `g^∧` is `C^{k,ℓ}`, then `g` is continuous for the compact-open `C^ℓ` topology. -/
theorem continuous_of_contMDiffMB₂ {k : ℕ} {g : L → CkMap H E ℓ M N}
    (hg : ContMDiffMB₂ H E B k ℓ (fun p ↦ g p.1 p.2)) : Continuous g := by
  rcases isEmpty_or_nonempty M with hM | hM
  · exact continuous_of_const fun _ _ ↦ Subsingleton.elim _ _
  have := locallyCompactSpace_of_compactSpace (H := H) M
  have h₀ := continuous_toC_of_continuous_uncurry hg.continuous
  rw [show (CkMap.instTopologicalSpace : TopologicalSpace (CkMap H E ℓ M N)) =
    CkMap.chartTopology H E ℓ M N from CkMap.topology_eq_chartTopology]
  refine CkMap.continuous_of_rep h₀ fun a x₀ hx₀ ↦ ?_
  have hdom : IsOpen (g ⁻¹' a.dom) := a.isOpen_domC.preimage h₀
  obtain ⟨i, hi⟩ := B.exists_mem_source x₀
  set φ := B.chart i
  set U₀ := φ.target ∩ φ.symm ⁻¹' (g ⁻¹' a.dom)
  have hU₀ : IsOpen U₀ := φ.isOpen_inter_preimage_symm hdom
  have hbox : IsChartBox (fun p : L × M ↦ g p.1 p.2) φ a.j.1 a.i.1 U₀ a.V :=
    ⟨hU₀, a.V.isOpen, fun _ h ↦ h.1, fun _ h ↦ a.L_subset (a.V_subset h),
      fun u hu v hv ↦ hu.2 (mem_image_of_mem _ (a.V_subset hv))⟩
  obtain ⟨Ψ, hΨ, hΨv⟩ := (hg.contDiffMBOn₂ i a.j.2 a.i.2 hbox).exists_curry hU₀ a.V.isOpen
  have hφx₀ : φ x₀ ∈ U₀ := ⟨φ.map_source hi, by rw [mem_preimage, φ.left_inv hi]; exact hx₀⟩
  have hc : ContinuousAt (fun x ↦ Ψ (φ x)) x₀ :=
    ContinuousAt.comp (f := φ) (hΨ.continuousOn.continuousAt (hU₀.mem_nhds hφx₀))
      (φ.continuousAt hi)
  refine (hc.congr (Filter.eventually_of_mem ((φ.open_source.inter hdom).mem_nhds ⟨hi, hx₀⟩)
    fun x hx ↦ ?_)).continuousWithinAt
  ext v
  by_cases hv : v ∈ a.V
  · have hφx : φ x ∈ U₀ := ⟨φ.map_source hx.1, by rw [mem_preimage, φ.left_inv hx.1]; exact hx.2⟩
    rw [hΨv _ hφx _ hv, a.rep_apply hx.2 hv]
    change a.i.1 (g (φ.symm (φ x)) _) = _
    rw [φ.left_inv hx.1]
  · rw [ContDiffMBMap.apply_of_notMem _ hv, ContDiffMBMap.apply_of_notMem _ hv]

/-- **Exponential law, second half** ([GN26, Theorem 4.2.2(a)]): if
`g^∧ : L × M → N`, `(x, y) ↦ g(x)(y)`, is `C^{k,ℓ}`, then `g : L → C^ℓ(M, N)` is `C^k`. -/
theorem contMDiffOn_of_contMDiffMB₂ {k : ℕ} {g : L → CkMap H E ℓ M N}
    (hg : ContMDiffMB₂ H E B k ℓ (fun p ↦ g p.1 p.2)) :
    B.ContMDiffOn A.mappingAtlasCk k g univ := by
  have hgc := continuous_of_contMDiffMB₂ hg
  rcases isEmpty_or_nonempty M with hM | hM
  · refine ⟨hgc.continuousOn, fun i j ↦ ?_⟩
    exact (contDiffMBOn_const k (0 : SecCk H E ℓ (CkMap.toC j)) _).congr_of_isOpen
      (isOpen_chartDomain isOpen_univ hgc.continuousOn _ _)
      fun _ _ ↦ Subsingleton.elim (α := SecCk H E ℓ (CkMap.toC j)) _ _
  have := locallyCompactSpace_of_compactSpace (H := H) M
  have h₀ := continuous_toC_of_continuous_uncurry hg.continuous
  refine VaryingAtlas.contMDiffOn_of_local isOpen_univ hgc.continuousOn fun x₀ _ ↦ ?_
  obtain ⟨i, hi⟩ := B.exists_mem_source x₀
  set f := g x₀
  set φ := B.chart i
  set D₁ := chartDomain g univ φ (A.chartCk f)
  have hD₁ : IsOpen D₁ := isOpen_chartDomain isOpen_univ hgc.continuousOn φ (A.chartCk f)
  have hx₀D₁ : φ x₀ ∈ D₁ := by
    refine ⟨φ.map_source hi, mem_univ _, ?_⟩
    rw [mem_preimage, φ.left_inv hi]
    exact A.mem_chartCk_source f
  refine ⟨i, f, D₁, hi, hD₁, hx₀D₁, subset_rfl, ?_⟩
  change ContDiffMBOn k (A.chartCk f ∘ g ∘ φ.symm) D₁
  refine ContDiffMBOn.of_local hD₁ fun x₁ hx₁ ↦ ?_
  set h := g (φ.symm x₁)
  -- a finite cover of `M` by compact sets on which `h` lies in single charts of `N`
  have hK : ∀ y : M, ∃ K ∈ 𝓝 y, K ⊆ h ⁻¹' (chartAt E (h y)).source ∧ IsCompact K := fun y ↦
    local_compact_nhds ((CkMap.toC h).continuous.continuousAt.preimage_mem_nhds
      ((chartAt E (h y)).open_source.mem_nhds (_root_.mem_chart_source E (h y))))
  choose K hKn hKs hKc using hK
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y ↦ interior (K y))
    (fun _ ↦ isOpen_interior) fun y _ ↦ mem_iUnion.2 ⟨y, mem_interior_iff_mem_nhds.2 (hKn y)⟩
  set W := φ.target ∩ φ.symm ⁻¹'
    (⋂ y ∈ t, {x | MapsTo (g x) (K y) (chartAt E (h y)).source})
  have hW : IsOpen W := by
    refine φ.isOpen_inter_preimage_symm (isOpen_biInter_finset fun y _ ↦ ?_)
    exact (ContinuousMap.isOpen_setOfPred_mapsTo (hKc y) (chartAt E (h y)).open_source).preimage h₀
  have hx₁W : x₁ ∈ W := ⟨hx₁.1, mem_iInter₂.2 fun y _ ↦ fun q hq ↦ hKs y hq⟩
  refine ⟨W, hW, hx₁W, SecCk.contDiffMBOn_of_coordFun (hD₁.inter hW) fun b ↦ ?_⟩
  set D := chartDomOpens (CkMap.toC f) b.1 b.2
  let V : t → Opens H := fun y ↦ D ⊓ ⟨b.1.1.target ∩ b.1.1.symm ⁻¹' interior (K y),
    b.1.1.isOpen_inter_preimage_symm isOpen_interior⟩
  have hVU : ∀ y, V y ≤ D := fun _ ↦ inf_le_left
  have hcov : (D : Set H) ⊆ ⋃ y, (V y : Set H) := fun v hv ↦ by
    obtain ⟨y, hy, hyv⟩ := mem_iUnion₂.1 (ht (mem_univ (b.1.1.symm v)))
    exact mem_iUnion.2 ⟨⟨y, hy⟩, hv, (mem_chartDomOpens.1 hv).1, hyv⟩
  refine ContDiffMBMap.contDiffMBOn_of_restrictCLM V hVU hcov (hD₁.inter hW) fun y ↦ ?_
  let iy : atlas E N := ⟨chartAt E (h y), chart_mem_atlas E _⟩
  have hbox : IsChartBox (fun p : L × M ↦ g p.1 p.2) φ b.1.1 iy.1 (D₁ ∩ W) (V y) :=
    ⟨hD₁.inter hW, (V y).isOpen, fun _ hu ↦ hu.1.1, fun _ hv ↦ hv.2.1,
      fun u hu v hv ↦ mem_iInter₂.1 hu.2.2 y y.2 (interior_subset hv.2.2)⟩
  obtain ⟨Ψ, hΨ, hΨv⟩ := (hg.contDiffMBOn₂ i b.1.2 iy.2 hbox).exists_curry (hD₁.inter hW)
    (V y).isOpen
  have hVD : V y ≤ D := hVU y
  let c_f : ContDiffMBMap E ℓ (V y) := ContDiffMBMap.restrictCLM hVD (CkMap.localRep f b.1 b.2)
  let Lm : ContDiffMBMap E ℓ (V y) →L[ℝ] ContDiffMBMap (E × E) ℓ (V y) :=
    ContDiffMBMap.prodMkCLM.comp (ContinuousLinearMap.inl ℝ _ _)
  let c₀ : ContDiffMBMap (E × E) ℓ (V y) := ContDiffMBMap.prodMkCLM (0, c_f)
  have hΛ : ∀ γ : ContDiffMBMap E ℓ (V y), ∀ v ∈ V y,
      (c₀ + Lm γ) v = (γ v, b.2.1 (f (b.1.1.symm v))) := fun γ v hv ↦ by
    have h1 : c_f v = b.2.1 (f (b.1.1.symm v)) := by
      simp only [c_f, ContDiffMBMap.restrictCLM_apply _ _ hv,
        CkMap.localRep_apply _ _ _ (hVD hv)]
    simp only [c₀, Lm, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      ContDiffMBMap.coe_add, Pi.add_apply]
    change ((0 : ContDiffMBMap E ℓ (V y)) v, c_f v) + (γ v, (0 : ContDiffMBMap E ℓ (V y)) v) = _
    rw [h1]
    simp
  have hspec : ∀ u ∈ D₁ ∩ W, ∀ v ∈ V y,
      ((iy.1 (g (φ.symm u) (b.1.1.symm v)), b.2.1 (f (b.1.1.symm v))) : E × E) ∈
        A.chartLocalDom iy b.2 ∧
      A.chartLocal iy b.2 (iy.1 (g (φ.symm u) (b.1.1.symm v)), b.2.1 (f (b.1.1.symm v))) =
        coordAt b.2 (A.toOpenPartialHomeomorph.symm (f (b.1.1.symm v),
          g (φ.symm u) (b.1.1.symm v))) := fun u hu v hv ↦
    A.chartLocal_spec iy b.2 (hbox.mapsTo u hu v hv) (mem_chartDomOpens.1 (hVD hv)).2
      (hu.1.2.2 _)
  have hmaps : ∀ u ∈ D₁ ∩ W, MapsTo (c₀ + Lm (Ψ u)) (V y) (A.chartLocalDom iy b.2) :=
    fun u hu v hv ↦ by
      rw [hΛ _ v hv, hΨv u hu v hv]
      exact (hspec u hu v hv).1
  have hcomp : ContDiffMBOn k (fun u ↦ c₀ + Lm (Ψ u)) (D₁ ∩ W) :=
    ContDiffMBOn.comp (g := fun γ ↦ c₀ + Lm γ) (hD₁.inter hW) isOpen_univ
      (contDiffMBOn_const_add_clm c₀ Lm k univ) hΨ (mapsTo_univ _ _)
  have hΦ := ContDiffMBMap.contDiffMBOn_compLeftOn ℓ (U := V y) (A.isOpen_chartLocalDom iy b.2)
    (A.smoothMBOn_chartLocal iy b.2) (hD₁.inter hW) hcomp hmaps
  refine ContDiffMBOn.congr_of_isOpen (hD₁.inter hW) (fun u hu ↦ ?_) hΦ
  ext v
  by_cases hv : v ∈ V y
  · rw [ContDiffMBMap.compLeftOn_apply (A.isOpen_chartLocalDom iy b.2)
      (A.smoothMBOn_chartLocal iy b.2 ℓ) (hmaps u hu) hv, hΛ _ v hv, hΨv u hu v hv,
      ContDiffMBMap.restrictCLM_apply _ _ hv, SecCk.coordFun_apply _ _ (hVD hv)]
    change _ = coordAt b.2 (⟨f (b.1.1.symm v),
      A.chartCk f (g (φ.symm u)) (b.1.1.symm v)⟩ : TangentBundle E N)
    rw [A.mk_chartCk f _ hu.1.2.2]
    exact (hspec u hu v hv).2
  · rw [ContDiffMBMap.apply_of_notMem _ hv, ContDiffMBMap.apply_of_notMem _ hv]

/-- **The exponential law for `C^ℓ(M, N)`** ([GN26, Theorem 4.2.2(a)], finite `ℓ`): for
every space `L` with an atlas with varying models (in particular every manifold) and every
`k ∈ ℕ`, a map `g : L → C^ℓ(M, N)` is `C^k` if and only if `g^∧ : L × M → N`,
`(x, y) ↦ g(x)(y)`, is `C^{k,ℓ}`. -/
theorem contMDiffOn_mappingAtlasCk_iff {k : ℕ} {g : L → CkMap H E ℓ M N} :
    B.ContMDiffOn A.mappingAtlasCk k g univ ↔ ContMDiffMB₂ H E B k ℓ (fun p ↦ g p.1 p.2) :=
  ⟨A.contMDiffMB₂_of_contMDiffOn, A.contMDiffOn_of_contMDiffMB₂⟩

/-- **Uniqueness of the manifold structure** ([GN26, Theorem 4.2.2(a)]): an atlas with
varying models `A'` on `C^ℓ(M, N)` for which the exponential law holds (for atlases on
`C^ℓ(M, N)` itself, which is all the proof uses) defines the same smooth structure as the atlas
`φ_f`. As in Glöckner–Neeb, the law is applied to the identity in both directions: the
evaluation map is `C^{k,ℓ}` for both atlases. -/
theorem equivalent_mappingAtlasCk_of_expLaw
    (A' : VaryingAtlas.{u, max u v, max u v} (CkMap H E ℓ M N))
    (hA' : ∀ (B' : VaryingAtlas.{u, max u v, max u v} (CkMap H E ℓ M N)) (k : ℕ)
      (g : CkMap H E ℓ M N → CkMap H E ℓ M N),
      B'.ContMDiffOn A' k g univ ↔ ContMDiffMB₂ H E B' k ℓ (fun p ↦ g p.1 p.2)) :
    A'.Equivalent A.mappingAtlasCk :=
  ⟨fun k ↦ A.contMDiffOn_of_contMDiffMB₂ ((hA' A' k id).1 (A'.smoothOn_id univ k)),
    fun k ↦ (hA' A.mappingAtlasCk k id).2
      (A.contMDiffMB₂_of_contMDiffOn (A.mappingAtlasCk.smoothOn_id univ k))⟩

/-! ### The case `ℓ = ∞` -/

/-- The inclusion `C^∞(M, N) → C^ℓ(M, N)` is smooth. -/
theorem smooth_toCk (ℓ' : ℕ) :
    A.mappingAtlasSm.Smooth A.mappingAtlasCk (SmoothMap.toCk (H := H) (E := E) (M := M) (N := N)
      ℓ') := by
  intro k
  refine VaryingAtlas.contMDiffOn_of_local isOpen_univ (SmoothMap.continuous_toCk ℓ').continuousOn
    fun f₀ _ ↦ ?_
  set O := chartDomain (SmoothMap.toCk ℓ') univ (A.chartSm f₀) (A.chartCk (SmoothMap.toCk ℓ' f₀))
  have hO : IsOpen O := isOpen_chartDomain isOpen_univ
    (SmoothMap.continuous_toCk ℓ').continuousOn _ _
  have hf₀ : f₀ ∈ (A.chartSm f₀).source := A.mem_chartSm_source f₀
  refine ⟨f₀, SmoothMap.toCk ℓ' f₀, O, hf₀, hO, ⟨(A.chartSm f₀).map_source hf₀, mem_univ _, ?_⟩,
    subset_rfl, ?_⟩
  · change SmoothMap.toCk ℓ' ((A.chartSm f₀).symm ((A.chartSm f₀) f₀)) ∈
      (A.chartCk (SmoothMap.toCk ℓ' f₀)).source
    rw [(A.chartSm f₀).left_inv hf₀]
    exact A.mem_chartSourceCk _
  · change ContDiffMBOn k (A.chartCk (SmoothMap.toCk ℓ' f₀) ∘ SmoothMap.toCk ℓ' ∘
      (A.chartSm f₀).symm) O
    refine ContDiffMBOn.congr_of_isOpen hO (fun τ hτ ↦ ?_)
      ((SecSm.toCkCLM ℓ').contDiffMBOn k O)
    have hτ' : SecSm.toCkCLM ℓ' τ ∈ (A.chartCk (SmoothMap.toCk ℓ' f₀)).target := hτ.1
    change SecSm.toCkCLM ℓ' τ =
      A.chartCk (SmoothMap.toCk ℓ' f₀) (SmoothMap.toCk ℓ' (A.chartInvFunSm f₀ τ))
    rw [A.toCk_chartInvFunSm f₀ τ ℓ']
    exact ((A.chartCk (SmoothMap.toCk ℓ' f₀)).right_inv hτ').symm

/-- **The exponential law for `C^∞(M, N)`** ([GN26, Theorem 4.2.2(a)], `ℓ = ∞`): a map
`g : L → C^∞(M, N)` is `C^k` if and only if `g^∧` is `C^{k,ℓ}` for every `ℓ ∈ ℕ`. -/
theorem contMDiffOn_mappingAtlasSm_iff {k : ℕ} {g : L → SmoothMap H E M N} :
    B.ContMDiffOn A.mappingAtlasSm k g univ ↔
      ∀ ℓ', ContMDiffMB₂ H E B k ℓ' (fun p ↦ g p.1 p.2) := by
  constructor
  · intro hg ℓ'
    exact A.contMDiffMB₂_of_contMDiffOn (g := fun x ↦ SmoothMap.toCk ℓ' (g x))
      (((A.smooth_toCk ℓ') k).comp isOpen_univ isOpen_univ hg (mapsTo_univ _ _))
  · intro hg
    have hgℓ : ∀ ℓ', B.ContMDiffOn A.mappingAtlasCk k (fun x ↦ SmoothMap.toCk ℓ' (g x)) univ :=
      fun ℓ' ↦ A.contMDiffOn_of_contMDiffMB₂ (g := fun x ↦ SmoothMap.toCk ℓ' (g x)) (hg ℓ')
    have hgc : ContinuousOn g univ :=
      SmoothMap.continuousOn_of_toCk fun ℓ' ↦ (hgℓ ℓ').continuousOn
    refine VaryingAtlas.contMDiffOn_of_local isOpen_univ hgc fun x₀ _ ↦ ?_
    obtain ⟨i, hi⟩ := B.exists_mem_source x₀
    set f := g x₀
    set φ := B.chart i
    set O := chartDomain g univ φ (A.chartSm f)
    have hO : IsOpen O := isOpen_chartDomain isOpen_univ hgc φ (A.chartSm f)
    refine ⟨i, f, O, hi, hO, ⟨φ.map_source hi, mem_univ _, ?_⟩, subset_rfl, ?_⟩
    · rw [mem_preimage, φ.left_inv hi]
      exact A.mem_chartSm_source f
    · change ContDiffMBOn k (A.chartFunSm f ∘ g ∘ φ.symm) O
      refine SecSm.contDiffMBOn_of_toCk hO fun ℓ' ↦ ?_
      have h0 : ContDiffMBOn k (A.chartCk (SmoothMap.toCk ℓ' f) ∘
          (fun x ↦ SmoothMap.toCk ℓ' (g x)) ∘ φ.symm) (chartDomain (fun x ↦ SmoothMap.toCk ℓ' (g x))
          univ φ (A.chartCk (SmoothMap.toCk ℓ' f))) := (hgℓ ℓ').2 i (SmoothMap.toCk ℓ' f)
      have h := h0.mono (show O ⊆ chartDomain (fun x ↦ SmoothMap.toCk ℓ' (g x)) univ φ
          (A.chartCk (SmoothMap.toCk ℓ' f)) from fun z hz ↦ hz)
      refine ContDiffMBOn.congr_of_isOpen hO (fun z _ ↦ ?_) h
      exact (A.toCkCLM_chartFunSm f (g (φ.symm z)) ℓ').symm

/-- **Uniqueness of the manifold structure on `C^∞(M, N)`** ([GN26, Theorem 4.2.2(a)],
`ℓ = ∞`): an atlas with varying models on `C^∞(M, N)` satisfying the exponential law defines the
same smooth structure as the atlas `φ_f`. -/
theorem equivalent_mappingAtlasSm_of_expLaw
    (A' : VaryingAtlas.{u, max u v, max u v} (SmoothMap H E M N))
    (hA' : ∀ (B' : VaryingAtlas.{u, max u v, max u v} (SmoothMap H E M N)) (k : ℕ)
      (g : SmoothMap H E M N → SmoothMap H E M N),
      B'.ContMDiffOn A' k g univ ↔ ∀ ℓ', ContMDiffMB₂ H E B' k ℓ' (fun p ↦ g p.1 p.2)) :
    A'.Equivalent A.mappingAtlasSm :=
  ⟨fun k ↦ A.contMDiffOn_mappingAtlasSm_iff.2 ((hA' A' k id).1 (A'.smoothOn_id univ k)),
    fun k ↦ (hA' A.mappingAtlasSm k id).2
      (A.contMDiffOn_mappingAtlasSm_iff.1 (A.mappingAtlasSm.smoothOn_id univ k))⟩

/-! ### The evaluation map -/

/-- **The evaluation map is `C^{∞,ℓ}`** ([GN26, Theorem 4.2.2(c)]):
`ε : C^ℓ(M, N) × M → N`, `(f, x) ↦ f(x)`, is `C^{k,ℓ}` for every `k`. This is the exponential
law applied to the identity. -/
theorem contMDiffMB₂_eval (k : ℕ) :
    ContMDiffMB₂ H E A.mappingAtlasCk k ℓ (fun p : CkMap H E ℓ M N × M ↦ p.1 p.2) :=
  A.contMDiffMB₂_of_contMDiffOn (g := id) (A.mappingAtlasCk.smoothOn_id univ k)

/-- **Point evaluations are smooth** ([GN26, Theorem 4.2.2(c)]): `ε_x : f ↦ f(x)` is a
smooth map `C^ℓ(M, N) → N`. -/
theorem smooth_eval (x : M) :
    A.mappingAtlasCk.Smooth (VaryingAtlas.ofChartedSpace E N) (fun f : CkMap H E ℓ M N ↦ f x) :=
  fun k ↦ (A.contMDiffMB₂_eval k).contMDiffOn_left x

/-- **The evaluation map is `C^{∞,∞}`** ([GN26, Theorem 4.2.2(c)], `ℓ = ∞`):
`ε : C^∞(M, N) × M → N` is `C^{k,ℓ}` for all `k`, `ℓ`. -/
theorem contMDiffMB₂_evalSm (k ℓ' : ℕ) :
    ContMDiffMB₂ H E A.mappingAtlasSm k ℓ' (fun p : SmoothMap H E M N × M ↦ p.1 p.2) :=
  (A.contMDiffOn_mappingAtlasSm_iff (g := id)).1 (A.mappingAtlasSm.smoothOn_id univ k) ℓ'

/-- **Point evaluations are smooth** on `C^∞(M, N)` ([GN26, Theorem 4.2.2(c)]). -/
theorem smooth_evalSm (x : M) :
    A.mappingAtlasSm.Smooth (VaryingAtlas.ofChartedSpace E N) (fun f : SmoothMap H E M N ↦ f x) :=
  fun k ↦ (A.contMDiffMB₂_evalSm k 0).contMDiffOn_left x

end LocalAddition

end ExpLawCk

end LocallyConvex.Manifolds
