/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Calculus.MBFrechetFinite
public import LocallyConvexManifolds.MappingSpace.Diffeomorphism.Normed
public import LocallyConvexManifolds.MappingSpace.Ck
public import LocallyConvexManifolds.MappingSpace.CompositionMap
public import LocallyConvexManifolds.Manifold.CkSuperposition
public import LocallyConvexManifolds.Manifold.LocalDiffeo
public import LocallyConvexManifolds.Manifold.VaryingAtlas
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# The diffeomorphisms of a compact manifold form an open set

Let `K` be a compact manifold. For `ℓ ≥ 1`, the `C^ℓ`-diffeomorphisms of `K` form an
open subset of `C^ℓ(K, K)`, and the smooth diffeomorphisms an open subset of `C^∞(K, K)`
([GN26, Proposition 13.1.10]).

## Main definitions

* `CkMap.IsDiffeo γ`: `γ ∈ C^ℓ(K, K)` has a two-sided inverse in `C^ℓ(K, K)`;
  `SmoothMap.IsDiffeo γ`: the same in `C^∞(K, K)`.
* `normedRep η e c`: the local representative `L ∘ c ∘ η ∘ e⁻¹ ∘ L⁻¹` in a Euclidean space;
  `HasInvDerivAt H η x`: its derivative at `x` is invertible, in some charts.

## Main results

* `CkMap.isOpen_setOf_isDiffeo`: **[GN26, Proposition 13.1.10]**: for `ℓ ≥ 1`, the
  `C^ℓ`-diffeomorphisms of a compact manifold form an open subset of `C^ℓ(K, K)`;
  `SmoothMap.isOpen_setOf_isDiffeo`: the case `ℓ = ∞`.
* `CkMap.isDiffeo_id`, `CkMap.IsDiffeo.comp`, `CkMap.IsDiffeo.symm` (and the same for
  `SmoothMap`): they form a group under composition (smoothness of the group operations is left to
  the Lie group phase).
* `CkMap.eventually_bijective_hasInvDerivAt`: near a bijection with invertible derivatives, all
  maps in `C^ℓ(K, K)` are bijections with invertible derivatives.
* `exists_isOpen_eventually_injOn`: local uniform injectivity ([GN26, Lemmas 13.1.5, 13.1.6]).
* `hasInvDerivAt_of_leftInverse`, `exists_localInverse`, `isOpenMap_of_hasInvDerivAt`,
  `contMDiffMB_symm_of_hasInvDerivAt`, `smoothMBM_symm_of_hasInvDerivAt`: the inverse function
  theorem on `K`.

## Implementation notes

* **Charts in `ℝⁿ`.** A nonempty compact manifold has a finite-dimensional model `H`
  (`finiteDimensional_of_compactSpace`), which `toEuclidean` identifies with a Euclidean space
  `Eⁿ`. The local representatives `L ∘ c ∘ η ∘ e⁻¹ ∘ L⁻¹` (`normedRep`) are then maps between open
  subsets of `Eⁿ`, where Mathlib's mean value and inverse function theorems apply. On a
  finite-dimensional domain, Michal–Bastiani and Fréchet `C^ℓ` agree (`contDiffMBOn_iff_contDiffOn`
  in [LCA]), so no derivative is lost and the finite case `ℓ ≥ 1` is covered.
* **The proof.** Glöckner–Neeb's proof of Proposition 13.1.10 is incomplete in the current version
  of their manuscript (Chapter 13 is marked unfinished), and it uses sequences, hence the
  metrizability of `C^1(K, K)` through Whitney's embedding theorem. We argue with neighborhoods
  instead. Let `γ₀` be a diffeomorphism.
  1. *Local uniform injectivity* ([GN26, Lemmas 13.1.5, 13.1.6]): around each `x₀ ∈ K` there are an
     open set `U` and a neighborhood `W` of `γ₀` such that every `η ∈ W` is injective on `U` with
     invertible derivatives there (`exists_injOn_of_fderiv_near`, applied to the local
     representatives, with the closeness of derivatives read off the `1`-jets that define the
     topology).
  2. *Global injectivity*: finitely many such `U` cover `K`; their squares cover a neighborhood `D`
     of the diagonal; off `D`, `γ₀(x) ≠ γ₀(y)`, an open condition on the compact set `(K × K) \ D`
     by the tube lemma.
  3. *Surjectivity*: the connected components of `K` are open and finitely many; a map with
     invertible derivatives is open, so it sends a component onto a clopen connected set, which is
     the component of the image of any of its points.
  4. *Smooth inverse*: a bijection with invertible derivatives has a smooth inverse, by the inverse
     function theorem.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
* [glaroton, *lc-analysis: Michal–Bastiani calculus on locally convex spaces*][LCA]
-/

@[expose] public section

open Set Function Filter Metric
open scoped Topology
open LocallyConvex.Analysis

noncomputable section

universe u

namespace LocallyConvex.Manifolds

variable {H : Type u} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [IsTopologicalAddGroup H]
  [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  {K : Type u} [TopologicalSpace K] [ChartedSpace H K] [MBManifold H K]

/-! ### Local representatives in a Euclidean space -/

section NormedRep

variable [FiniteDimensional ℝ H]

variable (H) in
/-- The Euclidean space identified with the finite-dimensional model `H` by `toEuclidean`. -/
abbrev EuclideanModel : Type := EuclideanSpace ℝ (Fin (Module.finrank ℝ H))

variable (H) in
/-- The identification `L : H ≃ Eⁿ` of the model with a Euclidean space (`toEuclidean`). -/
def euclideanEquiv : H ≃L[ℝ] EuclideanModel H := toEuclidean

/-- The local representative `L ∘ c ∘ η ∘ e⁻¹ ∘ L⁻¹` of `η : K → K` in the charts `e`, `c`,
read in the Euclidean space `L(H)`, `L = toEuclidean`. -/
def normedRep (η : K → K) (e c : OpenPartialHomeomorph K H) (z : EuclideanModel H) :
    EuclideanModel H :=
  euclideanEquiv H (c (η (e.symm ((euclideanEquiv H).symm z))))

/-- The domain of `normedRep η e c`: the preimage under `L⁻¹` of the domain of `c ∘ η ∘ e⁻¹`. -/
def normedDom (η : K → K) (e c : OpenPartialHomeomorph K H) : Set (EuclideanModel H) :=
  (euclideanEquiv H).symm ⁻¹' chartDomain η univ e c

omit [LocallyConvexSpace ℝ H] [ChartedSpace H K] [MBManifold H K] in
theorem isOpen_normedDom {η : K → K} (hη : Continuous η) (e c : OpenPartialHomeomorph K H) :
    IsOpen (normedDom η e c) :=
  (isOpen_chartDomain isOpen_univ hη.continuousOn e c).preimage (euclideanEquiv H).symm.continuous

/-- The Euclidean local representatives of a `C^k` map are Fréchet `C^k` (no derivative is lost:
the domain is finite-dimensional, `contDiffMBOn_iff_contDiffOn`). -/
theorem contDiffOn_normedRep {k : ℕ} {η : K → K} (hη : ContMDiffMB H H k η)
    {e c : OpenPartialHomeomorph K H} (he : e ∈ atlas H K) (hc : c ∈ atlas H K) :
    ContDiffOn ℝ k (normedRep η e c) (normedDom η e c) := by
  have hηc : Continuous η := continuousOn_univ.1 hη.1
  have hD := isOpen_chartDomain isOpen_univ hηc.continuousOn e c
  have h1 := hη.contDiffMBOn_chart isOpen_univ he hc
  have h2 := ContDiffMBOn.comp_clm ((euclideanEquiv H).symm : EuclideanModel H →L[ℝ] H) hD h1
  have h3 : ContDiffMBOn k (normedRep η e c) (normedDom η e c) :=
    ContDiffMBOn.comp (isOpen_normedDom hηc e c) isOpen_univ
      ((euclideanEquiv H : H →L[ℝ] EuclideanModel H).contDiffMBOn k univ) h2 (mapsTo_univ _ _)
  exact h3.contDiffOn_of_finiteDimensional (isOpen_normedDom hηc e c)

omit [FiniteDimensional ℝ H] [IsTopologicalAddGroup H] [ContinuousSMul ℝ H]
  [LocallyConvexSpace ℝ H] [T2Space H] [MBManifold H K] in
/-- `C^k` maps are `C^j` for `j ≤ k`. -/
theorem ContMDiffMB.of_le_self {k j : ℕ} {η : K → K} (hη : ContMDiffMB H H k η) (hjk : j ≤ k) :
    ContMDiffMB H H j η :=
  ⟨hη.1, fun x hx ↦ (hη.2 x hx).of_le hjk⟩

/-- The derivative of the Euclidean local representative is the Michal–Bastiani differential of
the local representative, read through `L`. -/
theorem fderiv_normedRep_apply {η : K → K} (hη : ContMDiffMB H H 1 η)
    {e c : OpenPartialHomeomorph K H} (he : e ∈ atlas H K) (hc : c ∈ atlas H K)
    {z : EuclideanModel H} (hz : z ∈ normedDom η e c) (v : EuclideanModel H) :
    fderiv ℝ (normedRep η e c) z v =
      euclideanEquiv H (dMB (c ∘ η ∘ e.symm) ((euclideanEquiv H).symm z,
        (euclideanEquiv H).symm v)) := by
  have hηc : Continuous η := continuousOn_univ.1 hη.1
  have hD := isOpen_chartDomain isOpen_univ hηc.continuousOn e c
  rw [← dMB_eq_fderiv (isOpen_normedDom hηc e c) (contDiffOn_normedRep hη he hc) hz v]
  have hcomp : normedRep η e c =
      (fun w ↦ (euclideanEquiv H : H →L[ℝ] EuclideanModel H) ((c ∘ η ∘ e.symm) w)) ∘
        (((euclideanEquiv H).symm : EuclideanModel H ≃L[ℝ] H) : EuclideanModel H →ₗ[ℝ] H) :=
    rfl
  rw [hcomp, dMB_comp_linearMap]
  have h1 := hη.contDiffMBOn_chart isOpen_univ he hc
  exact iteratedDMB_clm_comp hD h1 (euclideanEquiv H : H →L[ℝ] EuclideanModel H) 1
    (by norm_num) _ hz (fun _ ↦ (euclideanEquiv H).symm v)

variable (H) in
/-- `η` has an invertible derivative at `x`: in some charts `e` at `x` and `c` at `η x`, the
derivative of the Euclidean local representative at `L(e x)` is invertible. -/
def HasInvDerivAt (η : K → K) (x : K) : Prop :=
  ∃ e ∈ atlas H K, ∃ c ∈ atlas H K, x ∈ e.source ∧ η x ∈ c.source ∧
    fderiv ℝ (normedRep η e c) (euclideanEquiv H (e x)) ∈
      range ((↑) : (EuclideanModel H ≃L[ℝ] EuclideanModel H) → _)

omit [LocallyConvexSpace ℝ H] [ChartedSpace H K] [MBManifold H K] in
/-- `L(e x)` lies in the domain of the Euclidean local representative when `η x ∈ c.source`. -/
theorem mem_normedDom {η : K → K} {e c : OpenPartialHomeomorph K H} {x : K} (hx : x ∈ e.source)
    (hηx : η x ∈ c.source) : euclideanEquiv H (e x) ∈ normedDom η e c := by
  refine ⟨?_, mem_univ _, ?_⟩
  · rw [ContinuousLinearEquiv.symm_apply_apply]
    exact e.map_source hx
  · rw [mem_preimage, ContinuousLinearEquiv.symm_apply_apply, e.left_inv hx]
    exact hηx

omit [LocallyConvexSpace ℝ H] [ChartedSpace H K] [MBManifold H K] in
theorem normedRep_euclideanEquiv {η : K → K} {e c : OpenPartialHomeomorph K H} {x : K}
    (hx : x ∈ e.source) :
    normedRep η e c (euclideanEquiv H (e x)) = euclideanEquiv H (c (η x)) := by
  simp only [normedRep, ContinuousLinearEquiv.symm_apply_apply, e.left_inv hx]

/-- **A map with a `C^1` left inverse has invertible derivatives**: if `δ ∘ γ = id` with `γ`,
`δ` of class `C^1`, then `γ` has invertible derivatives at every point (in the preferred charts). -/
theorem hasInvDerivAt_of_leftInverse {γ δ : K → K} (hγ : ContMDiffMB H H 1 γ)
    (hδ : ContMDiffMB H H 1 δ) (hδγ : ∀ x, δ (γ x) = x) (x : K) : HasInvDerivAt H γ x := by
  set e := chartAt H x
  set c := chartAt H (γ x)
  have he : e ∈ atlas H K := chart_mem_atlas H x
  have hc : c ∈ atlas H K := chart_mem_atlas H (γ x)
  have hx : x ∈ e.source := mem_chart_source H x
  have hγx : γ x ∈ c.source := mem_chart_source H (γ x)
  refine ⟨e, he, c, hc, hx, hγx, ?_⟩
  set L := euclideanEquiv H
  set f := normedRep γ e c
  set g := normedRep δ c e
  set z₀ := L (e x)
  have hγc : Continuous γ := continuousOn_univ.1 hγ.1
  have hδc : Continuous δ := continuousOn_univ.1 hδ.1
  have hz₀ : z₀ ∈ normedDom γ e c := mem_normedDom hx hγx
  have hfz₀ : f z₀ = L (c (γ x)) := normedRep_euclideanEquiv hx
  have hfz₀' : f z₀ ∈ normedDom δ c e := by
    rw [hfz₀]
    exact mem_normedDom hγx (by rw [hδγ]; exact hx)
  have hf : ContDiffOn ℝ 1 f (normedDom γ e c) := contDiffOn_normedRep (k := 1) hγ he hc
  have hg : ContDiffOn ℝ 1 g (normedDom δ c e) := contDiffOn_normedRep (k := 1) hδ hc he
  have hfd : HasFDerivAt f (fderiv ℝ f z₀) z₀ :=
    ((hf.contDiffAt ((isOpen_normedDom hγc e c).mem_nhds hz₀)).differentiableAt
      one_ne_zero).hasFDerivAt
  have hgd : HasFDerivAt g (fderiv ℝ g (f z₀)) (f z₀) :=
    ((hg.contDiffAt ((isOpen_normedDom hδc c e).mem_nhds hfz₀')).differentiableAt
      one_ne_zero).hasFDerivAt
  -- `g ∘ f = id` near `z₀`
  have hgf : (g ∘ f) =ᶠ[𝓝 z₀] id := by
    filter_upwards [(isOpen_normedDom hγc e c).mem_nhds hz₀] with z hz
    obtain ⟨hzt, -, hzc⟩ := hz
    simp only [Function.comp_apply, id, g, f, normedRep, ContinuousLinearEquiv.symm_apply_apply,
      c.left_inv hzc, hδγ, e.right_inv hzt, ContinuousLinearEquiv.apply_symm_apply]
  have hcomp : (fderiv ℝ g (f z₀)).comp (fderiv ℝ f z₀) = ContinuousLinearMap.id ℝ _ :=
    (hgd.comp z₀ hfd).unique ((hasFDerivAt_id z₀).congr_of_eventuallyEq hgf)
  have hinj : Injective (fderiv ℝ f z₀) := by
    intro v w hvw
    have := congrArg (fderiv ℝ g (f z₀)) hvw
    simpa [← ContinuousLinearMap.comp_apply, hcomp] using this
  have hsurj : Surjective (fderiv ℝ f z₀) :=
    (LinearMap.injective_iff_surjective (f := ((fderiv ℝ f z₀ :
      EuclideanModel H →L[ℝ] EuclideanModel H) : EuclideanModel H →ₗ[ℝ] EuclideanModel H))).1 hinj
  exact ⟨ContinuousLinearEquiv.ofBijective (fderiv ℝ f z₀) (LinearMap.ker_eq_bot.2 hinj)
    (LinearMap.range_eq_top.2 hsurj), ContinuousLinearEquiv.coe_ofBijective _ _ _⟩

/-! ### Local uniform injectivity -/

/-- **Local uniform injectivity** ([GN26, Lemmas 13.1.5 and 13.1.6]): if `γ₀ ∈ C^ℓ(K, K)`,
`ℓ ≥ 1`, has an invertible derivative at `x₀`, there are an open neighborhood `U` of `x₀` and a
neighborhood of `γ₀` in `C^ℓ(K, K)` all of whose elements are injective on `U` with invertible
derivatives there. Only the `1`-jets of the maps on a compact set in a chart enter, so the
neighborhood is open in the `C^1` topology. -/
theorem exists_isOpen_eventually_injOn [LocallyCompactSpace H] {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (γ₀ : CkMap H H ℓ K K) {x₀ : K} (h₀ : HasInvDerivAt H γ₀ x₀) :
    ∃ U : Set K, IsOpen U ∧ x₀ ∈ U ∧
      ∀ᶠ η : CkMap H H ℓ K K in 𝓝 γ₀, InjOn η U ∧ ∀ x ∈ U, HasInvDerivAt H η x := by
  obtain ⟨e, he, c, hc, hx₀, hcx₀, A, hA⟩ := h₀
  set L := euclideanEquiv H
  set f := normedRep (⇑γ₀) e c
  set z₀ := L (e x₀)
  have hγ₀1 : ContMDiffMB H H 1 γ₀ := γ₀.contMDiffMB.of_le_self hℓ
  have hγ₀c : Continuous γ₀ := continuousOn_univ.1 γ₀.contMDiffMB.1
  have hDf := isOpen_normedDom hγ₀c e c
  have hz₀ : z₀ ∈ normedDom γ₀ e c := mem_normedDom hx₀ hcx₀
  have hf1 : ContDiffOn ℝ 1 f (normedDom γ₀ e c) := contDiffOn_normedRep hγ₀1 he hc
  have hfc : ContinuousAt (fderiv ℝ f) z₀ :=
    (hf1.continuousOn_fderiv_of_isOpen hDf le_rfl).continuousAt (hDf.mem_nhds hz₀)
  obtain ⟨r, hr, ε, hε, hmain⟩ := exists_injOn_of_fderiv_near A hA.symm hfc
  obtain ⟨ρD, hρD, hballD⟩ := Metric.isOpen_iff.1 hDf z₀ hz₀
  set ρ := min r ρD / 2
  have hρ : 0 < ρ := by positivity
  have hρr : ρ ≤ r := (half_le_self (le_min hr.le hρD.le)).trans (min_le_left _ _)
  have hρD' : ρ < ρD := (half_lt_self (lt_min hr hρD)).trans_le (min_le_right _ _)
  have hcl : closedBall z₀ ρ ⊆ normedDom γ₀ e c := (closedBall_subset_ball hρD').trans hballD
  -- the compact set `S = L⁻¹(B̄(z₀, ρ))` in the chart `e`, and the jet index on it
  set S := L.symm '' closedBall z₀ ρ
  have hS : IsCompact S := (isCompact_closedBall z₀ ρ).image L.symm.continuous
  have hSe : S ⊆ e.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hcl hz).1
  let idx : CkMap.CompactIdx H H K K := ⟨⟨e, he⟩, ⟨c, hc⟩, S, hS, hSe⟩
  have : CompactSpace idx.K := isCompact_iff_compactSpace.mp hS
  have hγ₀a : γ₀ ∈ idx.dom := by
    rintro _ ⟨w, ⟨z, hz, rfl⟩, rfl⟩
    exact (hcl hz).2.2
  -- `1`-jets close to that of `γ₀` on `S × L⁻¹(B̄(0, 1))`
  set Bv := L.symm '' closedBall (0 : EuclideanModel H) 1
  set T : Set (idx.K × (Fin 1 → H)) := univ ×ˢ (univ.pi fun _ ↦ Bv)
  have hT : IsCompact T := isCompact_univ.prod
    (isCompact_univ_pi fun _ ↦ (isCompact_closedBall _ _).image L.symm.continuous)
  set J₀ := idx.jet 1 γ₀
  have hJ : ∀ᶠ J in 𝓝 J₀, ∀ p ∈ T, dist (L (J p)) (L (J₀ p)) < ε / 2 := by
    refine hT.eventually_forall_of_forall_eventually fun p _ ↦ ?_
    have hcont : Continuous fun q : C(idx.K × (Fin 1 → H), H) × (idx.K × (Fin 1 → H)) ↦
        dist (L (q.1 q.2)) (L (J₀ q.2)) :=
      (L.continuous.comp continuous_eval).dist
        (L.continuous.comp (J₀.continuous.comp continuous_snd))
    refine (hcont.tendsto (J₀, p)).eventually (Iio_mem_nhds ?_)
    simpa using half_pos hε
  have hψ : ContinuousAt (fun η : CkMap H H ℓ K K ↦ idx.jet 1 η) γ₀ :=
    (idx.continuousOn_jet hℓ).continuousAt (idx.isOpen_dom.mem_nhds hγ₀a)
  have hdomη : ∀ᶠ η in 𝓝 γ₀, η ∈ idx.dom := idx.isOpen_dom.mem_nhds hγ₀a
  have hJη := hψ.eventually hJ
  -- the open set `U`
  set U := e.source ∩ (fun x ↦ L (e x)) ⁻¹' ball z₀ ρ
  have hU : IsOpen U :=
    (L.continuous.comp_continuousOn e.continuousOn).isOpen_inter_preimage e.open_source
      isOpen_ball
  refine ⟨U, hU, ⟨hx₀, mem_ball_self hρ⟩, ?_⟩
  filter_upwards [hdomη, hJη] with η hηa hηJ
  set g := normedRep (⇑η) e c
  have hη1 : ContMDiffMB H H 1 η := η.contMDiffMB.of_le_self hℓ
  have hηc : Continuous η := continuousOn_univ.1 η.contMDiffMB.1
  have hg1 : ContDiffOn ℝ 1 g (normedDom η e c) := contDiffOn_normedRep hη1 he hc
  have hballη : ball z₀ ρ ⊆ normedDom η e c := fun z hz ↦
    idx.subset_chartDomain hηa ⟨z, ball_subset_closedBall hz, rfl⟩
  have hgd : ∀ y ∈ ball z₀ ρ, HasFDerivAt g (fderiv ℝ g y) y := fun y hy ↦
    ((hg1.contDiffAt ((isOpen_normedDom hηc e c).mem_nhds (hballη hy))).differentiableAt
      one_ne_zero).hasFDerivAt
  have hclose : ∀ y ∈ ball z₀ ρ, ‖fderiv ℝ g y - fderiv ℝ f y‖ < ε := by
    intro y hy
    refine lt_of_le_of_lt (ContinuousLinearMap.opNorm_le_of_unit_norm (half_pos hε).le
      fun v hv ↦ ?_) (half_lt_self hε)
    have hyS : L.symm y ∈ S := ⟨y, ball_subset_closedBall hy, rfl⟩
    have hvB : L.symm v ∈ Bv := ⟨v, mem_closedBall_zero_iff.2 hv.le, rfl⟩
    have hp := hηJ (⟨L.symm y, hyS⟩, fun _ ↦ L.symm v) ⟨mem_univ _, fun _ _ ↦ hvB⟩
    rw [idx.jet_apply hηa hℓ, idx.jet_apply hγ₀a hℓ, iteratedDMB_one,
      iteratedDMB_one, dist_eq_norm, ← map_sub] at hp
    have h1 : fderiv ℝ g y v = L (dMB (c ∘ η ∘ e.symm) (L.symm y, L.symm v)) :=
      fderiv_normedRep_apply hη1 he hc (hballη hy) v
    have h2 : fderiv ℝ f y v = L (dMB (c ∘ γ₀ ∘ e.symm) (L.symm y, L.symm v)) :=
      fderiv_normedRep_apply hγ₀1 he hc (hcl (ball_subset_closedBall hy)) v
    rw [sub_apply, h1, h2, ← map_sub]
    exact hp.le
  obtain ⟨hinj, hinv⟩ := hmain ρ hρr g (fun y ↦ fderiv ℝ g y) hgd hclose
  refine ⟨fun a ha b hb hab ↦ ?_, fun x hx ↦ ⟨e, he, c, hc, hx.1, ?_, hinv _ hx.2⟩⟩
  · have h := hinj ha.2 hb.2 (by
      change normedRep η e c (L (e a)) = normedRep η e c (L (e b))
      rw [normedRep_euclideanEquiv ha.1, normedRep_euclideanEquiv hb.1, hab])
    exact e.injOn ha.1 hb.1 (L.injective h)
  · have h := (hballη hx.2).2.2
    rwa [mem_preimage, ContinuousLinearEquiv.symm_apply_apply, e.left_inv hx.1] at h

/-! ### The inverse function theorem on `K` -/

omit [FiniteDimensional ℝ H] [MBManifold H K] in
/-- `C^k` maps on an open set are `C^k` on its open subsets. -/
theorem ContMDiffMBOn.mono_isOpen {N' : Type*} [TopologicalSpace N'] [ChartedSpace H N'] {k : ℕ}
    {f : K → N'} {U V : Set K}
    (hf : ContMDiffMBOn (E := H) (F := H) k f U) (hVU : V ⊆ U) :
    ContMDiffMBOn (E := H) (F := H) k f V :=
  ⟨hf.1.mono hVU, fun x hx ↦ (hf.2 x (hVU hx)).mono fun _ hy ↦
    ⟨hy.1, hVU hy.2.1, hy.2.2⟩⟩

/-- **A local inverse** at a point where the derivative is invertible (the inverse function
theorem): for `η` of class `C^1`, a map `σ`, continuous at `η x` with `σ (η x) = x` and
`η ∘ σ = id` near `η x`, which is `C^{k+1}` on an open neighborhood of `η x` whenever `η` is
`C^{k+1}`. -/
theorem exists_localInverse {η : K → K} (hη1 : ContMDiffMB H H 1 η) {x : K}
    (hx : HasInvDerivAt H η x) :
    ∃ σ : K → K, ContinuousAt σ (η x) ∧ σ (η x) = x ∧ (∀ᶠ y in 𝓝 (η x), η (σ y) = y) ∧
      ∀ k, ContMDiffMB H H (k + 1) η →
        ∃ W, IsOpen W ∧ η x ∈ W ∧ ContMDiffMBOn (E := H) (F := H) (k + 1) σ W := by
  obtain ⟨e, he, c, hc, hxe, hηx, A, hA⟩ := hx
  set L := euclideanEquiv H
  set g := normedRep η e c
  set z := L (e x)
  have hηc : Continuous η := continuousOn_univ.1 hη1.1
  have hD := isOpen_normedDom hηc e c
  have hz : z ∈ normedDom η e c := mem_normedDom hxe hηx
  have hgz1 : ContDiffAt ℝ 1 g z :=
    (contDiffOn_normedRep hη1 he hc).contDiffAt (hD.mem_nhds hz)
  have hgd : HasFDerivAt g (A : _ →L[ℝ] _) z := by
    rw [hA]
    exact (hgz1.differentiableAt one_ne_zero).hasFDerivAt
  have hgs : HasStrictFDerivAt g (A : _ →L[ℝ] _) z := hgz1.hasStrictFDerivAt' hgd one_ne_zero
  set ψ := HasStrictFDerivAt.localInverse g A z hgs
  have hψ1 : ContDiffAt ℝ 1 ψ (g z) := hgz1.to_localInverse hgd one_ne_zero
  have hψz : ψ (g z) = z := hgs.localInverse_apply_image
  have hright : ∀ᶠ w in 𝓝 (g z), g (ψ w) = w := hgs.eventually_right_inverse
  have hgz' : g z = L (c (η x)) := normedRep_euclideanEquiv hxe
  -- `σ = e⁻¹ ∘ L⁻¹ ∘ ψ ∘ L ∘ c`
  set σ : K → K := fun y ↦ e.symm (L.symm (ψ (L (c y))))
  have hLc : ContinuousAt (fun y ↦ L (c y)) (η x) :=
    L.continuous.continuousAt.comp (c.continuousAt hηx)
  have hLcx : L (c (η x)) = g z := hgz'.symm
  have hψc : ContinuousAt (fun y ↦ ψ (L (c y))) (η x) := by
    refine ContinuousAt.comp (f := fun y ↦ L (c y)) ?_ hLc
    rw [hLcx]
    exact hψ1.continuousAt
  have hψx : ψ (L (c (η x))) = z := by rw [hLcx, hψz]
  have hez : L.symm z ∈ e.target := by
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact e.map_source hxe
  have hσx : σ (η x) = x := by
    simp only [σ, hψx, z, ContinuousLinearEquiv.symm_apply_apply, e.left_inv hxe]
  refine ⟨σ, ?_, hσx, ?_, fun k hηk ↦ ?_⟩
  · refine ContinuousAt.comp (f := fun y ↦ L.symm (ψ (L (c y)))) ?_
      (L.symm.continuous.continuousAt.comp hψc)
    simp only [hψx]
    exact e.continuousAt_symm hez
  · have h1 : ∀ᶠ y in 𝓝 (η x), ψ (L (c y)) ∈ normedDom η e c :=
      hψc.preimage_mem_nhds (by rw [hψx]; exact hD.mem_nhds hz)
    have hLc' : Tendsto (fun y ↦ L (c y)) (𝓝 (η x)) (𝓝 (g z)) := by
      rw [← hLcx]
      exact hLc
    have h2 : ∀ᶠ y in 𝓝 (η x), g (ψ (L (c y))) = L (c y) := hLc'.eventually hright
    filter_upwards [h1, h2, c.open_source.mem_nhds hηx] with y hy1 hy2 hy3
    have hmem : η (σ y) ∈ c.source := hy1.2.2
    have hgy : g (ψ (L (c y))) = L (c (η (σ y))) := rfl
    rw [hgy] at hy2
    have := congrArg (fun w ↦ c.symm (L.symm w)) hy2
    simpa only [ContinuousLinearEquiv.symm_apply_apply, c.left_inv hmem, c.left_inv hy3]
      using this
  · -- `ψ` is `C^{k+1}` on an open neighborhood `u` of `g z`
    have hgzk : ContDiffAt ℝ (k + 1 : ℕ) g z :=
      (contDiffOn_normedRep hηk he hc).contDiffAt (hD.mem_nhds hz)
    have hψk : ContDiffAt ℝ (k + 1 : ℕ) ψ (g z) := hgzk.to_localInverse hgd (by simp)
    obtain ⟨u, hu, hψu⟩ := hψk.contDiffOn (m := (k + 1 : ℕ)) le_rfl (by simp)
    set u' := interior u
    have hu' : IsOpen u' := isOpen_interior
    have hgu' : g z ∈ u' := mem_interior_iff_mem_nhds.2 hu
    have hψu' : ContDiffOn ℝ (k + 1 : ℕ) ψ u' := hψu.mono interior_subset
    set V := u' ∩ ψ ⁻¹' (L.symm ⁻¹' e.target)
    have hV : IsOpen V := hψu'.continuousOn.isOpen_inter_preimage hu'
      (e.open_target.preimage L.symm.continuous)
    set V' := L ⁻¹' V
    have hV' : IsOpen V' := hV.preimage L.continuous
    set W := c.source ∩ c ⁻¹' V'
    have hW : IsOpen W := c.continuousOn.isOpen_inter_preimage c.open_source hV'
    have hxW : η x ∈ W := ⟨hηx, by
      change L (c (η x)) ∈ V
      rw [hLcx]
      exact ⟨hgu', by simpa [hψz] using hez⟩⟩
    refine ⟨W, hW, hxW, ?_⟩
    -- the three factors
    have hcs : ContMDiffMBOn (E := H) (F := H) (k + 1) c c.source :=
      (VaryingAtlas.contMDiffOn_ofChartedSpace_iff c.open_source).1
        (VaryingAtlas.smoothOn_chart (VaryingAtlas.ofChartedSpace H K) ⟨c, hc⟩ (k + 1))
    have hes : ContMDiffMBOn (E := H) (F := H) (k + 1) e.symm e.target :=
      (VaryingAtlas.contMDiffOn_ofChartedSpace_iff e.open_target).1
        (VaryingAtlas.smoothOn_chart_symm (VaryingAtlas.ofChartedSpace H K) ⟨e, he⟩ (k + 1))
    have hΦ : ContMDiffMBOn (E := H) (F := H) (k + 1) (fun w ↦ L.symm (ψ (L w))) V' := by
      rw [contMDiffMBOn_iff_contDiffMBOn hV']
      have hψMB : ContDiffMBOn (k + 1) ψ V := (hψu'.mono inter_subset_left).contDiffMBOn hV
      have h1 := ContDiffMBOn.comp_clm (L : H →L[ℝ] EuclideanModel H) hV hψMB
      exact ContDiffMBOn.comp hV' isOpen_univ
        ((L.symm : EuclideanModel H →L[ℝ] H).contDiffMBOn (k + 1) univ) h1 (mapsTo_univ _ _)
    have h1 := ContMDiffMBOn.comp hW hV' hΦ (hcs.mono_isOpen inter_subset_left)
      fun y hy ↦ hy.2
    exact ContMDiffMBOn.comp hW e.open_target hes h1 fun y hy ↦ (hy.2 : L (c y) ∈ V).2

/-- **Maps with invertible derivatives are open.** -/
theorem isOpenMap_of_hasInvDerivAt {η : K → K} (hη : ContMDiffMB H H 1 η)
    (hinv : ∀ x, HasInvDerivAt H η x) : IsOpenMap η := by
  intro O hO
  refine isOpen_iff_mem_nhds.2 ?_
  rintro _ ⟨x, hxO, rfl⟩
  obtain ⟨σ, hσc, hσx, hησ, -⟩ := exists_localInverse hη (hinv x)
  have hσO : ∀ᶠ y in 𝓝 (η x), σ y ∈ O := hσc.preimage_mem_nhds (by rw [hσx]; exact hO.mem_nhds hxO)
  filter_upwards [hσO, hησ] with y hy1 hy2
  exact ⟨σ y, hy1, hy2⟩

/-- **The inverse of a `C^{k+1}` bijection with invertible derivatives is `C^{k+1}`.** -/
theorem contMDiffMB_symm_of_hasInvDerivAt {k : ℕ} {η : K → K} (hη : ContMDiffMB H H (k + 1) η)
    (hinv : ∀ x, HasInvDerivAt H η x) {δ : K → K} (hδη : ∀ x, δ (η x) = x)
    (hηδ : ∀ y, η (δ y) = y) : ContMDiffMB H H (k + 1) δ := by
  refine ContMDiffMBOn.of_local isOpen_univ fun y _ ↦ ?_
  obtain ⟨σ, -, -, hησ, hσk⟩ :=
    exists_localInverse (hη.of_le_self (by omega)) (hinv (δ y))
  rw [hηδ] at hησ
  obtain ⟨W, hW, hyW, hσW⟩ := hσk k hη
  rw [hηδ] at hyW
  obtain ⟨P, hPy, hPo, hP⟩ : ∃ P, y ∈ P ∧ IsOpen P ∧ ∀ y' ∈ P, η (σ y') = y' := by
    obtain ⟨P, hP, hPo, hyP⟩ := eventually_nhds_iff.1 hησ
    exact ⟨P, hyP, hPo, hP⟩
  refine ⟨W ∩ P, hW.inter hPo, ⟨hyW, hPy⟩, ?_⟩
  refine ContMDiffMBOn.congr_of_isOpen (hσW.mono_isOpen inter_subset_left) (hW.inter hPo)
    fun y' hy' ↦ ?_
  have := hδη (σ y')
  rw [hP y' hy'.2] at this
  exact this.symm

/-- **A smooth bijection with invertible derivatives has a smooth inverse.** -/
theorem smoothMBM_symm_of_hasInvDerivAt {η : K → K} (hη : SmoothMBM H H η)
    (hinv : ∀ x, HasInvDerivAt H η x) {δ : K → K} (hδη : ∀ x, δ (η x) = x)
    (hηδ : ∀ y, η (δ y) = y) : SmoothMBM H H δ := by
  have h : ∀ k, ContMDiffMB H H (k + 1) δ := fun k ↦
    contMDiffMB_symm_of_hasInvDerivAt (hη (k + 1)) hinv hδη hηδ
  intro k
  cases k with
  | zero => exact (h 0).of_le_self (by omega)
  | succ k => exact h k

end NormedRep

/-! ### The diffeomorphisms form an open set -/

section Global

variable [CompactSpace K] [T2Space K]

/-- **Bijections with invertible derivatives form an open set** in `C^ℓ(K, K)`, `ℓ ≥ 1`: near
such a map, all maps are bijective with invertible derivatives. The `C^1` topology suffices. -/
theorem CkMap.eventually_bijective_hasInvDerivAt [FiniteDimensional ℝ H] {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (γ₀ : CkMap H H ℓ K K) (hbij : Bijective γ₀) (hinv₀ : ∀ x, HasInvDerivAt H γ₀ x) :
    ∀ᶠ η : CkMap H H ℓ K K in 𝓝 γ₀, Bijective η ∧ ∀ x, HasInvDerivAt H η x := by
  rcases isEmpty_or_nonempty K with hK | hK
  · exact Filter.univ_mem' fun η ↦
      ⟨⟨fun x ↦ isEmptyElim x, fun y ↦ isEmptyElim y⟩, fun x ↦ isEmptyElim x⟩
  have := locallyCompactSpace_of_compactSpace (H := H) K
  have hφ := CkMap.continuous_toC (H := H) (E := H) (ℓ := ℓ) (M := K) (N := K)
  -- local uniform injectivity around every point
  choose U hUo hxU hUev using fun x ↦ exists_isOpen_eventually_injOn hℓ γ₀ (hinv₀ x)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUo
    fun x _ ↦ mem_iUnion.2 ⟨x, hxU x⟩
  have hW₁ : ∀ᶠ η : CkMap H H ℓ K K in 𝓝 γ₀,
      ∀ i ∈ t, InjOn η (U i) ∧ ∀ x ∈ U i, HasInvDerivAt H η x :=
    (Filter.eventually_all_finset t).2 fun i _ ↦ hUev i
  have hcover : ∀ x : K, ∃ i ∈ t, x ∈ U i := fun x ↦ by
    simpa using ht (mem_univ x)
  -- global injectivity: off a neighborhood `D` of the diagonal, by the tube lemma
  set D := ⋃ i ∈ t, U i ×ˢ U i
  have hDo : IsOpen D := isOpen_biUnion fun i _ ↦ (hUo i).prod (hUo i)
  have hC : IsCompact Dᶜ := hDo.isClosed_compl.isCompact
  have hγ₀C : ∀ p ∈ Dᶜ, γ₀ p.1 ≠ γ₀ p.2 := by
    intro p hp hp'
    have h12 : p.1 = p.2 := hbij.1 hp'
    obtain ⟨i, hi, hpi⟩ := hcover p.1
    exact hp (mem_biUnion hi ⟨hpi, h12 ▸ hpi⟩)
  have hW₂ : ∀ᶠ η : CkMap H H ℓ K K in 𝓝 γ₀, ∀ p ∈ Dᶜ, η p.1 ≠ η p.2 := by
    have hC' : ∀ᶠ g in 𝓝 (CkMap.toC γ₀), ∀ p ∈ Dᶜ, g p.1 ≠ g p.2 := by
      refine hC.eventually_forall_of_forall_eventually fun p hp ↦ ?_
      have ho : IsOpen {q : C(K, K) × (K × K) | q.1 q.2.1 ≠ q.1 q.2.2} :=
        isOpen_ne_fun (continuous_eval.comp (continuous_fst.prodMk (continuous_fst.comp
          continuous_snd))) (continuous_eval.comp (continuous_fst.prodMk (continuous_snd.comp
          continuous_snd)))
      exact ho.mem_nhds (hγ₀C p hp)
    exact hφ.continuousAt.eventually hC'
  -- surjectivity: the finitely many connected components
  have : LocallyConnectedSpace H :=
    (euclideanEquiv H).toHomeomorph.isOpenEmbedding.locallyConnectedSpace
  have : LocallyConnectedSpace K := ChartedSpace.locallyConnectedSpace H K
  obtain ⟨t₂, ht₂⟩ := isCompact_univ.elim_finite_subcover (fun x : K ↦ connectedComponent x)
    (fun _ ↦ isOpen_connectedComponent) fun x _ ↦ mem_iUnion.2 ⟨x, mem_connectedComponent⟩
  have hW₃ : ∀ᶠ η : CkMap H H ℓ K K in 𝓝 γ₀, ∀ j ∈ t₂, η j ∈ connectedComponent (γ₀ j) :=
    (Filter.eventually_all_finset t₂).2 fun j _ ↦
      ((continuous_eval_const j).comp hφ).continuousAt.eventually_mem
        (isOpen_connectedComponent.mem_nhds mem_connectedComponent)
  filter_upwards [hW₁, hW₂, hW₃] with η h1 h2 h3
  have hηc : Continuous η := continuousOn_univ.1 η.contMDiffMB.1
  have hγ₀c : Continuous γ₀ := continuousOn_univ.1 γ₀.contMDiffMB.1
  have hinvη : ∀ x, HasInvDerivAt H η x := fun x ↦ by
    obtain ⟨i, hi, hx⟩ := hcover x
    exact (h1 i hi).2 x hx
  have hinj : Injective η := by
    intro a b hab
    by_cases hD : (a, b) ∈ D
    · obtain ⟨i, ha, hi, hb⟩ : ∃ i, a ∈ U i ∧ i ∈ t ∧ b ∈ U i := by
        simpa [D] using hD
      exact (h1 i hi).1 ha hb hab
    · exact absurd hab (h2 (a, b) hD)
  have hopen := isOpenMap_of_hasInvDerivAt (η.contMDiffMB.of_le_self hℓ) hinvη
  have hsurj : Surjective η := by
    intro y
    obtain ⟨x₀, rfl⟩ := hbij.2 y
    obtain ⟨j, hj, hxj⟩ : ∃ j ∈ t₂, x₀ ∈ connectedComponent j := by
      simpa using ht₂ (mem_univ x₀)
    have hy : γ₀ x₀ ∈ connectedComponent (γ₀ j) :=
      (isPreconnected_connectedComponent.image γ₀ hγ₀c.continuousOn).subset_connectedComponent
        (mem_image_of_mem γ₀ mem_connectedComponent) (mem_image_of_mem γ₀ hxj)
    have hclopen : IsClopen (η '' connectedComponent j) :=
      ⟨(isClosed_connectedComponent.isCompact.image hηc).isClosed,
        hopen _ isOpen_connectedComponent⟩
    rw [connectedComponent_eq (h3 j hj)] at hy
    obtain ⟨x, -, hx⟩ := hclopen.connectedComponent_subset
      (mem_image_of_mem η mem_connectedComponent) hy
    exact ⟨x, hx⟩
  exact ⟨⟨hinj, hsurj⟩, hinvη⟩

namespace CkMap

variable {ℓ : ℕ}

/-- `γ ∈ C^ℓ(K, K)` is a **`C^ℓ`-diffeomorphism**: it has a two-sided inverse in `C^ℓ(K, K)`. -/
def IsDiffeo (γ : CkMap H H ℓ K K) : Prop :=
  ∃ δ : CkMap H H ℓ K K, (∀ x, δ (γ x) = x) ∧ ∀ x, γ (δ x) = x

/-- **[GN26, Proposition 13.1.10]**: for `ℓ ≥ 1`, the `C^ℓ`-diffeomorphisms of a compact manifold
`K` form an open subset of `C^ℓ(K, K)`. The proof only uses the `C^1` topology. -/
theorem isOpen_setOf_isDiffeo (hℓ : 1 ≤ ℓ) : IsOpen {γ : CkMap H H ℓ K K | γ.IsDiffeo} := by
  refine isOpen_iff_mem_nhds.2 fun γ₀ ⟨δ₀, hl, hr⟩ ↦ ?_
  rcases isEmpty_or_nonempty K with hK | hK
  · exact Filter.univ_mem' fun η ↦ ⟨η, fun x ↦ isEmptyElim x, fun x ↦ isEmptyElim x⟩
  have := finiteDimensional_of_compactSpace (H := H) K
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  have hinv₀ : ∀ x, HasInvDerivAt H γ₀ x := hasInvDerivAt_of_leftInverse
    (γ₀.contMDiffMB.of_le_self hℓ) (δ₀.contMDiffMB.of_le_self hℓ) hl
  have hbij : Bijective γ₀ := ⟨LeftInverse.injective hl, RightInverse.surjective hr⟩
  filter_upwards [eventually_bijective_hasInvDerivAt hℓ γ₀ hbij hinv₀] with η ⟨hb, hinv⟩
  set e := Equiv.ofBijective η hb
  have hδη : ∀ x, e.symm (η x) = x := e.symm_apply_apply
  have hηδ : ∀ y, η (e.symm y) = y := e.apply_symm_apply
  exact ⟨⟨e.symm, contMDiffMB_symm_of_hasInvDerivAt η.contMDiffMB hinv hδη hηδ⟩, hδη, hηδ⟩

omit [MBManifold H K] [CompactSpace K] [T2Space K] in
/-- The identity is a `C^ℓ`-diffeomorphism. -/
theorem isDiffeo_id : IsDiffeo (H := H) (K := K) (ℓ := ℓ)
    ⟨id, (smoothMBMOn_id isOpen_univ ℓ)⟩ :=
  ⟨⟨id, (smoothMBMOn_id isOpen_univ ℓ)⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩

omit [CompactSpace K] [T2Space K] in
/-- **The `C^ℓ`-diffeomorphisms are closed under composition.** -/
theorem IsDiffeo.comp {γ η : CkMap H H ℓ K K} (hγ : γ.IsDiffeo) (hη : η.IsDiffeo) :
    (CkMap.comp γ η le_rfl).IsDiffeo := by
  obtain ⟨γ', hγ1, hγ2⟩ := hγ
  obtain ⟨η', hη1, hη2⟩ := hη
  refine ⟨CkMap.comp η' γ' le_rfl, fun x ↦ ?_, fun x ↦ ?_⟩
  · simp only [CkMap.comp_apply, hγ1, hη1]
  · simp only [CkMap.comp_apply, hη2, hγ2]

omit [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  [CompactSpace K] [T2Space K] in
/-- **The inverse of a `C^ℓ`-diffeomorphism is a `C^ℓ`-diffeomorphism.** -/
theorem IsDiffeo.symm {γ δ : CkMap H H ℓ K K} (hl : ∀ x, δ (γ x) = x) (hr : ∀ x, γ (δ x) = x) :
    δ.IsDiffeo :=
  ⟨γ, hr, hl⟩

end CkMap

namespace SmoothMap

/-- `γ ∈ C^∞(K, K)` is a **diffeomorphism**: it has a smooth two-sided inverse. -/
def IsDiffeo (γ : SmoothMap H H K K) : Prop :=
  ∃ δ : SmoothMap H H K K, (∀ x, δ (γ x) = x) ∧ ∀ x, γ (δ x) = x

/-- **[GN26, Proposition 13.1.10]**, `ℓ = ∞`: the diffeomorphisms of a compact manifold `K` form
an open subset of `C^∞(K, K)`. The proof only uses the `C^1` topology. -/
theorem isOpen_setOf_isDiffeo : IsOpen {γ : SmoothMap H H K K | γ.IsDiffeo} := by
  refine isOpen_iff_mem_nhds.2 fun γ₀ ⟨δ₀, hl, hr⟩ ↦ ?_
  rcases isEmpty_or_nonempty K with hK | hK
  · exact Filter.univ_mem' fun η ↦ ⟨η, fun x ↦ isEmptyElim x, fun x ↦ isEmptyElim x⟩
  have := finiteDimensional_of_compactSpace (H := H) K
  have hinv₀ : ∀ x, HasInvDerivAt H (SmoothMap.toCk 1 γ₀) x :=
    hasInvDerivAt_of_leftInverse (γ₀.2 1) (δ₀.2 1) hl
  have hbij : Bijective (SmoothMap.toCk 1 γ₀) :=
    ⟨LeftInverse.injective hl, RightInverse.surjective hr⟩
  have h := (SmoothMap.continuous_toCk 1).continuousAt.eventually
    (CkMap.eventually_bijective_hasInvDerivAt le_rfl _ hbij hinv₀)
  filter_upwards [h] with η ⟨hb, hinv⟩
  set e := Equiv.ofBijective η hb
  have hδη : ∀ x, e.symm (η x) = x := e.symm_apply_apply
  have hηδ : ∀ y, η (e.symm y) = y := e.apply_symm_apply
  exact ⟨⟨e.symm, smoothMBM_symm_of_hasInvDerivAt η.2 hinv hδη hηδ⟩, hδη, hηδ⟩

omit [MBManifold H K] [CompactSpace K] [T2Space K] in
/-- The identity is a diffeomorphism. -/
theorem isDiffeo_id : IsDiffeo (H := H) (K := K) ⟨id, fun k ↦ (smoothMBMOn_id isOpen_univ k)⟩ :=
  ⟨⟨id, fun k ↦ (smoothMBMOn_id isOpen_univ k)⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩

omit [CompactSpace K] [T2Space K] in
/-- **The diffeomorphisms are closed under composition.** -/
theorem IsDiffeo.comp {γ η : SmoothMap H H K K} (hγ : γ.IsDiffeo) (hη : η.IsDiffeo) :
    (SmoothMap.comp γ η).IsDiffeo := by
  obtain ⟨γ', hγ1, hγ2⟩ := hγ
  obtain ⟨η', hη1, hη2⟩ := hη
  refine ⟨SmoothMap.comp η' γ', fun x ↦ ?_, fun x ↦ ?_⟩
  · simp only [SmoothMap.comp_apply, hγ1, hη1]
  · simp only [SmoothMap.comp_apply, hη2, hγ2]

omit [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  [CompactSpace K] [T2Space K] in
/-- **The inverse of a diffeomorphism is a diffeomorphism.** -/
theorem IsDiffeo.symm {γ δ : SmoothMap H H K K} (hl : ∀ x, δ (γ x) = x) (hr : ∀ x, γ (δ x) = x) :
    δ.IsDiffeo :=
  ⟨γ, hr, hl⟩

end SmoothMap

end Global

end LocallyConvex.Manifolds
