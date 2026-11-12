/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.Symplectic.Basic
public import LocallyConvexManifolds.Bundle.Hom

/-!
# The canonical symplectic form on the cotangent bundle

Let `M` be a manifold modeled on a **normed** space `E`. Its cotangent bundle
`T*M = (TM)'` (`cotangentCore`) is a vector bundle with fiber `E' = L(E, ℝ)` (operator norm), and
its total space is a manifold modeled on `E × E'`. The projection `π : T*M → M` and the pairing of
`T*_x M` with `T_x M` define the **canonical (Liouville) `1`-form**
`θ_λ(z) = λ(Tπ z)` for `λ ∈ T*_x M` and `z ∈ T_λ(T*M)`; in a bundle chart over a chart `c` of
`M` (with fiber coordinates in the same chart), `θ_{(x, λ)}(u, ψ) = λ(u)`. The
**canonical symplectic form** is `ω = -dθ`, with the local expression
`ω_{(x, λ)}((u₁, ψ₁), (u₂, ψ₂)) = ψ₂(u₁) - ψ₁(u₂)`.

We follow [Lan99, Ch. V, §7]: the canonical `1`-form and its local representation
(Proposition 7.1, p. 149), the canonical `2`-form `Ω = -dθ` and its local representation
(p. 150 and Proposition 7.2, p. 150). We follow Lang's sign. It is consistent with the
canonical form on `H × H` of `LocallyConvexManifolds.Symplectic.Basic` (`canonicalSymplectic`,
`ω = dθ'` for the form `θ'_{(x, a)}(y, b) = ⟨x, b⟩`): both are `Σ dqᵢ ∧ dpᵢ` in finite
dimensions, with `q` the base and `p` the fiber coordinate.

## Main definitions

* `CotangentBundle`: the total space of `T*M`.
* `cotangentLiouville`: the canonical `1`-form `θ` on `T*M`, a smooth form.
* `cotangentSymplectic`: the canonical symplectic form `ω = -dθ`; it is **weakly nondegenerate
  for every normed model** (by the Hahn–Banach theorem).

## Main results

* `cotangentLiouville_localRep`: the local representative of `θ` in every chart of `T*M`.
* `cotangentSymplectic_isExact`, `cotangentSymplectic_apply`: `ω` is exact, and its local
  expression.
* `cotangentSymplectic_isStrong_iff`: for nonempty `M`, `ω` is **strongly nondegenerate if and
  only if `E` is reflexive** (the canonical map `E → E''` is surjective).

## Implementation notes

**Infinite-dimensional subtleties.**

* Weak nondegeneracy uses that the continuous linear functionals separate the points of `E`
  (Hahn–Banach). This is why we work with a normed model: for a non-normable locally convex
  model the cotangent bundle is not available (see `LocallyConvexManifolds.Bundle.Hom`).
* Strong nondegeneracy needs every functional on `T_λ(T*M) ≅ E × E'` to be of the form
  `ω(z, ·)`; on the `E'`-component this asks every element of `E''` to come from `E`. So
  the cotangent bundle of a manifold modeled on a non-reflexive Banach space, such as `ℓ¹` or
  `c₀`, carries only a weak symplectic form. [Mar72, p. 590] mentions such cotangent bundles
  as natural examples of weak symplectic manifolds.
* No completeness is assumed: a normed space for which `E → E''` is onto is automatically
  complete (`E''` is), but this is never used.
* The converse direction could also be obtained from the general fact that a normed space
  carrying a strong symplectic form is reflexive
  (`SymplecticForm.IsStrong.surjective_inclusionInDoubleDual`), which gives the reflexivity of
  `E × E'`; the direct argument below gives that of `E`.

## References

* [S. Lang, *Fundamentals of Differential Geometry*][Lan99]
* [J. E. Marsden, *Darboux's theorem fails for weak symplectic forms*][Mar72]
-/

@[expose] public section

open Set Function Bundle
open scoped Manifold Topology
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe v

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

/-- The total space of the cotangent bundle, a manifold modeled on `E × E'`. -/
abbrev CotangentBundle (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Type v) [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M] : Type _ :=
  (cotangentCore E M).TotalSpace

namespace CotangentBundle

/-- The covector `λ ∈ T*_x M` represented by a point of `T*M`, in the preferred chart at `x`. -/
def covec (p : CotangentBundle E M) : E →L[ℝ] ℝ := p.2

/-- The coordinate changes of the cotangent bundle: `λ ↦ λ ∘ g_{ji}`, with `g` the coordinate
changes of the tangent bundle. -/
theorem coordChange_apply (i j : atlas E M) {x : M} (hx : x ∈ i.1.source ∩ j.1.source)
    (A : E →L[ℝ] ℝ) (v : E) :
    (cotangentCore E M).coordChange i j x A v = A (tangentCoordChange j i x v) := by
  have h := homCore_coordChange_apply (tangentMBCore E M) (trivialCore (atlasCover E M) ℝ) i j
    hx A v
  exact h

/-- The preferred chart of `T*M` at `λ` is the bundle chart over the preferred chart of `M`. -/
theorem chartAt_eq (p : CotangentBundle E M) :
    chartAt (E × (E →L[ℝ] ℝ)) p =
      (cotangentCore E M).bundleChart ⟨chartAt E p.1, chart_mem_atlas E p.1⟩ (chartAt E p.1) :=
  rfl

/-- Every chart of the atlas of `T*M` is a bundle chart. -/
theorem exists_eq_bundleChart {I : OpenPartialHomeomorph (CotangentBundle E M) (E × (E →L[ℝ] ℝ))}
    (hI : I ∈ atlas (E × (E →L[ℝ] ℝ)) (CotangentBundle E M)) :
    ∃ (j : atlas E M) (c : OpenPartialHomeomorph M E), c ∈ atlas E M ∧
      I = (cotangentCore E M).bundleChart j c := by
  obtain ⟨_, ⟨_, ⟨j, rfl⟩, rfl⟩, _, ⟨c, hc, r, hr, rfl⟩, rfl⟩ := hI
  rw [chartedSpaceSelf_atlas] at hr
  subst hr
  exact ⟨j, c, hc, rfl⟩

end CotangentBundle

open CotangentBundle

/-- The evaluation `(λ, v) ↦ λ v`, as a bilinear map. -/
private def evalBilin (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (E →L[ℝ] ℝ) →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
  ContinuousLinearMap.coeLM ℝ

private theorem continuous_evalBilin :
    Continuous fun p : (E →L[ℝ] ℝ) × E ↦ evalBilin E p.1 p.2 :=
  continuous_fst.clm_apply continuous_snd

/-- The local representative of the Liouville form in the bundle chart over `c`, with fiber
coordinates in the chart `j`: `((y, μ), (u, ψ)) ↦ μ(g_{cj}(y) u)`. -/
def liouvilleLoc (j c : atlas E M) (p : (E × (E →L[ℝ] ℝ)) × (Fin 1 → E × (E →L[ℝ] ℝ))) : ℝ :=
  p.1.2 (tangentCoordChange c j (c.1.symm p.1.1) (p.2 0).1)

/-- The family `θ_λ(u, ψ) = λ(u)`, with `(u, ψ)` given in the preferred chart at `λ`. -/
def liouvilleFun (p : CotangentBundle E M) (w : Fin 1 → E × (E →L[ℝ] ℝ)) : ℝ :=
  covec p (w 0).1

/-- In the bundle chart `ψ_{j, c}` of `T*M`, the Liouville form reads
`θ_{(y, μ)}(u, ψ) = μ(g_{cj}(y) u)`. -/
theorem formLocalRep_liouvilleFun (I : atlas (E × (E →L[ℝ] ℝ)) (CotangentBundle E M))
    (j c : atlas E M) (hI : I.1 = (cotangentCore E M).bundleChart j c.1)
    {q : E × (E →L[ℝ] ℝ)} (hq : q ∈ I.1.target) (w : Fin 1 → E × (E →L[ℝ] ℝ)) :
    formLocalRep 1 I liouvilleFun (q, w) = liouvilleLoc j c (q, w) := by
  obtain ⟨I, hImem⟩ := I
  simp only at hI hq
  subst hI
  set V := cotangentCore E M
  set I := V.bundleChart j c.1
  have hqT := (V.mem_bundleChart_target j c.1 q).1 hq
  set p := I.symm q with hpdef
  set x := c.1.symm q.1 with hxdef
  have hp1 : p.1 = x := rfl
  have hxc : x ∈ c.1.source := c.1.map_target hqT.1
  have hxj : x ∈ j.1.source := hqT.2
  have hIp : I p = q := I.right_inv hq
  set P := chartAt (E × (E →L[ℝ] ℝ)) p
  set k : atlas E M := ⟨chartAt E x, chart_mem_atlas E x⟩
  have hPk : P = V.bundleChart k (chartAt E x) := rfl
  -- the base component of the transition `P ∘ I⁻¹`
  have hfst : ∀ v : E × (E →L[ℝ] ℝ),
      (dMB (P ∘ I.symm) (q, v)).1 = tangentCoordChange c k x v.1 := by
    intro v
    -- `P ∘ I⁻¹` is smooth near `q`
    have hsm := V.smoothMBOn_bundleChart_transition j k c.2 (chart_mem_atlas E x)
    have hqsrc : q ∈ (I.symm ≫ₕ P).source := by
      refine ⟨hq, ?_⟩
      change p ∈ P.source
      rw [hPk, V.mem_bundleChart_source]
      exact ⟨mem_chart_source E x, mem_chart_source E x⟩
    have hd := (hsm 1).hasDirDerivAt hqsrc v
    have hd1 := hd.clm_comp_real (ContinuousLinearMap.fst ℝ E (E →L[ℝ] ℝ))
    -- near `q`, the base component is `k ∘ c⁻¹ ∘ fst`
    have hev : (fun z ↦ (ContinuousLinearMap.fst ℝ E (E →L[ℝ] ℝ)) ((I.symm ≫ₕ P) z)) =ᶠ[nhds q]
        (k.1 ∘ c.1.symm) ∘ (LinearMap.fst ℝ E (E →L[ℝ] ℝ)) := by
      filter_upwards [(I.symm ≫ₕ P).open_source.mem_nhds hqsrc] with z _
      rfl
    have h2 : dMB (fun z ↦ (ContinuousLinearMap.fst ℝ E (E →L[ℝ] ℝ)) ((I.symm ≫ₕ P) z)) (q, v) =
        (ContinuousLinearMap.fst ℝ E (E →L[ℝ] ℝ)) (dMB (I.symm ≫ₕ P) (q, v)) := hd1.dMB_eq
    rw [dMB_congr_of_eventuallyEq hev, dMB_comp_linearMap] at h2
    simp only [LinearMap.fst_apply, ContinuousLinearMap.coe_fst'] at h2
    rw [show (P ∘ I.symm : _ → _) = I.symm ≫ₕ P from rfl, ← h2]
    simp only [tangentCoordChange]
    rw [c.1.right_inv hqT.1]
  -- the fiber component of `p`
  have hp2 : ∀ u : E, covec p u = q.2 (tangentCoordChange k j x u) := by
    intro u
    have hq2 : q.2 = (cotangentCore E M).coordChange k j x (covec p) := by
      rw [← hIp]; rfl
    rw [hq2, CotangentBundle.coordChange_apply _ _ ⟨mem_chart_source E x, hxj⟩,
      tangentCoordChange_comp k j k ⟨⟨mem_chart_source E x, hxj⟩, mem_chart_source E x⟩,
      tangentCoordChange_self k (mem_chart_source E x)]
  simp only [formLocalRep, liouvilleFun, liouvilleLoc]
  change covec p (tangentCoordChange _ (prefChart p) p (w 0)).1 = _
  rw [show tangentCoordChange _ (prefChart p) p (w 0) = dMB (P ∘ I.symm) (q, w 0) by
    simp only [tangentCoordChange]; rw [hIp]]
  rw [hfst, hp2, tangentCoordChange_comp c k j ⟨⟨hxc, mem_chart_source E x⟩, hxj⟩]

/-- The local representative of the Liouville form is smooth. -/
theorem smoothMBOn_liouvilleLoc (j c : atlas E M) :
    SmoothMBOn (liouvilleLoc j c)
      ((((atlasCover E M).transDomain c j) ×ˢ (univ : Set (E →L[ℝ] ℝ))) ×ˢ univ) := by
  intro k
  set D := (((atlasCover E M).transDomain c j) ×ˢ (univ : Set (E →L[ℝ] ℝ))) ×ˢ
    (univ : Set (Fin 1 → E × (E →L[ℝ] ℝ)))
  have hT := (atlasCover E M).isOpen_transDomain c j
  have hD : IsOpen D := (hT.prod isOpen_univ).prod isOpen_univ
  set L : (E × (E →L[ℝ] ℝ)) × (Fin 1 → E × (E →L[ℝ] ℝ)) →L[ℝ] E × E :=
    ((ContinuousLinearMap.fst ℝ E (E →L[ℝ] ℝ)).comp (ContinuousLinearMap.fst ℝ _ _)).prod
      ((ContinuousLinearMap.fst ℝ E (E →L[ℝ] ℝ)).comp
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 ↦ E × (E →L[ℝ] ℝ)) 0).comp
          (ContinuousLinearMap.snd ℝ _ _)))
  set Λ : (E × (E →L[ℝ] ℝ)) × (Fin 1 → E × (E →L[ℝ] ℝ)) →L[ℝ] (E →L[ℝ] ℝ) :=
    (ContinuousLinearMap.snd ℝ E (E →L[ℝ] ℝ)).comp (ContinuousLinearMap.fst ℝ _ _)
  have hg : ContDiffMBOn k (fun p : E × E ↦ tangentCoordChange c j (c.1.symm p.1) p.2)
      ((atlasCover E M).transDomain c j ×ˢ univ) :=
    (tangentMBCore E M).smooth c j k
  have hgL := hg.comp hD (hT.prod isOpen_univ) (L.contDiffMBOn k D)
    fun p hp ↦ ⟨hp.1.1, mem_univ _⟩
  have h := ContDiffMBOn.bilin (evalBilin E) continuous_evalBilin hD (Λ.contDiffMBOn k D) hgL
  exact ContDiffMBOn.congr_of_isOpen hD (fun p _ ↦ rfl) h

/-- **The canonical (Liouville) `1`-form** `θ` on the cotangent bundle: `θ_λ(z) = λ(Tπ z)`; with
tangent vectors `z = (u, ψ)` given in the preferred chart at `λ`, `θ_λ(u, ψ) = λ(u)`
[Lan99, Ch. V, §7, Proposition 7.1, p. 149]. It is a smooth
`1`-form: its local representatives are computed in `formLocalRep_liouvilleFun`. -/
def cotangentLiouville : DifferentialForm (E × (E →L[ℝ] ℝ)) (CotangentBundle E M) ℝ 1 where
  toFun := liouvilleFun
  alternating' p :=
    ⟨AlternatingMap.ofSubsingleton ℝ (E × (E →L[ℝ] ℝ)) ℝ 0
      ((covec p).toLinearMap.comp (LinearMap.fst ℝ E (E →L[ℝ] ℝ))), fun _ ↦ rfl⟩
  smooth' I k := by
    obtain ⟨j, c, hc, hI⟩ := exists_eq_bundleChart I.2
    have hsub : I.1.target ×ˢ (univ : Set (Fin 1 → E × (E →L[ℝ] ℝ))) ⊆
        (((atlasCover E M).transDomain ⟨c, hc⟩ j) ×ˢ (univ : Set (E →L[ℝ] ℝ))) ×ˢ univ := by
      rintro ⟨q, w⟩ ⟨hq, -⟩
      rw [hI] at hq
      have hqT := ((cotangentCore E M).mem_bundleChart_target j c q).1 hq
      exact ⟨⟨⟨hqT.1, c.map_target hqT.1, hqT.2⟩, mem_univ _⟩, mem_univ _⟩
    exact ContDiffMBOn.congr_of_isOpen (I.1.open_target.prod isOpen_univ)
      (fun p hp ↦ (formLocalRep_liouvilleFun I j ⟨c, hc⟩ hI hp.1 p.2).symm)
      ((smoothMBOn_liouvilleLoc j ⟨c, hc⟩ k).mono hsub)

theorem cotangentLiouville_apply (p : CotangentBundle E M) (w : Fin 1 → E × (E →L[ℝ] ℝ)) :
    cotangentLiouville p w = covec p (w 0).1 :=
  rfl

/-- **Local formula for the Liouville form.** In the chart of `T*M` built from a chart `c` of `M`
and the trivialization of `T*M` over a chart `j`, the local representative of `θ` is
`((y, μ), (u, ψ)) ↦ μ(g_{cj}(y) u)`, where `g_{cj}(y) = d(j ∘ c⁻¹)(y)` is the coordinate change
of tangent vectors. For `j = c` it is `((y, μ), (u, ψ)) ↦ μ(u)` [Lan99, Proposition V.7.1]. -/
theorem cotangentLiouville_localRep (I : atlas (E × (E →L[ℝ] ℝ)) (CotangentBundle E M))
    (j c : atlas E M) (hI : I.1 = (cotangentCore E M).bundleChart j c.1)
    {q : E × (E →L[ℝ] ℝ)} (hq : q ∈ I.1.target) (u : E) (ψ : E →L[ℝ] ℝ) :
    cotangentLiouville.localRep I (q, ![(u, ψ)]) = q.2 (tangentCoordChange c j (c.1.symm q.1) u) :=
  formLocalRep_liouvilleFun I j c hI hq _

/-- In the preferred chart at `λ`, the Liouville form is `((y, μ), (u, ψ)) ↦ μ(u)`. -/
theorem cotangentLiouville_localRep_prefChart (p : CotangentBundle E M)
    {q : E × (E →L[ℝ] ℝ)} (hq : q ∈ (chartAt (E × (E →L[ℝ] ℝ)) p).target)
    (w : Fin 1 → E × (E →L[ℝ] ℝ)) :
    cotangentLiouville.localRep (prefChart p) (q, w) = q.2 (w 0).1 := by
  set k : atlas E M := ⟨chartAt E p.1, chart_mem_atlas E p.1⟩
  change formLocalRep 1 (prefChart p) liouvilleFun (q, w) = _
  rw [formLocalRep_liouvilleFun (prefChart p) k k rfl hq w, liouvilleLoc]
  have hqT := ((cotangentCore E M).mem_bundleChart_target k k.1 q).1 hq
  rw [tangentCoordChange_self k (k.1.map_target hqT.1)]

/-- `dθ_λ((u₁, ψ₁), (u₂, ψ₂)) = ψ₁(u₂) - ψ₂(u₁)`, tangent vectors given in the preferred chart
at `λ`. -/
theorem cotangentLiouville_d_apply (p : CotangentBundle E M) (u w : E × (E →L[ℝ] ℝ)) :
    (cotangentLiouville (E := E) (M := M)).d p ![u, w] = u.2 w.1 - w.2 u.1 := by
  have hW := (chartAt (E × (E →L[ℝ] ℝ)) p).open_target
  have hy : chartAt (E × (E →L[ℝ] ℝ)) p p ∈ (chartAt (E × (E →L[ℝ] ℝ)) p).target :=
    (chartAt _ p).map_source (mem_chart_source _ p)
  have key : ∀ (a : E) (b : E × (E →L[ℝ] ℝ)),
      dMB (fun z : E × (E →L[ℝ] ℝ) ↦ z.2 a) (chartAt (E × (E →L[ℝ] ℝ)) p p, b) = b.2 a := by
    intro a b
    have e : (fun z : E × (E →L[ℝ] ℝ) ↦ z.2 a) =
        ⇑((ContinuousLinearMap.apply ℝ ℝ a).comp (ContinuousLinearMap.snd ℝ E (E →L[ℝ] ℝ))) := by
      funext z; rfl
    rw [e, (ContinuousLinearMap.hasDirDerivAt _ _ b).dMB_eq]
    rfl
  rw [DifferentialForm.d_apply, DifferentialForm.dLoc_congr (ω₂ := fun q ↦ q.1.2 (q.2 0).1) hW
    (fun q hq ↦ cotangentLiouville_localRep_prefChart p hq.1 q.2) hy]
  rw [IsLocalForm.dLoc_apply, Fin.sum_univ_two]
  simp only [Fin.removeNth_apply]
  have e0 : (![u, w] : Fin 2 → E × (E →L[ℝ] ℝ)) (Fin.succAbove 0 0) = w := rfl
  have e1 : (![u, w] : Fin 2 → E × (E →L[ℝ] ℝ)) (Fin.succAbove 1 0) = u := rfl
  rw [e0, e1, key, key]
  simp [sub_eq_add_neg]

/-- **The canonical symplectic form** `ω = -dθ` on the cotangent bundle of a manifold modeled on
a normed space [Lan99, Ch. V, §7, p. 150]: with tangent vectors in the preferred chart,
`ω_λ((u₁, ψ₁), (u₂, ψ₂)) = ψ₂(u₁) - ψ₁(u₂)` [Lan99, Proposition V.7.2]. It is exact, hence closed,
and it is **weakly nondegenerate for every normed model**: if `ψ(u₁) = 0` for all `ψ ∈ E'`,
then `u₁ = 0` by the Hahn–Banach theorem. No completeness or reflexivity is assumed. -/
def cotangentSymplectic : SymplecticForm (E × (E →L[ℝ] ℝ)) (CotangentBundle E M) where
  form := -(cotangentLiouville (E := E) (M := M)).d
  isClosed x v := by rw [DifferentialForm.d_neg, DifferentialForm.d_d_eq_zero, neg_zero]; rfl
  nondegenerate p u hu := by
    have hω : ∀ w, (-(cotangentLiouville (E := E) (M := M)).d) p ![u, w] = w.2 u.1 - u.2 w.1 :=
      fun w ↦ by rw [DifferentialForm.neg_apply, cotangentLiouville_d_apply]; ring
    have h1 : u.1 = 0 := SeparatingDual.eq_zero_of_forall_dual_eq_zero fun ψ ↦ by
      have := hu (0, ψ)
      rw [hω] at this
      simpa using this
    have h2 : u.2 = 0 := ContinuousLinearMap.ext fun v ↦ by
      have := hu (v, 0)
      rw [hω] at this
      simpa using this
    exact Prod.ext h1 h2

/-- The canonical symplectic form in the preferred chart:
`ω_λ((u₁, ψ₁), (u₂, ψ₂)) = ψ₂(u₁) - ψ₁(u₂)` [Lan99, Proposition V.7.2]. -/
theorem cotangentSymplectic_apply (p : CotangentBundle E M) (u w : E × (E →L[ℝ] ℝ)) :
    (cotangentSymplectic (E := E) (M := M)).form p ![u, w] = w.2 u.1 - u.2 w.1 := by
  change (-(cotangentLiouville (E := E) (M := M)).d) p ![u, w] = _
  rw [DifferentialForm.neg_apply, cotangentLiouville_d_apply]
  ring

/-- The canonical symplectic form is exact: `ω = d(-θ)`. -/
theorem cotangentSymplectic_isExact : (cotangentSymplectic (E := E) (M := M)).form.IsExact :=
  ⟨-cotangentLiouville, DifferentialForm.d_neg _⟩

/-- **Strong nondegeneracy of the canonical form and reflexivity.** For a nonempty manifold `M`
modeled on a normed space `E`, the canonical symplectic form on `T*M` is strongly nondegenerate if
and only if `E` is reflexive, i.e. the canonical map `E → E''` is surjective. A functional `φ` on
`E × E'` is `ω((u, ψ), ·)` for `ψ = -φ(·, 0)` and `u ∈ E` representing `φ(0, ·) ∈ E''`; and
conversely, taking `φ = Φ ∘ pr₂` for `Φ ∈ E''` and testing on `(0, ψ)` shows that `Φ` comes from
`E`. No completeness is assumed (it would follow from reflexivity). In particular, for a
non-reflexive Banach model such as `ℓ¹` or `c₀`, `T*M` is only a weak symplectic manifold. -/
theorem cotangentSymplectic_isStrong_iff [Nonempty M] :
    (cotangentSymplectic (E := E) (M := M)).IsStrong ↔
      Surjective (NormedSpace.inclusionInDoubleDual ℝ E) := by
  constructor
  · intro h Φ
    obtain ⟨x⟩ := ‹Nonempty M›
    let p : CotangentBundle E M := ⟨x, (0 : E →L[ℝ] ℝ)⟩
    obtain ⟨v, hv⟩ := h p (Φ.comp (ContinuousLinearMap.snd ℝ E (E →L[ℝ] ℝ)))
    refine ⟨v.1, ContinuousLinearMap.ext fun ψ ↦ ?_⟩
    have := hv (0, ψ)
    rw [cotangentSymplectic_apply] at this
    simpa [NormedSpace.dual_def] using this
  · intro h p φ
    obtain ⟨u, hu⟩ := h (φ.comp (ContinuousLinearMap.inr ℝ E (E →L[ℝ] ℝ)))
    refine ⟨(u, -φ.comp (ContinuousLinearMap.inl ℝ E (E →L[ℝ] ℝ))), fun w ↦ ?_⟩
    rw [cotangentSymplectic_apply]
    have hw : w.2 u = φ (0, w.2) := by
      have := congrArg (fun Ψ : StrongDual ℝ (StrongDual ℝ E) ↦ Ψ w.2) hu
      simpa [NormedSpace.dual_def] using this
    rw [hw]
    have hφ : φ w = φ (w.1, 0) + φ (0, w.2) := by
      rw [← map_add]; simp
    rw [hφ]
    simp only [_root_.neg_apply, ContinuousLinearMap.coe_comp, comp_apply,
      ContinuousLinearMap.inl_apply, sub_neg_eq_add]
    ring

end LocallyConvex.Manifolds
