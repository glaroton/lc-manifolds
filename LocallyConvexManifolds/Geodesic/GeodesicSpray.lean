/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.Geodesic.Maximal
public import LocallyConvexManifolds.Flow.Maximal
public import LocallyConvexManifolds.Tangent.Double
public import LocallyConvexManifolds.MappingSpace.TopologyJet
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The geodesic spray; openness of `D(exp)` and smoothness of `exp`

Let `C` be a connection on a manifold `M` modeled on a Banach space `E`. Its **geodesic spray**
is the vector field `S` on the manifold `TM` (modeled on `E × E`) which, in the chart of `TM`
over a chart `i` of `M`, reads `(x, w) ↦ (x, w; w, Γᵢ(x)(w, w))`; with the sign convention of
`LocallyConvexManifolds.Geodesic.Banach`, geodesics are the curves with `c'' = Γ_c(c', c')`. We
follow [Lan99, Ch. IV §3] (second-order vector fields and geodesics, p. 97; local representation,
p. 98) and [Lan99, Ch. IV §4] (the domain `𝔇` of the exponential map is open and `exp` is a
morphism, p. 107), and [Lar26, §6.1.2 (p. 160) and Ejercicio 6.III (p. 174)].

## Main definitions

* `Connection.spray`: the geodesic spray `S`, a smooth vector field on `TM`.

## Main results

* `Connection.rep_spray`, `Connection.spray_isSecondOrder`: `S` has the local representative
  above in **every** chart of `TM` over a chart of `M` (`Connection.ddChart_sprayFun`: the change
  of charts law of the symbols is exactly what makes the local formulas agree under the
  transition maps of `TTM`), and it is a second-order vector field.
* `Connection.IsGeodesicOn.isIntegralCurveOn_velocity`,
  `Connection.isGeodesicOn_proj_of_isIntegralCurveOn`,
  `Connection.velocity_proj_of_isIntegralCurveOn`: the velocity `α̇` of a geodesic `α` is an
  integral curve of `S`, and conversely every integral curve of `S` is the velocity of its
  projection, which is a geodesic.
* `Connection.maxInterval_eq_spray`, `Connection.maxGeodesic_eq_proj_flow`,
  `Connection.flow_spray_eq_velocity`: hence the maximal interval `J_v` of the geodesic with
  initial velocity `v` is the maximal interval of the integral curve of `S` through `v`, and
  `γ_v(t) = π(Fl_S(t, v))`, `Fl_S(t, v) = γ̇_v(t)`.
* `Connection.isOpen_expDomain`, `Connection.smoothMBMOn_exp` ([Lan99, p. 107]): the domain
  `D(exp) = {v | (1, v) ∈ D(Fl_S)}` is open in `TM`, and `exp = π ∘ Fl_S(1, ·)` is smooth on it.
* `Connection.isOpen_expDomainAt`, `Connection.smoothMBMOn_expAt`: the same for `exp_p` on its
  domain in `T_pM = E`.
* `Connection.zero_mem_expDomain`, `Connection.tangentSMul_mem_expDomain`,
  `Connection.starConvex_expDomainAt`: `D(exp)` contains the zero section and is star-shaped in
  the fibers.

## Implementation notes

* Hypotheses. As in `LocallyConvexManifolds.Geodesic.Maximal`, the model `E` is a Banach space
  (for the flow of `S`: Picard–Lindelöf and smooth dependence on initial conditions) and `M` is
  Hausdorff (so that `TM` is Hausdorff, `t2Space_tangentBundle`, and maximal integral curves
  exist). The spray itself, its smoothness and the correspondence between geodesics and integral
  curves of `S` use neither completeness nor the Hausdorff property.
* Smoothness of `S` is checked in the preferred charts of `TM` (`contMDiffMB_of_localRep`); the
  local formula in an arbitrary chart over a chart of `M` is needed to identify integral curves
  of `S` with velocities of geodesics, since integral curves are tested in every chart.
* The library works with smooth (`C^∞`) manifolds, so `exp` is smooth, rather than `C^{p-2}` on a
  `C^p` manifold as in Lang.
* Infinite-dimensional subtleties. For each `p`, `D(exp_p)` is an open star-shaped neighbourhood
  of `0` in `T_pM`; but since `M` need not be locally compact, openness of `D(exp)` in `TM` does
  not give balls of a uniform radius in `T_pM` for `p` in a closed neighbourhood of a point
  (uniformly normal neighbourhoods, [Lar26, §6.2.1], need a separate argument with the
  norms of a chart). Both facts are in `LocallyConvexManifolds.Geodesic.Normal`: `exp_p` is a
  local diffeomorphism at `0` ([Lan99, Theorem IV.4.1]), and uniformly normal neighbourhoods come
  from the inverse function theorem applied to `v ↦ (π v, exp v)`.
* We do not claim the arguments are new; they follow Lang's construction of `exp` through the
  flow of the spray.

## References

* [S. Lang, *Fundamentals of Differential Geometry*][Lan99]
* [G. Larotonda, *Estructuras geométricas para las variedades de Banach*][Lar26]
-/

@[expose] public section

open Set Filter Bundle
open scoped Topology Manifold
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe u

/-! ### Smooth maps attached to the tangent bundle -/

section Maps

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

/-- A tangent vector read in the chart of `TM` over the preferred chart at its base point. -/
theorem tangentChart_prefChart (v : TangentBundle E M) :
    tangentChart (prefChart v.proj) (prefChart v.proj).1 v =
      ((prefChart v.proj).1 v.proj, (v.2 : E)) := by
  rw [tangentChart_apply]
  exact Prod.ext rfl (tangentCoordChange_self _ (mem_chart_source E _) _)

/-- **The projection `TM → M` is smooth.** -/
theorem smoothMBM_tangentBundle_proj :
    SmoothMBM (E × E) E (TotalSpace.proj : TangentBundle E M → M) := by
  intro k
  have hc : Continuous (TotalSpace.proj : TangentBundle E M → M) :=
    (tangentBundleCore E M).continuous_proj
  refine ⟨hc.continuousOn, fun v _ ↦ ?_⟩
  refine ContDiffMBOn.congr_of_isOpen (isOpen_chartDomain isOpen_univ hc.continuousOn _ _)
    (fun y hy ↦ ?_) (((ContinuousLinearMap.fst ℝ E E).contDiffMBOn k univ).mono (subset_univ _))
  have hy' : y ∈ (tangentChart (prefChart v.proj) (prefChart v.proj).1).target := hy.1
  rw [mem_tangentChart_target] at hy'
  change y.1 = chartAt E v.proj ((chartAt E v.proj).symm y.1)
  rw [(chartAt E v.proj).right_inv hy'.1]

/-- **The inclusion of a fiber `T_pM = E → TM` is smooth.** -/
theorem smoothMBM_tangentBundle_mk (p : M) :
    SmoothMBM E (E × E) (fun w : E ↦ (⟨p, w⟩ : TangentBundle E M)) := by
  intro k
  have hc : Continuous (fun w : E ↦ (⟨p, w⟩ : TangentBundle E M)) :=
    (tangentBundleCore E M).continuous_totalSpaceMk p
  refine ⟨hc.continuousOn, fun w _ ↦ ?_⟩
  refine ContDiffMBOn.congr_of_isOpen (isOpen_chartDomain isOpen_univ hc.continuousOn _ _)
    (fun w' _ ↦ ?_) (((contDiffMBOn_const k (chartAt E p p) univ).prodMk isOpen_univ
      ((ContinuousLinearMap.id ℝ E).contDiffMBOn k univ)).mono (subset_univ _))
  change (chartAt E p p, w') = tangentChart (prefChart p) (prefChart p).1 ⟨p, w'⟩
  rw [tangentChart_apply]
  exact Prod.ext rfl (tangentCoordChange_self _ (mem_chart_source E p) w').symm

omit [MBManifold E M] in
/-- **The slice `x ↦ (a, x)`, `M → ℝ × M`, is smooth.** -/
theorem smoothMBM_prodMk_const (a : ℝ) :
    SmoothMBM E (ModelProd ℝ E) (fun x : M ↦ ((a, x) : ℝ × M)) := by
  intro k
  have hc : Continuous (fun x : M ↦ ((a, x) : ℝ × M)) := continuous_const.prodMk continuous_id
  refine ⟨hc.continuousOn, fun x _ ↦ ?_⟩
  refine ContDiffMBOn.congr_of_isOpen (isOpen_chartDomain isOpen_univ hc.continuousOn _ _)
    (fun y hy ↦ ?_) (((contDiffMBOn_const k a univ).prodMk isOpen_univ
      ((ContinuousLinearMap.id ℝ E).contDiffMBOn k univ)).mono (subset_univ _))
  change ((a, y) : ℝ × E) = (a, chartAt E x ((chartAt E x).symm y))
  rw [(chartAt E x).right_inv hy.1]

end Maps

/-! ### The geodesic spray as a smooth vector field on `TM` -/

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

namespace Connection

variable (C : Connection E M)

/-- The **geodesic spray** of `C` as a section `TM → TTM`: at `v ∈ T_pM`, read in the preferred
chart `i` at `p` as `(x, w)`, it is the vector `(w, Γᵢ(x)(w, w))` at `v`. -/
def sprayFun (v : TangentBundle E M) : DoubleTangentBundle E M :=
  ⟨v, ((v.2 : E), C.Γ (prefChart v.proj) ((prefChart v.proj).1 v.proj) (v.2 : E) (v.2 : E))⟩

/-- **The geodesic spray in any chart.** If `v` lies over the domain of a chart `i` of `M` and
reads `(x, w)` in the chart of `TM` over `i`, then the geodesic spray at `v` reads
`((x, w), (w, Γᵢ(x)(w, w)))` in the chart of `TTM` over `i`. This is the change of charts law of
the symbols, applied through the transition maps of `TTM` (`dMB_tangentChart_transition`). -/
theorem ddChart_sprayFun (i : atlas E M) {v : TangentBundle E M} (hv : v.proj ∈ i.1.source) :
    ddChart i (C.sprayFun v) =
      (tangentChart i i.1 v, ((tangentChart i i.1 v).2,
        C.Γ i (tangentChart i i.1 v).1 (tangentChart i i.1 v).2 (tangentChart i i.1 v).2)) := by
  set j := prefChart (E := E) v.proj
  have hj : v.proj ∈ j.1.source := mem_chart_source E _
  have hx : j.1 v.proj ∈ j.1.target ∩ j.1.symm ⁻¹' i.1.source :=
    ⟨j.1.map_source hj, by simpa [j.1.left_inv hj] using hv⟩
  have hjv : tangentChart j j.1 v = (j.1 v.proj, (v.2 : E)) := tangentChart_prefChart v
  have hiv : tangentChart i i.1 v =
      ((i.1 ∘ j.1.symm) (j.1 v.proj), dMB (i.1 ∘ j.1.symm) (j.1 v.proj, (v.2 : E))) := by
    rw [tangentChart_apply]
    simp only [Function.comp_apply, j.1.left_inv hj]
    rfl
  change (tangentChart i i.1 v, dMB ((tangentAtlas i).1 ∘ (tangentAtlas j).1.symm)
    (tangentChart j j.1 v, ((v.2 : E), C.Γ j (j.1 v.proj) (v.2 : E) (v.2 : E)))) = _
  rw [hjv]
  erw [dMB_tangentChart_transition j i hx]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · exact (congrArg Prod.snd hiv).symm
  · rw [hiv]
    exact (add_comm _ _).trans (C.transition j i _ hx _ _).symm

/-- The local representative of the geodesic spray in the chart of `TM` over a chart `i` of `M`:
`(x, w) ↦ (w, Γᵢ(x)(w, w))`. -/
theorem localRep_sprayFun (i : atlas E M) {y : E × E} (hy : y ∈ (tangentAtlas i).1.target) :
    localRep (tangentAtlas i) C.sprayFun y = (y.2, C.Γ i y.1 y.2 y.2) := by
  have hy' := (mem_tangentChart_target _ _ _).mp hy
  have hsrc : ((tangentAtlas i).1.symm y).proj ∈ i.1.source := hy'.2
  have hR : tangentChart i i.1 ((tangentAtlas i).1.symm y) = y := (tangentAtlas i).1.right_inv hy
  change (ddChart i (C.sprayFun ((tangentAtlas i).1.symm y))).2 = _
  rw [C.ddChart_sprayFun i hsrc, hR]

/-- The local representatives of the geodesic spray are smooth. -/
theorem contDiffMBOn_localRep_sprayFun (i : atlas E M) (k : ℕ) :
    ContDiffMBOn k (localRep (tangentAtlas i) C.sprayFun) (tangentAtlas i).1.target := by
  have hU : IsOpen (i.1.target ×ˢ (univ : Set E)) := i.1.open_target.prod isOpen_univ
  have hsub : (tangentAtlas i).1.target ⊆ i.1.target ×ˢ univ := fun y hy ↦
    ⟨((mem_tangentChart_target _ _ _).mp hy).1, mem_univ _⟩
  have hg : ContDiffMBOn k (fun y : E × E ↦ (y.2, C.Γ i y.1 y.2 y.2)) (i.1.target ×ˢ univ) :=
    ((ContinuousLinearMap.snd ℝ E E).contDiffMBOn k _).prodMk hU (C.toSpray.smooth i k)
  exact ContDiffMBOn.congr_of_isOpen (tangentAtlas i).1.open_target
    (fun y hy ↦ (C.localRep_sprayFun i hy).symm) (hg.mono hsub)

/-- **The geodesic spray** of the connection `C`, as a smooth vector field on the manifold `TM`
(modeled on `E × E`). In the chart of `TM` over a chart `i` of `M` it is
`(x, w) ↦ (w, Γᵢ(x)(w, w))` (`Connection.rep_spray`). -/
def spray : SmoothVectorField (E × E) (TangentBundle E M) where
  toFun := C.sprayFun
  isVectorField _ := rfl
  smooth k := contMDiffMB_of_localRep (fun _ ↦ rfl) fun v ↦
    C.contDiffMBOn_localRep_sprayFun (prefChart v.proj) k

theorem spray_apply (v : TangentBundle E M) : C.spray v = C.sprayFun v := rfl

/-- **The geodesic spray in the charts of `TM`**: over a chart `i` of `M`, its local
representative is `(x, w) ↦ (w, Γᵢ(x)(w, w))`. -/
theorem rep_spray (i : atlas E M) {y : E × E} (hy : y ∈ (tangentAtlas i).1.target) :
    C.spray.rep (tangentAtlas i) y = (y.2, C.Γ i y.1 y.2 y.2) :=
  C.localRep_sprayFun i hy

/-- **The geodesic spray is a second-order vector field** [Lan99, Ch. IV §3,
p. 97]: `π_* S(v) = v`, that is, in the chart of `TTM` over any chart of `M` around the base point,
the point `((x, w), (u, w'))` of `S(v)` has `u = w`. -/
theorem spray_isSecondOrder (i : atlas E M) {v : TangentBundle E M} (hv : v.proj ∈ i.1.source) :
    (ddChart i (C.spray v)).2.1 = (ddChart i (C.spray v)).1.2 := by
  rw [spray_apply, C.ddChart_sprayFun i hv]

/-! ### Integral curves of the spray and geodesics -/

/-- A variant of `velocity_eq_of_hasDerivAt` with the base point named. -/
theorem velocity_eq_mk {α : ℝ → M} {t : ℝ} {p : M} {w : E} (hp : α t = p)
    (hw : HasDerivAt (chartAt E p ∘ α) w t) : velocity E α t = ⟨p, w⟩ := by
  subst hp
  exact velocity_eq_of_hasDerivAt hw

/-- The velocity of a curve, read in any chart `i` around `α t`: `(i (α t), (i ∘ α)'(t))`. -/
theorem tangentChart_velocity {α : ℝ → M} {t : ℝ} (hα : ContinuousAt α t)
    (hd : DifferentiableAt ℝ (chartAt E (α t) ∘ α) t) (i : atlas E M) (hi : α t ∈ i.1.source) :
    tangentChart i i.1 (velocity E α t) = (i.1 (α t), deriv (i.1 ∘ α) t) := by
  set j := prefChart (E := E) (α t)
  have hj : α t ∈ j.1.source := mem_chart_source E _
  have hy : j.1 (α t) ∈ j.1.target ∩ j.1.symm ⁻¹' i.1.source :=
    ⟨j.1.map_source hj, by simpa [j.1.left_inv hj] using hi⟩
  obtain ⟨hτ, hτd⟩ := SmoothVectorField.hasFDerivAt_transition j i hy
  have hev : (i.1 ∘ j.1.symm) ∘ (j.1 ∘ α) =ᶠ[𝓝 t] i.1 ∘ α := by
    filter_upwards [hα.preimage_mem_nhds (j.1.open_source.mem_nhds hj)] with s hs
    simp [j.1.left_inv hs]
  have hd' : HasDerivAt (i.1 ∘ α)
      (fderiv ℝ (i.1 ∘ j.1.symm) (j.1 (α t)) (deriv (j.1 ∘ α) t)) t :=
    (hτ.comp_hasDerivAt t hd.hasDerivAt).congr_of_eventuallyEq hev.symm
  rw [velocity_eq_of_hasDerivAt hd.hasDerivAt, tangentChart_apply, hd'.deriv, hτd]
  rfl

/-- **The velocity of a geodesic is an integral curve of the geodesic spray**
([Lan99, Ch. IV §3, p. 97], where this is the definition of a geodesic). -/
theorem IsGeodesicOn.isIntegralCurveOn_velocity {C : Connection E M} {α : ℝ → M} {I : Set ℝ}
    (h : C.IsGeodesicOn α I) : C.spray.IsIntegralCurveOn (velocity E α) I := by
  have hαc : ∀ s ∈ I, ContinuousAt α s := fun s hs ↦ (h.2.1 s hs).continuousAt (h.1.mem_nhds hs)
  have hαd : ∀ s ∈ I, DifferentiableAt ℝ (chartAt E (α s) ∘ α) s := fun s hs ↦ by
    obtain ⟨c₁, hc, -⟩ := h.2.2 s hs
    exact hc.self_of_nhds.differentiableAt
  refine C.spray.isIntegralCurveOn_of_exists_chart fun t ht ↦ ?_
  set j := prefChart (E := E) (α t)
  set ψ := tangentAtlas j
  have hj : α t ∈ j.1.source := mem_chart_source E _
  obtain ⟨c₁, hc, hc₁⟩ := h.2.2 t ht
  have hnear : ∀ᶠ s in 𝓝 t, s ∈ I ∧ α s ∈ j.1.source :=
    Filter.Eventually.and (h.1.mem_nhds ht)
      ((hαc t ht).preimage_mem_nhds (j.1.open_source.mem_nhds hj))
  set g : ℝ → E × E := fun s ↦ (j.1 (α s), deriv (j.1 ∘ α) s)
  have hcd : c₁ =ᶠ[𝓝 t] deriv (j.1 ∘ α) := by
    filter_upwards [hc] with s hs using hs.deriv.symm
  have heq : ψ.1 ∘ velocity E α =ᶠ[𝓝 t] g := by
    filter_upwards [hnear] with s hs
    exact tangentChart_velocity (hαc s hs.1) (hαd s hs.1) j hs.2
  have hct : c₁ t = deriv (j.1 ∘ α) t := hcd.self_of_nhds
  have hg : HasDerivAt g (deriv (j.1 ∘ α) t,
      C.Γ j (j.1 (α t)) (deriv (j.1 ∘ α) t) (deriv (j.1 ∘ α) t)) t := by
    refine HasDerivAt.prodMk ?_ ?_
    · rw [← hct]; exact hc.self_of_nhds
    · rw [← hct]; exact hc₁.congr_of_eventuallyEq hcd.symm
  have hgt : g t ∈ ψ.1.target := (mem_tangentChart_target _ _ _).mpr
    ⟨j.1.map_source hj, by
      change j.1.symm (j.1 (α t)) ∈ j.1.source
      rw [j.1.left_inv hj]
      exact hj⟩
  have hsrc : velocity E α t ∈ ψ.1.source := (mem_tangentChart_source _ _ _).mpr ⟨hj, hj⟩
  -- continuity of the velocity, through the chart `ψ`
  have hcont : ContinuousAt (velocity E α) t := by
    have hev : ψ.1.symm ∘ g =ᶠ[𝓝 t] velocity E α := by
      filter_upwards [hnear, heq] with s hs hs'
      have hsrc' : velocity E α s ∈ ψ.1.source := (mem_tangentChart_source _ _ _).mpr ⟨hs.2, hs.2⟩
      simp only [Function.comp_apply] at hs' ⊢
      rw [← hs', ψ.1.left_inv hsrc']
    exact ((ψ.1.continuousOn_symm.continuousAt (ψ.1.open_target.mem_nhds hgt)).comp
      hg.continuousAt).congr hev
  refine ⟨hcont, ψ, hsrc, ?_⟩
  rw [show ψ.1 (velocity E α t) = g t from heq.self_of_nhds, C.rep_spray j hgt]
  exact hg.congr_of_eventuallyEq heq

/-- An integral curve of the geodesic spray, read in a chart `i` of `M`: the base curve has
velocity the fiber coordinate `w`, and `w' = Γᵢ(x)(w, w)`. -/
theorem hasDerivAt_proj_of_isIntegralCurveOn {C : Connection E M} {c : ℝ → TangentBundle E M}
    {I : Set ℝ} (h : C.spray.IsIntegralCurveOn c I) {t : ℝ} (ht : t ∈ I) (i : atlas E M)
    (hi : (c t).proj ∈ i.1.source) :
    HasDerivAt (i.1 ∘ fun s ↦ (c s).proj) (tangentChart i i.1 (c t)).2 t ∧
      HasDerivAt (fun s ↦ (tangentChart i i.1 (c s)).2)
        (C.Γ i (i.1 (c t).proj) (tangentChart i i.1 (c t)).2 (tangentChart i i.1 (c t)).2) t := by
  have hsrc : c t ∈ (tangentAtlas i).1.source := (mem_tangentChart_source _ _ _).mpr ⟨hi, hi⟩
  have H := (h t ht).2 (tangentAtlas i) hsrc
  rw [C.rep_spray i ((tangentAtlas i).1.map_source hsrc)] at H
  have H1 := (hasFDerivAt_fst (p := (tangentAtlas i).1 (c t))).comp_hasDerivAt t H
  have H2 := (hasFDerivAt_snd (p := (tangentAtlas i).1 (c t))).comp_hasDerivAt t H
  exact ⟨H1, H2⟩

/-- **The projection of an integral curve of the geodesic spray is a geodesic**
[Lan99, Ch. IV §3, p. 97]. -/
theorem isGeodesicOn_proj_of_isIntegralCurveOn {C : Connection E M} {c : ℝ → TangentBundle E M}
    {I : Set ℝ} (hI : IsOpen I) (h : C.spray.IsIntegralCurveOn c I) :
    C.IsGeodesicOn (fun s ↦ (c s).proj) I := by
  have hc : Continuous (TotalSpace.proj : TangentBundle E M → M) :=
    (tangentBundleCore E M).continuous_proj
  refine ⟨hI, fun t ht ↦ (hc.continuousAt.comp (h t ht).1).continuousWithinAt, fun t ht ↦ ?_⟩
  set j := prefChart (E := E) (c t).proj
  have hj : (c t).proj ∈ j.1.source := mem_chart_source E _
  have hnear : ∀ᶠ s in 𝓝 t, s ∈ I ∧ (c s).proj ∈ j.1.source :=
    Filter.Eventually.and (hI.mem_nhds ht) ((hc.continuousAt.comp (h t ht).1).preimage_mem_nhds
      (j.1.open_source.mem_nhds hj))
  refine ⟨fun s ↦ (tangentChart j j.1 (c s)).2, ?_, ?_⟩
  · filter_upwards [hnear] with s hs
    exact (hasDerivAt_proj_of_isIntegralCurveOn h hs.1 j hs.2).1
  · exact (hasDerivAt_proj_of_isIntegralCurveOn h ht j hj).2

/-- **An integral curve of the geodesic spray is the velocity of its projection**
([Lan99, Ch. IV §3, p. 97]: `(πβ)' = β`). -/
theorem velocity_proj_of_isIntegralCurveOn {C : Connection E M} {c : ℝ → TangentBundle E M}
    {I : Set ℝ} (h : C.spray.IsIntegralCurveOn c I) {t : ℝ} (ht : t ∈ I) :
    velocity E (fun s ↦ (c s).proj) t = c t := by
  have hd := (hasDerivAt_proj_of_isIntegralCurveOn h ht (prefChart (c t).proj)
    (mem_chart_source E _)).1
  rw [tangentChart_prefChart] at hd
  exact velocity_eq_mk rfl hd

/-- A geodesic with initial velocity `v` gives an integral curve of the spray through `v`. -/
theorem IsGeodesicThrough.isIntegralCurveThrough_velocity {C : Connection E M}
    {v : TangentBundle E M} {α : ℝ → M} {I : Set ℝ} (h : C.IsGeodesicThrough v α I) :
    C.spray.IsIntegralCurveThrough v (velocity E α) I where
  isOpen := h.isOpen
  ordConnected := h.ordConnected
  zero_mem := h.zero_mem
  map_zero := velocity_eq_mk h.map_zero h.hasDerivAt_zero
  isIntegralCurveOn := h.isGeodesicOn.isIntegralCurveOn_velocity

/-- An integral curve of the spray through `v` projects to a geodesic with initial velocity `v`. -/
theorem isGeodesicThrough_proj {C : Connection E M} {v : TangentBundle E M}
    {c : ℝ → TangentBundle E M} {I : Set ℝ} (h : C.spray.IsIntegralCurveThrough v c I) :
    C.IsGeodesicThrough v (fun s ↦ (c s).proj) I where
  isOpen := h.isOpen
  ordConnected := h.ordConnected
  zero_mem := h.zero_mem
  map_zero := by rw [h.map_zero]
  hasDerivAt_zero := by
    have hd := (hasDerivAt_proj_of_isIntegralCurveOn h.isIntegralCurveOn h.zero_mem
      (prefChart v.proj) (by rw [h.map_zero]; exact mem_chart_source E _)).1
    rw [h.map_zero, tangentChart_prefChart] at hd
    exact hd
  isGeodesicOn := isGeodesicOn_proj_of_isIntegralCurveOn h.isOpen h.isIntegralCurveOn

/-! ### Maximal geodesics are projections of the maximal flow of the spray -/

/-- **The maximal interval of the geodesic with initial velocity `v` is the maximal interval of the
integral curve of the spray through `v`.** -/
theorem maxInterval_eq_spray (v : TangentBundle E M) :
    C.maxInterval v = C.spray.maxInterval v := by
  ext t
  constructor
  · rintro ⟨α, I, h, ht⟩
    exact h.isIntegralCurveThrough_velocity.subset_maxInterval ht
  · rintro ⟨c, I, h, ht⟩
    exact (isGeodesicThrough_proj h).subset_maxInterval ht

variable [CompleteSpace E] [T2Space M]

/-- **The maximal geodesic is the projection of the maximal flow of the spray**:
`γ_v(t) = π(Fl_S(t, v))` for all `t` (both sides take the junk value `p` when `t ∉ J_v`). -/
theorem maxGeodesic_eq_proj_flow (v : TangentBundle E M) (t : ℝ) :
    C.maxGeodesic v t = (C.spray.flow (t, v)).proj := by
  by_cases ht : t ∈ C.maxInterval v
  · rw [C.maxInterval_eq_spray] at ht
    exact (isGeodesicThrough_proj (C.spray.isIntegralCurveThrough_flow v)).maxGeodesic_eq ht
  · rw [maxGeodesic_of_notMem ht]
    rw [C.maxInterval_eq_spray] at ht
    have ht' : ¬ ∃ c I, C.spray.IsIntegralCurveThrough v c I ∧ t ∈ I := ht
    simp only [SmoothVectorField.flow, ht', dite_false]

/-- **The maximal flow of the spray is the velocity of the maximal geodesic**:
`Fl_S(t, v) = γ̇_v(t)` for `t ∈ J_v`. -/
theorem flow_spray_eq_velocity (v : TangentBundle E M) {t : ℝ} (ht : t ∈ C.maxInterval v) :
    C.spray.flow (t, v) = velocity E (C.maxGeodesic v) t :=
  (C.isGeodesicThrough_maxGeodesic v).isIntegralCurveThrough_velocity.flow_eq ht

/-! ### Openness of `D(exp)` and smoothness of `exp` -/

omit [CompleteSpace E] [T2Space M] in
/-- `D(exp) = {v | (1, v) ∈ D}`, where `D` is the domain of the maximal flow of the spray. -/
theorem expDomain_eq_preimage_flowDomain :
    C.expDomain = (fun v ↦ ((1 : ℝ), v)) ⁻¹' C.spray.flowDomain := by
  ext v
  simp [mem_expDomain, SmoothVectorField.mem_flowDomain, C.maxInterval_eq_spray]

/-- `exp v = π(Fl_S(1, v))`. -/
theorem exp_eq_proj_flow (v : TangentBundle E M) : C.exp v = (C.spray.flow (1, v)).proj :=
  C.maxGeodesic_eq_proj_flow v 1

/-- **The domain of the exponential map is open in `TM`** ([Lan99, Ch. IV §4,
p. 107]; [Lar26, §6.1.2, p. 160, and Ejercicio 6.III, p. 174]). -/
theorem isOpen_expDomain : IsOpen C.expDomain := by
  rw [expDomain_eq_preimage_flowDomain]
  exact C.spray.isOpen_flowDomain.preimage (continuous_const.prodMk continuous_id)

/-- **The exponential map is smooth on its domain** [Lan99, Ch. IV §4, p. 107]. -/
theorem smoothMBMOn_exp : SmoothMBMOn (E × E) E C.exp C.expDomain := by
  have hU := C.isOpen_expDomain
  have h1 : SmoothMBMOn (E × E) (ModelProd ℝ (E × E))
      (fun v : TangentBundle E M ↦ ((1 : ℝ), v)) C.expDomain :=
    SmoothMBMOn.mono_of_isOpen isOpen_univ hU
      (fun k ↦ smoothMBM_prodMk_const (M := TangentBundle E M) 1 k) (subset_univ _)
  have h2 := C.spray.smoothMBMOn_flow.comp hU C.spray.isOpen_flowDomain h1
    (by rw [expDomain_eq_preimage_flowDomain]; exact fun v hv ↦ hv)
  have h3 := SmoothMBMOn.comp (g := TotalSpace.proj) (V := univ) hU isOpen_univ
    (fun k ↦ smoothMBM_tangentBundle_proj (M := M) k) h2 (mapsTo_univ _ _)
  refine fun k ↦ (h3 k).congr_of_isOpen hU fun v _ ↦ ?_
  exact (C.exp_eq_proj_flow v).symm

omit [CompleteSpace E] [T2Space M] in
/-- `D(exp_p)` is the preimage of `D(exp)` under the inclusion of the fiber `T_pM = E`. -/
theorem expDomainAt_eq_preimage (p : M) :
    C.expDomainAt p = (fun w : E ↦ (⟨p, w⟩ : TangentBundle E M)) ⁻¹' C.expDomain :=
  rfl

/-- **The domain of `exp_p` is open in `T_pM`.** -/
theorem isOpen_expDomainAt (p : M) : IsOpen (C.expDomainAt p) :=
  C.isOpen_expDomain.preimage ((tangentBundleCore E M).continuous_totalSpaceMk p)

/-- **`exp_p` is smooth on its domain.** -/
theorem smoothMBMOn_expAt (p : M) : SmoothMBMOn E E (C.expAt p) (C.expDomainAt p) := by
  have h1 : SmoothMBMOn E (E × E) (fun w : E ↦ (⟨p, w⟩ : TangentBundle E M)) (C.expDomainAt p) :=
    SmoothMBMOn.mono_of_isOpen isOpen_univ (C.isOpen_expDomainAt p)
      (fun k ↦ smoothMBM_tangentBundle_mk (M := M) p k) (subset_univ _)
  exact C.smoothMBMOn_exp.comp (C.isOpen_expDomainAt p) C.isOpen_expDomain h1 fun _ hw ↦ hw

/-- **`D(exp)` contains the zero section.** -/
theorem zero_mem_expDomain (p : M) : (⟨p, 0⟩ : TangentBundle E M) ∈ C.expDomain := by
  have h := (C.smul_mem_expDomain_iff (⟨p, 0⟩ : TangentBundle E M) 0).2
    (C.zero_mem_maxInterval _)
  simpa [tangentSMul] using h

/-- **`D(exp)` is star-shaped in the fibers**: if `v ∈ D(exp)` and `t ∈ [0, 1]`, then
`t v ∈ D(exp)`. -/
theorem tangentSMul_mem_expDomain {v : TangentBundle E M} (hv : v ∈ C.expDomain) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : tangentSMul t v ∈ C.expDomain :=
  (C.smul_mem_expDomain_iff v t).2
    ((C.ordConnected_maxInterval v).out (C.zero_mem_maxInterval v) hv ht)

/-- **The domain of `exp_p` is star-shaped with respect to `0`.** -/
theorem starConvex_expDomainAt (p : M) : StarConvex ℝ 0 (C.expDomainAt p) := by
  intro w hw a b ha hb hab
  have h := C.tangentSMul_mem_expDomain (v := ⟨p, w⟩) hw ⟨hb, by linarith⟩
  rw [smul_zero, zero_add]
  exact h

end Connection

end LocallyConvex.Manifolds
