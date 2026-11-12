/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.Geodesic.GeodesicSpray

/-!
# `exp_p` is a local diffeomorphism; uniformly normal neighbourhoods

References: S. Lang, *Fundamentals of Differential Geometry*, Springer GTM 191 (1999), Ch. IV §4,
Theorem 4.1 (p. 108), and Ch. VIII §5, Proposition 5.1 (p. 215) and Corollary 5.2
(p. 216); G. Larotonda, *Estructuras geométricas para las variedades de Banach* (version of
29 November 2023), §6.2, Observación 6.2.2 (p. 155), §6.2.1 and Teorema 6.2.3 (p. 156).

Let `C` be a connection on a Hausdorff manifold `M` modeled on a Banach space `E`, with exponential
map `exp` defined on the open set `D(exp) ⊆ TM` (`LocallyConvexManifolds.Geodesic.GeodesicSpray`).
We prove:

* `Connection.hasFDerivAt_expAt_zero` (**Lang, Theorem IV.4.1; *Estructuras*, Observación
  6.2.2**): `d(exp_p)(0_p) = id`. Read in the preferred chart `φ` at `p` (which identifies
  `T_pM` with `E`), the derivative at `0` of `w ↦ φ(exp_p w)` is the identity. The proof is
  Lang's: `exp_p(t w) = γ_w(t)` (`Connection.exp_smul`) and `γ_w'(0) = w`.
* `Connection.exists_expAt_openPartialHomeomorph` (**Lang, Theorem IV.4.1**): `exp_p` is a local
  diffeomorphism at `0`: it restricts to a diffeomorphism (smooth, with smooth inverse) from an
  open neighbourhood of `0` in `T_pM`, contained in `D(exp_p)`, onto an open neighbourhood of `p`.
* `Connection.hasFDerivAt_expChart`, `Connection.exists_expChart_openPartialHomeomorph`,
  `Connection.exists_expPair_openPartialHomeomorph` (**Lang, Proposition VIII.5.1;
  *Estructuras*, §6.2.1**): the map `G(v) = (π v, exp v)`, `TM → M × M`, has differential
  `(a, b) ↦ (a, a + b)` at `0_p` in charts, hence is a local diffeomorphism at `0_p`.
* `Connection.exists_expPair_normal` (**Teorema 6.2.3 (1); Lang, Corollary VIII.5.2 (1)**): there
  is an open `W ∋ p` with `W × W ⊆ G(V)`; any two points of `W` are joined by a unique geodesic
  `t ↦ exp(t v)` with `v ∈ V`, and `v` depends smoothly on the endpoints.
* `Connection.exists_uniformlyNormal` (**Teorema 6.2.3 (2); Lang, Corollary VIII.5.2 (2)**):
  uniformly normal neighbourhoods. There are an open `W ∋ p` and `r > 0` such that for every
  `q ∈ W`, `exp_q` is defined on the ball of radius `r` of `T_qM` (read in the chart of `TM`
  over the chart `φ` at `p`) and maps it diffeomorphically onto an open set containing `W`.

Auxiliary results: `exists_openPartialHomeomorph_of_contDiffOn`, the inverse function theorem on
Banach spaces with a smooth inverse (Mathlib's `ContDiffAt.toOpenPartialHomeomorph`, cut down to
the open set where the derivative is invertible so that `OpenPartialHomeomorph.contDiffAt_symm`
applies everywhere); `smoothMBMOn_trans_chart_symm`, which turns a Fréchet diffeomorphism of the
model composed with a chart into a diffeomorphism onto an open set of `M`; and
`OpenPartialHomeomorph.slice`, the slices `u ↦ (Ψ(x, u)).2` of a partial homeomorphism of a product
preserving the first coordinate.

## Implementation notes

* Hypotheses. `E` is a Banach space and `M` is Hausdorff, as for the smoothness of `exp`
  (`Connection.smoothMBMOn_exp`); completeness of `E` is also used by the inverse function
  theorem. No symmetry of the connection is assumed: only `exp` enters. Michal–Bastiani smooth
  maps between open sets of Banach spaces are Fréchet smooth (`smoothMBOn_iff_contDiffOn`), which
  gives the strict differentiability needed by the inverse function theorem.
* `T_qM` is identified with `E` through the preferred chart at `q`, so `exp_q` is a map `E → M`
  (`Connection.expAt`). In the uniform statement the vectors of `T_qM` for `q` near `p` are read
  in the single chart `T` of `TM` over the chart `φ` at `p`: the vector with coordinates
  `(φ q, u)` is `T⁻¹(φ q, u)`, and the ball `B_r(0)` is a ball of `E` in these coordinates. This
  is how Lang states Corollary VIII.5.2 (2) ("the open set in `T_xX` represented by `(x, E(ε))`").
* *Estructuras*, Teorema 6.2.3 (2) also asserts the same for every `r ≤ R` and that the geodesic
  joining two points of `W` stays in `U_R(x)`; we formalize the case `r = R` (smaller radii follow
  by restricting the diffeomorphism) and do not formalize the localization of the geodesic.
  Lang writes the Jacobian of `G` as `[[id, id], [0, id]]`; in the coordinates `(x, u)` used here
  it is `[[id, 0], [id, id]]`, as in *Estructuras*.
* Infinite-dimensional subtleties. `M` need not be locally compact, so the uniform radius cannot
  come from a compactness argument over a closed neighbourhood of `p`. It comes from the inverse
  function theorem applied to `G` at the single point `0_p`: the source of the local inverse is a
  neighbourhood of `(φ p, 0)` in `E × E`, hence contains a product of balls `B_r(φ p) × B_r(0)`
  (max norm), and slicing at `x = φ q` gives the diffeomorphism at `q`. The radius refers to the
  norm of the chart `φ`; in another chart the balls are only comparable through the norms of the
  coordinate changes, which are bounded near `p` but not uniformly on larger sets.
* The construction of the slices and the derivation of the uniform statement from the local
  inverse of `G` are routine; we do not claim this argument is new.
-/

@[expose] public section

open Set Filter Bundle Metric
open scoped Topology Manifold ContDiff
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe u

/-! ### The inverse function theorem with a smooth inverse -/

section InverseFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The inverse function theorem on Banach spaces, with a smooth inverse.** If `f` is smooth
(Fréchet `C^∞`) on an open set `U` of a Banach space and its derivative at `a ∈ U` is a
topological isomorphism, then `f` restricts to a diffeomorphism between an open neighbourhood of
`a` contained in `U` and an open set. -/
theorem exists_openPartialHomeomorph_of_contDiffOn {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) {a : E} (ha : a ∈ U) {f' : E ≃L[ℝ] F}
    (hf' : HasFDerivAt f (f' : E →L[ℝ] F) a) :
    ∃ ψ : OpenPartialHomeomorph E F, a ∈ ψ.source ∧ ψ.source ⊆ U ∧ ⇑ψ = f ∧
      ContDiffOn ℝ ∞ ψ ψ.source ∧ ContDiffOn ℝ ∞ ψ.symm ψ.target := by
  have hfa : ContDiffAt ℝ ∞ f a := hf.contDiffAt (hU.mem_nhds ha)
  set ψ₀ := hfa.toOpenPartialHomeomorph f hf' (by simp)
  set S : Set E := U ∩ (fun x ↦ fderiv ℝ f x) ⁻¹' {L | L.IsInvertible} with hSdef
  have hS : IsOpen S := by
    refine (hf.continuousOn_fderiv_of_isOpen hU (by simp)).isOpen_inter_preimage hU ?_
    convert ContinuousLinearEquiv.isOpen (𝕜 := ℝ) (E := E) (F := F) using 1
    ext L
    exact ⟨fun ⟨e, he⟩ ↦ ⟨e, he⟩, fun ⟨e, he⟩ ↦ ⟨e, he⟩⟩
  have haS : a ∈ S := ⟨ha, by
    change (fderiv ℝ f a).IsInvertible
    rw [hf'.fderiv]; exact ContinuousLinearMap.isInvertible_equiv⟩
  have hsrc : (ψ₀.restrOpen S hS).source ⊆ S := fun x hx ↦ by
    rw [OpenPartialHomeomorph.restrOpen_source] at hx; exact hx.2
  refine ⟨ψ₀.restrOpen S hS, ?_, fun x hx ↦ (hsrc hx).1, rfl, hf.mono fun x hx ↦ (hsrc hx).1,
    ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hfa.mem_toOpenPartialHomeomorph_source hf' (by simp), haS⟩
  · intro z hz
    have hx := (ψ₀.restrOpen S hS).map_target hz
    obtain ⟨hxU, e, he⟩ := hsrc hx
    have hd : DifferentiableAt ℝ f ((ψ₀.restrOpen S hS).symm z) :=
      (hf.differentiableOn (by simp) _ hxU).differentiableAt (hU.mem_nhds hxU)
    refine ((ψ₀.restrOpen S hS).contDiffAt_symm hz (f₀' := e) ?_ ?_).contDiffWithinAt
    · rw [he]
      exact hd.hasFDerivAt
    · exact hf.contDiffAt (hU.mem_nhds hxU)

end InverseFunction

/-! ### Charts composed with Fréchet diffeomorphisms of the model -/

section ChartComp

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

/-- If `ψ` is a Fréchet diffeomorphism between open sets of the model `E` and `φ` is a chart of
`M`, then `φ⁻¹ ∘ ψ` is a smooth map with smooth inverse `ψ⁻¹ ∘ φ` (on their natural domains). -/
theorem smoothMBMOn_trans_chart_symm {ψ : OpenPartialHomeomorph E E}
    {φ : OpenPartialHomeomorph M E} (hφ : φ ∈ atlas E M) (hψ : ContDiffOn ℝ ∞ ψ ψ.source)
    (hψ' : ContDiffOn ℝ ∞ ψ.symm ψ.target) :
    SmoothMBMOn E E (ψ.trans φ.symm) (ψ.trans φ.symm).source ∧
      SmoothMBMOn E E (ψ.trans φ.symm).symm (ψ.trans φ.symm).target := by
  have hψs : SmoothMBMOn E E ψ ψ.source := fun k ↦
    (contMDiffMBOn_iff_contDiffMBOn ψ.open_source).2
      ((smoothMBOn_iff_contDiffOn ψ.open_source).2 hψ k)
  have hψs' : SmoothMBMOn E E ψ.symm ψ.target := fun k ↦
    (contMDiffMBOn_iff_contDiffMBOn ψ.open_target).2
      ((smoothMBOn_iff_contDiffOn ψ.open_target).2 hψ' k)
  constructor
  · have hsub : (ψ.trans φ.symm).source ⊆ ψ.source := by
      rw [OpenPartialHomeomorph.trans_source]; exact inter_subset_left
    have h := SmoothMBMOn.comp (ψ.trans φ.symm).open_source φ.open_target
      (smoothMBMOn_symm_of_mem_atlas hφ)
      (SmoothMBMOn.mono_of_isOpen ψ.open_source (ψ.trans φ.symm).open_source hψs hsub)
      (fun x hx ↦ by rw [OpenPartialHomeomorph.trans_source] at hx; exact hx.2)
    rwa [OpenPartialHomeomorph.coe_trans]
  · have hsub : (ψ.trans φ.symm).target ⊆ φ.source := by
      rw [OpenPartialHomeomorph.trans_target]; exact inter_subset_left
    have h := SmoothMBMOn.comp (ψ.trans φ.symm).open_target ψ.open_target hψs'
      (SmoothMBMOn.mono_of_isOpen φ.open_source (ψ.trans φ.symm).open_target
        (smoothMBMOn_of_mem_atlas hφ) hsub)
      (fun x hx ↦ by rw [OpenPartialHomeomorph.trans_target] at hx; exact hx.2)
    rwa [OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.symm_symm]

end ChartComp

/-! ### The exponential map in charts -/

/-! ### Slices of partial homeomorphisms preserving the first coordinate -/

section Slice

variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]

/-- The **slice at `x`** of a partial homeomorphism `Ψ` of `A × B` that preserves the first
coordinate: the partial homeomorphism `u ↦ (Ψ(x, u)).2` of `B`, with source
`{u | (x, u) ∈ Ψ.source}`, target `{z | (x, z) ∈ Ψ.target}` and inverse `z ↦ (Ψ⁻¹(x, z)).2`. -/
def OpenPartialHomeomorph.slice (Ψ : OpenPartialHomeomorph (A × B) (A × B))
    (hΨ : ∀ y ∈ Ψ.source, (Ψ y).1 = y.1) (x : A) : OpenPartialHomeomorph B B where
  toFun u := (Ψ (x, u)).2
  invFun z := (Ψ.symm (x, z)).2
  source := {u | (x, u) ∈ Ψ.source}
  target := {z | (x, z) ∈ Ψ.target}
  map_source' u hu := by
    have h := Ψ.map_source hu
    rwa [show Ψ (x, u) = (x, (Ψ (x, u)).2) from Prod.ext (hΨ _ hu) rfl] at h
  map_target' z hz := by
    have h := Ψ.map_target hz
    have h1 := hΨ _ h
    rw [Ψ.right_inv hz] at h1
    rwa [show Ψ.symm (x, z) = (x, (Ψ.symm (x, z)).2) from Prod.ext h1.symm rfl] at h
  left_inv' u hu := by
    rw [show (x, (Ψ (x, u)).2) = Ψ (x, u) from Prod.ext (hΨ _ hu).symm rfl, Ψ.left_inv hu]
  right_inv' z hz := by
    have h := Ψ.map_target hz
    have h1 := hΨ _ h
    rw [Ψ.right_inv hz] at h1
    rw [show (x, (Ψ.symm (x, z)).2) = Ψ.symm (x, z) from Prod.ext h1 rfl, Ψ.right_inv hz]
  open_source := Ψ.open_source.preimage (continuous_const.prodMk continuous_id)
  open_target := Ψ.open_target.preimage (continuous_const.prodMk continuous_id)
  continuousOn_toFun := continuous_snd.comp_continuousOn
    (Ψ.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn fun _ hu ↦ hu)
  continuousOn_invFun := continuous_snd.comp_continuousOn
    (Ψ.continuousOn_symm.comp (continuous_const.prodMk continuous_id).continuousOn fun _ hz ↦ hz)

/-- The slice at `x` is `u ↦ (Ψ(x, u)).2`. -/
theorem OpenPartialHomeomorph.slice_apply (Ψ : OpenPartialHomeomorph (A × B) (A × B))
    (hΨ : ∀ y ∈ Ψ.source, (Ψ y).1 = y.1) (x : A) (u : B) :
    OpenPartialHomeomorph.slice Ψ hΨ x u = (Ψ (x, u)).2 :=
  rfl

/-- The inverse of the slice at `x` is `z ↦ (Ψ⁻¹(x, z)).2`. -/
theorem OpenPartialHomeomorph.slice_symm_apply (Ψ : OpenPartialHomeomorph (A × B) (A × B))
    (hΨ : ∀ y ∈ Ψ.source, (Ψ y).1 = y.1) (x : A) (z : B) :
    (OpenPartialHomeomorph.slice Ψ hΨ x).symm z = (Ψ.symm (x, z)).2 :=
  rfl

/-- The source of the slice at `x`. -/
theorem OpenPartialHomeomorph.mem_slice_source (Ψ : OpenPartialHomeomorph (A × B) (A × B))
    (hΨ : ∀ y ∈ Ψ.source, (Ψ y).1 = y.1) (x : A) (u : B) :
    u ∈ (OpenPartialHomeomorph.slice Ψ hΨ x).source ↔ (x, u) ∈ Ψ.source :=
  Iff.rfl

/-- The target of the slice at `x`. -/
theorem OpenPartialHomeomorph.mem_slice_target (Ψ : OpenPartialHomeomorph (A × B) (A × B))
    (hΨ : ∀ y ∈ Ψ.source, (Ψ y).1 = y.1) (x : A) (z : B) :
    z ∈ (OpenPartialHomeomorph.slice Ψ hΨ x).target ↔ (x, z) ∈ Ψ.target :=
  Iff.rfl

end Slice

section SliceSmooth

variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B]
  [NormedSpace ℝ B]

/-- Slices of smooth partial homeomorphisms are smooth. -/
theorem OpenPartialHomeomorph.contDiffOn_slice {Ψ : OpenPartialHomeomorph (A × B) (A × B)}
    (hΨ : ∀ y ∈ Ψ.source, (Ψ y).1 = y.1) (x : A) (h : ContDiffOn ℝ ∞ Ψ Ψ.source) :
    ContDiffOn ℝ ∞ (OpenPartialHomeomorph.slice Ψ hΨ x)
      (OpenPartialHomeomorph.slice Ψ hΨ x).source :=
  contDiff_snd.comp_contDiffOn (h.comp (contDiffOn_const.prodMk contDiffOn_id) fun _ hu ↦ hu)

/-- Slices of partial homeomorphisms with smooth inverse have smooth inverse. -/
theorem OpenPartialHomeomorph.contDiffOn_slice_symm {Ψ : OpenPartialHomeomorph (A × B) (A × B)}
    (hΨ : ∀ y ∈ Ψ.source, (Ψ y).1 = y.1) (x : A) (h : ContDiffOn ℝ ∞ Ψ.symm Ψ.target) :
    ContDiffOn ℝ ∞ (OpenPartialHomeomorph.slice Ψ hΨ x).symm
      (OpenPartialHomeomorph.slice Ψ hΨ x).target :=
  contDiff_snd.comp_contDiffOn (h.comp (contDiffOn_const.prodMk contDiffOn_id) fun _ hz ↦ hz)

/-- The shear `(a, b) ↦ (a, a + b)` of `A × A`, as a topological isomorphism. -/
def prodShear : (A × A) ≃L[ℝ] (A × A) :=
  ContinuousLinearEquiv.equivOfInverse
    ((ContinuousLinearMap.fst ℝ A A).prod
      (ContinuousLinearMap.fst ℝ A A + ContinuousLinearMap.snd ℝ A A))
    ((ContinuousLinearMap.fst ℝ A A).prod
      (ContinuousLinearMap.snd ℝ A A - ContinuousLinearMap.fst ℝ A A))
    (fun y ↦ by simp) (fun y ↦ by simp)

/-- `prodShear (a, b) = (a, a + b)`. -/
theorem prodShear_apply (y : A × A) : (prodShear : (A × A) ≃L[ℝ] (A × A)) y = (y.1, y.1 + y.2) :=
  rfl

end SliceSmooth

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

namespace Connection

variable (C : Connection E M)

/-- The **exponential map read in charts around `p`**: in the chart of `TM` over the preferred
chart `φ` at `p` and the chart `φ` of `M`, the map `G(v) = (π v, exp v)` reads
`(x, u) ↦ (x, φ(exp(x, u)))`. -/
def expChart (p : M) (y : E × E) : E × E :=
  (y.1, chartAt E p (C.exp ((tangentChart (prefChart (E := E) p) (chartAt E p)).symm y)))

/-- The open set of `E × E` on which `Connection.expChart` is meaningful: the points `(x, u)` of
the target of the chart of `TM` over `φ` that are in `D(exp)` and whose exponential lies in the
source of `φ`. -/
def expChartDomain (p : M) : Set (E × E) :=
  chartDomain C.exp C.expDomain (tangentChart (prefChart (E := E) p) (chartAt E p)) (chartAt E p)

/-- In the chart of `TM` over the preferred chart at `p`, the point `(φ p, w)` is `w ∈ T_pM`. -/
theorem tangentChart_prefChart_symm (p : M) (w : E) :
    (tangentChart (prefChart (E := E) p) (chartAt E p)).symm ((chartAt E p) p, w) =
      (⟨p, w⟩ : TangentBundle E M) := by
  have h := tangentChart_prefChart (E := E) (⟨p, w⟩ : TangentBundle E M)
  have hs : (⟨p, w⟩ : TangentBundle E M) ∈
      (tangentChart (prefChart (E := E) p) (chartAt E p)).source :=
    (mem_tangentChart_source _ _ _).mpr ⟨mem_chart_source E p, mem_chart_source E p⟩
  rw [← (tangentChart (prefChart (E := E) p) (chartAt E p)).left_inv hs]
  exact congrArg _ h.symm

/-- On the fiber over `p`, `G` reads `(φ p, w) ↦ (φ p, φ(exp_p w))`. -/
theorem expChart_prefChart (p : M) (w : E) :
    C.expChart p ((chartAt E p) p, w) = ((chartAt E p) p, chartAt E p (C.expAt p w)) := by
  rw [expChart, tangentChart_prefChart_symm]
  rfl

/-- `(φ p, w)` lies in the domain of `G` in charts iff `w ∈ D(exp_p)` and `exp_p w ∈ dom φ`. -/
theorem mem_expChartDomain_prefChart {p : M} {w : E} :
    ((chartAt E p) p, w) ∈ C.expChartDomain p ↔
      w ∈ C.expDomainAt p ∧ C.expAt p w ∈ (chartAt E p).source := by
  simp only [expChartDomain, chartDomain, mem_inter_iff, mem_preimage, tangentChart_prefChart_symm]
  have ht : ((chartAt E p) p, w) ∈ (tangentChart (prefChart (E := E) p) (chartAt E p)).target :=
    (mem_tangentChart_target _ _ _).mpr ⟨(chartAt E p).map_source (mem_chart_source E p), by
      simp [(chartAt E p).left_inv (mem_chart_source E p)]⟩
  exact ⟨fun h ↦ ⟨h.2.1, h.2.2⟩, fun h ↦ ⟨ht, h.1, h.2⟩⟩

variable [CompleteSpace E] [T2Space M]

/-- The domain of `G` in charts is open. -/
theorem isOpen_expChartDomain (p : M) : IsOpen (C.expChartDomain p) :=
  isOpen_chartDomain C.isOpen_expDomain (C.smoothMBMOn_exp 0).continuousOn _ _

/-- **`G` read in charts is smooth.** -/
theorem contDiffOn_expChart (p : M) : ContDiffOn ℝ ∞ (C.expChart p) (C.expChartDomain p) := by
  refine (smoothMBOn_iff_contDiffOn (C.isOpen_expChartDomain p)).1 fun k ↦ ?_
  have h := (C.smoothMBMOn_exp k).contDiffMBOn_chart C.isOpen_expDomain
    (tangentChart_mem_atlas (prefChart (E := E) p)) (chart_mem_atlas E p)
  exact ((ContinuousLinearMap.fst ℝ E E).contDiffMBOn k _).prodMk
    (C.isOpen_expChartDomain p) h

/-- `exp_p(0) = p`. -/
theorem expAt_zero (p : M) : C.expAt p 0 = p := by
  have h := C.exp_zero_smul (⟨p, 0⟩ : TangentBundle E M)
  have hv : tangentSMul 0 (⟨p, 0⟩ : TangentBundle E M) = ⟨p, 0⟩ := by simp [tangentSMul]
  rw [hv] at h
  exact h

/-- `0 ∈ D(exp_p)`. -/
theorem zero_mem_expDomainAt (p : M) : (0 : E) ∈ C.expDomainAt p :=
  C.zero_mem_expDomain p

/-- `(φ p, 0)` lies in the domain of `G` in charts. -/
theorem prefChart_zero_mem_expChartDomain (p : M) :
    ((chartAt E p) p, (0 : E)) ∈ C.expChartDomain p :=
  C.mem_expChartDomain_prefChart.2 ⟨C.zero_mem_expDomainAt p, by
    rw [expAt_zero]; exact mem_chart_source E p⟩

/-- `exp_p` read in the preferred chart at `p` is smooth on the open set `{w | (φ p, w) ∈ D}`. -/
theorem contDiffOn_chart_expAt (p : M) :
    ContDiffOn ℝ ∞ (fun w ↦ chartAt E p (C.expAt p w))
      {w | (chartAt E p p, w) ∈ C.expChartDomain p} := by
  have h := (C.contDiffOn_expChart p).comp (contDiffOn_const.prodMk contDiffOn_id)
    (fun w hw ↦ hw : MapsTo (fun w : E ↦ (chartAt E p p, w))
      {w | (chartAt E p p, w) ∈ C.expChartDomain p} (C.expChartDomain p))
  refine (contDiff_snd.comp_contDiffOn h).congr fun w _ ↦ ?_
  simp [Function.comp_def, expChart_prefChart]

/-- **The differential of `exp_p` at `0` is the identity** (Lang, *Fundamentals*, Ch. IV §4,
Theorem 4.1, p. 108; *Estructuras*, Observación 6.2.2, p. 155): read in the preferred chart
`φ` at `p`, the derivative at `0` of `w ↦ φ(exp_p w)` is the identity of `T_pM = E`. -/
theorem hasFDerivAt_expAt_zero (p : M) :
    HasFDerivAt (fun w ↦ chartAt E p (C.expAt p w)) (ContinuousLinearMap.id ℝ E) 0 := by
  set f : E → E := fun w ↦ chartAt E p (C.expAt p w)
  set U : Set E := {w | (chartAt E p p, w) ∈ C.expChartDomain p}
  have hU : IsOpen U :=
    (C.isOpen_expChartDomain p).preimage (continuous_const.prodMk continuous_id)
  have h0 : (0 : E) ∈ U := C.prefChart_zero_mem_expChartDomain p
  have hfU : ContDiffOn ℝ ∞ f U := C.contDiffOn_chart_expAt p
  have hd : HasFDerivAt f (fderiv ℝ f 0) 0 :=
    ((hfU.differentiableOn (by simp) 0 h0).differentiableAt (hU.mem_nhds h0)).hasFDerivAt
  have hclaim : ∀ w, fderiv ℝ f 0 w = w := by
    intro w
    set v : TangentBundle E M := ⟨p, w⟩
    have h1 : HasDerivAt (fun t : ℝ ↦ f (t • w)) (fderiv ℝ f 0 w) 0 := by
      have := hd.comp_hasDerivAt_of_eq (x := (0 : ℝ)) ((hasDerivAt_id (0 : ℝ)).smul_const w)
        (by simp)
      simpa [Function.comp_def] using this
    have h2 : HasDerivAt (chartAt E p ∘ C.maxGeodesic v) w 0 := C.hasDerivAt_maxGeodesic_zero v
    have heq : (chartAt E p ∘ C.maxGeodesic v) =ᶠ[𝓝 0] fun t : ℝ ↦ f (t • w) := by
      filter_upwards [(C.isOpen_maxInterval v).mem_nhds (C.zero_mem_maxInterval v)] with t ht
      change chartAt E p (C.maxGeodesic v t) = chartAt E p (C.exp ⟨p, t • w⟩)
      rw [← C.exp_smul v ht]
      rfl
    exact (h1.congr_of_eventuallyEq heq).unique h2
  have hid : fderiv ℝ f 0 = ContinuousLinearMap.id ℝ E := ContinuousLinearMap.ext hclaim
  rwa [hid] at hd

/-- **`exp_p` is a local diffeomorphism at `0`** (Lang, *Fundamentals*, Ch. IV §4, Theorem 4.1,
p. 108; *Estructuras*, Observación 6.2.2, p. 155). There is a partial homeomorphism `e`
from an open neighbourhood of `0` in `T_pM = E`, contained in `D(exp_p)`, onto an open
neighbourhood of `p` in `M`, which agrees with `exp_p` on its source and is smooth with smooth
inverse. -/
theorem exists_expAt_openPartialHomeomorph (p : M) :
    ∃ e : OpenPartialHomeomorph E M, (0 : E) ∈ e.source ∧ p ∈ e.target ∧
      e.source ⊆ C.expDomainAt p ∧ EqOn (C.expAt p) e e.source ∧
      SmoothMBMOn E E e e.source ∧ SmoothMBMOn E E e.symm e.target := by
  set φ := chartAt E p
  set U : Set E := {w | (φ p, w) ∈ C.expChartDomain p}
  have hU : IsOpen U :=
    (C.isOpen_expChartDomain p).preimage (continuous_const.prodMk continuous_id)
  have h0 : (0 : E) ∈ U := C.prefChart_zero_mem_expChartDomain p
  obtain ⟨ψ, hψ0, hψU, hψf, hψs, hψs'⟩ := exists_openPartialHomeomorph_of_contDiffOn hU
    (C.contDiffOn_chart_expAt p) h0 (f' := ContinuousLinearEquiv.refl ℝ E)
    (by simpa using C.hasFDerivAt_expAt_zero p)
  have hmem : ∀ w ∈ ψ.source, w ∈ C.expDomainAt p ∧ C.expAt p w ∈ φ.source :=
    fun w hw ↦ C.mem_expChartDomain_prefChart.1 (hψU hw)
  have hsrc : (ψ.trans φ.symm).source = ψ.source := by
    rw [OpenPartialHomeomorph.trans_source]
    refine inter_eq_left.2 fun w hw ↦ ?_
    change ψ w ∈ φ.target
    rw [hψf]
    exact φ.map_source (hmem w hw).2
  have heq : EqOn (C.expAt p) (ψ.trans φ.symm) (ψ.trans φ.symm).source := by
    intro w hw
    rw [hsrc] at hw
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hψf]
    exact (φ.left_inv (hmem w hw).2).symm
  have h0' : (0 : E) ∈ (ψ.trans φ.symm).source := by rw [hsrc]; exact hψ0
  obtain ⟨hs, hs'⟩ := smoothMBMOn_trans_chart_symm (chart_mem_atlas E p) hψs hψs'
  refine ⟨ψ.trans φ.symm, h0', ?_, by rw [hsrc]; exact fun w hw ↦ (hmem w hw).1, heq, hs, hs'⟩
  have h := (ψ.trans φ.symm).map_source h0'
  rwa [← heq h0', expAt_zero] at h

/-! ### The map `G(v) = (π v, exp v)` near the zero section -/

omit [CompleteSpace E] [T2Space M] in
/-- A point of the target of the chart of `TM` over a chart `φ` of `M` lies over `φ⁻¹(x)`. -/
theorem tangentChart_symm_proj_chart (p : M) {q : M} (hq : q ∈ (chartAt E p).source) (u : E) :
    ((tangentChart (prefChart (E := E) p) (chartAt E p)).symm (chartAt E p q, u)).proj = q :=
  (chartAt E p).left_inv hq

/-- The zero section in charts: `G(x, 0) = (x, x)`. -/
theorem expChart_zero (p : M) {x : E} (hx : x ∈ (chartAt E p).target) :
    C.expChart p (x, 0) = (x, x) := by
  set φ := chartAt E p
  set T := tangentChart (prefChart (E := E) p) φ
  set q := φ.symm x
  have hq : q ∈ φ.source := φ.map_target hx
  have hT : T ⟨q, 0⟩ = (x, 0) := by
    obtain ⟨L, hL⟩ := exists_linear_tangentCoordChange (prefChart (E := E) q)
      (prefChart (E := E) p) ⟨mem_chart_source E q, hq⟩
    rw [tangentChart_apply]
    refine Prod.ext (φ.right_inv hx) ?_
    change tangentCoordChange (prefChart (E := E) q) (prefChart (E := E) p) q 0 = 0
    rw [hL, map_zero]
  have hsrc : (⟨q, 0⟩ : TangentBundle E M) ∈ T.source :=
    (mem_tangentChart_source _ _ _).mpr ⟨hq, hq⟩
  have hTs : T.symm (x, 0) = ⟨q, 0⟩ := by rw [← hT, T.left_inv hsrc]
  change (x, φ (C.exp (T.symm (x, 0)))) = (x, x)
  rw [hTs]
  change (x, φ (C.expAt q 0)) = (x, x)
  rw [expAt_zero, φ.right_inv hx]

/-- **The differential of `G(v) = (π v, exp v)` at `0_p`** (Lang, *Fundamentals*, Ch. VIII §5,
Proposition 5.1, p. 215; *Estructuras*, §6.2.1, p. 156): in charts it is
`(a, b) ↦ (a, a + b)`, the matrix `[[id, 0], [id, id]]`. The first column comes from `G(x, 0) =
(x, x)`, the second from `d(exp_p)(0) = id`. -/
theorem hasFDerivAt_expChart (p : M) :
    HasFDerivAt (C.expChart p) ((prodShear : (E × E) ≃L[ℝ] (E × E)) : E × E →L[ℝ] E × E)
      (chartAt E p p, 0) := by
  set φ := chartAt E p
  have h0 := C.prefChart_zero_mem_expChartDomain p
  have hF : HasFDerivAt (C.expChart p) (fderiv ℝ (C.expChart p) (φ p, (0 : E))) (φ p, (0 : E)) :=
    (((C.contDiffOn_expChart p).differentiableOn (by simp) _ h0).differentiableAt
      ((C.isOpen_expChartDomain p).mem_nhds h0)).hasFDerivAt
  set D := fderiv ℝ (C.expChart p) (φ p, (0 : E))
  have hhor : ∀ a, D (a, 0) = (a, a) := by
    have h1 : HasFDerivAt (C.expChart p ∘ fun x ↦ (x, (0 : E)))
        (D.comp (ContinuousLinearMap.inl ℝ E E)) (φ p) :=
      hF.comp (φ p) (hasFDerivAt_prodMk_left (𝕜 := ℝ) (φ p) (0 : E))
    have hev : (fun x ↦ (x, x)) =ᶠ[𝓝 (φ p)] C.expChart p ∘ fun x ↦ (x, (0 : E)) := by
      filter_upwards [φ.open_target.mem_nhds (φ.map_source (mem_chart_source E p))] with x hx
      exact (C.expChart_zero p hx).symm
    have h2 : HasFDerivAt (fun x : E ↦ (x, x))
        ((ContinuousLinearMap.id ℝ E).prod (ContinuousLinearMap.id ℝ E)) (φ p) :=
      (hasFDerivAt_id _).prodMk (hasFDerivAt_id _)
    intro a
    have := congrArg (fun L : E →L[ℝ] E × E ↦ L a) ((h1.congr_of_eventuallyEq hev).unique h2)
    simpa using this
  have hver : ∀ b, D (0, b) = (0, b) := by
    have h1 : HasFDerivAt (C.expChart p ∘ fun w ↦ (φ p, w))
        (D.comp (ContinuousLinearMap.inr ℝ E E)) 0 :=
      hF.comp (0 : E) (hasFDerivAt_prodMk_right (𝕜 := ℝ) (φ p) (0 : E))
    have hfun : (C.expChart p ∘ fun w ↦ (φ p, w)) = fun w ↦ (φ p, φ (C.expAt p w)) :=
      funext fun w ↦ C.expChart_prefChart p w
    have h2 : HasFDerivAt (fun w ↦ (φ p, φ (C.expAt p w)))
        ((0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E)) 0 :=
      (hasFDerivAt_const _ _).prodMk (C.hasFDerivAt_expAt_zero p)
    rw [hfun] at h1
    intro b
    have := congrArg (fun L : E →L[ℝ] E × E ↦ L b) (h1.unique h2)
    simpa using this
  have hD : D = ((prodShear : (E × E) ≃L[ℝ] (E × E)) : E × E →L[ℝ] E × E) := by
    refine ContinuousLinearMap.ext fun y ↦ ?_
    obtain ⟨a, b⟩ := y
    calc D (a, b) = D ((a, 0) + (0, b)) := by simp
      _ = (a, a + b) := by rw [map_add, hhor, hver]; simp
  rw [← hD]
  exact hF

/-- **`G(v) = (π v, exp v)` is a local diffeomorphism at `0_p`, in charts** (Lang,
*Fundamentals*, Ch. VIII §5, Proposition 5.1, p. 215; *Estructuras*, §6.2.1, p. 156). -/
theorem exists_expChart_openPartialHomeomorph (p : M) :
    ∃ Ψ : OpenPartialHomeomorph (E × E) (E × E), (chartAt E p p, (0 : E)) ∈ Ψ.source ∧
      Ψ.source ⊆ C.expChartDomain p ∧ ⇑Ψ = C.expChart p ∧
      ContDiffOn ℝ ∞ Ψ Ψ.source ∧ ContDiffOn ℝ ∞ Ψ.symm Ψ.target :=
  exists_openPartialHomeomorph_of_contDiffOn (C.isOpen_expChartDomain p) (C.contDiffOn_expChart p)
    (C.prefChart_zero_mem_expChartDomain p) (C.hasFDerivAt_expChart p)

/-- **`G(v) = (π v, exp v)` is a local diffeomorphism `TM → M × M` at `0_p`** (Lang,
*Fundamentals*, Ch. VIII §5, Proposition 5.1, p. 215; *Estructuras*, §6.2.1, p. 156). There is a
partial homeomorphism `Φ` from an open neighbourhood of `0_p` in `TM`, contained in `D(exp)`,
onto an open neighbourhood of `(p, p)` in `M × M`, with `Φ v = (π v, exp v)` on its source, smooth
with smooth inverse. -/
theorem exists_expPair_openPartialHomeomorph (p : M) :
    ∃ Φ : OpenPartialHomeomorph (TangentBundle E M) (M × M),
      (⟨p, 0⟩ : TangentBundle E M) ∈ Φ.source ∧ Φ.source ⊆ C.expDomain ∧
      (∀ v ∈ Φ.source, Φ v = (v.proj, C.exp v)) ∧
      SmoothMBMOn (E × E) (ModelProd E E) Φ Φ.source ∧
      SmoothMBMOn (ModelProd E E) (E × E) Φ.symm Φ.target := by
  obtain ⟨Ψ, h0, hsub, hΨF, hΨs, hΨs'⟩ := C.exists_expChart_openPartialHomeomorph p
  set φ := chartAt E p
  set T := tangentChart (prefChart (E := E) p) φ
  set Θ : OpenPartialHomeomorph (M × M) (ModelProd E E) := φ.prod φ
  have hΘ : Θ ∈ atlas (ModelProd E E) (M × M) :=
    prodChart_mem_atlas (chart_mem_atlas E p) (chart_mem_atlas E p)
  have hTatlas : T ∈ atlas (E × E) (TangentBundle E M) := tangentChart_mem_atlas _
  -- `Ψ` maps its source into the target of `φ × φ`
  have hΨΘ : (Ψ.trans Θ.symm).source = Ψ.source := by
    rw [OpenPartialHomeomorph.trans_source]
    refine inter_eq_left.2 fun y hy ↦ ?_
    have hd := hsub hy
    have hyT : y.1 ∈ φ.target := ((mem_tangentChart_target _ _ _).mp hd.1).1
    change Ψ y ∈ Θ.target
    rw [hΨF]
    exact ⟨hyT, φ.map_source hd.2.2⟩
  set Φ := T.trans (Ψ.trans Θ.symm)
  have hΦsrc : Φ.source = T.source ∩ T ⁻¹' Ψ.source := by
    rw [OpenPartialHomeomorph.trans_source, hΨΘ]
  have hval : ∀ v ∈ Φ.source, Φ v = (v.proj, C.exp v) := by
    intro v hv
    rw [hΦsrc] at hv
    have hvp : v.proj ∈ φ.source := ((mem_tangentChart_source _ _ _).mp hv.1).2
    have hd : C.exp (T.symm (T v)) ∈ φ.source := (hsub hv.2).2.2
    rw [T.left_inv hv.1] at hd
    change Θ.symm (Ψ (T v)) = _
    rw [hΨF]
    change (φ.symm (T v).1, φ.symm (φ (C.exp (T.symm (T v))))) = _
    rw [T.left_inv hv.1, φ.left_inv hd]
    exact Prod.ext (φ.left_inv hvp) rfl
  have hΦexp : Φ.source ⊆ C.expDomain := fun v hv ↦ by
    rw [hΦsrc] at hv
    have hd := (hsub hv.2).2.1
    rwa [T.left_inv hv.1] at hd
  have h0' : (⟨p, 0⟩ : TangentBundle E M) ∈ Φ.source := by
    rw [hΦsrc]
    have hs : (⟨p, 0⟩ : TangentBundle E M) ∈ T.source :=
      (mem_tangentChart_source _ _ _).mpr ⟨mem_chart_source E p, mem_chart_source E p⟩
    refine ⟨hs, ?_⟩
    change T ⟨p, 0⟩ ∈ Ψ.source
    rw [show T ⟨p, 0⟩ = (φ p, 0) from tangentChart_prefChart (E := E) (⟨p, 0⟩ : TangentBundle E M)]
    exact h0
  refine ⟨Φ, h0', hΦexp, hval, ?_, ?_⟩
  · -- `Φ = (π, exp)` on its source
    have hG : SmoothMBMOn (E × E) (ModelProd E E) (fun v : TangentBundle E M ↦ (v.proj, C.exp v))
        Φ.source := fun k ↦
      ContMDiffMBOn.prodMk Φ.open_source
        (ContMDiffMBOn.comp Φ.open_source isOpen_univ (smoothMBM_tangentBundle_proj (M := M) k)
          ((smoothMBMOn_id Φ.open_source) k) (mapsTo_univ _ _))
        ((SmoothMBMOn.mono_of_isOpen C.isOpen_expDomain Φ.open_source C.smoothMBMOn_exp hΦexp) k)
    exact hG.congr_of_isOpen Φ.open_source fun v hv ↦ (hval v hv).symm
  · -- `Φ⁻¹ = T⁻¹ ∘ Ψ⁻¹ ∘ (φ × φ)`
    have hΘs : SmoothMBMOn (ModelProd E E) (ModelProd E E) Θ Θ.source :=
      smoothMBMOn_of_mem_atlas hΘ
    have hΨs'M : SmoothMBMOn (M := ModelProd E E) (N := E × E) (ModelProd E E) (E × E)
        (Ψ.symm : ModelProd E E → E × E) (Ψ.target : Set (ModelProd E E)) := fun k ↦
      (contMDiffMBOn_iff_contDiffMBOn (E := ModelProd E E) (F := E × E) Ψ.open_target).2
        ((smoothMBOn_iff_contDiffOn Ψ.open_target).2 hΨs' k)
    have hTs : SmoothMBMOn (E × E) (E × E) T.symm T.target := smoothMBMOn_symm_of_mem_atlas hTatlas
    have htgt : Φ.target = Θ.source ∩ Θ ⁻¹' (Ψ.target ∩ Ψ.symm ⁻¹' T.target) := by
      simp only [Φ, OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
        OpenPartialHomeomorph.symm_symm, preimage_inter, inter_assoc]
      rfl
    have h1 := SmoothMBMOn.comp (N := ModelProd E E) (V := (Ψ.target : Set (ModelProd E E)))
      Φ.open_target Ψ.open_target hΨs'M
      (SmoothMBMOn.mono_of_isOpen Θ.open_source Φ.open_target hΘs
        (by rw [htgt]; exact inter_subset_left))
      (fun z hz ↦ by rw [htgt] at hz; exact hz.2.1)
    have h2 := SmoothMBMOn.comp Φ.open_target T.open_target hTs h1
      (fun z hz ↦ by rw [htgt] at hz; exact hz.2.2)
    refine h2.congr_of_isOpen Φ.open_target fun z _ ↦ ?_
    rfl

/-- **Normal neighbourhoods: points of `W` are joined by a unique short geodesic** (*Estructuras*,
Teorema 6.2.3 (1), p. 156; Lang, *Fundamentals*, Ch. VIII §5, Corollary 5.2 (1), p. 216).
With `Φ = (π, exp)` as in `Connection.exists_expPair_openPartialHomeomorph`, there is an open
neighbourhood `W` of `p` with `W × W ⊆ Φ(V)`, `V` the source of `Φ`. Hence for `x, y ∈ W` there is
exactly one `v ∈ V` over `x` with `exp v = y`, i.e. exactly one geodesic `t ↦ exp(t v)`,
`0 ≤ t ≤ 1`, from `x` to `y` with initial velocity in `V`; and `(x, y) ↦ v = Φ⁻¹(x, y)` is
smooth. -/
theorem exists_expPair_normal (p : M) :
    ∃ Φ : OpenPartialHomeomorph (TangentBundle E M) (M × M), ∃ W : Set M,
      (⟨p, 0⟩ : TangentBundle E M) ∈ Φ.source ∧ Φ.source ⊆ C.expDomain ∧
      (∀ v ∈ Φ.source, Φ v = (v.proj, C.exp v)) ∧
      SmoothMBMOn (E × E) (ModelProd E E) Φ Φ.source ∧
      SmoothMBMOn (ModelProd E E) (E × E) Φ.symm Φ.target ∧
      IsOpen W ∧ p ∈ W ∧ W ×ˢ W ⊆ Φ.target ∧
      ∀ x ∈ W, ∀ y ∈ W, ∃! v, v ∈ Φ.source ∧ v.proj = x ∧ C.exp v = y := by
  obtain ⟨Φ, h0, hexp, hval, hs, hs'⟩ := C.exists_expPair_openPartialHomeomorph p
  have hpp : (p, p) ∈ Φ.target := by
    have h := Φ.map_source h0
    rwa [hval _ h0, show C.exp ⟨p, 0⟩ = p from C.expAt_zero p] at h
  obtain ⟨U₁, U₂, hU₁, hU₂, hp₁, hp₂, hUU⟩ := isOpen_prod_iff.1 Φ.open_target p p hpp
  have hWW : (U₁ ∩ U₂) ×ˢ (U₁ ∩ U₂) ⊆ Φ.target := fun z hz ↦ hUU ⟨hz.1.1, hz.2.2⟩
  refine ⟨Φ, U₁ ∩ U₂, h0, hexp, hval, hs, hs', hU₁.inter hU₂, ⟨hp₁, hp₂⟩, hWW,
    fun x hx y hy ↦ ?_⟩
  have hxy : (x, y) ∈ Φ.target := hWW ⟨hx, hy⟩
  have hsrc := Φ.map_target hxy
  have hΦ : (Φ.symm (x, y)).proj = x ∧ C.exp (Φ.symm (x, y)) = y := by
    have h := Φ.right_inv hxy
    rw [hval _ hsrc] at h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  refine ⟨Φ.symm (x, y), ⟨hsrc, hΦ⟩, fun v ⟨hv, hvx, hvy⟩ ↦ ?_⟩
  refine Φ.injOn hv hsrc ?_
  rw [hval _ hv, hval _ hsrc, hvx, hvy, hΦ.1, hΦ.2]

/-- **Uniformly normal neighbourhoods** (*Estructuras*, Teorema 6.2.3 (2), p. 156; Lang,
*Fundamentals*, Ch. VIII §5, Corollary 5.2 (2), p. 216). Let `φ` be the preferred chart at
`p` and read tangent vectors in the chart of `TM` over `φ`: the vector of `T_qM` with coordinates
`(φ q, u)` is `T⁻¹(φ q, u)`. There are an open neighbourhood `W ⊆ dom φ` of `p` and a radius
`r > 0`, the same for all `q ∈ W`, such that for every `q ∈ W` the exponential map at `q` is
defined on the vectors with coordinates in the ball `B_r(0) ⊆ E`, and
`u ↦ exp_q(T⁻¹(φ q, u))` is a diffeomorphism of `B_r(0)` onto an open set containing `W`. -/
theorem exists_uniformlyNormal (p : M) :
    ∃ W : Set M, ∃ r : ℝ, IsOpen W ∧ p ∈ W ∧ W ⊆ (chartAt E p).source ∧ 0 < r ∧
      ∀ q ∈ W, ∃ e : OpenPartialHomeomorph E M, e.source = ball (0 : E) r ∧ W ⊆ e.target ∧
        (∀ u ∈ ball (0 : E) r,
          (tangentChart (prefChart (E := E) p) (chartAt E p)).symm (chartAt E p q, u) ∈
            C.expDomain ∧
          e u = C.exp ((tangentChart (prefChart (E := E) p) (chartAt E p)).symm
            (chartAt E p q, u))) ∧
        SmoothMBMOn E E e e.source ∧ SmoothMBMOn E E e.symm e.target := by
  obtain ⟨Ψ, h0, hsub, hΨF, hΨs, hΨs'⟩ := C.exists_expChart_openPartialHomeomorph p
  set φ := chartAt E p
  set T := tangentChart (prefChart (E := E) p) φ
  set x₀ := φ p
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 Ψ.open_source _ h0
  set Ψ' := Ψ.restrOpen (ball (x₀, (0 : E)) ε) isOpen_ball
  have hΨ'src : Ψ'.source = ball (x₀, (0 : E)) ε := by
    rw [OpenPartialHomeomorph.restrOpen_source]; exact inter_eq_right.2 hεsub
  have hfst : ∀ y ∈ Ψ'.source, (Ψ' y).1 = y.1 := fun y _ ↦ by
    rw [OpenPartialHomeomorph.coe_restrOpen, hΨF]; rfl
  have hval : ∀ y, Ψ' y = C.expChart p y := fun y ↦ by
    rw [OpenPartialHomeomorph.coe_restrOpen, hΨF]
  have hx₀t : (x₀, x₀) ∈ Ψ'.target := by
    have h := Ψ'.map_source (hΨ'src ▸ mem_ball_self hε)
    rwa [hval, C.expChart_zero p (φ.map_source (mem_chart_source E p))] at h
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.1 Ψ'.open_target _ hx₀t
  have hΨ's : ContDiffOn ℝ ∞ Ψ' Ψ'.source :=
    hΨs.mono fun y hy ↦ hεsub (hΨ'src ▸ hy)
  have hΨ's' : ContDiffOn ℝ ∞ Ψ'.symm Ψ'.target :=
    hΨs'.mono fun y hy ↦ by
      rw [OpenPartialHomeomorph.restrOpen_toPartialEquiv] at hy
      exact hy.1
  refine ⟨φ.source ∩ φ ⁻¹' ball x₀ (min δ ε), ε, φ.isOpen_inter_preimage isOpen_ball,
    ⟨mem_chart_source E p, mem_ball_self (lt_min hδ hε)⟩, inter_subset_left, hε, ?_⟩
  rintro q ⟨hq, hqb⟩
  set x := φ q
  have hxε : x ∈ ball x₀ ε := ball_subset_ball (min_le_right _ _) hqb
  set S := OpenPartialHomeomorph.slice Ψ' hfst x
  have hSsrc : S.source = ball (0 : E) ε := by
    ext u
    rw [OpenPartialHomeomorph.mem_slice_source, hΨ'src, ← ball_prod_same]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨hxε, h⟩⟩
  have hdom : ∀ u ∈ S.source, (x, u) ∈ C.expChartDomain p := fun u hu ↦
    hsub (hεsub (hΨ'src ▸ hu))
  have hSval : ∀ u, S u = φ (C.exp (T.symm (x, u))) := fun u ↦ by
    rw [OpenPartialHomeomorph.slice_apply, hval]; rfl
  have hesrc : (S.trans φ.symm).source = S.source := by
    rw [OpenPartialHomeomorph.trans_source]
    refine inter_eq_left.2 fun u hu ↦ ?_
    change S u ∈ φ.target
    rw [hSval]
    exact φ.map_source (hdom u hu).2.2
  obtain ⟨hs, hs'⟩ := smoothMBMOn_trans_chart_symm (chart_mem_atlas E p)
    (OpenPartialHomeomorph.contDiffOn_slice hfst x hΨ's)
    (OpenPartialHomeomorph.contDiffOn_slice_symm hfst x hΨ's')
  refine ⟨S.trans φ.symm, hesrc.trans hSsrc, ?_, fun u hu ↦ ?_, hs, hs'⟩
  · rintro y ⟨hy, hyb⟩
    rw [OpenPartialHomeomorph.trans_target]
    refine ⟨by simpa using hy, ?_⟩
    change (x, φ y) ∈ Ψ'.target
    apply hδsub
    rw [← ball_prod_same]
    exact ⟨ball_subset_ball (min_le_left _ _) hqb, ball_subset_ball (min_le_left _ _) hyb⟩
  · have hu' : u ∈ S.source := hSsrc ▸ hu
    have hd := hdom u hu'
    refine ⟨hd.2.1, ?_⟩
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hSval]
    exact φ.left_inv hd.2.2

end Connection

end LocallyConvex.Manifolds
