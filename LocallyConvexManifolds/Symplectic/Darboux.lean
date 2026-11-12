/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.Symplectic.Basic
public import LocallyConvexManifolds.Flow.Analytic
public import LocallyConvexManifolds.LocalAddition.Basic
public import LocallyConvexAnalysis.Calculus.OperatorValued
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# The Darboux theorem for strong symplectic forms on Banach manifolds

Let `M` be a manifold modeled on a Banach space `E` and `ω` a closed real `2`-form on `M` which is
**strongly nondegenerate** at a point `x₀`: the flat map `v ↦ ω_{x₀}(v, ·)` is a bijection of
`T_{x₀}M` onto its topological dual. Then there is a chart `φ` of the smooth structure around
`x₀` in which `ω` has constant coefficients, equal to its value at `x₀`
(`DifferentialForm.exists_darboux_chart`). In particular every strong symplectic manifold
modeled on a Banach space is locally isomorphic to a constant form on its model
(`SymplecticForm.IsStrong.exists_darboux_chart`).

The theorem is [Wei69, §1, Theorem (p. 1040)] and [Lan99, Ch. V, §8, Theorem 8.1 (pp. 152–153)],
where "non-singular" means strongly nondegenerate ([Lan99, §V.6, p. 145]). Both follow
[Mos65, §4, Theorem 2 and its proof, pp. 292–294], where Darboux's theorem is mentioned as an
application (p. 294). See also [Wei71, Theorem 4.1 (p. 333) and Corollary 4.2 (p. 334)], for
local manifold pairs.

## Main results

* `Darboux.exists_darboux_local`: **the local theorem.** Let `U ⊆ E` be open and
  `Ω : U → L(E, E')` smooth (operator norm), with `Ω(y)` skew-symmetric and `dΩ = 0`, and
  `Ω(p)` bijective. Then there is a diffeomorphism `ψ` between open neighbourhoods of `p` inside
  `U` with `ψ(p) = p`, `dψ(p) = id` and `ψ*Ω = Ω(p)`:
  `Ω(ψ x)(dψ(x) u, dψ(x) v) = Ω(p)(u, v)`.
  `Darboux.exists_darboux_local'` is the same statement for `Ω : U → L(E, D)` with `D ≃ E'`.
* `DifferentialForm.exists_darboux_chart`: **the manifold version.** `φ = ψ⁻¹ ∘ i` for the
  preferred chart `i` at `x₀` belongs to the maximal atlas, `φ(x₀) = i(x₀)`, `φ` and `i` have the
  same differential at `x₀`, and for `x` in the domain of `φ` and `u, v ∈ E`,
  `ω_x(Tu, Tv) = ω_{x₀}(u, v)`, where `T` reads a vector given in the chart `φ` in the preferred
  chart at `x`.
* `SymplecticForm.IsStrong.exists_darboux_chart`: the case of strong symplectic forms.
* `Darboux.exists_darboux_local_of_primitive`: Moser's method for a given primitive; if `Ω` and
  the primitive are real analytic, so are `ψ` and `ψ⁻¹` (used in
  `LocallyConvexManifolds.Symplectic.DarbouxAnalytic` for the real analytic Darboux theorem).
* `DifferentialForm.exists_clm_localRep`, `DifferentialForm.clm_localRep_spec`,
  `DifferentialForm.darboux_chart_of_local`: the passage between the manifold and the local
  statements.

## Moser's method

Put `Ω₀ = Ω(p)`, `Θ = Ω - Ω₀` and `Ωₜ = Ω₀ + tΘ`.

1. *Primitive.* On a ball `B` around `p`, `Θ = dα` with `α(p) = 0` and `dα(p) = 0`
   (`Darboux.exists_primitive`). The Poincaré lemma for star-shaped open sets
   (`DifferentialForm.IsClosed.isExact_of_starConvex`, [GN26, Corollary 3.6.29]) gives a
   primitive `η` on the manifold `B`; we read it as a smooth map `B → E'` and subtract the closed
   affine form `η(p) + dη(p)(y - p)` (`dη(p)` is symmetric because `Θ(p) = 0`).
2. *Moser's vector field.* `Wₜ = {y ∈ B | Ωₜ(y) is invertible}` is open, and contains `p` for all
   `t` because `Ωₜ(p) = Ω₀`. On `W = {(t, y) | y ∈ Wₜ}` put `Xₜ(y) = -Ωₜ(y)⁻¹ α(y)`, so that
   `Ωₜ(Xₜ, ·) = -α`. Then `Xₜ(p) = 0` and `∂ₓXₜ(p) = 0`.
3. *The flow up to time `1`* (`Darboux.exists_flow_of_stationary`). The time-dependent field is
   made autonomous: `Z(t, y) = (1, Xₜ(y))` is a smooth vector field on the open set
   `W ⊆ ℝ × E`, regarded as a manifold (`SmoothVectorField.ofOpens`). Its integral curve through
   `(0, p)` is `t ↦ (t, p)`, defined for all `t`. Since the domain of the maximal flow is open
   (`SmoothVectorField.isOpen_flowDomain`) and `[-1, 2]` is compact, there are `δ > 0` and a
   neighbourhood `V` of `p` such that the flow `Fₜ(x)` of `Xₜ` with `F₀(x) = x` is defined and
   smooth on `(-δ, 1 + δ) × V` (`SmoothVectorField.smoothMBMOn_flow`). This is Weinstein's
   "compactness of `[0, 1]` and openness of the domain".
4. *Moser's computation.* For `x ∈ V` and `u, v ∈ E`, the function
   `t ↦ Ωₜ(Fₜ x)(∂ₓFₜ(x) u, ∂ₓFₜ(x) v)` has derivative `0`. Differentiating uses
   `∂ₜFₜ = Xₜ ∘ Fₜ` and the variational equation `∂ₜ ∂ₓFₜ = ∂ₓXₜ ∘ ∂ₓFₜ`, obtained from the
   symmetry of the second derivative of `F`. The derivative is
   `Θ(a, b) + (∂_X Ωₜ)(a, b) + Ωₜ(∂ₓX a, b) + Ωₜ(a, ∂ₓX b)`, and it vanishes by the algebraic
   identity `Darboux.moser_identity`, fed with the derivative of `Ωₜ(Xₜ, ·) = -α`, with
   `dΩₜ = 0` and with `dα = Θ`. This is the pointwise form of
   `d/dt (Fₜ*Ωₜ) = Fₜ*(Θ + L_{Xₜ}Ωₜ) = Fₜ*(dα + d(i_{Xₜ}Ωₜ)) = 0` (Cartan's formula).
5. *Conclusion.* `F₁*Ω = F₀*Ω₀ = Ω₀`. Since `∂ₓXₜ(p) = 0`, `∂ₓFₜ(p) = id`, so the inverse function
   theorem makes `ψ = F₁` a local diffeomorphism at `p`; we restrict it to where `dψ` is
   invertible, so that its inverse is smooth. The inverse is also `y ↦ Fl(-1, (1, y))` for the
   flow `Fl` of the suspended field `(1, Xₜ)`; `exists_flow_of_stationary` records this, together
   with the real analyticity of the flow when `Xₜ` is real analytic.

## Implementation notes

**Infinite-dimensional subtleties.**

* **Strong nondegeneracy** is used exactly once, to define `Xₜ`: `α(y)` must lie in the range of
  `Ωₜ(y)^♭`. With completeness, the open mapping theorem turns the bijection `Ω₀ : E → E'` into a
  topological isomorphism, and invertible operators form an open set for the operator norm. It is
  only needed at the point `x₀` itself. For weakly nondegenerate forms the theorem fails, even on
  Hilbert space: [Mar72, Proposition (p. 591)]. Marsden's example is formalized in
  lc-analysis [LCA] (`Counterexamples.Marsden.no_darboux_chart`, in
  `Counterexamples/WeakDarboux.lean`).
* **Reflexivity** is not a hypothesis but a consequence: a Banach space carrying a strongly
  nondegenerate skew form is reflexive (`surjective_inclusionInDoubleDual_of_skew`), so
  `ℓ¹` or `c₀` are never models of strong symplectic manifolds.
* **The operator norm.** Openness of invertibles needs `y ↦ Ω(y)` continuous into `L(E, E')` with
  the operator norm, which is stronger than smoothness of `(y, u, v) ↦ Ω(y)(u, v)`. On a normed
  model it follows from the latter ([LCA], `contDiffMBOn_of_unc_clm`, applied twice in
  `DifferentialForm.exists_darboux_chart`). On non-normable locally convex models there is no
  vector topology on `L(E, E')` for which evaluation is continuous, and strong symplectic forms
  behave differently (see the module docstring of `LocallyConvexManifolds.Symplectic.Basic`);
  neither the flows nor the inverse function theorem used here are available there.
* **Completeness** of `E` is used for the flows (Picard–Lindelöf through the flow boxes of
  `LocallyConvexManifolds.Flow.Existence`), for the inverse function theorem, for the smoothness of
  `L ↦ L⁻¹` and for the open mapping theorem. The Poincaré lemma only uses the (Mackey)
  completeness of `ℝ`.
* **No bump functions.** Smooth bump functions need not exist on a Banach space, so Moser's field
  cannot be extended to `ℝ × E`. We work on the open set `W ⊆ ℝ × E`, regarded as a manifold, and
  never cut off.
* **No Hausdorff hypothesis on `M`**: the flows live in the open set `W ⊆ ℝ × E`, which is
  Hausdorff, and the argument takes place in one chart.

**Design choices.**

* We do not use the Lie derivative of `LocallyConvexManifolds.DifferentialForm.LieDerivative` or the
  formula `d/dt|₀ (Fl_t)* ω = L_X ω` of `LocallyConvexManifolds.Flow.Maximal`, which concern
  autonomous vector fields: Moser's derivative is computed in the chart, where Cartan's formula
  becomes the identity `Darboux.moser_identity`. Weinstein and Lang compute with forms and Cartan's
  formula. We also normalize the primitive so that `dα(p) = 0`, which Weinstein asserts for his
  primitive; this gives `dψ(p) = id`. We do not claim this argument is new.
* The local theorem is stated for `Ω : E → L(E, D)` with `D ≃ E'`
  (`Darboux.exists_darboux_local'`): in the current Mathlib, the calculus lemmas for sums and
  multiples of maps with values in the iterated space `L(E, L(E, ℝ))` do not elaborate (instance
  unification fails), while they do for `L(E, D)`. `Darboux.exists_darboux_local` is the case
  `D = E'`.
* Real-valued forms require models in `Type`, since the value space of a form lives in the
  universe of the model.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
* [S. Lang, *Fundamentals of Differential Geometry*][Lan99]
* [glaroton, *lc-analysis: Michal–Bastiani calculus on locally convex spaces*][LCA]
* [J. E. Marsden, *Darboux's theorem fails for weak symplectic forms*][Mar72]
* [J. Moser, *On the volume elements on a manifold*][Mos65]
* [A. Weinstein, *Symplectic structures on Banach manifolds*][Wei69]
* [A. Weinstein, *Symplectic manifolds and their Lagrangian submanifolds*][Wei71]
-/

@[expose] public section

open Set Function Filter Metric TopologicalSpace
open LocallyConvex.Analysis
open scoped Topology

noncomputable section

namespace LocallyConvex.Manifolds

/-! ### Vector fields on open subsets of the model space -/

section OpensField

variable {G : Type} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G]

/-- A map `Z : G → G`, smooth on an open subset `U` of the model space, as a smooth vector field
on the manifold `U`: `z ↦ Z(z) ∈ T_z U = G`. -/
def SmoothVectorField.ofOpens (U : Opens G) (Z : G → G) (hZ : SmoothMBOn Z U) :
    SmoothVectorField G U where
  toFun z := ⟨z, Z z⟩
  isVectorField _ := rfl
  smooth k := by
    refine contMDiffMB_of_chartAt ?_ fun x ↦ ⟨U, U.isOpen, ?_, ?_, ?_⟩
    · have hc : Continuous fun z : U ↦ Z z :=
        (hZ 0).continuousOn.comp_continuous continuous_subtype_val fun z ↦ z.2
      exact (continuous_tangentBundle_opens_mk U).comp (continuous_id.prodMk hc)
    · rw [opens_atlas_apply (chart_mem_atlas G x)]; exact x.2
    · intro y hy
      refine ⟨?_, ?_, ?_⟩
      · rw [opens_atlas_target (chart_mem_atlas G x)]; exact hy
      · exact mem_univ _
      · simp only [mem_preimage]
        rw [chartAt_tangentBundle_opens_source]; exact mem_univ _
    · refine ContDiffMBOn.congr_of_isOpen U.isOpen (fun y hy ↦ ?_)
        (ContDiffMBOn.prodMk U.isOpen (smoothMBOn_id _ k) (hZ k))
      simp only [comp_apply, chartAt_tangentBundle_opens_apply]
      rw [opens_atlas_symm (chart_mem_atlas G x) hy]
      rfl

/-- In every chart of `U` (all of them are the inclusion), the local representative of
`SmoothVectorField.ofOpens U Z` is `Z`. -/
theorem SmoothVectorField.rep_ofOpens (U : Opens G) (Z : G → G) (hZ : SmoothMBOn Z U)
    (i : atlas G U) {y : G} (hy : y ∈ U) : (SmoothVectorField.ofOpens U Z hZ).rep i y = Z y := by
  change (tangentChart i i.1 ⟨i.1.symm y, Z (i.1.symm y)⟩).2 = Z y
  rw [tangentChart_apply, tangentCoordChange_opens]
  change Z (i.1.symm y : G) = Z y
  rw [opens_atlas_symm i.2 hy]

end OpensField

/-- The value `ωₓ : Eⁿ → ℝ` of a smooth form at a point is continuous. -/
theorem DifferentialForm.continuous_apply {E : Type} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [T2Space E] {M : Type} [TopologicalSpace M] [ChartedSpace E M] {n : ℕ}
    (β : DifferentialForm E M ℝ n) (x : M) : Continuous (β x) := by
  have h := ((β.smooth' (prefChart x)) 0).continuousOn
  have hy : chartAt E x x ∈ (prefChart (E := E) x).1.target :=
    (chartAt E x).map_source (mem_chart_source E x)
  have hc : Continuous fun u : Fin n → E ↦ β.localRep (prefChart x) (chartAt E x x, u) := by
    refine continuous_iff_continuousAt.2 fun u ↦ ?_
    exact (h.continuousAt
      (prod_mem_nhds ((prefChart (E := E) x).1.open_target.mem_nhds hy) Filter.univ_mem)).comp
      (continuous_const.prodMk continuous_id).continuousAt
  convert hc using 1
  funext u
  exact (β.localRep_prefChart x u).symm


namespace Darboux

open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- A skew-symmetric continuous bilinear form, as an alternating map on `E²`. -/
def altOfSkew (f : E →L[ℝ] E →L[ℝ] ℝ) (hf : ∀ a b, f a b = -f b a) : E [⋀^Fin 2]→ₗ[ℝ] ℝ where
  toFun v := f (v 0) (v 1)
  map_update_add' v i a b := by
    fin_cases i <;> simp
  map_update_smul' v i c a := by
    fin_cases i <;> simp
  map_eq_zero_of_eq' v i j hv hij := by
    have h0 : ∀ a, f a a = 0 := fun a ↦ by linarith [hf a a]
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · change f (v 0) (v 1) = 0
      rw [show v 1 = v 0 from hv.symm]; exact h0 _
    · change f (v 0) (v 1) = 0
      rw [show v 1 = v 0 from hv]; exact h0 _
    · exact absurd rfl hij

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- **The algebraic core of Moser's argument**: Cartan's formula at a point. Read `σ` as
`Ωₜ(y)`, `K u v w` as `t ∂ᵤΩ(y)(v, w)`, `X` as `Xₜ(y)`, `DX` as `∂ₓXₜ(y)`, `dα c w` as
`∂_c α(y)(w)` and `θ` as `Θ(y) = (Ω - Ω₀)(y)`. If `σ` is skew-symmetric, `K` satisfies the cocycle
identity `dΩₜ = 0`, `σ(X, ·) = -α` has been differentiated (`hβ`) and `dα = θ`, then the
derivative `θ + L_X σ` of `t ↦ Fₜ*Ωₜ` vanishes. -/
theorem moser_identity {σ θ dα : E → E → ℝ} {K : E → E → E → ℝ} {X : E} {DX : E → E}
    (hskew : ∀ a b, σ a b = -σ b a) (hclosed : ∀ u v w, K u v w - K v u w + K w u v = 0)
    (hβ : ∀ c w, K c X w + σ (DX c) w = -dα c w) (hdα : ∀ a b, dα a b - dα b a = θ a b)
    (a b : E) : θ a b + K X a b + σ (DX a) b + σ a (DX b) = 0 := by
  have h1 := hβ a b
  have h2 := hβ b a
  have h3 := hclosed X a b
  have h4 := hdα a b
  rw [hskew a (DX b)]
  linarith

/-- **Time-dependent flows near a stationary point, up to time `1`.** Let `X : W → E` be smooth on
an open set `W ⊆ ℝ × E` of a Banach space, and `p` a stationary point: `(t, p) ∈ W` and
`Xₜ(p) = 0` for all `t`. Then there are `δ > 0`, an open `V ∋ p` and a map `F`, smooth on
`(-δ, 1 + δ) × V`, with `F(t, p) = p`, `F(0, x) = x`, `(t, F(t, x)) ∈ W` and
`∂ₜF(t, x) = X(t, F(t, x))`. If moreover `X` is **real analytic** on `W`, then `F` is real
analytic on `(-δ, 1 + δ) × V`, and so is a left inverse `G` of `F(1, ·)` on its image, namely
`G(y) = Fl(-1, (1, y))` for the maximal flow `Fl` of `(1, X)`.

The proof makes the field autonomous on the manifold `W` (`Z = (1, X)`), and uses the openness of
the domain of its maximal flow (`SmoothVectorField.isOpen_flowDomain`) around the compact set
`[-1, 2] × {(0, p)}` (tube lemma), and the smoothness of the maximal flow; its real analyticity
is `SmoothVectorField.realAnalyticMOn_flow`. -/
theorem exists_flow_of_stationary [CompleteSpace E] {W : Set (ℝ × E)} (hW : IsOpen W)
    {Xf : ℝ × E → E} (hX : ContDiffOn ℝ ∞ Xf W) {p : E} (hpW : ∀ t : ℝ, (t, p) ∈ W)
    (hXp : ∀ t : ℝ, Xf (t, p) = 0) :
    ∃ δ > (0 : ℝ), ∃ V : Set E, IsOpen V ∧ p ∈ V ∧ ∃ F : ℝ × E → E,
      ContDiffOn ℝ ∞ F (Ioo (-δ) (1 + δ) ×ˢ V) ∧ (∀ t ∈ Ioo (-δ) (1 + δ), F (t, p) = p) ∧
      (∀ x ∈ V, F (0, x) = x ∧ ∀ t ∈ Ioo (-δ) (1 + δ),
        (t, F (t, x)) ∈ W ∧ HasDerivAt (fun s ↦ F (s, x)) (Xf (t, F (t, x))) t) ∧
      (RealAnalyticOn Xf W → RealAnalyticOn F (Ioo (-δ) (1 + δ) ×ˢ V) ∧
        ∃ G : E → E, RealAnalyticOn G (F '' ({1} ×ˢ V)) ∧ ∀ x ∈ V, G (F (1, x)) = x) := by
  classical
  set Wo : Opens (ℝ × E) := ⟨W, hW⟩ with hWo
  set Z : ℝ × E → ℝ × E := fun q ↦ ((1 : ℝ), Xf q) with hZdef
  have hZ : SmoothMBOn Z Wo := (smoothMBOn_iff_contDiffOn hW).2 (contDiffOn_const.prodMk hX)
  set X := SmoothVectorField.ofOpens Wo Z hZ with hXdef
  -- integral curves of `X`, read in `ℝ × E`
  have hval : ∀ (i : atlas (ℝ × E) Wo) (c : ℝ → Wo), i.1 ∘ c = fun s ↦ (c s : ℝ × E) :=
    fun i c ↦ funext fun s ↦ opens_atlas_apply i.2 (c s)
  have hrep : ∀ (i : atlas (ℝ × E) Wo) (z : Wo), X.rep i (i.1 z) = Z z := fun i z ↦ by
    rw [opens_atlas_apply i.2 z]
    exact SmoothVectorField.rep_ofOpens Wo Z hZ i z.2
  have hcurve : ∀ (c : ℝ → Wo) (I : Set ℝ), X.IsIntegralCurveOn c I → ∀ t ∈ I,
      HasDerivAt (fun s ↦ (c s : ℝ × E)) (Z (c t)) t := fun c I hc t ht ↦ by
    have h := (hc t ht).2 (prefChart (c t)) (mem_chart_source _ _)
    rwa [hval, hrep] at h
  -- the stationary curve through `(0, p)`
  set c₀ : ℝ → Wo := fun τ ↦ ⟨(τ, p), hpW τ⟩ with hc₀def
  have hc₀ : X.IsIntegralCurveThrough (c₀ 0) c₀ univ := by
    refine ⟨isOpen_univ, ordConnected_univ, mem_univ _, rfl, fun t _ ↦ ?_⟩
    refine ⟨((continuous_id.prodMk continuous_const).subtype_mk _).continuousAt,
      fun i _ ↦ ?_⟩
    rw [hval, hrep]
    have : HasDerivAt (fun s : ℝ ↦ (s, p)) ((1 : ℝ), (0 : E)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t p)
    simpa [hZdef, hc₀def, hXp] using this
  have hD₀ : ∀ τ : ℝ, (τ, c₀ 0) ∈ X.flowDomain := fun τ ↦ hc₀.subset_maxInterval (mem_univ τ)
  -- a uniform neighbourhood of `(0, p)` on which the flow is defined for `t ∈ [-1, 2]`
  have htube : Icc (-1 : ℝ) 2 ×ˢ {c₀ 0} ⊆ X.flowDomain := fun q hq ↦ by
    rw [show q = (q.1, c₀ 0) from Prod.ext rfl hq.2]; exact hD₀ q.1
  obtain ⟨u, v, hu, hv, hsu, htv, huv⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton X.isOpen_flowDomain htube
  obtain ⟨v', hv', hvv'⟩ := isOpen_induced_iff.1 hv
  set V : Set E := (fun x : E ↦ ((0 : ℝ), x)) ⁻¹' (W ∩ v') with hVdef
  have hVo : IsOpen V := (hW.inter hv').preimage (continuous_const.prodMk continuous_id)
  have hpV : p ∈ V := ⟨hpW 0, by
    have : c₀ 0 ∈ v := htv (mem_singleton _)
    rw [← hvv'] at this; exact this⟩
  set F : ℝ × E → E := fun q ↦
    if h : ((0 : ℝ), q.2) ∈ W then (X.flow (q.1, ⟨((0 : ℝ), q.2), h⟩) : ℝ × E).2 else q.2
    with hFdef
  set I := Ioo (-(1 / 2 : ℝ)) (1 + 1 / 2) with hIdef
  have hIu : I ⊆ u := fun t ht ↦ hsu ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- the curves `t ↦ Fl(t, (0, x))`
  have hmemD : ∀ x (hx : x ∈ V), ∀ t ∈ I,
      (t, (⟨((0 : ℝ), x), hx.1⟩ : Wo)) ∈ X.flowDomain := by
    intro x hx t ht
    refine huv ⟨hIu ht, ?_⟩
    rw [← hvv']; exact hx.2
  have hcx : ∀ x (hx : x ∈ V), ∀ t ∈ X.maxInterval ⟨((0 : ℝ), x), hx.1⟩,
      HasDerivAt (fun s ↦ (X.flow (s, ⟨((0 : ℝ), x), hx.1⟩) : ℝ × E))
        (Z (X.flow (t, ⟨((0 : ℝ), x), hx.1⟩))) t :=
    fun x hx t ht ↦ hcurve _ _ (X.isIntegralCurveOn_flow _) t ht
  -- along these curves the time coordinate is `t`
  have hfst : ∀ x (hx : x ∈ V), ∀ t ∈ X.maxInterval ⟨((0 : ℝ), x), hx.1⟩,
      (X.flow (t, ⟨((0 : ℝ), x), hx.1⟩) : ℝ × E).1 = t := by
    intro x hx t ht
    have hd : ∀ s ∈ X.maxInterval ⟨((0 : ℝ), x), hx.1⟩, HasDerivAt
        (fun s ↦ (X.flow (s, ⟨((0 : ℝ), x), hx.1⟩) : ℝ × E).1 - s) 0 s := fun s hs ↦ by
      have h1 : HasDerivAt (fun s ↦ (X.flow (s, ⟨((0 : ℝ), x), hx.1⟩) : ℝ × E).1) 1 s := by
        have := hasFDerivAt_fst.comp_hasDerivAt s (hcx x hx s hs)
        convert this using 1
        · rfl
        · simp [hZdef]
      exact (h1.sub (hasDerivAt_id s)).congr_deriv (sub_self _)
    have hc := (X.isOpen_maxInterval _).is_const_of_deriv_eq_zero
      (X.ordConnected_maxInterval _).isPreconnected
      (fun s hs ↦ (hd s hs).differentiableAt.differentiableWithinAt)
      (fun s hs ↦ (hd s hs).deriv) ht (X.zero_mem_maxInterval _)
    simp only [X.flow_zero, sub_zero] at hc
    linarith
  have hFeq : ∀ x (hx : x ∈ V) (t : ℝ),
      F (t, x) = (X.flow (t, ⟨((0 : ℝ), x), hx.1⟩) : ℝ × E).2 := fun x hx t ↦ by
    have h0 : ((0 : ℝ), x) ∈ W := hx.1
    simp only [hFdef, h0, ↓reduceDIte]
  have hFW : ∀ x (hx : x ∈ V), ∀ t ∈ I, (t, F (t, x)) ∈ W := fun x hx t ht ↦ by
    have e : (t, F (t, x)) = (X.flow (t, ⟨((0 : ℝ), x), hx.1⟩) : ℝ × E) :=
      Prod.ext (hfst x hx t (hmemD x hx t ht)).symm (hFeq x hx t)
    rw [e]; exact (X.flow (t, ⟨((0 : ℝ), x), hx.1⟩)).2
  -- smoothness, from the smoothness of the maximal flow in the chart `id × i`
  set i : atlas (ℝ × E) Wo := prefChart (c₀ 0) with hidef
  set Φ : ℝ × (ℝ × E) → ℝ × E := i.1 ∘ X.flow ∘ (prodAtlas i).1.symm with hΦdef
  set Dom := chartDomain X.flow X.flowDomain (prodAtlas i).1 i.1 with hDomdef
  have hDom : IsOpen Dom :=
    isOpen_chartDomain X.isOpen_flowDomain (X.smoothMBMOn_flow 0).continuousOn _ _
  have hΦ : ContDiffOn ℝ ∞ Φ Dom := (smoothMBOn_iff_contDiffOn hDom).1 fun k ↦
    (X.smoothMBMOn_flow k).contDiffMBOn_chart X.isOpen_flowDomain (prodAtlas i).2 i.2
  have hsymm : ∀ (t : ℝ) (y : ℝ × E) (hy : y ∈ W),
      (prodAtlas i).1.symm (t, y) = (t, (⟨y, hy⟩ : Wo)) := fun t y hy ↦ by
    change ((OpenPartialHomeomorph.refl ℝ).prod i.1).symm (t, y) = _
    rw [OpenPartialHomeomorph.prod_symm, OpenPartialHomeomorph.prod_apply]
    exact Prod.ext rfl (Subtype.ext (opens_atlas_symm i.2 hy))
  have hmemDom : ∀ q ∈ I ×ˢ V, (q.1, ((0 : ℝ), q.2)) ∈ Dom := fun q hq ↦ by
    refine ⟨?_, ?_, ?_⟩
    · rw [prodAtlas_target, opens_atlas_target i.2]; exact ⟨mem_univ _, hq.2.1⟩
    · rw [hsymm _ _ hq.2.1]; exact hmemD q.2 hq.2 q.1 hq.1
    · rw [opens_atlas_source i.2]; exact mem_univ _
  have hΦF : ∀ q ∈ I ×ˢ V, F q = (Φ (q.1, ((0 : ℝ), q.2))).2 := fun q hq ↦ by
    rw [hFeq q.2 hq.2 q.1, hΦdef, comp_apply, comp_apply, hsymm _ _ hq.2.1,
      opens_atlas_apply i.2]
  -- real analyticity, from the real analyticity of the maximal flow (`Flow/Analytic.lean`)
  have hanalytic : RealAnalyticOn Xf W → RealAnalyticOn F (I ×ˢ V) ∧
      ∃ G : E → E, RealAnalyticOn G (F '' ({1} ×ˢ V)) ∧ ∀ x ∈ V, G (F (1, x)) = x := by
    intro hXa
    have hI1 : (1 : ℝ) ∈ I := ⟨by norm_num, by norm_num⟩
    have hZa : RealAnalyticOn Z W :=
      (realAnalyticOn_const (1 : ℝ) W).prodMk hXa
    have hXω : X.IsRealAnalytic := fun j ↦ by
      rw [opens_atlas_target j.2]
      exact realAnalyticOn_congr (fun y hy ↦ (SmoothVectorField.rep_ofOpens Wo Z hZ j hy).symm)
        hZa
    have hΦa : RealAnalyticOn Φ Dom :=
      (X.realAnalyticMOn_flow hXω).realAnalyticOn_chart X.isOpen_flowDomain
        ((realAnalyticGroupoid _).subset_maximalAtlas (prodAtlas i).2)
        ((realAnalyticGroupoid _).subset_maximalAtlas i.2)
    -- the backward map `y ↦ Fl(-1, (1, y))`
    set G : E → E := fun y ↦ (Φ ((-1 : ℝ), ((1 : ℝ), y))).2 with hGdef
    have hFΦ : ∀ x ∈ V, (Φ ((1 : ℝ), ((0 : ℝ), x))) = ((1 : ℝ), F (1, x)) := fun x hx ↦ by
      have hfl := hfst x hx 1 (hmemD x hx 1 hI1)
      rw [hΦF (1, x) ⟨hI1, hx⟩]
      refine Prod.ext ?_ rfl
      rw [hΦdef, comp_apply, comp_apply, hsymm _ _ hx.1, opens_atlas_apply i.2]
      exact hfl
    have hmemDom' : ∀ x ∈ V, ((-1 : ℝ), ((1 : ℝ), F (1, x))) ∈ Dom ∧
        G (F (1, x)) = x := by
      intro x hx
      set z : Wo := ⟨((0 : ℝ), x), hx.1⟩
      have h1 : ((1 : ℝ), z) ∈ X.flowDomain := hmemD x hx 1 hI1
      have h0 : (((-1 : ℝ) + 1), z) ∈ X.flowDomain := by
        norm_num; exact X.zero_mem_flowDomain z
      have hz1 : (X.flow ((1 : ℝ), z) : ℝ × E) = ((1 : ℝ), F (1, x)) :=
        Prod.ext (hfst x hx 1 h1) (hFeq x hx 1).symm
      have hW1 : ((1 : ℝ), F (1, x)) ∈ W := by rw [← hz1]; exact (X.flow (1, z)).2
      have hz1' : X.flow ((1 : ℝ), z) = ⟨((1 : ℝ), F (1, x)), hW1⟩ := Subtype.ext hz1
      have hback : ((-1 : ℝ), X.flow ((1 : ℝ), z)) ∈ X.flowDomain :=
        (X.mem_flowDomain_flow_iff h1).2 h0
      rw [hz1'] at hback
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · rw [prodAtlas_target, opens_atlas_target i.2]; exact ⟨mem_univ _, hW1⟩
      · rw [hsymm _ _ hW1]; exact hback
      · rw [opens_atlas_source i.2]; exact mem_univ _
      · have hflow := X.flow_add h1 (by rw [hz1']; exact hback)
        rw [hz1'] at hflow
        simp only [hGdef, hΦdef, comp_apply]
        rw [hsymm _ _ hW1, ← hflow, show (-1 : ℝ) + 1 = 0 by norm_num, X.flow_zero,
          opens_atlas_apply i.2]
    refine ⟨?_, G, ?_, fun x hx ↦ (hmemDom' x hx).2⟩
    · have hin : RealAnalyticOn (fun q : ℝ × E ↦ (q.1, ((0 : ℝ), q.2))) (I ×ˢ V) :=
        ((ContinuousLinearMap.fst ℝ ℝ E).prod
          ((0 : ℝ × E →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ E))).realAnalyticOn _
      have h := ((ContinuousLinearMap.snd ℝ ℝ E).realAnalyticOn _).comp
        (hΦa.comp hin hmemDom) (mapsTo_univ _ _)
      exact realAnalyticOn_congr (fun q hq ↦ (hΦF q hq).symm) h
    · have hin : RealAnalyticOn (fun y : E ↦ ((-1 : ℝ), ((1 : ℝ), y))) (F '' ({1} ×ˢ V)) :=
        (realAnalyticOn_const (-1 : ℝ) _).prodMk
          ((realAnalyticOn_const (1 : ℝ) _).prodMk ((ContinuousLinearMap.id ℝ E).realAnalyticOn _))
      have hmaps : MapsTo (fun y : E ↦ ((-1 : ℝ), ((1 : ℝ), y))) (F '' ({1} ×ˢ V)) Dom := by
        rintro _ ⟨q, ⟨hq1, hqV⟩, rfl⟩
        rw [mem_singleton_iff] at hq1
        obtain ⟨t, x⟩ := q
        simp only at hq1 hqV
        subst hq1
        exact (hmemDom' x hqV).1
      exact ((ContinuousLinearMap.snd ℝ ℝ E).realAnalyticOn _).comp (hΦa.comp hin hmaps)
        (mapsTo_univ _ _)
  refine ⟨1 / 2, by norm_num, V, hVo, hpV, F, ?_, ?_,
    fun x hx ↦ ⟨?_, fun t ht ↦ ⟨hFW x hx t ht, ?_⟩⟩, hanalytic⟩
  · have hin : ContDiffOn ℝ ∞ (fun q : ℝ × E ↦ (q.1, ((0 : ℝ), q.2))) (I ×ˢ V) :=
      contDiffOn_fst.prodMk (contDiffOn_const.prodMk contDiffOn_snd)
    exact ((contDiffOn_snd.comp hΦ (mapsTo_univ _ _)).comp hin hmemDom).congr hΦF
  · intro t ht
    rw [hFeq p hpV t]
    have := hc₀.flow_eq (mem_univ t)
    rw [this]
  · rw [hFeq x hx 0, X.flow_zero]
  · have hJ : t ∈ X.maxInterval ⟨((0 : ℝ), x), hx.1⟩ := hmemD x hx t ht
    have h := (hasFDerivAt_snd.comp_hasDerivAt t (hcx x hx t hJ))
    have hfun : (fun s ↦ F (s, x)) = fun s ↦ (X.flow (s, ⟨((0 : ℝ), x), hx.1⟩) : ℝ × E).2 :=
      funext fun s ↦ hFeq x hx s
    rw [hfun]
    convert h using 1
    · rfl
    simp only [hZdef, ContinuousLinearMap.coe_snd']
    congr 1
    exact Prod.ext (hfst x hx t hJ).symm (hFeq x hx t)

/-- **A normalized primitive.** Let `Θ : B → L(E, D)`, `D ≃ E'`, be a smooth closed `2`-form on a
ball `B` around `p` with `Θ(p) = 0`. Then `Θ = dα` on `B` for a smooth `α : B → D` with
`α(p) = 0` and `dα(p) = 0`.

The primitive comes from the Poincaré lemma on the star-shaped manifold `B`
(`DifferentialForm.IsClosed.isExact_of_starConvex`, [GN26, Corollary 3.6.29]); it is
smooth for the operator norm by `contDiffMBOn_of_unc_clm`. Subtracting the affine form
`α(p) + dα(p)(y - p)`, which is closed because `Θ(p) = 0`, normalizes it. -/
theorem exists_primitive (ev : D ≃L[ℝ] (E →L[ℝ] ℝ)) {Θ : E → E →L[ℝ] D} {p : E} {r : ℝ}
    (hr : 0 < r) (hΘ : ContDiffOn ℝ ∞ Θ (ball p r))
    (hskew : ∀ y ∈ ball p r, ∀ a b, ev (Θ y a) b = -ev (Θ y b) a)
    (hclosed : ∀ y ∈ ball p r, ∀ u v w,
      ev (fderiv ℝ Θ y u v) w - ev (fderiv ℝ Θ y v u) w + ev (fderiv ℝ Θ y w u) v = 0)
    (hp : Θ p = 0) :
    ∃ α : E → D, ContDiffOn ℝ ∞ α (ball p r) ∧ α p = 0 ∧ fderiv ℝ α p = 0 ∧
      ∀ y ∈ ball p r, ∀ a b, ev (fderiv ℝ α y a) b - ev (fderiv ℝ α y b) a = ev (Θ y a) b := by
  classical
  set B : Opens E := ⟨ball p r, isOpen_ball⟩ with hBdef
  have hBo : IsOpen (B : Set E) := isOpen_ball
  have hpB : p ∈ (B : Set E) := mem_ball_self hr
  have hΘd : ∀ y ∈ (B : Set E), HasFDerivAt Θ (fderiv ℝ Θ y) y := fun y hy ↦
    ((hΘ.contDiffAt (hBo.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
  -- the local `2`-form `θ(y)(v₀, v₁) = ⟨Θ(y) v₀, v₁⟩`
  set θ : E × (Fin 2 → E) → ℝ := fun q ↦ ev (Θ q.1 (q.2 0)) (q.2 1) with hθdef
  have hθs : SmoothMBOn θ ((B : Set E) ×ˢ univ) := by
    refine (smoothMBOn_iff_contDiffOn (hBo.prod isOpen_univ)).2 ?_
    have h1 : ContDiffOn ℝ ∞ (fun q : E × (Fin 2 → E) ↦ Θ q.1) ((B : Set E) ×ˢ univ) :=
      hΘ.comp contDiffOn_fst fun q (hq : q ∈ (B : Set E) ×ˢ univ) ↦ hq.1
    have h2 : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun q : E × (Fin 2 → E) ↦ q.2 j)
        ((B : Set E) ×ˢ univ) := fun j ↦
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ E) j).contDiff.comp
        contDiff_snd).contDiffOn
    exact ((ev : D →L[ℝ] E →L[ℝ] ℝ).contDiff.comp_contDiffOn (h1.clm_apply (h2 0))).clm_apply
      (h2 1)
  have hdθ : ∀ y ∈ (B : Set E), ∀ (w : Fin 2 → E) (c : E),
      dMB (fun z ↦ θ (z, w)) (y, c) = ev (fderiv ℝ Θ y c (w 0)) (w 1) := fun y hy w c ↦ by
    have h : HasFDerivAt (fun z ↦ ev (Θ z (w 0)) (w 1))
        (((ev : D →L[ℝ] E →L[ℝ] ℝ).comp ((fderiv ℝ Θ y).flip (w 0))).flip (w 1)) y := by
      have := ((ev : D →L[ℝ] E →L[ℝ] ℝ).hasFDerivAt.comp y
        ((hΘd y hy).clm_apply (hasFDerivAt_const (w 0) y))).clm_apply (hasFDerivAt_const (w 1) y)
      simpa using this
    rw [(h.hasDirDerivAt c).dMB_eq]
    simp
  -- the closed `2`-form on the ball `B`
  have hrep2 : ∀ (i : atlas E B) (q : E × (Fin 2 → E)), q.1 ∈ (B : Set E) →
      formLocalRep 2 i (fun z v ↦ θ ((z : E), v)) q = θ q := fun i q hq ↦ by
    simp only [formLocalRep, tangentCoordChange_opens]
    rw [opens_atlas_symm i.2 hq]
  set ω₂ : DifferentialForm E B ℝ 2 :=
    { toFun := fun z v ↦ θ ((z : E), v)
      alternating' := fun z ↦ ⟨altOfSkew ((ev : D →L[ℝ] E →L[ℝ] ℝ).comp (Θ z))
        (fun a b ↦ hskew z z.2 a b), fun v ↦ rfl⟩
      smooth' := fun i k ↦ by
        rw [opens_atlas_target i.2]
        exact ContDiffMBOn.congr_of_isOpen (hBo.prod isOpen_univ)
          (fun q hq ↦ (hrep2 i q hq.1).symm) (hθs k) } with hω₂def
  have hω₂ : ω₂.IsClosed := fun x v ↦ by
    rw [DifferentialForm.d_apply, opens_atlas_apply (chart_mem_atlas E x) x]
    have hrepω : ∀ q : E × (Fin 2 → E), q.1 ∈ (B : Set E) →
        ω₂.localRep (prefChart x) q = θ q := hrep2 (prefChart x)
    rw [DifferentialForm.dLoc_congr (ω₂ := θ) hBo (fun q hq ↦ hrepω q hq.1) x.2]
    rw [IsLocalForm.dLoc_apply, Fin.sum_univ_three, hdθ _ x.2, hdθ _ x.2, hdθ _ x.2]
    have e0 : (Fin.removeNth 0 v) 0 = v 1 := rfl
    have e1 : (Fin.removeNth 0 v) 1 = v 2 := rfl
    have e2 : (Fin.removeNth 1 v) 0 = v 0 := rfl
    have e3 : (Fin.removeNth 1 v) 1 = v 2 := rfl
    have e4 : (Fin.removeNth 2 v) 0 = v 0 := rfl
    have e5 : (Fin.removeNth 2 v) 1 = v 1 := rfl
    rw [e0, e1, e2, e3, e4, e5]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, smul_eq_mul]
    linarith [hclosed x x.2 (v 0) (v 1) (v 2)]
  obtain ⟨η, hη⟩ := hω₂.isExact_of_starConvex (k := 1) hpB ((convex_ball p r).starConvex hpB)
  -- `η` as an operator-valued map `g : B → E'`
  have hvec : ∀ c : E, (![c] : Fin 1 → E) = fun _ ↦ c := fun c ↦ by
    funext j; fin_cases j; rfl
  have hupd : ∀ c : E, Function.update (![0] : Fin 1 → E) 0 c = ![c] := fun c ↦ by
    funext j; fin_cases j; simp
  have hL : ∀ z : B, ∃ L : E →L[ℝ] ℝ, ∀ c, L c = η z ![c] := fun z ↦ by
    obtain ⟨A, hA⟩ := η.alternating' z
    have hc : Continuous fun c : E ↦ η z ![c] := by
      have : (fun c : E ↦ η z ![c]) = (η z) ∘ fun c ↦ fun _ ↦ c := funext fun c ↦ by
        simp only [comp_apply, hvec]
      rw [this]
      exact (DifferentialForm.continuous_apply η z).comp (continuous_pi fun _ ↦ continuous_id)
    refine ⟨⟨⟨⟨fun c ↦ η z ![c], fun a b ↦ ?_⟩, fun c a ↦ ?_⟩, hc⟩, fun c ↦ rfl⟩
    · change η z ![a + b] = η z ![a] + η z ![b]
      rw [hA, hA, hA, ← hupd (a + b), ← hupd a, ← hupd b]
      exact A.map_update_add _ _ _ _
    · change η z ![c • a] = c • η z ![a]
      rw [hA, hA, ← hupd (c • a), ← hupd a]
      exact A.map_update_smul _ _ _ _
  set g : E → E →L[ℝ] ℝ := fun y ↦ if h : y ∈ (B : Set E) then (hL ⟨y, h⟩).choose else 0
    with hgdef
  have hg : ∀ y (hy : y ∈ (B : Set E)) (c : E), g y c = η ⟨y, hy⟩ ![c] := fun y hy c ↦ by
    simp only [hgdef, hy, ↓reduceDIte]; exact (hL ⟨y, hy⟩).choose_spec c
  set i₀ : atlas E B := prefChart (⟨p, hpB⟩ : B)
  have hrep1 : ∀ (i : atlas E B) (q : E × (Fin 1 → E)) (hq : q.1 ∈ (B : Set E)),
      η.localRep i q = η ⟨q.1, hq⟩ q.2 := fun i q hq ↦ by
    simp only [DifferentialForm.localRep, formLocalRep, tangentCoordChange_opens]
    congr 1
    exact Subtype.ext (opens_atlas_symm i.2 hq)
  have hunc : SmoothMBOn (fun q : E × E ↦ g q.1 q.2) ((B : Set E) ×ˢ univ) := fun k ↦ by
    set Lc : E × E →L[ℝ] E × (Fin 1 → E) := (ContinuousLinearMap.fst ℝ E E).prod
      (ContinuousLinearMap.pi fun _ : Fin 1 ↦ ContinuousLinearMap.snd ℝ E E)
    have h := ((η.isLocalForm_localRep i₀).smooth k).comp_clm Lc
      (i₀.1.open_target.prod isOpen_univ)
    rw [opens_atlas_target i₀.2] at h
    have hpre : Lc ⁻¹' ((B : Set E) ×ˢ univ) = (B : Set E) ×ˢ univ := by ext; simp [Lc]
    rw [hpre] at h
    refine ContDiffMBOn.congr_of_isOpen (hBo.prod isOpen_univ) (fun q hq ↦ ?_) h
    simp only [comp_apply, Lc, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst']
    rw [hrep1 i₀ _ hq.1, hg q.1 hq.1, hvec]
    rfl
  have hgs : ContDiffOn ℝ ∞ g (B : Set E) :=
    (smoothMBOn_iff_contDiffOn hBo).1 fun k ↦ contDiffMBOn_of_unc_clm k hBo (hunc (k + 1))
  have hgd : ∀ y ∈ (B : Set E), HasFDerivAt g (fderiv ℝ g y) y := fun y hy ↦
    ((hgs.contDiffAt (hBo.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
  -- `dη = θ`, in terms of `g`
  have hdg : ∀ y ∈ (B : Set E), ∀ a b : E,
      fderiv ℝ g y a b - fderiv ℝ g y b a = ev (Θ y a) b := fun y hy a b ↦ by
    have h := congrArg (fun β : DifferentialForm E B ℝ 2 ↦ β ⟨y, hy⟩ ![a, b]) hη
    change (η.d ⟨y, hy⟩ ![a, b]) = θ (y, ![a, b]) at h
    rw [DifferentialForm.d_apply, opens_atlas_apply (chart_mem_atlas E _) _] at h
    have hrepη : ∀ q : E × (Fin 1 → E), q.1 ∈ (B : Set E) →
        η.localRep (prefChart (⟨y, hy⟩ : B)) q = g q.1 (q.2 0) := fun q hq ↦ by
      rw [hrep1 _ q hq, hg q.1 hq]
      congr 1
      funext j; fin_cases j; rfl
    rw [DifferentialForm.dLoc_congr (ω₂ := fun q ↦ g q.1 (q.2 0)) hBo
      (fun q hq ↦ hrepη q hq.1) hy] at h
    have hdir : ∀ w c : E, dMB (fun z ↦ g z w) (y, c) = fderiv ℝ g y c w := fun w c ↦ by
      have h1 := (hgd y hy).clm_apply (hasFDerivAt_const w y)
      rw [(h1.hasDirDerivAt c).dMB_eq]
      simp
    rw [IsLocalForm.dLoc_apply, Fin.sum_univ_two] at h
    simp only [Fin.removeNth_apply] at h
    have e0 : (![a, b] : Fin 2 → E) (Fin.succAbove 0 0) = b := rfl
    have e1 : (![a, b] : Fin 2 → E) (Fin.succAbove 1 0) = a := rfl
    rw [e0, e1, hdir, hdir] at h
    simp only [hθdef] at h
    simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero, Matrix.cons_val_zero,
      smul_eq_mul, one_mul, Nat.mod_succ, pow_one, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      neg_mul] at h
    linarith
  -- normalization: subtract the closed affine form `g(p) + dg(p)(y - p)`
  set α : E → D := fun y ↦ ev.symm (g y - g p - fderiv ℝ g p (y - p)) with hαdef
  have hαd : ∀ y ∈ (B : Set E), ∀ c, fderiv ℝ α y c = ev.symm (fderiv ℝ g y c - fderiv ℝ g p c) :=
    fun y hy c ↦ by
      have h1 := ((hgd y hy).sub_const (g p)).sub
        ((fderiv ℝ g p).hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const p))
      have h2 : HasFDerivAt α (_ : E →L[ℝ] D) y :=
        (ev.symm : (E →L[ℝ] ℝ) →L[ℝ] D).hasFDerivAt.comp y h1
      rw [h2.fderiv]
      simp
  refine ⟨α, ?_, ?_, ?_, fun y hy a b ↦ ?_⟩
  · exact (ev.symm : (E →L[ℝ] ℝ) →L[ℝ] D).contDiff.comp_contDiffOn
      ((hgs.sub contDiffOn_const).sub
        ((fderiv ℝ g p).contDiff.comp (contDiff_id.sub contDiff_const)).contDiffOn)
  · simp [hαdef]
  · ext c
    rw [hαd p hpB c]
    simp
  · rw [hαd y hy, hαd y hy]
    simp only [ContinuousLinearEquiv.apply_symm_apply, sub_apply]
    have h1 := hdg y hy a b
    have h2 := hdg p hpB a b
    rw [hp] at h2
    simp only [zero_apply, map_zero] at h2
    linarith

/-- **Moser's method for a given primitive.** This is the local Darboux theorem
(`exists_darboux_local'`) for a prescribed primitive `α` of `Ω - Ω(p)` on a ball `B ⊆ U` around
`p`, normalized by `α(p) = 0` and `dα(p) = 0`. The map `ψ` is the time-`1` map of the Moser flow,
restricted to where its differential is invertible. If moreover `Ω : U → L(E, D)` and `α` are
**real analytic** (in the sense of Milnor, `LocallyConvex.Analysis.RealAnalyticOn`), then so are
`ψ` and `ψ⁻¹`: the Moser field `Xₜ = -Ωₜ⁻¹ α` is real analytic since inversion is
(`LocallyConvex.Analysis.realAnalyticOn_inverse`), its flow is real analytic
(`SmoothVectorField.realAnalyticMOn_flow`), and `ψ⁻¹` is the time-`(-1)` map of the suspended
flow started at time `1` (`exists_flow_of_stationary`), so no real analytic inverse function
theorem is needed. -/
theorem exists_darboux_local_of_primitive [CompleteSpace E] [CompleteSpace D]
    (ev : D ≃L[ℝ] (E →L[ℝ] ℝ))
    {Ω : E → E →L[ℝ] D} {U : Set E} (hU : IsOpen U) (hΩ : ContDiffOn ℝ ∞ Ω U)
    (hskew : ∀ y ∈ U, ∀ a b, ev (Ω y a) b = -ev (Ω y b) a)
    (hclosed : ∀ y ∈ U, ∀ u v w,
      ev (fderiv ℝ Ω y u v) w - ev (fderiv ℝ Ω y v u) w + ev (fderiv ℝ Ω y w u) v = 0)
    {p : E} (hp : p ∈ U) (hstrong : Bijective (Ω p)) {r : ℝ} (hr : 0 < r) (hrU : ball p r ⊆ U)
    {α : E → D} (hα : ContDiffOn ℝ ∞ α (ball p r)) (hαp : α p = 0) (hdαp : fderiv ℝ α p = 0)
    (hdα : ∀ y ∈ ball p r, ∀ a b,
      ev (fderiv ℝ α y a) b - ev (fderiv ℝ α y b) a = ev ((Ω y - Ω p) a) b) :
    ∃ ψ : OpenPartialHomeomorph E E, p ∈ ψ.source ∧ ψ p = p ∧
      fderiv ℝ ψ p = ContinuousLinearMap.id ℝ E ∧ ψ.source ⊆ U ∧ ψ.target ⊆ U ∧
      ContDiffOn ℝ ∞ ψ ψ.source ∧ ContDiffOn ℝ ∞ ψ.symm ψ.target ∧
      (∀ x ∈ ψ.source, ∀ u v,
        ev (Ω (ψ x) (fderiv ℝ ψ x u)) (fderiv ℝ ψ x v) = ev (Ω p u) v) ∧
      (RealAnalyticOn Ω U → RealAnalyticOn α (ball p r) →
        RealAnalyticOn ψ ψ.source ∧ RealAnalyticOn ψ.symm ψ.target) := by
  set B := ball p r with hBdef
  have hB : IsOpen B := isOpen_ball
  have hpB : p ∈ B := mem_ball_self hr
  have hΩd : ∀ y ∈ U, HasFDerivAt Ω (fderiv ℝ Ω y) y := fun y hy ↦
    ((hΩ.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
  -- the difference `Θ = Ω - Ω(p)`
  set Θ : E → E →L[ℝ] D := fun y ↦ Ω y - Ω p with hΘdef
  have hΘB : ContDiffOn ℝ ∞ Θ B := (hΩ.mono hrU).sub contDiffOn_const
  have hαd : ∀ y ∈ B, HasFDerivAt α (fderiv ℝ α y) y := fun y hy ↦
    ((hα.contDiffAt (hB.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
  -- the Moser family `Ωₜ = Ω(p) + t (Ω - Ω(p))` and its domain of invertibility
  set A : ℝ × E → E →L[ℝ] D := fun q ↦ Ω p + q.1 • Θ q.2 with hAdef
  have hA : ContDiffOn ℝ ∞ A (univ ×ˢ B) :=
    contDiffOn_const.add (contDiffOn_fst.smul
      (hΘB.comp contDiffOn_snd fun q (hq : q ∈ univ ×ˢ B) ↦ hq.2))
  set W : Set (ℝ × E) := (univ ×ˢ B) ∩ A ⁻¹' {L | L.IsInvertible} with hWdef
  have hW : IsOpen W := by
    refine hA.continuousOn.isOpen_inter_preimage (isOpen_univ.prod hB) ?_
    convert ContinuousLinearEquiv.isOpen (𝕜 := ℝ) (E := E) (F := D) using 1
    ext L
    exact ⟨fun ⟨e, he⟩ ↦ ⟨e, he⟩, fun ⟨e, he⟩ ↦ ⟨e, he⟩⟩
  have hAp : ∀ t : ℝ, A (t, p) = Ω p := fun t ↦ by simp [hAdef, hΘdef]
  have hΩp : (Ω p).IsInvertible :=
    ⟨ContinuousLinearEquiv.ofBijective (Ω p) (LinearMap.ker_eq_bot.2 hstrong.1)
      (LinearMap.range_eq_top.2 hstrong.2), ContinuousLinearEquiv.coe_ofBijective _ _ _⟩
  have hpW : ∀ t : ℝ, (t, p) ∈ W := fun t ↦ ⟨⟨mem_univ _, hpB⟩, by
    change (A (t, p)).IsInvertible
    rw [hAp]; exact hΩp⟩
  -- the time-dependent vector field `Xₜ`, defined by `Ωₜ(Xₜ, ·) = -α`
  set Xf : ℝ × E → E := fun q ↦ -(A q).inverse (α q.2) with hXfdef
  have hXf : ContDiffOn ℝ ∞ Xf W := fun q hq ↦ by
    have hqA : ContDiffAt ℝ ∞ A q :=
      hA.contDiffAt ((isOpen_univ.prod hB).mem_nhds hq.1)
    have hqα : ContDiffAt ℝ ∞ (fun q : ℝ × E ↦ α q.2) q :=
      (hα.contDiffAt (hB.mem_nhds hq.1.2)).comp q contDiffAt_snd
    exact ((((hq.2 : (A q).IsInvertible).contDiffAt_map_inverse).comp q hqA).clm_apply
      hqα).neg.contDiffWithinAt
  have hXp : ∀ t : ℝ, Xf (t, p) = 0 := fun t ↦ by simp [hXfdef, hαp]
  -- the flow of `Xₜ` up to time `1`
  obtain ⟨δ, hδ, V, hV, hpV, F, hF, hFp, hFx, hFa⟩ := exists_flow_of_stationary hW hXf hpW hXp
  set I := Ioo (-δ) (1 + δ) with hIdef
  have hI0 : (0 : ℝ) ∈ I := ⟨by linarith, by linarith⟩
  have hI1 : (1 : ℝ) ∈ I := ⟨by linarith, by linarith⟩
  have hO : IsOpen (I ×ˢ V) := isOpen_Ioo.prod hV
  have hVB : V ⊆ B := fun x hx ↦ by
    have h := ((hFx x hx).2 0 hI0).1.1.2
    rwa [(hFx x hx).1] at h
  have hFW : ∀ x ∈ V, ∀ t ∈ I, (t, F (t, x)) ∈ W := fun x hx t ht ↦ ((hFx x hx).2 t ht).1
  have hFd : ∀ q ∈ I ×ˢ V, ContDiffAt ℝ ∞ F q := fun q hq ↦ hF.contDiffAt (hO.mem_nhds hq)
  have hFD : ∀ q ∈ I ×ˢ V, HasFDerivAt F (fderiv ℝ F q) q := fun q hq ↦
    ((hFd q hq).differentiableAt (by simp)).hasFDerivAt
  have hXd : ∀ q ∈ W, HasFDerivAt Xf (fderiv ℝ Xf q) q := fun q hq ↦
    ((hXf.contDiffAt (hW.mem_nhds hq)).differentiableAt (by simp)).hasFDerivAt
  -- `∂ₜ F = X ∘ F`
  have hline : ∀ (t : ℝ) (x : E), HasDerivAt (fun s : ℝ ↦ (s, x)) ((1 : ℝ), (0 : E)) t :=
    fun t x ↦ (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  have hFt : ∀ q ∈ I ×ˢ V, fderiv ℝ F q (1, 0) = Xf (q.1, F q) := fun q hq ↦ by
    have h1 := (hFD q hq).comp_hasDerivAt q.1 (hline q.1 q.2)
    exact h1.unique ((hFx q.2 hq.2).2 q.1 hq.1).2
  -- derivatives in the space variable
  have hslice : ∀ q ∈ I ×ˢ V, HasFDerivAt (fun y ↦ F (q.1, y))
      ((fderiv ℝ F q).comp (ContinuousLinearMap.inr ℝ ℝ E)) q.2 := fun q hq ↦
    (hFD q hq).comp q.2 (hasFDerivAt_prodMk_right q.1 q.2)
  have hF0 : ∀ x ∈ V, ∀ u, fderiv ℝ F (0, x) (0, u) = u := fun x hx u ↦ by
    have h1 := hslice (0, x) ⟨hI0, hx⟩
    have h2 : HasFDerivAt (fun y ↦ F (0, y)) (ContinuousLinearMap.id ℝ E) x :=
      (hasFDerivAt_id x).congr_of_eventuallyEq
        (eventually_of_mem (hV.mem_nhds hx) fun y hy ↦ (hFx y hy).1)
    have := congrArg (fun L : E →L[ℝ] E ↦ L u) (h1.unique h2)
    simpa using this
  -- the variational equation `∂ₜ (∂ₓ F) = ∂ₓ X ∘ ∂ₓ F`
  have hvar : ∀ q ∈ I ×ˢ V, ∀ w : E, HasDerivAt (fun s ↦ fderiv ℝ F (s, q.2) (0, w))
      (fderiv ℝ Xf (q.1, F q) (0, fderiv ℝ F q (0, w))) q.1 := by
    rintro ⟨t, x⟩ hq w
    have hC := hFd _ hq
    have hsymm : IsSymmSndFDerivAt ℝ F (t, x) := hC.isSymmSndFDerivAt (by simp)
    have hdd : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) (t, x)) (t, x) :=
      ((hC.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)).hasFDerivAt
    have happ : ∀ v : ℝ × E, HasFDerivAt (fun q' ↦ fderiv ℝ F q' v)
        ((fderiv ℝ (fderiv ℝ F) (t, x)).flip v) (t, x) := fun v ↦ by
      have := hdd.clm_apply (hasFDerivAt_const v (t, x))
      simpa using this
    -- `∂ₜ` of `q' ↦ ∂F(q')(0, w)`
    have h1 : HasDerivAt (fun s ↦ fderiv ℝ F (s, x) (0, w))
        ((fderiv ℝ (fderiv ℝ F) (t, x)).flip (0, w) (1, 0)) t := by
      have := (happ (0, w)).comp_hasDerivAt t (hline t x)
      exact this
    -- `q' ↦ ∂F(q')(1, 0)` agrees with `q' ↦ X(q'.1, F q')` near `(t, x)`
    have hk : HasFDerivAt (fun q' : ℝ × E ↦ Xf (q'.1, F q'))
        ((fderiv ℝ Xf (t, F (t, x))).comp
          ((ContinuousLinearMap.fst ℝ ℝ E).prod (fderiv ℝ F (t, x)))) (t, x) :=
      (hXd _ (hFW x hq.2 t hq.1)).comp (f := fun q' : ℝ × E ↦ (q'.1, F q')) (t, x)
        (hasFDerivAt_fst.prodMk (hFD _ hq))
    have hev : (fun q' ↦ fderiv ℝ F q' (1, 0)) =ᶠ[𝓝 (t, x)] fun q' ↦ Xf (q'.1, F q') :=
      eventually_of_mem (hO.mem_nhds hq) fun q' hq' ↦ hFt q' hq'
    have h2 := (happ (1, 0)).unique (hk.congr_of_eventuallyEq hev)
    have h3 := congrArg (fun L : ℝ × E →L[ℝ] E ↦ L (0, w)) h2
    simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.coe_comp, comp_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst'] at h3
    convert h1 using 1
    rw [ContinuousLinearMap.flip_apply, hsymm (1, 0) (0, w)]
    exact h3.symm
  -- `Ωₜ(Xₜ, ·) = -α`, differentiated in the space variable
  have hβ : ∀ t y, (t, y) ∈ W → ∀ c w : E,
      t * ev (fderiv ℝ Ω y c (Xf (t, y))) w + ev (A (t, y) (fderiv ℝ Xf (t, y) (0, c))) w =
        -ev (fderiv ℝ α y c) w := by
    intro t y hq c w
    have hyB : y ∈ B := hq.1.2
    have hAy : HasFDerivAt (fun y' ↦ A (t, y')) (t • fderiv ℝ Ω y) y :=
      (((hΩd y (hrU hyB)).sub_const (Ω p)).const_smul t).const_add (Ω p)
    have hXy : HasFDerivAt (fun y' ↦ Xf (t, y'))
        ((fderiv ℝ Xf (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ E)) y :=
      (hXd _ hq).comp y (hasFDerivAt_prodMk_right t y)
    have hφ := hAy.clm_apply hXy
    have hev : (fun y' ↦ A (t, y') (Xf (t, y'))) =ᶠ[𝓝 y] fun y' ↦ -α y' := by
      have : ∀ᶠ y' in 𝓝 y, (t, y') ∈ W :=
        (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hW.mem_nhds hq)
      filter_upwards [this] with y' hy'
      have hinv : (A (t, y')).IsInvertible := hy'.2
      simp only [hXfdef, map_neg, hinv.self_apply_inverse]
    have h2 := hφ.unique (((hαd y hyB).neg).congr_of_eventuallyEq hev)
    have h3 := congrArg (fun L : E →L[ℝ] D ↦ ev (L c) w) h2
    simp only [add_apply, ContinuousLinearMap.coe_comp, comp_apply,
      ContinuousLinearMap.inr_apply, ContinuousLinearMap.flip_apply,
      smul_apply, neg_apply, map_add, map_smul,
      map_neg, smul_eq_mul] at h3
    linarith
  -- **Moser's computation**: `t ↦ (Fₜ* Ωₜ)ₓ(u, v)` has derivative `0`
  have hG : ∀ x ∈ V, ∀ u v : E, ∀ t ∈ I, HasDerivAt
      (fun s ↦ ev (A (s, F (s, x)) (fderiv ℝ F (s, x) (0, u))) (fderiv ℝ F (s, x) (0, v))) 0 t := by
    intro x hx u v t ht
    have hq : (t, F (t, x)) ∈ W := hFW x hx t ht
    have hyB : F (t, x) ∈ B := hq.1.2
    have hFl : HasDerivAt (fun s ↦ F (s, x)) (Xf (t, F (t, x))) t := ((hFx x hx).2 t ht).2
    have hΩt : HasDerivAt (fun s ↦ Ω (F (s, x))) (fderiv ℝ Ω (F (t, x)) (Xf (t, F (t, x)))) t :=
      (hΩd _ (hrU hyB)).comp_hasDerivAt t hFl
    have hAt : HasDerivAt (fun s ↦ A (s, F (s, x)))
        (t • fderiv ℝ Ω (F (t, x)) (Xf (t, F (t, x))) + (1 : ℝ) • (Ω (F (t, x)) - Ω p)) t :=
      ((hasDerivAt_id t).smul (hΩt.sub_const (Ω p))).const_add (Ω p)
    have hu := hvar (t, x) ⟨ht, hx⟩ u
    have hv := hvar (t, x) ⟨ht, hx⟩ v
    have h1 := hAt.clm_apply hu
    have h2 := ev.hasFDerivAt.comp_hasDerivAt t h1
    have h3 := h2.clm_apply hv
    refine h3.congr_deriv ?_
    have hm := moser_identity (σ := fun a b ↦ ev (A (t, F (t, x)) a) b)
      (θ := fun a b ↦ ev (Θ (F (t, x)) a) b)
      (dα := fun c w ↦ ev (fderiv ℝ α (F (t, x)) c) w)
      (K := fun u v w ↦ t * ev (fderiv ℝ Ω (F (t, x)) u v) w)
      (X := Xf (t, F (t, x))) (DX := fun c ↦ fderiv ℝ Xf (t, F (t, x)) (0, c))
      (fun a b ↦ by
        simp only [hAdef, hΘdef, add_apply, smul_apply, sub_apply, map_add, map_smul, map_sub,
          smul_eq_mul]
        rw [hskew p hp a b, hskew _ (hrU hyB) a b]; ring)
      (fun u v w ↦ by linear_combination t * hclosed _ (hrU hyB) u v w)
      (fun c w ↦ hβ t _ hq c w) (fun a b ↦ hdα _ hyB a b)
      (fderiv ℝ F (t, x) (0, u)) (fderiv ℝ F (t, x) (0, v))
    simp only [hΘdef] at hm
    simp only [add_apply, smul_apply, sub_apply, map_add, map_smul, map_sub, smul_eq_mul,
      comp_apply, one_mul, ContinuousLinearEquiv.coe_coe] at hm ⊢
    linarith
  have hIcc : Icc (0 : ℝ) 1 ⊆ I := fun t ht ↦ ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- hence `F₁* Ω = Ω(p)` on `V`
  have hpull : ∀ x ∈ V, ∀ u v : E,
      ev (Ω (F (1, x)) (fderiv ℝ F (1, x) (0, u))) (fderiv ℝ F (1, x) (0, v)) = ev (Ω p u) v := by
    intro x hx u v
    have hc := constant_of_has_deriv_right_zero
      (f := fun s ↦ ev (A (s, F (s, x)) (fderiv ℝ F (s, x) (0, u))) (fderiv ℝ F (s, x) (0, v)))
      (a := 0) (b := 1)
      (fun t ht ↦ (hG x hx u v t (hIcc ht)).continuousAt.continuousWithinAt)
      (fun t ht ↦ (hG x hx u v t (hIcc (Ico_subset_Icc_self ht))).hasDerivWithinAt) 1
      ⟨zero_le_one, le_rfl⟩
    simp only [hAdef, hΘdef, one_smul, add_sub_cancel, zero_smul, add_zero,
      (hFx x hx).1, hF0 x hx] at hc
    exact hc
  -- `∂ₓ X(t, p) = 0`, since `α(p) = 0` and `dα(p) = 0`
  have hDXp : ∀ t : ℝ, ∀ c : E, fderiv ℝ Xf (t, p) (0, c) = 0 := fun t c ↦ by
    have h : ev (A (t, p) (fderiv ℝ Xf (t, p) (0, c))) = 0 := by
      ext w
      have := hβ t p (hpW t) c w
      simp only [hXp, map_zero, hdαp, zero_apply, mul_zero,
        zero_add, neg_zero] at this
      simpa using this
    rw [map_eq_zero_iff _ ev.injective, hAp] at h
    exact (map_eq_zero_iff _ hstrong.1).1 h
  -- hence `∂ₓ F(t, p) = id`
  have hDp : ∀ u : E, fderiv ℝ F (1, p) (0, u) = u := fun u ↦ by
    have hc := constant_of_has_deriv_right_zero (f := fun s ↦ fderiv ℝ F (s, p) (0, u))
      (a := 0) (b := 1)
      (fun t ht ↦ (hvar (t, p) ⟨hIcc ht, hpV⟩ u).continuousAt.continuousWithinAt)
      (fun t ht ↦ by
        have h := hvar (t, p) ⟨hIcc (Ico_subset_Icc_self ht), hpV⟩ u
        simp only [hFp t (hIcc (Ico_subset_Icc_self ht)), hDXp] at h
        exact h.hasDerivWithinAt) 1 ⟨zero_le_one, le_rfl⟩
    rw [hc, hF0 p hpV]
  -- the inverse function theorem for `ψ = F₁`, restricted to where `dψ` is invertible
  set ψ : E → E := fun y ↦ F (1, y) with hψdef
  have hψd : ∀ x ∈ V, HasFDerivAt ψ ((fderiv ℝ F (1, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)) x :=
    fun x hx ↦ hslice (1, x) ⟨hI1, hx⟩
  have hψc : ContDiffOn ℝ ∞ ψ V :=
    hF.comp (contDiffOn_const.prodMk contDiffOn_id) fun y hy ↦ ⟨hI1, hy⟩
  have hψ1 : HasFDerivAt ψ ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) p := by
    convert hψd p hpV using 1
    ext u
    simp [hDp u]
  have hψa : ContDiffAt ℝ ∞ ψ p := hψc.contDiffAt (hV.mem_nhds hpV)
  set ψ₀ := hψa.toOpenPartialHomeomorph ψ hψ1 (by simp)
  set S : Set E := V ∩ (fun x ↦ fderiv ℝ ψ x) ⁻¹' {L | L.IsInvertible} with hSdef
  have hS : IsOpen S := by
    refine (hψc.continuousOn_fderiv_of_isOpen hV (by simp)).isOpen_inter_preimage hV ?_
    convert ContinuousLinearEquiv.isOpen (𝕜 := ℝ) (E := E) (F := E) using 1
    ext L
    exact ⟨fun ⟨e, he⟩ ↦ ⟨e, he⟩, fun ⟨e, he⟩ ↦ ⟨e, he⟩⟩
  have hpS : p ∈ S := ⟨hpV, by
    change (fderiv ℝ ψ p).IsInvertible
    rw [hψ1.fderiv]; exact ContinuousLinearMap.isInvertible_equiv⟩
  have hsrc : (ψ₀.restrOpen S hS).source ⊆ V := fun x hx ↦ by
    rw [OpenPartialHomeomorph.restrOpen_source] at hx; exact hx.2.1
  refine ⟨ψ₀.restrOpen S hS, ?_, hFp 1 hI1, ?_, fun x hx ↦ hrU (hVB (hsrc hx)), ?_, ?_, ?_, ?_,
    ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hψa.mem_toOpenPartialHomeomorph_source hψ1 (by simp), hpS⟩
  · rw [OpenPartialHomeomorph.coe_restrOpen]
    exact hψ1.fderiv
  · intro z hz
    have hx := (ψ₀.restrOpen S hS).map_target hz
    rw [← (ψ₀.restrOpen S hS).right_inv hz]
    exact hrU (hFW _ (hsrc hx) 1 hI1).1.2
  · exact hψc.mono hsrc
  · intro z hz
    have hx := (ψ₀.restrOpen S hS).map_target hz
    have hxS : (ψ₀.restrOpen S hS).symm z ∈ S := by
      rw [OpenPartialHomeomorph.restrOpen_source] at hx; exact hx.2
    obtain ⟨e, he⟩ := hxS.2
    refine ((ψ₀.restrOpen S hS).contDiffAt_symm hz (f₀' := e) ?_ ?_).contDiffWithinAt
    · rw [he]
      exact ((hψd _ hxS.1).differentiableAt).hasFDerivAt
    · exact hψc.contDiffAt (hV.mem_nhds hxS.1)
  · intro x hx u v
    have hxV := hsrc hx
    have hd := (hψd x hxV).fderiv
    rw [OpenPartialHomeomorph.coe_restrOpen]
    change ev (Ω (ψ x) (fderiv ℝ ψ x u)) (fderiv ℝ ψ x v) = _
    rw [hd]
    exact hpull x hxV u v
  · -- real analyticity
    intro hΩa hαa
    obtain ⟨e, he⟩ := hΩp
    set L : (E →L[ℝ] D) →L[ℝ] (E →L[ℝ] E) :=
      ContinuousLinearMap.compL ℝ E D E (e.symm : D →L[ℝ] E) with hLdef
    have hΘa : RealAnalyticOn Θ B := (hΩa.mono hrU).sub (realAnalyticOn_const _ _)
    have hAa : RealAnalyticOn A (univ ×ˢ B) := by
      have h1 : RealAnalyticOn (fun q : ℝ × E ↦ Θ q.2) (univ ×ˢ B) :=
        hΘa.comp ((ContinuousLinearMap.snd ℝ ℝ E).realAnalyticOn _) fun q hq ↦ hq.2
      have h2 := RealAnalyticOn.bilin (LinearMap.lsmul ℝ (E →L[ℝ] D))
        (continuous_fst.smul continuous_snd) ((ContinuousLinearMap.fst ℝ ℝ E).realAnalyticOn _) h1
      exact (realAnalyticOn_const (Ω p) _).add h2
    have hunit : ∀ q ∈ W, IsUnit (L (A q)) := fun q hq ↦ by
      obtain ⟨f, hf⟩ := (hq.2 : (A q).IsInvertible)
      refine ⟨(ContinuousLinearEquiv.unitsEquiv ℝ E).symm (f.trans e.symm), ?_⟩
      ext v
      simp only [hLdef, ← hf, ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe]
      rfl
    have hR : RealAnalyticOn (fun q ↦ Ring.inverse (L (A q))) W :=
      realAnalyticOn_inverse.comp ((hAa.clm_comp L).mono fun q hq ↦ hq.1) hunit
    have hα2 : RealAnalyticOn (fun q : ℝ × E ↦ (e.symm : D →L[ℝ] E) (α q.2)) W :=
      ((hαa.comp ((ContinuousLinearMap.snd ℝ ℝ E).realAnalyticOn _)
        fun q (hq : q ∈ W) ↦ hq.1.2).clm_comp
        (e.symm : D →L[ℝ] E))
    have hXa : RealAnalyticOn Xf W := by
      refine realAnalyticOn_congr (fun q _ ↦ ?_)
        (RealAnalyticOn.bilin (ContinuousLinearMap.coeLM ℝ : (E →L[ℝ] E) →ₗ[ℝ] E →ₗ[ℝ] E)
          (continuous_fst.clm_apply continuous_snd) hR hα2).neg
      simp only [hXfdef, ContinuousLinearMap.inverse_eq_ringInverse e (A q), hLdef,
        ContinuousLinearMap.coeLM_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.compL_apply]
      rfl
    obtain ⟨hFan, G, hGa, hGF⟩ := hFa hXa
    have hψan : RealAnalyticOn ψ V :=
      hFan.comp ((realAnalyticOn_const (1 : ℝ) V).prodMk
        ((ContinuousLinearMap.id ℝ E).realAnalyticOn V)) fun y hy ↦ ⟨hI1, hy⟩
    refine ⟨hψan.mono hsrc, realAnalyticOn_congr (fun z hz ↦ ?_) (hGa.mono fun z hz ↦ ?_)⟩
    · have hx := (ψ₀.restrOpen S hS).map_target hz
      have hz' := (ψ₀.restrOpen S hS).right_inv hz
      rw [OpenPartialHomeomorph.coe_restrOpen] at hz'
      conv_lhs => rw [← hz']
      exact hGF _ (hsrc hx)
    · have hx := (ψ₀.restrOpen S hS).map_target hz
      have hz' := (ψ₀.restrOpen S hS).right_inv hz
      rw [OpenPartialHomeomorph.coe_restrOpen] at hz'
      exact ⟨(1, (ψ₀.restrOpen S hS).symm z), ⟨rfl, hsrc hx⟩, hz'⟩

/-- **The local Darboux theorem**, for forms with values in `L(E, D)`, `D ≃ E'` (see
`exists_darboux_local` for `D = E'`). Let `E` be a Banach space, `U ⊆ E` open and `Ω : U → L(E, D)`
smooth, with `Ω(y)` skew-symmetric, `dΩ = 0` on `U`, and `Ω(p)` bijective for one `p ∈ U`. Then
there is a diffeomorphism `ψ` between open subsets of `U`, with `p` in its domain, `ψ(p) = p`,
`dψ(p) = id`, and `ψ*Ω = Ω(p)`. The primitive of `Ω - Ω(p)` comes from the Poincaré lemma
(`exists_primitive`), and the rest is `exists_darboux_local_of_primitive`. -/
theorem exists_darboux_local' [CompleteSpace E] [CompleteSpace D] (ev : D ≃L[ℝ] (E →L[ℝ] ℝ))
    {Ω : E → E →L[ℝ] D} {U : Set E} (hU : IsOpen U) (hΩ : ContDiffOn ℝ ∞ Ω U)
    (hskew : ∀ y ∈ U, ∀ a b, ev (Ω y a) b = -ev (Ω y b) a)
    (hclosed : ∀ y ∈ U, ∀ u v w,
      ev (fderiv ℝ Ω y u v) w - ev (fderiv ℝ Ω y v u) w + ev (fderiv ℝ Ω y w u) v = 0)
    {p : E} (hp : p ∈ U) (hstrong : Bijective (Ω p)) :
    ∃ ψ : OpenPartialHomeomorph E E, p ∈ ψ.source ∧ ψ p = p ∧
      fderiv ℝ ψ p = ContinuousLinearMap.id ℝ E ∧ ψ.source ⊆ U ∧ ψ.target ⊆ U ∧
      ContDiffOn ℝ ∞ ψ ψ.source ∧ ContDiffOn ℝ ∞ ψ.symm ψ.target ∧
      ∀ x ∈ ψ.source, ∀ u v,
        ev (Ω (ψ x) (fderiv ℝ ψ x u)) (fderiv ℝ ψ x v) = ev (Ω p u) v := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU p hp
  have hΩd : ∀ y ∈ U, HasFDerivAt Ω (fderiv ℝ Ω y) y := fun y hy ↦
    ((hΩ.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
  have hfdΘ : ∀ y ∈ ball p r, fderiv ℝ (fun y ↦ Ω y - Ω p) y = fderiv ℝ Ω y := fun y hy ↦
    ((hΩd y (hrU hy)).sub_const (Ω p)).fderiv
  obtain ⟨α, hα, hαp, hdαp, hdα⟩ := exists_primitive ev hr
    (Θ := fun y ↦ Ω y - Ω p) ((hΩ.mono hrU).sub contDiffOn_const)
    (fun y hy a b ↦ by
      simp only [sub_apply, map_sub]
      rw [hskew y (hrU hy) a b, hskew p hp a b]; ring)
    (fun y hy u v w ↦ by rw [hfdΘ y hy]; exact hclosed y (hrU hy) u v w)
    (by simp)
  obtain ⟨ψ, h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := exists_darboux_local_of_primitive ev hU hΩ hskew
    hclosed hp hstrong hr hrU hα hαp hdαp hdα
  exact ⟨ψ, h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- **The local Darboux theorem** ([Wei69, §1, Theorem]; [Lan99, Theorem V.8.1]). Let `E` be a
Banach space, `U ⊆ E` open and `Ω : U → L(E, L(E, ℝ))` smooth for the operator norm, with
`Ω(y)` skew-symmetric and closed: `∂ᵤΩ(v, w) - ∂ᵥΩ(u, w) + ∂_wΩ(u, v) = 0`. If `Ω(p)` is
**strongly nondegenerate** (`Ω(p) : E → E'` is bijective), there is a diffeomorphism `ψ` between
open neighbourhoods of `p` in `U` with `ψ(p) = p`, `dψ(p) = id` and
`Ω(ψ x)(dψ(x) u, dψ(x) v) = Ω(p)(u, v)`: in the coordinates given by `ψ`, `Ω` is constant. -/
theorem exists_darboux_local [CompleteSpace E] {Ω : E → E →L[ℝ] E →L[ℝ] ℝ} {U : Set E}
    (hU : IsOpen U) (hΩ : ContDiffOn ℝ ∞ Ω U) (hskew : ∀ y ∈ U, ∀ a b, Ω y a b = -Ω y b a)
    (hclosed : ∀ y ∈ U, ∀ u v w,
      fderiv ℝ Ω y u v w - fderiv ℝ Ω y v u w + fderiv ℝ Ω y w u v = 0)
    {p : E} (hp : p ∈ U) (hstrong : Bijective (Ω p)) :
    ∃ ψ : OpenPartialHomeomorph E E, p ∈ ψ.source ∧ ψ p = p ∧
      fderiv ℝ ψ p = ContinuousLinearMap.id ℝ E ∧ ψ.source ⊆ U ∧ ψ.target ⊆ U ∧
      ContDiffOn ℝ ∞ ψ ψ.source ∧ ContDiffOn ℝ ∞ ψ.symm ψ.target ∧
      ∀ x ∈ ψ.source, ∀ u v, Ω (ψ x) (fderiv ℝ ψ x u) (fderiv ℝ ψ x v) = Ω p u v :=
  exists_darboux_local' (ContinuousLinearEquiv.refl ℝ (E →L[ℝ] ℝ)) hU hΩ hskew hclosed hp hstrong

end Darboux

/-! ### Darboux charts on Banach manifolds -/

section Manifold

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

/-- A continuous alternating `2`-form on a normed space, as a continuous bilinear map (compare
`SymplecticForm.flatCLM`). -/
def clm₂OfAlternating (A : E [⋀^Fin 2]→ₗ[ℝ] ℝ) (hA : Continuous A) : E →L[ℝ] E →L[ℝ] ℝ :=
  let C : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ E) ℝ :=
    { toMultilinearMap := A.toMultilinearMap, cont := hA }
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun v w ↦ A ![v, w])
      (fun v v' w ↦ by
        have := A.map_update_add ![v, w] 0 v v'
        convert this using 2 <;> (congr 1; funext k; fin_cases k <;> rfl))
      (fun c v w ↦ by
        have := A.map_update_smul ![v, w] 0 c v
        convert this using 2 <;> (congr 1; funext k; fin_cases k <;> rfl))
      (fun v w w' ↦ by
        have := A.map_update_add ![v, w] 1 w w'
        convert this using 2 <;> (congr 1; funext k; fin_cases k <;> rfl))
      (fun c v w ↦ by
        have := A.map_update_smul ![v, w] 1 c w
        convert this using 2 <;> (congr 1; funext k; fin_cases k <;> rfl)))
    ‖C‖ (fun v w ↦ by
      change ‖C ![v, w]‖ ≤ ‖C‖ * ‖v‖ * ‖w‖
      calc ‖C ![v, w]‖ ≤ ‖C‖ * ∏ i, ‖(![v, w] : Fin 2 → E) i‖ := C.le_opNorm _
        _ = ‖C‖ * ‖v‖ * ‖w‖ := by simp [Fin.prod_univ_two, mul_assoc])

theorem clm₂OfAlternating_apply (A : E [⋀^Fin 2]→ₗ[ℝ] ℝ) (hA : Continuous A) (v w : E) :
    clm₂OfAlternating A hA v w = A ![v, w] :=
  rfl

/-- **A `2`-form in a chart, as an operator-valued map.** On a manifold modeled on a normed space,
the local representative of a `2`-form in the preferred chart at `x₀` is a smooth map
`Ω : i(U) → L(E, E')` for the operator norm (lc-analysis, `contDiffMBOn_of_unc_clm`, twice). -/
theorem DifferentialForm.exists_clm_localRep (ω : DifferentialForm E M ℝ 2) (x₀ : M) :
    ∃ Ω : E → E →L[ℝ] E →L[ℝ] ℝ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ω (chartAt E x₀).target ∧
      ∀ y ∈ (chartAt E x₀).target, ∀ a b, Ω y a b = ω.localRep (prefChart x₀) (y, ![a, b]) := by
  classical
  set i : atlas E M := prefChart x₀ with hidef
  have hT : IsOpen i.1.target := i.1.open_target
  have hωl : IsLocalForm 2 (ω.localRep i) i.1.target := ω.isLocalForm_localRep i
  have hcont : ∀ y ∈ i.1.target, Continuous fun v ↦ ω.localRep i (y, v) := fun y hy ↦ by
    have h := (hωl.smooth 0).continuousOn
    refine continuous_iff_continuousAt.2 fun v ↦ ?_
    exact (h.continuousAt (prod_mem_nhds (hT.mem_nhds hy) Filter.univ_mem)).comp
      (continuous_const.prodMk continuous_id).continuousAt
  have hAc : ∀ y (hy : y ∈ i.1.target), Continuous (hωl.alternating y hy).choose := fun y hy ↦ by
    have : ⇑(hωl.alternating y hy).choose = fun v ↦ ω.localRep i (y, v) :=
      funext fun v ↦ ((hωl.alternating y hy).choose_spec v).symm
    rw [this]; exact hcont y hy
  set Ω : E → E →L[ℝ] E →L[ℝ] ℝ := fun y ↦
    if hy : y ∈ i.1.target then clm₂OfAlternating _ (hAc y hy) else 0 with hΩdef
  have hΩ : ∀ y ∈ i.1.target, ∀ a b, Ω y a b = ω.localRep i (y, ![a, b]) := fun y hy a b ↦ by
    simp only [hΩdef, hy, ↓reduceDIte, clm₂OfAlternating_apply]
    exact ((hωl.alternating y hy).choose_spec _).symm
  have hΩ3 : SmoothMBOn (fun r : (E × E) × E ↦ Ω r.1.1 r.1.2 r.2)
      ((i.1.target ×ˢ univ) ×ˢ univ) := fun k ↦ by
    set Lc : (E × E) × E →L[ℝ] E × (Fin 2 → E) :=
      ((ContinuousLinearMap.fst ℝ E E).comp (ContinuousLinearMap.fst ℝ (E × E) E)).prod
        (ContinuousLinearMap.pi ![(ContinuousLinearMap.snd ℝ E E).comp
          (ContinuousLinearMap.fst ℝ (E × E) E), ContinuousLinearMap.snd ℝ (E × E) E])
    have h := (hωl.smooth k).comp_clm Lc (hT.prod isOpen_univ)
    have hpre : Lc ⁻¹' (i.1.target ×ˢ univ) = (i.1.target ×ˢ univ) ×ˢ univ := by
      ext; simp [Lc]
    rw [hpre] at h
    refine ContDiffMBOn.congr_of_isOpen ((hT.prod isOpen_univ).prod isOpen_univ)
      (fun r hr ↦ ?_) h
    rw [comp_apply, hΩ _ hr.1.1]
    congr 1
    refine Prod.ext rfl ?_
    funext j; fin_cases j <;> rfl
  exact ⟨Ω, (smoothMBOn_iff_contDiffOn hT).1 fun k ↦ contDiffMBOn_of_unc_clm k hT
    (contDiffMBOn_of_unc_clm (k + 1) (hT.prod isOpen_univ) (hΩ3 (k + 1 + 1))), hΩ⟩

/-- An operator-valued representative `Ω` of a closed `2`-form `ω` in the preferred chart at `x₀`
is skew-symmetric and closed, and `Ω` at `x₀` is `ω_{x₀}`. -/
theorem DifferentialForm.clm_localRep_spec (ω : DifferentialForm E M ℝ 2) (hω : ω.IsClosed)
    (x₀ : M) {Ω : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hΩs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ω (chartAt E x₀).target)
    (hΩ : ∀ y ∈ (chartAt E x₀).target, ∀ a b, Ω y a b = ω.localRep (prefChart x₀) (y, ![a, b])) :
    (∀ y ∈ (chartAt E x₀).target, ∀ a b, Ω y a b = -Ω y b a) ∧
    (∀ y ∈ (chartAt E x₀).target, ∀ u v w,
      fderiv ℝ Ω y u v w - fderiv ℝ Ω y v u w + fderiv ℝ Ω y w u v = 0) ∧
    ∀ a b, Ω (chartAt E x₀ x₀) a b = ω x₀ ![a, b] := by
  set i : atlas E M := prefChart x₀ with hidef
  have hT : IsOpen i.1.target := i.1.open_target
  have hωl : IsLocalForm 2 (ω.localRep i) i.1.target := ω.isLocalForm_localRep i
  have hpT : i.1 x₀ ∈ i.1.target := i.1.map_source (mem_chart_source E x₀)
  have hΩd : ∀ y ∈ i.1.target, HasFDerivAt Ω (fderiv ℝ Ω y) y := fun y hy ↦
    ((hΩs.contDiffAt (hT.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
  have hdΩ : ∀ y ∈ i.1.target, ∀ a b c : E,
      dMB (fun z ↦ ω.localRep i (z, ![a, b])) (y, c) = fderiv ℝ Ω y c a b := fun y hy a b c ↦ by
    have h := ((hΩd y hy).clm_apply (hasFDerivAt_const a y)).clm_apply (hasFDerivAt_const b y)
    have hev : (fun z ↦ Ω z a b) =ᶠ[𝓝 y] fun z ↦ ω.localRep i (z, ![a, b]) :=
      eventually_of_mem (hT.mem_nhds hy) fun z hz ↦ hΩ z hz a b
    rw [((h.congr_of_eventuallyEq hev.symm).hasDirDerivAt c).dMB_eq]
    simp
  refine ⟨fun y hy a b ↦ ?_, fun y hy u v w ↦ ?_, fun a b ↦ ?_⟩
  · obtain ⟨A, hA⟩ := hωl.alternating y hy
    rw [hΩ y hy, hΩ y hy, hA, hA]
    have := A.map_swap ![b, a] (i := 0) (j := 1) (by decide)
    rw [← this]
    congr 1
    funext k
    fin_cases k <;> rfl
  · have h0 : ω.d.localRep i (y, ![u, v, w]) = 0 := hω _ _
    rw [ω.localRep_d i hy, IsLocalForm.dLoc_apply, Fin.sum_univ_three] at h0
    have e0 : Fin.removeNth 0 ![u, v, w] = ![v, w] := by funext j; fin_cases j <;> rfl
    have e1 : Fin.removeNth 1 ![u, v, w] = ![u, w] := by funext j; fin_cases j <;> rfl
    have e2 : Fin.removeNth 2 ![u, v, w] = ![u, v] := by funext j; fin_cases j <;> rfl
    rw [e0, e1, e2, hdΩ y hy, hdΩ y hy, hdΩ y hy] at h0
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, smul_eq_mul] at h0
    have e3 : (![u, v, w] : Fin 3 → E) 0 = u := rfl
    have e4 : (![u, v, w] : Fin 3 → E) 1 = v := rfl
    have e5 : (![u, v, w] : Fin 3 → E) 2 = w := rfl
    rw [e3, e4, e5] at h0
    linarith
  · rw [hΩ _ hpT]; exact ω.localRep_prefChart x₀ _

/-- **From a local Darboux map to a Darboux chart.** Let `Ω` represent the `2`-form `ω` in the
preferred chart `i` at `x₀`, and let `ψ` be a diffeomorphism between open subsets of `i(U)`
fixing `i(x₀)`, with `dψ(i x₀) = id` and `ψ*Ω = Ω(i x₀)`. Then `φ = ψ⁻¹ ∘ i` is a chart of the
maximal atlas around `x₀`, with `φ(x₀) = i(x₀)`, the same differential at `x₀` as `i`, and in which
`ω` has constant coefficients. (`ψ` need not map into `i(U)`: the chart `ψ⁻¹ ∘ i` is restricted
to where it is defined.) -/
theorem DifferentialForm.darboux_chart_of_local (ω : DifferentialForm E M ℝ 2) (x₀ : M)
    {Ω : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hΩ : ∀ y ∈ (chartAt E x₀).target, ∀ a b, Ω y a b = ω.localRep (prefChart x₀) (y, ![a, b]))
    {ψ : OpenPartialHomeomorph E E} (hpψ : chartAt E x₀ x₀ ∈ ψ.source)
    (hψp : ψ (chartAt E x₀ x₀) = chartAt E x₀ x₀)
    (hDψp : fderiv ℝ ψ (chartAt E x₀ x₀) = ContinuousLinearMap.id ℝ E)
    (hψs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ψ.source)
    (hψs' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ.symm ψ.target)
    (hψpull : ∀ x ∈ ψ.source, ∀ u v,
      Ω (ψ x) (fderiv ℝ ψ x u) (fderiv ℝ ψ x v) = Ω (chartAt E x₀ x₀) u v)
    (hΩp : ∀ a b, Ω (chartAt E x₀ x₀) a b = ω x₀ ![a, b]) :
    x₀ ∈ ((chartAt E x₀).trans ψ.symm).source ∧
      (chartAt E x₀).trans ψ.symm ∈ (mbGroupoid E).maximalAtlas M ∧
      (chartAt E x₀).trans ψ.symm x₀ = chartAt E x₀ x₀ ∧
      (∀ u, dMB (chartAt E x₀ ∘ ((chartAt E x₀).trans ψ.symm).symm)
        ((chartAt E x₀).trans ψ.symm x₀, u) = u) ∧
      ∀ x ∈ ((chartAt E x₀).trans ψ.symm).source, ∀ u v : E,
        ω x ![dMB (chartAt E x ∘ ((chartAt E x₀).trans ψ.symm).symm)
            ((chartAt E x₀).trans ψ.symm x, u),
          dMB (chartAt E x ∘ ((chartAt E x₀).trans ψ.symm).symm)
            ((chartAt E x₀).trans ψ.symm x, v)] = ω x₀ ![u, v] := by
  set i : atlas E M := prefChart x₀ with hidef
  have hψG : ψ.symm ∈ mbGroupoid E :=
    ⟨(smoothMBOn_iff_contDiffOn ψ.open_target).2 hψs',
      (smoothMBOn_iff_contDiffOn ψ.open_source).2 hψs⟩
  have hψG' : ψ ∈ mbGroupoid E := by simpa using (mbGroupoid E).symm hψG
  -- tangent vectors given in the chart `φ = ψ⁻¹ ∘ i`, read in the preferred charts
  have hvec : ∀ x ∈ (i.1.trans ψ.symm).source, ∀ u,
      dMB (chartAt E x ∘ (i.1.trans ψ.symm).symm) ((i.1.trans ψ.symm) x, u) =
        tangentCoordChange i (prefChart x) x (fderiv ℝ ψ ((i.1.trans ψ.symm) x) u) := by
    intro x hx u
    rw [OpenPartialHomeomorph.trans_source] at hx
    obtain ⟨hxi, hxψ⟩ := hx
    have hxψ' : i.1 x ∈ ψ.target := hxψ
    have hy : ψ.symm (i.1 x) ∈ ψ.source := ψ.map_target hxψ'
    have hψy : ψ (ψ.symm (i.1 x)) = i.1 x := ψ.right_inv hxψ'
    have hfun : ⇑(chartAt E x) ∘ ⇑(i.1.trans ψ.symm).symm = (chartAt E x ∘ i.1.symm) ∘ ψ := by
      rw [OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.symm_symm]; rfl
    rw [hfun]
    change dMB ((chartAt E x ∘ i.1.symm) ∘ ψ) (ψ.symm (i.1 x), u) = _
    have hτ := SmoothVectorField.hasFDerivAt_transition i (prefChart x) (y := i.1 x)
      ⟨i.1.map_source hxi, by simp [i.1.left_inv hxi]⟩
    have hψd : HasFDerivAt ψ (fderiv ℝ ψ (ψ.symm (i.1 x))) (ψ.symm (i.1 x)) :=
      ((hψs.contDiffAt (ψ.open_source.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
    have hτ' : HasFDerivAt (chartAt E x ∘ i.1.symm)
        (fderiv ℝ (chartAt E x ∘ i.1.symm) (i.1 x)) (ψ (ψ.symm (i.1 x))) := by
      rw [hψy]; exact hτ.1
    have hcomp := hτ'.comp (ψ.symm (i.1 x)) hψd
    rw [(hcomp.hasDirDerivAt u).dMB_eq, ContinuousLinearMap.comp_apply, hτ.2,
      ← tangentCoordChange_eq_dMB i _ (i.1.map_source hxi), i.1.left_inv hxi]
    rfl
  have hx₀ : x₀ ∈ (i.1.trans ψ.symm).source := by
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨mem_chart_source E x₀, ?_⟩
    change i.1 x₀ ∈ ψ.target
    rw [← hψp]; exact ψ.map_source hpψ
  have hφx₀ : (i.1.trans ψ.symm) x₀ = i.1 x₀ := by
    change ψ.symm (i.1 x₀) = i.1 x₀
    conv_lhs => rw [← hψp]
    exact ψ.left_inv hpψ
  refine ⟨hx₀, ?_, hφx₀, fun u ↦ ?_, fun x hx u v ↦ ?_⟩
  · refine mem_maximalAtlas_iff.2 fun e' he' ↦ ⟨?_, ?_⟩
    · rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm,
        OpenPartialHomeomorph.trans_assoc]
      exact (mbGroupoid E).trans hψG' ((mbGroupoid E).compatible i.2 he')
    · rw [← OpenPartialHomeomorph.trans_assoc]
      exact (mbGroupoid E).trans ((mbGroupoid E).compatible he' i.2) hψG
  · rw [hvec x₀ hx₀ u, hφx₀, hDψp]
    exact tangentCoordChange_self i (mem_chart_source E x₀) u
  · rw [hvec x hx u, hvec x hx v]
    have hx' := hx
    rw [OpenPartialHomeomorph.trans_source] at hx'
    obtain ⟨hxi, hxψ⟩ := hx'
    have hxψ' : i.1 x ∈ ψ.target := hxψ
    have hy : (i.1.trans ψ.symm) x ∈ ψ.source := ψ.map_target hxψ'
    have hψy : ψ ((i.1.trans ψ.symm) x) = i.1 x := ψ.right_inv hxψ'
    have hrep : ∀ a b : E, ω x ![tangentCoordChange i (prefChart x) x a,
        tangentCoordChange i (prefChart x) x b] = ω.localRep i (i.1 x, ![a, b]) := fun a b ↦ by
      simp only [DifferentialForm.localRep, formLocalRep, i.1.left_inv hxi]
      congr 1
      funext k; fin_cases k <;> rfl
    rw [hrep, ← hΩ _ (i.1.map_source hxi), ← hψy, hψpull _ hy, hΩp]

/-- **Darboux charts on Banach manifolds.** Let `M` be a manifold modeled on a Banach space `E` (not
necessarily Hausdorff) and `ω` a closed real `2`-form on `M` which is strongly nondegenerate at
`x₀`: `v ↦ ω_{x₀}(v, ·)` is a bijection of `E` onto `E'` (`hinj`, `hsurj`). Then there is a chart
`φ` of the maximal atlas around `x₀`, with `φ(x₀) = i(x₀)` and the same differential at `x₀` as the
preferred chart `i`, in which **`ω` is constant**: for `x` in the domain of `φ` and `u, v ∈ E`,
`ω_x(Tu, Tv) = ω_{x₀}(u, v)`, where `T = d(chartAt x ∘ φ⁻¹)(φ x)` reads a tangent vector given in
the chart `φ` in the preferred chart at `x`.

The coordinate expression of `ω` in `i` is smooth into `L(E, E')` for the operator norm
(`DifferentialForm.exists_clm_localRep`); `φ = ψ⁻¹ ∘ i` for the map `ψ` of
`Darboux.exists_darboux_local` (`DifferentialForm.darboux_chart_of_local`). -/
theorem DifferentialForm.exists_darboux_chart [CompleteSpace E] (ω : DifferentialForm E M ℝ 2)
    (hω : ω.IsClosed) (x₀ : M) (hinj : ∀ v, (∀ w, ω x₀ ![v, w] = 0) → v = 0)
    (hsurj : ∀ φ : E →L[ℝ] ℝ, ∃ v, ∀ w, ω x₀ ![v, w] = φ w) :
    ∃ φ : OpenPartialHomeomorph M E, x₀ ∈ φ.source ∧ φ ∈ (mbGroupoid E).maximalAtlas M ∧
      φ x₀ = chartAt E x₀ x₀ ∧ (∀ u, dMB (chartAt E x₀ ∘ φ.symm) (φ x₀, u) = u) ∧
      ∀ x ∈ φ.source, ∀ u v : E,
        ω x ![dMB (chartAt E x ∘ φ.symm) (φ x, u), dMB (chartAt E x ∘ φ.symm) (φ x, v)] =
          ω x₀ ![u, v] := by
  obtain ⟨Ω, hΩs, hΩ⟩ := ω.exists_clm_localRep x₀
  obtain ⟨hskew, hclosed, hΩp⟩ := ω.clm_localRep_spec hω x₀ hΩs hΩ
  have hpT : chartAt E x₀ x₀ ∈ (chartAt E x₀).target :=
    (chartAt E x₀).map_source (mem_chart_source E x₀)
  have hstrong : Bijective (Ω (chartAt E x₀ x₀)) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun a ha ↦ hinj a fun w ↦ ?_, fun φ ↦ ?_⟩
    · rw [← hΩp, ha]; rfl
    · obtain ⟨v, hv⟩ := hsurj φ
      exact ⟨v, ContinuousLinearMap.ext fun w ↦ by rw [hΩp, hv]⟩
  obtain ⟨ψ, hpψ, hψp, hDψp, -, -, hψs, hψs', hψpull⟩ :=
    Darboux.exists_darboux_local (chartAt E x₀).open_target hΩs hskew hclosed hpT hstrong
  exact ⟨_, ω.darboux_chart_of_local x₀ hΩ hpψ hψp hDψp hψs hψs' hψpull hΩp⟩

/-- **The Darboux theorem for strong symplectic forms on Banach manifolds**
([Wei69]; [Lan99, Theorem V.8.1]): every point of a manifold modeled on a
Banach space and carrying a strong symplectic form `ω` lies in a chart of the smooth structure in
which `ω` has constant coefficients, equal to `ω_{x₀}`. -/
theorem SymplecticForm.IsStrong.exists_darboux_chart [CompleteSpace E] {ω : SymplecticForm E M}
    (hω : ω.IsStrong) (x₀ : M) :
    ∃ φ : OpenPartialHomeomorph M E, x₀ ∈ φ.source ∧ φ ∈ (mbGroupoid E).maximalAtlas M ∧
      φ x₀ = chartAt E x₀ x₀ ∧ (∀ u, dMB (chartAt E x₀ ∘ φ.symm) (φ x₀, u) = u) ∧
      ∀ x ∈ φ.source, ∀ u v : E,
        ω.form x ![dMB (chartAt E x ∘ φ.symm) (φ x, u), dMB (chartAt E x ∘ φ.symm) (φ x, v)] =
          ω.form x₀ ![u, v] :=
  ω.form.exists_darboux_chart ω.isClosed x₀ (ω.nondegenerate x₀) (hω x₀)

end Manifold

end LocallyConvex.Manifolds
