/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.Flow.LieDerivative
public import LocallyConvexManifolds.MappingSpace.Basic
public import LocallyConvexManifolds.Manifold.LocalDiffeo
public import LocallyConvexAnalysis.ODE.Flow

/-!
# Local flows of smooth vector fields on Banach manifolds

On manifolds modeled on locally convex spaces vector fields need not have flows, so
`LocallyConvexManifolds.Flow.LieDerivative` takes a local flow (`IsLocalFlow`) as a hypothesis. On a
Hausdorff manifold modeled on a **Banach** space every smooth vector field has one. We prove:

* `SmoothVectorField.IsIntegralCurveOn`: integral curves, read in every chart. By the chart change
  lemma for velocities (`SmoothVectorField.hasDerivAt_rep_of_chart`) it suffices to check the
  equation in one chart at each instant (`SmoothVectorField.isIntegralCurveOn_of_exists_chart`).
* `SmoothVectorField.IsIntegralCurveOn.eqOn` (**uniqueness**): on a Hausdorff manifold, two
  integral curves on an open connected set of times that agree at one instant agree everywhere.
* `SmoothVectorField.exists_flowBox` (**flow boxes**): around each point there are `ε > 0`, an
  open set `V` and a smooth `φ : (-ε, ε) × V → M` whose curves `t ↦ φ(t, x)` are integral curves
  with `φ(0, x) = x`. This transports the local flows of `LocallyConvexAnalysis.ODE.Flow` through
  a chart.
* `SmoothVectorField.boxFlow`, `SmoothVectorField.boxFlowDomain`: the chosen flow boxes glued by
  uniqueness. `SmoothVectorField.isLocalFlow_boxFlow` (**existence of local flows**): `boxFlow`
  is a local flow of `X` on the open set `boxFlowDomain ⊇ {0} × M` in the sense of `IsLocalFlow`;
  it is smooth (`SmoothVectorField.smoothMBMOn_boxFlow`), its curves are integral curves on
  intervals (`SmoothVectorField.isIntegralCurveOn_boxFlow`,
  `SmoothVectorField.ordConnected_boxFlowDomain_slice`), and it satisfies the **group law**
  `Fl(s + t, x) = Fl(s, Fl(t, x))` where both sides are defined (`SmoothVectorField.boxFlow_add`).

The **maximal flow** `SmoothVectorField.flow` on its open domain `SmoothVectorField.flowDomain`,
which is the main API, is built in `LocallyConvexManifolds.Flow.Maximal` from the flow boxes of this
file; there `boxFlow` is shown to be its restriction to `boxFlowDomain`.

References: S. Lang, *Fundamentals of Differential Geometry*, Springer GTM 191 (1999),
Ch. IV, §2, Theorem 2.1 (p. 90, uniqueness) and Theorem 2.2 (p. 91, group law); H. Glöckner,
K.-H. Neeb, *Infinite-Dimensional Lie Groups*, Corollary 2.5.21 (p. 222).

## Implementation notes

* The domain `boxFlowDomain` is the union of the chosen flow boxes, not the maximal domain of the
  flow. Each slice `{t | (t, x) ∈ boxFlowDomain}` is an interval containing `0`.
* `E` is a Banach space (`[CompleteSpace E]`, for the local flows of `ODEFlow`) and `M` is
  Hausdorff (for the uniqueness of integral curves, which fails on the line with two origins).
* On manifolds modeled on Fréchet or general locally convex spaces smooth vector fields need not
  have local flows, nor unique integral curves (Glöckner–Neeb, Examples 2.4.2 and 2.4.3).
-/

@[expose] public section

open Set Filter Function
open LocallyConvex.Analysis
open scoped Topology

noncomputable section

namespace LocallyConvex.Manifolds

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

namespace SmoothVectorField

/-! ### Integral curves -/

/-- `c` is an **integral curve** of `X` on `I`: at every `t ∈ I` it is continuous and, read in
every chart `i` around `c t`, it has velocity `X̃ᵢ(i (c t))`. -/
def IsIntegralCurveOn (X : SmoothVectorField E M) (c : ℝ → M) (I : Set ℝ) : Prop :=
  ∀ t ∈ I, ContinuousAt c t ∧ ∀ i : atlas E M, c t ∈ i.1.source →
    HasDerivAt (i.1 ∘ c) (X.rep i (i.1 (c t))) t

/-- The transition maps of a Banach manifold are Fréchet differentiable, with derivative the
Michal–Bastiani derivative. -/
theorem hasFDerivAt_transition (i j : atlas E M) {y : E}
    (hy : y ∈ i.1.target ∩ i.1.symm ⁻¹' j.1.source) :
    HasFDerivAt (j.1 ∘ i.1.symm) (fderiv ℝ (j.1 ∘ i.1.symm) y) y ∧
      ∀ w, fderiv ℝ (j.1 ∘ i.1.symm) y w = dMB (j.1 ∘ i.1.symm) (y, w) := by
  have hT := isOpen_transition_domain i j
  have hd : HasFDerivAt (j.1 ∘ i.1.symm) (fderiv ℝ (j.1 ∘ i.1.symm) y) y :=
    ((((smoothMBOn_iff_contDiffOn hT).1 (smoothMBOn_transition' i j)).differentiableOn
      (by simp)) y hy).differentiableAt (hT.mem_nhds hy) |>.hasFDerivAt
  exact ⟨hd, fun w ↦ ((hd.hasDirDerivAt w).dMB_eq).symm⟩

/-- **Chart change for velocities.** If a curve continuous at `t`, read in the chart `i`, has
velocity `X̃ᵢ` at `t`, then read in any other chart `j` around `c t` it has velocity `X̃ⱼ`. -/
theorem hasDerivAt_rep_of_chart (X : SmoothVectorField E M) {c : ℝ → M} {t : ℝ}
    (hc : ContinuousAt c t) {i j : atlas E M} (hi : c t ∈ i.1.source) (hj : c t ∈ j.1.source)
    (h : HasDerivAt (i.1 ∘ c) (X.rep i (i.1 (c t))) t) :
    HasDerivAt (j.1 ∘ c) (X.rep j (j.1 (c t))) t := by
  have hy : i.1 (c t) ∈ i.1.target ∩ i.1.symm ⁻¹' j.1.source :=
    ⟨i.1.map_source hi, by simp [i.1.left_inv hi, hj]⟩
  obtain ⟨hτ, hτd⟩ := hasFDerivAt_transition i j hy
  have hev : (j.1 ∘ i.1.symm) ∘ (i.1 ∘ c) =ᶠ[𝓝 t] j.1 ∘ c := by
    filter_upwards [hc.preimage_mem_nhds (i.1.open_source.mem_nhds hi)] with s hs
    simp [i.1.left_inv hs]
  have hval : fderiv ℝ (j.1 ∘ i.1.symm) (i.1 (c t)) (X.rep i (i.1 (c t))) =
      X.rep j (j.1 (c t)) := by
    rw [hτd, ← localRep_transition X.isVectorField i j hy.1 hy.2]
    simp [i.1.left_inv hi]
  exact ((hτ.comp_hasDerivAt t h).congr_of_eventuallyEq hev.symm).congr_deriv hval

/-- It suffices to check the equation of integral curves in one chart at each instant. -/
theorem isIntegralCurveOn_of_exists_chart (X : SmoothVectorField E M) {c : ℝ → M} {I : Set ℝ}
    (h : ∀ t ∈ I, ContinuousAt c t ∧ ∃ i : atlas E M, c t ∈ i.1.source ∧
      HasDerivAt (i.1 ∘ c) (X.rep i (i.1 (c t))) t) :
    X.IsIntegralCurveOn c I := fun t ht ↦ by
  obtain ⟨hc, i, hi, hd⟩ := h t ht
  exact ⟨hc, fun j hj ↦ X.hasDerivAt_rep_of_chart hc hi hj hd⟩

variable {X : SmoothVectorField E M}

/-- Restriction of an integral curve to a smaller set of times. -/
theorem IsIntegralCurveOn.mono {c : ℝ → M} {I J : Set ℝ} (h : X.IsIntegralCurveOn c I)
    (hJ : J ⊆ I) : X.IsIntegralCurveOn c J :=
  fun t ht ↦ h t (hJ ht)

/-- Integral curves only depend on their values on the open set of times. -/
theorem IsIntegralCurveOn.congr {c c' : ℝ → M} {I : Set ℝ} (h : X.IsIntegralCurveOn c I)
    (hI : IsOpen I) (heq : EqOn c c' I) : X.IsIntegralCurveOn c' I := fun t ht ↦ by
  have hev : c =ᶠ[𝓝 t] c' := eventually_of_mem (hI.mem_nhds ht) heq
  refine ⟨(h t ht).1.congr hev, fun i hi ↦ ?_⟩
  rw [← heq ht] at hi ⊢
  exact ((h t ht).2 i hi).congr_of_eventuallyEq (hev.fun_comp i.1).symm

/-- Time translates of integral curves are integral curves. -/
theorem IsIntegralCurveOn.comp_add {c : ℝ → M} {I : Set ℝ} (h : X.IsIntegralCurveOn c I)
    (a : ℝ) : X.IsIntegralCurveOn (fun s ↦ c (s + a)) ((· + a) ⁻¹' I) := fun t ht ↦ by
  refine ⟨ContinuousAt.comp (f := fun s : ℝ ↦ s + a) (h _ ht).1
    (continuous_id.add continuous_const).continuousAt, fun i hi ↦ ?_⟩
  exact ((h _ ht).2 i hi).comp_add_const t a

/-! ### Uniqueness of integral curves -/

/-- The local representatives of a smooth vector field on a Banach manifold are Fréchet `C¹`. -/
theorem contDiffOn_rep (X : SmoothVectorField E M) (i : atlas E M) :
    ContDiffOn ℝ 1 (X.rep i) i.1.target :=
  ((smoothMBOn_iff_contDiffOn i.1.open_target).1 (X.smoothMBOn_localRep i)).of_le
    (by exact_mod_cast le_top)

/-- Local uniqueness: two integral curves on an open set that meet at `t` agree near `t`. -/
theorem IsIntegralCurveOn.eventuallyEq [CompleteSpace E] {c₁ c₂ : ℝ → M} {I : Set ℝ}
    (hI : IsOpen I) (h₁ : X.IsIntegralCurveOn c₁ I) (h₂ : X.IsIntegralCurveOn c₂ I) {t : ℝ}
    (ht : t ∈ I) (heq : c₁ t = c₂ t) : c₁ =ᶠ[𝓝 t] c₂ := by
  set i : atlas E M := ⟨chartAt E (c₁ t), chart_mem_atlas E _⟩
  have hi : c₁ t ∈ i.1.source := mem_chart_source E _
  have hN : I ∩ (c₁ ⁻¹' i.1.source ∩ c₂ ⁻¹' i.1.source) ∈ 𝓝 t :=
    inter_mem (hI.mem_nhds ht) (inter_mem
      ((h₁ t ht).1.preimage_mem_nhds (i.1.open_source.mem_nhds hi))
      ((h₂ t ht).1.preimage_mem_nhds (i.1.open_source.mem_nhds (heq ▸ hi))))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hN
  rw [Real.ball_eq_Ioo] at hball
  have hcurve : ∀ {c : ℝ → M}, X.IsIntegralCurveOn c I → (∀ s ∈ Ioo (t - δ) (t + δ),
      c s ∈ i.1.source) → ∀ s ∈ Ioo (t - δ) (t + δ),
      HasDerivAt (i.1 ∘ c) (X.rep i ((i.1 ∘ c) s)) s ∧ (i.1 ∘ c) s ∈ i.1.target :=
    fun hc hsrc s hs ↦ ⟨(hc s (hball hs).1).2 i (hsrc s hs), i.1.map_source (hsrc s hs)⟩
  have hts : t ∈ Ioo (t - δ) (t + δ) := ⟨by linarith, by linarith⟩
  have H := eqOn_Ioo_of_contDiffOn i.1.open_target (X.contDiffOn_rep i)
    (hcurve h₁ fun s hs ↦ (hball hs).2.1) (hcurve h₂ fun s hs ↦ (hball hs).2.2) hts
    (by simp [heq])
  filter_upwards [Ioo_mem_nhds hts.1 hts.2] with s hs
  exact i.1.injOn (hball hs).2.1 (hball hs).2.2 (H hs)

/-- **Uniqueness of integral curves.** On a Hausdorff manifold modeled on a Banach space, two
integral curves of a smooth vector field on an open connected set `I` of times that agree at one
instant agree on `I` (compare Lang, *Fundamentals of Differential Geometry*, Theorem IV.2.1). -/
theorem IsIntegralCurveOn.eqOn [CompleteSpace E] [T2Space M] {c₁ c₂ : ℝ → M} {I : Set ℝ}
    (hI : IsOpen I) (hI' : IsPreconnected I) (h₁ : X.IsIntegralCurveOn c₁ I)
    (h₂ : X.IsIntegralCurveOn c₂ I) {t₀ : ℝ} (ht₀ : t₀ ∈ I) (heq : c₁ t₀ = c₂ t₀) :
    EqOn c₁ c₂ I := by
  set u : Set ℝ := {t | c₁ =ᶠ[𝓝 t] c₂}
  have hu : IsOpen u := isOpen_setOfPred_eventually_nhds
  have hsub : I ⊆ u := by
    refine hI'.subset_of_closure_inter_subset hu ⟨t₀, ht₀, h₁.eventuallyEq hI h₂ ht₀ heq⟩ ?_
    rintro t ⟨htc, ht⟩
    have hfreq : ∃ᶠ τ in 𝓝 t, τ ∈ u := mem_closure_iff_frequently.mp htc
    -- the curves meet at `t`, since `M` is Hausdorff
    have heqt : c₁ t = c₂ t := tendsto_nhds_unique_of_frequently_eq (h₁ t ht).1 (h₂ t ht).1
      (hfreq.mono fun τ hτ ↦ hτ.self_of_nhds)
    exact h₁.eventuallyEq hI h₂ ht heqt
  exact fun t ht ↦ (hsub ht).self_of_nhds

/-! ### Flow boxes -/

variable (X) in
/-- A **flow box** of `X` around `x`: a time `ε > 0`, an open neighbourhood `V` of `x` and a smooth
map `φ` on `(-ε, ε) × V` whose curves `t ↦ φ(t, y)` are integral curves of `X` with
`φ(0, y) = y`. -/
structure FlowBox (x : M) where
  /-- The time of existence. -/
  ε : ℝ
  /-- The time of existence is positive. -/
  ε_pos : 0 < ε
  /-- The set of initial conditions. -/
  V : Set M
  /-- The set of initial conditions is open. -/
  isOpen : IsOpen V
  /-- The set of initial conditions contains `x`. -/
  mem : x ∈ V
  /-- The local flow. -/
  φ : ℝ × M → M
  /-- The local flow is smooth on `(-ε, ε) × V`. -/
  smooth : SmoothMBMOn (ModelProd ℝ E) E φ (Ioo (-ε) ε ×ˢ V)
  /-- `φ(0, y) = y`. -/
  map_zero : ∀ y ∈ V, φ (0, y) = y
  /-- The curves `t ↦ φ(t, y)` are integral curves of `X` on `(-ε, ε)`. -/
  isIntegralCurveOn : ∀ y ∈ V, X.IsIntegralCurveOn (fun t ↦ φ (t, y)) (Ioo (-ε) ε)

/-- **Existence of flow boxes**: the local flows of the local representative of `X` in a chart,
`LocallyConvex.Analysis.exists_smoothMBOn_flow`, transported to `M`. -/
theorem exists_flowBox [CompleteSpace E] (X : SmoothVectorField E M) (x : M) :
    Nonempty (X.FlowBox x) := by
  set i : atlas E M := ⟨chartAt E x, chart_mem_atlas E x⟩
  have hx : x ∈ i.1.source := mem_chart_source E x
  obtain ⟨ε, hε, V', hV', hxV', ψ, hψ, H⟩ :=
    exists_smoothMBOn_flow i.1.open_target (X.smoothMBOn_localRep i) (i.1.map_source hx)
  set V := i.1.source ∩ i.1 ⁻¹' V'
  have hV : IsOpen V := i.1.isOpen_inter_preimage hV'
  set φ : ℝ × M → M := fun p ↦ i.1.symm (ψ (p.1, i.1 p.2))
  have hbox : IsOpen (Ioo (-ε) ε ×ˢ V) := isOpen_Ioo.prod hV
  -- `g = ψ ∘ (id × i)` is smooth: its local representatives are `ψ ∘ (id × (i ∘ c⁻¹))`
  set g : ℝ × M → E := fun p ↦ ψ (p.1, i.1 p.2)
  have hgc : ContinuousOn g (Ioo (-ε) ε ×ˢ V) :=
    (hψ 0).continuousOn.comp (continuousOn_fst.prodMk
      (i.1.continuousOn.comp continuousOn_snd fun p hp ↦ hp.2.1)) fun p hp ↦ ⟨hp.1, hp.2.2⟩
  have hg : SmoothMBMOn (ModelProd ℝ E) E g (Ioo (-ε) ε ×ˢ V) := by
    intro k
    refine ⟨hgc, fun q _ ↦ ?_⟩
    set c := chartAt E q.2
    set T := c.target ∩ c.symm ⁻¹' i.1.source
    have hT : IsOpen T := c.isOpen_inter_preimage_symm i.1.open_source
    have hτ : ContDiffMBOn k (i.1 ∘ c.symm) T := smoothMBOn_transition (chart_mem_atlas E _) i.2 k
    have hpair : ContDiffMBOn k (fun r : ℝ × E ↦ (r.1, (i.1 ∘ c.symm) r.2)) (univ ×ˢ T) :=
      ContDiffMBOn.prodMk (isOpen_univ.prod hT)
        ((ContinuousLinearMap.fst ℝ ℝ E).contDiffMBOn k _)
        (hτ.comp (g := i.1 ∘ c.symm) (f := Prod.snd) (isOpen_univ.prod hT) hT
          ((ContinuousLinearMap.snd ℝ ℝ E).contDiffMBOn k _) fun r hr ↦ hr.2)
    have hO : IsOpen (univ ×ˢ T ∩ (fun r : ℝ × E ↦ (r.1, (i.1 ∘ c.symm) r.2)) ⁻¹'
        (Ioo (-ε) ε ×ˢ V')) :=
      hpair.continuousOn.isOpen_inter_preimage (isOpen_univ.prod hT) (isOpen_Ioo.prod hV')
    have hcomp := (hψ k).comp hO (isOpen_Ioo.prod hV') (hpair.mono inter_subset_left)
      fun r hr ↦ hr.2
    refine ContDiffMBOn.congr_of_isOpen
      (isOpen_chartDomain hbox hgc (chartAt (ModelProd ℝ E) q) (chartAt E (g q)))
      (fun r hr ↦ ?_) (hcomp.mono fun r hr ↦ ?_)
    · rfl
    · simp only [chartDomain, prodChartedSpace_chartAt, chartAt_self_eq,
        OpenPartialHomeomorph.prod_target, OpenPartialHomeomorph.refl_target, mem_inter_iff,
        mem_prod, mem_univ, true_and, mem_preimage, OpenPartialHomeomorph.refl_source,
        and_true] at hr
      exact ⟨⟨mem_univ _, hr.1, hr.2.2.1⟩, hr.2.1, hr.2.2.2⟩
  -- `φ = i⁻¹ ∘ g` is smooth
  have hsmooth : SmoothMBMOn (ModelProd ℝ E) E φ (Ioo (-ε) ε ×ˢ V) :=
    (smoothMBMOn_symm_of_mem_atlas i.2).comp hbox i.1.open_target hg fun p hp ↦
      ((H _ hp.2.2).2 p.1 hp.1).1
  refine ⟨⟨ε, hε, V, hV, ⟨hx, hxV'⟩, φ, hsmooth, fun y hy ↦ ?_, fun y hy ↦ ?_⟩⟩
  · simp [φ, (H _ hy.2).1, i.1.left_inv hy.1]
  · refine X.isIntegralCurveOn_of_exists_chart fun t ht ↦ ?_
    obtain ⟨htU, hd⟩ := (H _ hy.2).2 t ht
    refine ⟨(i.1.continuousAt_symm htU).comp (f := fun s ↦ ψ (s, i.1 y)) hd.continuousAt, i,
      i.1.map_target htU, ?_⟩
    have hev : (fun s ↦ ψ (s, i.1 y)) =ᶠ[𝓝 t] i.1 ∘ fun s ↦ φ (s, y) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      simp [φ, i.1.right_inv ((H _ hy.2).2 s hs).1]
    have hval : i.1 (φ (t, y)) = ψ (t, i.1 y) := by simp [φ, i.1.right_inv htU]
    rw [hval]
    exact hd.congr_of_eventuallyEq hev.symm

/-- The box `(-ε, ε) × V` of a flow box. -/
def FlowBox.box {x : M} (B : X.FlowBox x) : Set (ℝ × M) :=
  Ioo (-B.ε) B.ε ×ˢ B.V

/-- The box of a flow box is open. -/
theorem FlowBox.isOpen_box {x : M} (B : X.FlowBox x) : IsOpen B.box :=
  isOpen_Ioo.prod B.isOpen

/-- Two flow boxes agree where both are defined. -/
theorem FlowBox.φ_eq [CompleteSpace E] [T2Space M] {x₁ x₂ : M} (B₁ : X.FlowBox x₁)
    (B₂ : X.FlowBox x₂) {p : ℝ × M} (h₁ : p ∈ B₁.box) (h₂ : p ∈ B₂.box) : B₁.φ p = B₂.φ p := by
  set m := min B₁.ε B₂.ε
  have hI₁ : Ioo (-m) m ⊆ Ioo (-B₁.ε) B₁.ε :=
    Ioo_subset_Ioo (neg_le_neg (min_le_left _ _)) (min_le_left _ _)
  have hI₂ : Ioo (-m) m ⊆ Ioo (-B₂.ε) B₂.ε :=
    Ioo_subset_Ioo (neg_le_neg (min_le_right _ _)) (min_le_right _ _)
  have h0 : (0 : ℝ) ∈ Ioo (-m) m := ⟨neg_lt_zero.2 (lt_min B₁.ε_pos B₂.ε_pos),
    lt_min B₁.ε_pos B₂.ε_pos⟩
  have hp : p.1 ∈ Ioo (-m) m :=
    ⟨neg_lt.1 (lt_min (neg_lt.1 h₁.1.1) (neg_lt.1 h₂.1.1)), lt_min h₁.1.2 h₂.1.2⟩
  have H := IsIntegralCurveOn.eqOn isOpen_Ioo isPreconnected_Ioo
    ((B₁.isIntegralCurveOn _ h₁.2).mono hI₁) ((B₂.isIntegralCurveOn _ h₂.2).mono hI₂) h0
    (by simp [B₁.map_zero _ h₁.2, B₂.map_zero _ h₂.2])
  exact H hp

/-! ### The flow obtained by gluing flow boxes -/

variable [CompleteSpace E]

variable (X) in
/-- A chosen flow box of `X` around each point. -/
def flowBox (x : M) : X.FlowBox x :=
  Classical.choice (X.exists_flowBox x)

variable (X) in
/-- The domain of `X.boxFlow`: the union of the chosen flow boxes. It is open and contains
`{0} × M`; it is not the maximal domain of the flow. -/
def boxFlowDomain : Set (ℝ × M) :=
  ⋃ x, (X.flowBox x).box

open scoped Classical in
variable (X) in
/-- The **local flow** of `X`, obtained by gluing the chosen flow boxes; it is well defined on
`boxFlowDomain` by uniqueness of integral curves (`SmoothVectorField.boxFlow_eq`). Outside
`boxFlowDomain` it takes the junk value `Fl(t, x) = x`. -/
def boxFlow (p : ℝ × M) : M :=
  if h : ∃ x, p ∈ (X.flowBox x).box then (X.flowBox h.choose).φ p else p.2

/-- On each flow box, the flow is given by the flow box. -/
theorem boxFlow_eq [T2Space M] {x : M} {p : ℝ × M} (hp : p ∈ (X.flowBox x).box) :
    X.boxFlow p = (X.flowBox x).φ p := by
  have h : ∃ x, p ∈ (X.flowBox x).box := ⟨x, hp⟩
  rw [boxFlow, dite_eq_left_of_eq_true (eq_true h)]
  exact FlowBox.φ_eq _ _ h.choose_spec hp

/-- A point lies in the domain of the flow iff it lies in one of the chosen flow boxes. -/
theorem mem_boxFlowDomain {p : ℝ × M} : p ∈ X.boxFlowDomain ↔ ∃ x, p ∈ (X.flowBox x).box :=
  mem_iUnion

/-- The domain of the flow is open. -/
theorem isOpen_boxFlowDomain : IsOpen X.boxFlowDomain :=
  isOpen_iUnion fun x ↦ (X.flowBox x).isOpen_box

/-- The domain of the flow contains `{0} × M`. -/
theorem zero_mem_boxFlowDomain (x : M) : ((0 : ℝ), x) ∈ X.boxFlowDomain :=
  mem_boxFlowDomain.2 ⟨x, ⟨neg_lt_zero.2 (X.flowBox x).ε_pos, (X.flowBox x).ε_pos⟩,
    (X.flowBox x).mem⟩

/-- `Fl(0, x) = x`. -/
theorem boxFlow_zero [T2Space M] (x : M) : X.boxFlow (0, x) = x := by
  rw [boxFlow_eq (x := x) ⟨⟨neg_lt_zero.2 (X.flowBox x).ε_pos, (X.flowBox x).ε_pos⟩,
    (X.flowBox x).mem⟩]
  exact (X.flowBox x).map_zero x (X.flowBox x).mem

/-- **The flow is smooth** on its domain. -/
theorem smoothMBMOn_boxFlow [T2Space M] :
    SmoothMBMOn (ModelProd ℝ E) E X.boxFlow X.boxFlowDomain := by
  intro k
  refine ContMDiffMBOn.of_local X.isOpen_boxFlowDomain fun p hp ↦ ?_
  obtain ⟨x, hx⟩ := mem_boxFlowDomain.1 hp
  exact ⟨_, (X.flowBox x).isOpen_box, hx, ((X.flowBox x).smooth k).congr_of_isOpen
    (X.flowBox x).isOpen_box fun q hq ↦ (boxFlow_eq hq).symm⟩

/-- The curves of the flow are integral curves of `X` on the slices of its domain. -/
theorem isIntegralCurveOn_boxFlow [T2Space M] (x : M) :
    X.IsIntegralCurveOn (fun t ↦ X.boxFlow (t, x)) {t | (t, x) ∈ X.boxFlowDomain} := by
  intro t ht
  obtain ⟨y, hy⟩ := mem_boxFlowDomain.1 ht
  have H := ((X.flowBox y).isIntegralCurveOn x hy.2).congr isOpen_Ioo
    (c' := fun t ↦ X.boxFlow (t, x)) fun s hs ↦ (boxFlow_eq (p := (s, x)) ⟨hs, hy.2⟩).symm
  exact H t hy.1

/-- The slices `{t | (t, x) ∈ boxFlowDomain}` are intervals (containing `0`). -/
theorem ordConnected_boxFlowDomain_slice (x : M) : OrdConnected {t | (t, x) ∈ X.boxFlowDomain} := by
  refine ⟨fun a ha b hb c hc ↦ ?_⟩
  have habs : |c| ≤ max |a| |b| := abs_le_max_abs_abs hc.1 hc.2
  have key : ∀ d, (d, x) ∈ X.boxFlowDomain → |c| ≤ |d| → (c, x) ∈ X.boxFlowDomain := by
    intro d hd hcd
    obtain ⟨y, hy⟩ := mem_boxFlowDomain.1 hd
    exact mem_boxFlowDomain.2 ⟨y, abs_lt.1 (hcd.trans_lt (abs_lt.2 hy.1)), hy.2⟩
  rcases le_total |a| |b| with h | h
  · exact key b hb (habs.trans (max_le h le_rfl))
  · exact key a ha (habs.trans (max_le le_rfl h))

/-- The slices `{t | (t, x) ∈ boxFlowDomain}` are open. -/
theorem isOpen_boxFlowDomain_slice (x : M) : IsOpen {t | (t, x) ∈ X.boxFlowDomain} :=
  X.isOpen_boxFlowDomain.preimage (continuous_id.prodMk continuous_const)

/-- **Existence of local flows on Banach manifolds.** Every smooth vector field on a Hausdorff
manifold modeled on a Banach space has a local flow in the sense of `IsLocalFlow`: `X.boxFlow` on
the open set `X.boxFlowDomain ⊇ {0} × M` (compare Glöckner–Neeb, Corollary 2.5.21). -/
theorem isLocalFlow_boxFlow [T2Space M] : IsLocalFlow X X.boxFlow X.boxFlowDomain where
  isOpen := X.isOpen_boxFlowDomain
  zero_mem := X.zero_mem_boxFlowDomain
  map_zero := X.boxFlow_zero
  contMDiffMBOn := X.smoothMBMOn_boxFlow 2
  hasDirDerivAt := by
    rintro ⟨t, x⟩ hp i hi
    have h := (((X.isIntegralCurveOn_boxFlow x) t hp).2 i hi).hasFDerivAt.hasDirDerivAt 1
    simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at h
    exact h

/-- **The group law** `Fl(s + t, x) = Fl(s, Fl(t, x))`, whenever `(t, x)`, `(s, Fl(t, x))` and
`(s + t, x)` lie in the domain of the flow (compare Lang, *Fundamentals of Differential
Geometry*, Theorem IV.2.2). -/
theorem boxFlow_add [T2Space M] {x : M} {s t : ℝ} (ht : (t, x) ∈ X.boxFlowDomain)
    (hs : (s, X.boxFlow (t, x)) ∈ X.boxFlowDomain) (hst : (s + t, x) ∈ X.boxFlowDomain) :
    X.boxFlow (s + t, x) = X.boxFlow (s, X.boxFlow (t, x)) := by
  set y := X.boxFlow (t, x)
  set A : Set ℝ := (· + t) ⁻¹' {u | (u, x) ∈ X.boxFlowDomain}
  set B : Set ℝ := {u | (u, y) ∈ X.boxFlowDomain}
  have hA : IsOpen A :=
    (X.isOpen_boxFlowDomain_slice x).preimage (continuous_id.add continuous_const)
  have hAc : OrdConnected A := ⟨fun a ha b hb c hc ↦
    (X.ordConnected_boxFlowDomain_slice x).out ha hb ⟨by linarith [hc.1], by linarith [hc.2]⟩⟩
  have hI : IsOpen (A ∩ B) := hA.inter (X.isOpen_boxFlowDomain_slice y)
  have hI' : IsPreconnected (A ∩ B) :=
    (hAc.inter (X.ordConnected_boxFlowDomain_slice y)).isPreconnected
  have h0 : (0 : ℝ) ∈ A ∩ B := ⟨by simpa [A] using ht, X.zero_mem_boxFlowDomain y⟩
  have H := IsIntegralCurveOn.eqOn hI hI'
    (((X.isIntegralCurveOn_boxFlow x).comp_add t).mono inter_subset_left)
    ((X.isIntegralCurveOn_boxFlow y).mono inter_subset_right) h0
    (by simp [y, X.boxFlow_zero])
  exact H ⟨hst, hs⟩

end SmoothVectorField

end LocallyConvex.Manifolds
