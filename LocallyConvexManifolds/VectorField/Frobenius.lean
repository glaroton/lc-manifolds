/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.Symplectic.Darboux
public import LocallyConvexAnalysis.Frobenius.Chart

/-!
# The Frobenius theorem on Banach manifolds

Let `M` be a manifold modeled on a normed space `E`. A **distribution** `D` on `M` assigns to each
`x ∈ M` a subspace `D x` of `T_x M`, read in the preferred chart at `x`. We call it **smooth and
split of type `(E₁, E₂)`** (`Distribution.IsSmoothSplit`) if around each point `x₀`, read in the
preferred chart `i` at `x₀` and after a linear isomorphism `ℓ : E ≃ E₁ × E₂`, it is the field of
graphs of a smooth map `f : ℓ(W) → L(E₁, E₂)`. This is the local form of a split subbundle of
`TM` with fibre `E₁` and complement `E₂` (Lang, *Fundamentals of Differential Geometry*, GTM 191,
Springer (1999), Ch. VI, §1, pp. 155–157). `D` is **involutive** (`Distribution.IsInvolutive`) if
the bracket of two `C¹` vector fields tangent to `D` near a point lies in `D` at that point.

**Theorem** (`Distribution.IsInvolutive.exists_flat_chart`, `Distribution.isInvolutive_iff_flat`).
If `E₁` and `E₂` are Banach spaces and `D` is smooth, split and involutive, then around every
point there is a chart `φ` of the maximal atlas in which `D` is the constant subspace `ℓ⁻¹(E₁ × 0)`
(Lang, Ch. VI, Theorem 1.1, p. 156, and Theorem 1.2, p. 158). Conversely, a distribution with flat
charts is involutive (`Distribution.isInvolutive_of_flat`), with no completeness or splitting
hypothesis.

## Proof

In the chart `i`, after `ℓ`, the fields `X_a(z) = (a, f(z) a)`, `a ∈ E₁`, are tangent to `D`, and
their bracket lies in `D` exactly when `f` satisfies Penot's condition (Frob)
(`LocallyConvex.Analysis.lieBracket_mem_graph_iff`). Extending `X_a` by `0` outside the chart
domain gives vector fields on `M` that are smooth near every point of the domain, so involutivity
gives (Frob) on `ℓ(W)` (`Distribution.IsInvolutive.frob`). The Frobenius theorem in chart form
(`LocallyConvex.Analysis.exists_frobenius_chart`) gives `Φ` with `DΦ(q)(E₁ × 0) = graph f(Φ q)`,
and `φ = ψ⁻¹ ∘ i` with `ψ = ℓ⁻¹ ∘ Φ ∘ ℓ` is the required chart.

For the converse, the fields read in a flat chart take values in the closed subspace
`ℓ⁻¹(E₁ × 0)`, so their bracket does too (`localBracket_mem_of_eventually_mem`), and the bracket
is transported back to the preferred chart by `localBracket_transition`.

## Infinite-dimensional subtleties

* **Local fields.** On a Banach manifold there need not be smooth bump functions, so a local
  vector field need not extend to a global one. Involutivity is therefore required for vector
  fields that are only `C¹` near the point (in the preferred chart there); asking it only for
  global fields would be a weaker condition, and the proof would not go through.
* **Splitting.** The subspaces `D x` must be complemented, with a complement depending smoothly on
  the point; this is part of `IsSmoothSplit`. Closed subspaces of Banach spaces need not be
  complemented.
* **Completeness.** `E₁` and `E₂` are complete, for the inverse function theorem and the linear
  differential equations in Penot's proof.
-/

@[expose] public section

open Set Filter Bundle
open scoped Topology Manifold ContDiff
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

section Local

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- On normed spaces the local bracket of fields differentiable at `y` is the Lie bracket of
Mathlib. -/
theorem localBracket_eq_lieBracket {X Y : E → E} {y : E} (hX : DifferentiableAt ℝ X y)
    (hY : DifferentiableAt ℝ Y y) : localBracket X Y y = VectorField.lieBracket ℝ X Y y := by
  rw [localBracket, VectorField.lieBracket_eq, (hY.hasFDerivAt.hasDirDerivAt _).dMB_eq,
    (hX.hasFDerivAt.hasDirDerivAt _).dMB_eq]

/-- The Lie bracket commutes with a linear change of variables. -/
theorem lieBracket_conj (ℓ : E ≃L[ℝ] F) {V W : F → F} {y : E}
    (hV : DifferentiableAt ℝ V (ℓ y)) (hW : DifferentiableAt ℝ W (ℓ y)) :
    VectorField.lieBracket ℝ (fun y ↦ ℓ.symm (V (ℓ y))) (fun y ↦ ℓ.symm (W (ℓ y))) y =
      ℓ.symm (VectorField.lieBracket ℝ V W (ℓ y)) := by
  have hd : ∀ {Z : F → F}, DifferentiableAt ℝ Z (ℓ y) →
      HasFDerivAt (fun y ↦ ℓ.symm (Z (ℓ y)))
        ((ℓ.symm : F →L[ℝ] E).comp ((fderiv ℝ Z (ℓ y)).comp (ℓ : E →L[ℝ] F))) y :=
    fun hZ ↦ ℓ.symm.hasFDerivAt.comp y (hZ.hasFDerivAt.comp y ℓ.hasFDerivAt)
  rw [VectorField.lieBracket_eq, VectorField.lieBracket_eq]
  beta_reduce
  rw [(hd hV).fderiv, (hd hW).fderiv]
  simp [map_sub]

variable {E₁ E₂ : Type} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- **(Frob) from the bracket of the graph fields.** For `V_a(z) = (a, f(z) a)`, if the bracket
of `ℓ⁻¹ ∘ V_a ∘ ℓ` and `ℓ⁻¹ ∘ V_b ∘ ℓ` at `y`, read through `ℓ`, lies in `graph f(ℓ y)`, then
`Df(ℓ y)(a, f a) b = Df(ℓ y)(b, f b) a`. -/
theorem frob_of_localBracket (ℓ : E ≃L[ℝ] E₁ × E₂) {f : E₁ × E₂ → E₁ →L[ℝ] E₂} {y : E}
    (hf : DifferentiableAt ℝ f (ℓ y)) (a b : E₁)
    (h : (ℓ (localBracket (fun y ↦ ℓ.symm (a, f (ℓ y) a)) (fun y ↦ ℓ.symm (b, f (ℓ y) b)) y)).2 =
      f (ℓ y) (ℓ (localBracket (fun y ↦ ℓ.symm (a, f (ℓ y) a))
        (fun y ↦ ℓ.symm (b, f (ℓ y) b)) y)).1) :
    fderiv ℝ f (ℓ y) (a, f (ℓ y) a) b = fderiv ℝ f (ℓ y) (b, f (ℓ y) b) a := by
  have hS : ∀ c : E₁, DifferentiableAt ℝ (fun z : E₁ × E₂ ↦ (c, f z c)) (ℓ y) := fun c ↦
    (differentiableAt_const c).prodMk (hf.clm_apply (differentiableAt_const c))
  have hSf : ∀ c : E₁, ∀ᶠ z in 𝓝 (ℓ y),
      ((fun z : E₁ × E₂ ↦ (c, f z c)) z) ∈ (f z : E₁ →ₗ[ℝ] E₂).graph := fun c ↦
    Eventually.of_forall fun z ↦ (LinearMap.mem_graph_iff _ _).2 rfl
  have hw : ∀ c : E₁, DifferentiableAt ℝ (fun y ↦ ℓ.symm (c, f (ℓ y) c)) y := fun c ↦
    ℓ.symm.differentiableAt.comp y ((hS c).comp y ℓ.differentiableAt)
  rw [localBracket_eq_lieBracket (hw a) (hw b),
    lieBracket_conj ℓ (V := fun z ↦ (a, f z a)) (W := fun z ↦ (b, f z b)) (hS a) (hS b),
    ContinuousLinearEquiv.apply_symm_apply] at h
  exact (lieBracket_mem_graph_iff hf (hS a) (hS b) (hSf a) (hSf b)).1
    ((LinearMap.mem_graph_iff _ _).2 h)

/-- If `Φ(x, y) = (x, α(x, y))` is a local diffeomorphism with `DΦ(q)(a, 0) = (a, g a)`, then
`DΦ(q) v ∈ graph g` exactly when `v ∈ E₁ × 0`. -/
theorem fderiv_mem_graph_iff {g : E₁ →L[ℝ] E₂}
    {L : E₁ × E₂ →L[ℝ] E₁ × E₂} (hL : ∀ a : E₁, L (a, 0) = (a, g a))
    (hfst : ∀ v, (L v).1 = v.1) (hinj : Function.Injective L) (v : E₁ × E₂) :
    (L v).2 = g (L v).1 ↔ v.2 = 0 := by
  have hv : v = (v.1, 0) + (0, v.2) := by simp
  have h0 : (L (0, v.2)).1 = 0 := hfst _
  constructor
  · intro h
    rw [hv, map_add, hL] at h
    simp only [Prod.fst_add, Prod.snd_add, h0, add_zero, add_eq_left] at h
    have : L (0, v.2) = 0 := Prod.ext h0 h
    have := hinj (this.trans (map_zero L).symm)
    exact congrArg Prod.snd this
  · intro h
    rw [hv, h, Prod.mk_zero_zero, add_zero, hL]

/-- A left inverse differentiable at the image point makes the derivative injective. -/
theorem fderiv_injective_of_leftInverse {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {Φ Ψ : G → G} {q : G} (hΦ : DifferentiableAt ℝ Φ q) (hΨ : DifferentiableAt ℝ Ψ (Φ q))
    (h : ∀ᶠ p in 𝓝 q, Ψ (Φ p) = p) : Function.Injective (fderiv ℝ Φ q) := by
  have hcomp := (hΨ.hasFDerivAt.comp q hΦ.hasFDerivAt).congr_of_eventuallyEq
    (h.mono fun p hp ↦ hp.symm : (fun p ↦ p) =ᶠ[𝓝 q] Ψ ∘ Φ)
  have hid := hcomp.unique (hasFDerivAt_id q)
  intro a b hab
  have := congrArg (fun L : G →L[ℝ] G ↦ L a) hid
  have h2 := congrArg (fun L : G →L[ℝ] G ↦ L b) hid
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this h2
  rw [← this, ← h2, hab]

/-- If `(Φ p).1 = p.1` near `q`, the derivative of `Φ` at `q` preserves first components. -/
theorem fderiv_fst_of_fst_eq {Φ : E₁ × E₂ → E₁ × E₂} {q : E₁ × E₂}
    (hΦ : DifferentiableAt ℝ Φ q) (h : ∀ᶠ p in 𝓝 q, (Φ p).1 = p.1) (v : E₁ × E₂) :
    (fderiv ℝ Φ q v).1 = v.1 := by
  have h1 := hΦ.hasFDerivAt.fst
  have h2 := (hasFDerivAt_fst (𝕜 := ℝ) (E := E₁) (F := E₂) (p := q)).congr_of_eventuallyEq h
  exact congrArg (fun L : E₁ × E₂ →L[ℝ] E₁ ↦ L v) (h1.unique h2)

end Local

section Distribution

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

/-! ### Transition maps and subspace-valued fields -/


omit [MBManifold E M] in
/-- Transition maps between charts of the maximal atlas are Fréchet differentiable. -/
theorem hasFDerivAt_transition_of_mem_maximalAtlas {e e' : OpenPartialHomeomorph M E}
    (he : e ∈ (mbGroupoid E).maximalAtlas M) (he' : e' ∈ (mbGroupoid E).maximalAtlas M)
    {z : E} (hz : z ∈ e.target) (hz' : e.symm z ∈ e'.source) :
    HasFDerivAt (e' ∘ e.symm) (fderiv ℝ (e' ∘ e.symm) z) z := by
  have h := (mbGroupoid E).compatible_of_mem_maximalAtlas he he'
  have hs : IsOpen (e.symm ≫ₕ e').source := (e.symm ≫ₕ e').open_source
  have hzs : z ∈ (e.symm ≫ₕ e').source := by
    rw [OpenPartialHomeomorph.trans_source]
    exact ⟨hz, hz'⟩
  have hd := (((smoothMBOn_iff_contDiffOn hs).1 h.1).contDiffAt
    (hs.mem_nhds hzs)).differentiableAt (by simp)
  rw [OpenPartialHomeomorph.coe_trans] at hd
  exact hd.hasFDerivAt

omit [MBManifold E M] in
/-- The cocycle identity for tangent vectors in charts of the maximal atlas. -/
theorem dMB_transition_comp {e₁ e₂ e₃ : OpenPartialHomeomorph M E}
    (he₁ : e₁ ∈ (mbGroupoid E).maximalAtlas M) (he₂ : e₂ ∈ (mbGroupoid E).maximalAtlas M)
    (he₃ : e₃ ∈ (mbGroupoid E).maximalAtlas M) {x : M} (h₁ : x ∈ e₁.source)
    (h₂ : x ∈ e₂.source) (h₃ : x ∈ e₃.source) (v : E) :
    dMB (e₂ ∘ e₃.symm) (e₃ x, dMB (e₃ ∘ e₁.symm) (e₁ x, v)) = dMB (e₂ ∘ e₁.symm) (e₁ x, v) := by
  have H31 := hasFDerivAt_transition_of_mem_maximalAtlas he₁ he₃ (e₁.map_source h₁)
    (by rw [e₁.left_inv h₁]; exact h₃)
  have H23 := hasFDerivAt_transition_of_mem_maximalAtlas he₃ he₂ (e₃.map_source h₃)
    (by rw [e₃.left_inv h₃]; exact h₂)
  have H21 := hasFDerivAt_transition_of_mem_maximalAtlas he₁ he₂ (e₁.map_source h₁)
    (by rw [e₁.left_inv h₁]; exact h₂)
  have hpt : (e₃ ∘ e₁.symm) (e₁ x) = e₃ x := by simp [e₁.left_inv h₁]
  have H23' : HasFDerivAt (e₂ ∘ e₃.symm) (fderiv ℝ (e₂ ∘ e₃.symm) (e₃ x))
      ((e₃ ∘ e₁.symm) (e₁ x)) := by rw [hpt]; exact H23
  have Hc := H23'.comp (e₁ x) H31
  have hev : (e₂ ∘ e₃.symm) ∘ (e₃ ∘ e₁.symm) =ᶠ[𝓝 (e₁ x)] e₂ ∘ e₁.symm := by
    have hn : e₁.target ∩ e₁.symm ⁻¹' e₃.source ∈ 𝓝 (e₁ x) :=
      (e₁.isOpen_inter_preimage_symm e₃.open_source).mem_nhds
        ⟨e₁.map_source h₁, by simp [e₁.left_inv h₁, h₃]⟩
    filter_upwards [hn] with z hz
    simp [e₃.left_inv hz.2]
  have hL := (Hc.congr_of_eventuallyEq hev.symm).unique H21
  rw [(H31.hasDirDerivAt v).dMB_eq, (H23.hasDirDerivAt _).dMB_eq, (H21.hasDirDerivAt v).dMB_eq,
    ← hL]
  rfl

omit [ChartedSpace E M] [MBManifold E M] in
/-- `dMB (e ∘ e⁻¹) (e x, v) = v`. -/
theorem dMB_transition_self {e : OpenPartialHomeomorph M E} {x : M} (hx : x ∈ e.source) (v : E) :
    dMB (e ∘ e.symm) (e x, v) = v := by
  have hev : (e ∘ e.symm) =ᶠ[𝓝 (e x)] id :=
    Filter.eventuallyEq_of_mem (e.open_target.mem_nhds (e.map_source hx)) fun y hy ↦
      e.right_inv hy
  rw [dMB_congr_of_eventuallyEq hev, ((hasFDerivAt_id (e x)).hasDirDerivAt v).dMB_eq]
  rfl

/-- A derivative of a map with values in a closed subspace near the point lies in it. -/
theorem mem_of_hasDirDerivAt_of_eventually_mem {K : Submodule ℝ E} (hK : IsClosed (K : Set E))
    {g : E → E} {y v w : E} (hd : HasDirDerivAt g y v w) (hg : ∀ᶠ z in 𝓝 y, g z ∈ K) :
    w ∈ K := by
  have hc : Tendsto (fun t : ℝ ↦ y + t • v) (𝓝[≠] 0) (𝓝 y) := by
    have hct : Continuous fun t : ℝ ↦ y + t • v := by fun_prop
    have := hct.tendsto 0
    rw [zero_smul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine hK.mem_of_tendsto hd ?_
  filter_upwards [hc.eventually hg] with t ht
  exact K.smul_mem _ (K.sub_mem ht hg.self_of_nhds)

/-- The local bracket of `C¹` fields with values in a closed subspace near `y` lies in it. -/
theorem localBracket_mem_of_eventually_mem {K : Submodule ℝ E} (hK : IsClosed (K : Set E))
    {X Y : E → E} {V : Set E} {y : E} (hy : y ∈ V) (hX : ContDiffMBOn 1 X V)
    (hY : ContDiffMBOn 1 Y V) (hXK : ∀ᶠ z in 𝓝 y, X z ∈ K) (hYK : ∀ᶠ z in 𝓝 y, Y z ∈ K) :
    localBracket X Y y ∈ K :=
  K.sub_mem (mem_of_hasDirDerivAt_of_eventually_mem hK (hY.2.1 y hy (X y)) hYK)
    (mem_of_hasDirDerivAt_of_eventually_mem hK (hX.2.1 y hy (Y y)) hXK)

variable (E M) in
/-- A distribution on `M`: a subspace `D x ⊆ T_x M`, given in the preferred chart at `x`. -/
abbrev Distribution := M → Submodule ℝ E

namespace Distribution

variable (D : Distribution E M)

/-- The subspace `D x`, read in the chart `i` of the atlas. -/
def inChart (i : atlas E M) (x : M) : Set E :=
  {v | tangentCoordChange i (prefChart x) x v ∈ D x}

variable (E₁ E₂ : Type) [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- `D` is **smooth and split of type `(E₁, E₂)`**: around each point `x₀`, read in the preferred
chart at `x₀` and through a linear isomorphism `ℓ : E ≃ E₁ × E₂`, `D` is the field of graphs of a
smooth map `f : ℓ(W) → L(E₁, E₂)`. -/
def IsSmoothSplit : Prop :=
  ∀ x₀ : M, ∃ ℓ : E ≃L[ℝ] E₁ × E₂, ∃ f : E₁ × E₂ → E₁ →L[ℝ] E₂, ∃ W : Set E,
    IsOpen W ∧ chartAt E x₀ x₀ ∈ W ∧ W ⊆ (chartAt E x₀).target ∧
    ContDiffOn ℝ ∞ f (ℓ '' W) ∧
    ∀ y ∈ W, ∀ v : E, v ∈ D.inChart (prefChart x₀) ((chartAt E x₀).symm y) ↔
      (ℓ v).2 = f (ℓ y) (ℓ v).1

/-- `D` is **involutive**: for vector fields `X`, `Y` which are `C¹` near `x` (in the preferred
chart at `x`) and tangent to `D` near `x`, the bracket `[X, Y](x)` lies in `D x`. The fields need
not be `C¹` away from `x`; see the module docstring. -/
def IsInvolutive : Prop :=
  ∀ (x : M) (X Y : M → TangentBundle E M), IsVectorField X → IsVectorField Y →
    ∀ U : Set E, IsOpen U → chartAt E x x ∈ U → U ⊆ (chartAt E x).target →
    ContDiffMBOn 1 (localRep (prefChart x) X) U → ContDiffMBOn 1 (localRep (prefChart x) Y) U →
    (∀ᶠ x' in 𝓝 x, (show E from (X x').2) ∈ D x') →
    (∀ᶠ x' in 𝓝 x, (show E from (Y x').2) ∈ D x') →
    (show E from (lieBracket X Y x).2) ∈ D x

variable {D E₁ E₂}

open Classical in
/-- The vector field which reads `w` in the chart `i`, extended by `0` outside its domain. -/
def chartField (i : atlas E M) (w : E → E) (x : M) : TangentBundle E M :=
  ⟨x, (show E from
    if x ∈ i.1.source then tangentCoordChange i (prefChart (E := E) x) x (w (i.1 x)) else 0)⟩

theorem isVectorField_chartField (i : atlas E M) (w : E → E) :
    IsVectorField (chartField i w) := fun _ ↦ rfl

open Classical in
theorem localRep_chartField (i k : atlas E M) (w : E → E) {y : E} (hy : y ∈ k.1.target)
    (hyi : k.1.symm y ∈ i.1.source) :
    localRep k (chartField i w) y =
      tangentCoordChange i k (k.1.symm y) (w (i.1 (k.1.symm y))) := by
  set q := k.1.symm y
  have hqk : q ∈ k.1.source := k.1.map_target hy
  unfold localRep
  rw [tangentChart_apply]
  change tangentCoordChange (prefChart q) k q
    (if q ∈ i.1.source then tangentCoordChange i (prefChart (E := E) q) q (w (i.1 q))
      else 0) = _
  simp only [hyi, ↓reduceIte]
  rw [tangentCoordChange_comp i (prefChart q) k
    ⟨⟨hyi, mem_chart_source E q⟩, hqk⟩]

open Classical in
/-- **Involutivity gives (Frob).** Under the hypotheses of `IsSmoothSplit` at `x₀`, if `D` is
involutive then `f` satisfies (Frob) on `ℓ(W)`. -/
theorem IsInvolutive.frob (hinv : D.IsInvolutive) {x₀ : M} (ℓ : E ≃L[ℝ] E₁ × E₂)
    {f : E₁ × E₂ → E₁ →L[ℝ] E₂} {W : Set E} (hW : IsOpen W)
    (hWt : W ⊆ (chartAt E x₀).target) (hf : ContDiffOn ℝ ∞ f (ℓ '' W))
    (hgraph : ∀ y ∈ W, ∀ v : E, v ∈ D.inChart (prefChart x₀) ((chartAt E x₀).symm y) ↔
      (ℓ v).2 = f (ℓ y) (ℓ v).1)
    {y : E} (hy : y ∈ W) (a b : E₁) :
    fderiv ℝ f (ℓ y) (a, f (ℓ y) a) b = fderiv ℝ f (ℓ y) (b, f (ℓ y) b) a := by
  set i : atlas E M := prefChart x₀
  have hO : IsOpen (ℓ '' W) := ℓ.toHomeomorph.isOpenMap W hW
  have hfd : DifferentiableAt ℝ f (ℓ y) :=
    ((hf.differentiableOn (by simp)) _ ⟨y, hy, rfl⟩).differentiableAt
      (hO.mem_nhds ⟨y, hy, rfl⟩)
  -- the fields `w_c = ℓ⁻¹ ∘ V_c ∘ ℓ` on `W`
  set w : E₁ → E → E := fun c y ↦ ℓ.symm (c, f (ℓ y) c) with hwdef
  have hwF : ∀ c, ContDiffOn ℝ ∞ (w c) W := fun c ↦ by
    have h1 : ContDiffOn ℝ ∞ (fun z : E₁ × E₂ ↦ (c, f z c)) (ℓ '' W) :=
      contDiffOn_const.prodMk (hf.clm_apply contDiffOn_const)
    exact ℓ.symm.contDiff.comp_contDiffOn (h1.comp ℓ.contDiff.contDiffOn
      fun y hy ↦ ⟨y, hy, rfl⟩)
  have hw1 : ∀ c, ContDiffMBOn 1 (w c) W := fun c ↦
    ContDiffOn.contDiffMBOn hW ((hwF c).of_le (by exact_mod_cast le_top))
  have hwg : ∀ c, ∀ y' ∈ W, w c y' ∈ D.inChart i ((chartAt E x₀).symm y') := fun c y' hy' ↦ by
    rw [hgraph y' hy']; simp [w]
  -- the point and the preferred chart there
  have hyi : y ∈ i.1.target := hWt hy
  set x := i.1.symm y
  have hxi : x ∈ i.1.source := i.1.map_target hyi
  have hix : i.1 x = y := i.1.right_inv hyi
  set j : atlas E M := prefChart x
  set τ := j.1 ∘ i.1.symm
  set T := i.1.target ∩ i.1.symm ⁻¹' j.1.source
  have hT : IsOpen T := isOpen_transition_domain i j
  have hτ : ContDiffMBOn 2 τ T := smoothMBOn_transition' i j 2
  set U := T ∩ W
  have hU : IsOpen U := hT.inter hW
  have hyU : y ∈ U := ⟨⟨hyi, mem_chart_source E x⟩, hy⟩
  set Vj := j.1.target ∩ j.1.symm ⁻¹' (i.1.source ∩ i.1 ⁻¹' W)
  have hVj : IsOpen Vj := j.1.isOpen_inter_preimage_symm (i.1.isOpen_inter_preimage hW)
  have hτU : MapsTo τ U Vj := fun y' hy' ↦ by
    refine ⟨j.1.map_source hy'.1.2, ?_⟩
    simp only [mem_preimage, τ, Function.comp_apply, j.1.left_inv hy'.1.2]
    exact ⟨i.1.map_target hy'.1.1, by
      change i.1 (i.1.symm y') ∈ W; rw [i.1.right_inv hy'.1.1]; exact hy'.2⟩
  -- the fields on `M`
  set X : E₁ → M → TangentBundle E M := fun c ↦ chartField i (w c)
  have hXj : ∀ c, ∀ y' ∈ Vj, localRep j (X c) y' =
      dMB τ ((i.1 ∘ j.1.symm) y', w c ((i.1 ∘ j.1.symm) y')) := fun c y' hy' ↦ by
    rw [localRep_chartField i j _ hy'.1 hy'.2.1]
    simp only [tangentCoordChange, τ, Function.comp_apply]
  -- smoothness of the local representatives in `j`
  have hτF : ContDiffOn ℝ ∞ τ T := (smoothMBOn_iff_contDiffOn hT).1 (smoothMBOn_transition' i j)
  have hσF : ContDiffOn ℝ ∞ (i.1 ∘ j.1.symm) Vj :=
    ((smoothMBOn_iff_contDiffOn (isOpen_transition_domain j i)).1
      (smoothMBOn_transition' j i)).mono fun y' hy' ↦ ⟨hy'.1, hy'.2.1⟩
  have hσU : MapsTo (i.1 ∘ j.1.symm) Vj U := fun y' hy' ↦ by
    have h1 := hy'.2.1
    refine ⟨⟨i.1.map_source h1, ?_⟩, hy'.2.2⟩
    simp only [mem_preimage, Function.comp_apply, i.1.left_inv h1]
    exact j.1.map_target hy'.1
  have hXj1 : ∀ c, ContDiffMBOn 1 (localRep j (X c)) Vj := fun c ↦ by
    have hDτ : ContDiffOn ℝ 1 (fderiv ℝ τ) T :=
      hτF.fderiv_of_isOpen hT (by simp)
    have h1 : ContDiffOn ℝ 1
        (fun y' ↦ fderiv ℝ τ ((i.1 ∘ j.1.symm) y') (w c ((i.1 ∘ j.1.symm) y'))) Vj :=
      (hDτ.comp (hσF.of_le (by exact_mod_cast le_top)) fun y' hy' ↦ (hσU hy').1).clm_apply
        (((hwF c).of_le (by exact_mod_cast le_top)).comp
          (hσF.of_le (by exact_mod_cast le_top)) fun y' hy' ↦ (hσU hy').2)
    refine ContDiffOn.contDiffMBOn hVj (h1.congr fun y' hy' ↦ ?_)
    rw [hXj c y' hy']
    exact ((SmoothVectorField.hasFDerivAt_transition i j (hσU hy').1).2 _).symm
  -- the bracket in `j` is the transported bracket in `i`
  have htrans := localBracket_transition hT hU hVj inter_subset_left hτ hτU
    ((hw1 a).mono inter_subset_right) ((hw1 b).mono inter_subset_right) (hXj1 a) (hXj1 b)
    (fun y' hy' ↦ by
      have h : (i.1 ∘ j.1.symm) (τ y') = y' := by
        simp only [τ, Function.comp_apply, j.1.left_inv hy'.1.2, i.1.right_inv hy'.1.1]
      rw [hXj a _ (hτU hy'), h])
    (fun y' hy' ↦ by
      have h : (i.1 ∘ j.1.symm) (τ y') = y' := by
        simp only [τ, Function.comp_apply, j.1.left_inv hy'.1.2, i.1.right_inv hy'.1.1]
      rw [hXj b _ (hτU hy'), h]) hyU
  -- involutivity at `x`
  have hjx : chartAt E x x ∈ Vj := by
    refine ⟨(chartAt E x).map_source (mem_chart_source E x), ?_⟩
    change (chartAt E x).symm (chartAt E x x) ∈ i.1.source ∩ i.1 ⁻¹' W
    rw [(chartAt E x).left_inv (mem_chart_source E x)]
    exact ⟨hxi, by rw [mem_preimage, hix]; exact hy⟩
  have htan : ∀ c, ∀ᶠ x' in 𝓝 x, (show E from (X c x').2) ∈ D x' := fun c ↦ by
    have hnhds : i.1.source ∩ i.1 ⁻¹' W ∈ 𝓝 x :=
      (i.1.isOpen_inter_preimage hW).mem_nhds ⟨hxi, by rw [mem_preimage, hix]; exact hy⟩
    filter_upwards [hnhds] with x' hx'
    have h := hwg c (i.1 x') hx'.2
    rw [i.1.left_inv hx'.1] at h
    change (if x' ∈ i.1.source then _ else _) ∈ D x'
    simp only [hx'.1, ↓reduceIte]
    exact h
  have hbr := hinv x (X a) (X b) (isVectorField_chartField _ _) (isVectorField_chartField _ _)
    Vj hVj hjx (fun _ h ↦ h.1) (hXj1 a) (hXj1 b) (htan a) (htan b)
  have hτy : τ y = chartAt E x x := rfl
  change localBracket (localRep j (X a)) (localRep j (X b)) (chartAt E x x) ∈ D x at hbr
  rw [← hτy, htrans] at hbr
  have hmem : localBracket (w a) (w b) y ∈ D.inChart i x := by
    change tangentCoordChange i (prefChart x) x _ ∈ D x
    rw [tangentCoordChange, hix]
    exact hbr
  exact frob_of_localBracket ℓ hfd a b ((hgraph y hy _).1 hmem)

/-- **The Frobenius theorem on Banach manifolds** (Lang, *Fundamentals of Differential
Geometry*, Ch. VI, Theorem 1.1, p. 156, and Theorem 1.2, p. 158). Let `D` be a smooth split
distribution of type `(E₁, E₂)`, with `E₁` and `E₂` Banach spaces, which is involutive. Then
around every `x₀ ∈ M` there is a chart `φ` of the maximal atlas, with `φ(x₀) = i(x₀)` for the
preferred chart `i` at `x₀`, in which `D` is constant: a vector `u` given in the chart `φ` at `x`
lies in `D x` if and only if `ℓ u ∈ E₁ × 0`. -/
theorem IsInvolutive.exists_flat_chart [CompleteSpace E₁] [CompleteSpace E₂]
    (hsplit : D.IsSmoothSplit E₁ E₂) (hinv : D.IsInvolutive) (x₀ : M) :
    ∃ ℓ : E ≃L[ℝ] E₁ × E₂, ∃ φ : OpenPartialHomeomorph M E,
      φ ∈ (mbGroupoid E).maximalAtlas M ∧ x₀ ∈ φ.source ∧ φ x₀ = chartAt E x₀ x₀ ∧
      ∀ x ∈ φ.source, ∀ u : E,
        dMB (chartAt E x ∘ φ.symm) (φ x, u) ∈ D x ↔ (ℓ u).2 = 0 := by
  obtain ⟨ℓ, f, W, hW, hx₀W, hWt, hf, hgraph⟩ := hsplit x₀
  set i : atlas E M := prefChart x₀ with hidef
  set O := ℓ '' W
  have hO : IsOpen O := ℓ.toHomeomorph.isOpenMap W hW
  have hfrob : ∀ q ∈ O, ∀ a b : E₁, fderiv ℝ f q (a, f q a) b = fderiv ℝ f q (b, f q b) a := by
    rintro _ ⟨y, hy, rfl⟩ a b
    exact hinv.frob ℓ hW hWt hf hgraph hy a b
  set z₀ := ℓ (chartAt E x₀ x₀)
  have hz₀ : (z₀.1, z₀.2) ∈ O := ⟨_, hx₀W, rfl⟩
  obtain ⟨Φ, hz₀s, hΦz₀, -, hΦtO, hΦs, hΦs', hΦ1, hΦd, -⟩ :=
    exists_frobenius_chart (𝕜 := ℝ) hO (n := ⊤) le_top hf hfrob hz₀
  simp only [Prod.mk.eta] at hz₀s hΦz₀
  -- `ψ = ℓ⁻¹ ∘ Φ ∘ ℓ`
  set eℓ : OpenPartialHomeomorph E (E₁ × E₂) := ℓ.toHomeomorph.toOpenPartialHomeomorph
  set ψ : OpenPartialHomeomorph E E := eℓ.trans (Φ.trans eℓ.symm)
  have hψ : ∀ y, ψ y = ℓ.symm (Φ (ℓ y)) := fun _ ↦ rfl
  have hψsymm : ∀ y, ψ.symm y = ℓ.symm (Φ.symm (ℓ y)) := fun _ ↦ rfl
  have hψsrc : ∀ y, y ∈ ψ.source ↔ ℓ y ∈ Φ.source := fun y ↦ by simp [ψ, eℓ]
  have hψtgt : ∀ y, y ∈ ψ.target ↔ ℓ y ∈ Φ.target := fun y ↦ by simp [ψ, eℓ]
  have hψs : ContDiffOn ℝ ∞ ψ ψ.source := by
    have := ℓ.symm.contDiff.comp_contDiffOn (hΦs.comp ℓ.contDiff.contDiffOn
      fun y hy ↦ (hψsrc y).1 hy)
    exact this.congr fun y _ ↦ rfl
  have hψs' : ContDiffOn ℝ ∞ ψ.symm ψ.target := by
    have := ℓ.symm.contDiff.comp_contDiffOn (hΦs'.comp ℓ.contDiff.contDiffOn
      fun y hy ↦ (hψtgt y).1 hy)
    exact this.congr fun y _ ↦ rfl
  have hψG : ψ.symm ∈ mbGroupoid E :=
    ⟨(smoothMBOn_iff_contDiffOn ψ.open_target).2 hψs',
      (smoothMBOn_iff_contDiffOn ψ.open_source).2 hψs⟩
  have hψG' : ψ ∈ mbGroupoid E := by simpa using (mbGroupoid E).symm hψG
  set φ := i.1.trans ψ.symm
  -- tangent vectors given in the chart `φ`, read in the preferred charts
  have hvec : ∀ x ∈ φ.source, ∀ u,
      dMB (chartAt E x ∘ φ.symm) (φ x, u) =
        tangentCoordChange i (prefChart x) x (fderiv ℝ ψ (φ x) u) := by
    intro x hx u
    rw [OpenPartialHomeomorph.trans_source] at hx
    obtain ⟨hxi, hxψ⟩ := hx
    have hxψ' : i.1 x ∈ ψ.target := hxψ
    have hy : ψ.symm (i.1 x) ∈ ψ.source := ψ.map_target hxψ'
    have hψy : ψ (ψ.symm (i.1 x)) = i.1 x := ψ.right_inv hxψ'
    have hfun : ⇑(chartAt E x) ∘ ⇑φ.symm = (chartAt E x ∘ i.1.symm) ∘ ψ := by
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
  -- `Φ` fixes `z₀`
  have hz₀t : z₀ ∈ Φ.target := by rw [← hΦz₀]; exact Φ.map_source hz₀s
  have hΦsz₀ : Φ.symm z₀ = z₀ := by
    have := Φ.left_inv hz₀s
    rwa [hΦz₀] at this
  have hx₀ : x₀ ∈ φ.source := by
    rw [OpenPartialHomeomorph.trans_source]
    exact ⟨mem_chart_source E x₀, (hψtgt _).2 hz₀t⟩
  have hφx₀ : φ x₀ = i.1 x₀ := by
    change ψ.symm (i.1 x₀) = i.1 x₀
    rw [hψsymm]
    change ℓ.symm (Φ.symm z₀) = _
    rw [hΦsz₀, ContinuousLinearEquiv.symm_apply_apply]
  refine ⟨ℓ, φ, ?_, hx₀, hφx₀, fun x hx u ↦ ?_⟩
  · refine mem_maximalAtlas_iff.2 fun e' he' ↦ ⟨?_, ?_⟩
    · rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm,
        OpenPartialHomeomorph.trans_assoc]
      exact (mbGroupoid E).trans hψG' ((mbGroupoid E).compatible i.2 he')
    · rw [← OpenPartialHomeomorph.trans_assoc]
      exact (mbGroupoid E).trans ((mbGroupoid E).compatible he' i.2) hψG
  rw [hvec x hx u]
  have hx' := hx
  rw [OpenPartialHomeomorph.trans_source] at hx'
  obtain ⟨hxi, hxψ⟩ := hx'
  set y := i.1 x with hydef
  have hyψ : y ∈ ψ.target := hxψ
  have hℓy : ℓ y ∈ Φ.target := (hψtgt y).1 hyψ
  obtain ⟨y', hy'W, hy'⟩ := hΦtO hℓy
  have hyW : y ∈ W := by rwa [← ℓ.injective hy']
  set p := φ x
  have hp : p = ψ.symm y := rfl
  have hps : p ∈ ψ.source := ψ.map_target hyψ
  set q := ℓ p
  have hqs : q ∈ Φ.source := (hψsrc p).1 hps
  have hΦq : Φ q = ℓ y := by
    have h := ψ.right_inv hyψ
    rw [← hp, hψ] at h
    rw [← h, ContinuousLinearEquiv.apply_symm_apply]
  have hΦdiff : DifferentiableAt ℝ Φ q :=
    (hΦs.differentiableOn (by simp) q hqs).differentiableAt (Φ.open_source.mem_nhds hqs)
  have hψdq : fderiv ℝ ψ p u = ℓ.symm (fderiv ℝ Φ q (ℓ u)) := by
    have hd : HasFDerivAt (fun y ↦ ℓ.symm (Φ (ℓ y)))
        ((ℓ.symm : E₁ × E₂ →L[ℝ] E).comp ((fderiv ℝ Φ q).comp (ℓ : E →L[ℝ] E₁ × E₂))) p :=
      ℓ.symm.hasFDerivAt.comp p (hΦdiff.hasFDerivAt.comp p ℓ.hasFDerivAt)
    rw [show (ψ : E → E) = fun y ↦ ℓ.symm (Φ (ℓ y)) from rfl, hd.fderiv]
    rfl
  -- `D x` in the chart `i` is the graph of `f`
  have hmem : tangentCoordChange i (prefChart x) x (fderiv ℝ ψ p u) ∈ D x ↔
      (ℓ (fderiv ℝ ψ p u)).2 = f (ℓ y) (ℓ (fderiv ℝ ψ p u)).1 := by
    have := hgraph y hyW (fderiv ℝ ψ p u)
    rwa [hydef, i.1.left_inv hxi] at this
  rw [hmem, hψdq, ContinuousLinearEquiv.apply_symm_apply, ← hΦq]
  have hΦtq : Φ q ∈ Φ.target := Φ.map_source hqs
  have hΦsdiff : DifferentiableAt ℝ Φ.symm (Φ q) :=
    (hΦs'.differentiableOn (by simp) _ hΦtq).differentiableAt (Φ.open_target.mem_nhds hΦtq)
  have hinj := fderiv_injective_of_leftInverse hΦdiff hΦsdiff
    (eventually_of_mem (Φ.open_source.mem_nhds hqs) fun r hr ↦ Φ.left_inv hr)
  have hfst := fderiv_fst_of_fst_eq hΦdiff
    (eventually_of_mem (Φ.open_source.mem_nhds hqs) fun r hr ↦ hΦ1 r hr)
  exact fderiv_mem_graph_iff (hΦd q hqs) hfst hinj (ℓ u)

/-- **Converse of the Frobenius theorem.** If around every point there is a chart `φ` of the
maximal atlas in which `D` is constant, `D x = {u : (ℓ u).2 = 0}` read in `φ`, then `D` is
involutive. -/
theorem isInvolutive_of_flat
    (hflat : ∀ x₀ : M, ∃ ℓ : E ≃L[ℝ] E₁ × E₂, ∃ φ : OpenPartialHomeomorph M E,
      φ ∈ (mbGroupoid E).maximalAtlas M ∧ x₀ ∈ φ.source ∧ ∀ x ∈ φ.source, ∀ u : E,
        dMB (chartAt E x ∘ φ.symm) (φ x, u) ∈ D x ↔ (ℓ u).2 = 0) :
    D.IsInvolutive := by
  intro x X Y hXv hYv U hU hxU hUt hX1 hY1 hXD hYD
  obtain ⟨ℓ, φ, hφ, hxφ, hfl⟩ := hflat x
  set c := chartAt E x with hcdef
  have hcm : ∀ x' : M, chartAt E x' ∈ (mbGroupoid E).maximalAtlas M := fun x' ↦
    StructureGroupoid.subset_maximalAtlas _ (chart_mem_atlas E x')
  -- the constant subspace `K = ℓ⁻¹(E₁ × 0)`
  let L : E →L[ℝ] E₂ := (ContinuousLinearMap.snd ℝ E₁ E₂).comp (ℓ : E →L[ℝ] E₁ × E₂)
  let K : Submodule ℝ E := LinearMap.ker (L : E →ₗ[ℝ] E₂)
  have hKc : IsClosed (K : Set E) := L.isClosed_ker
  have hK : ∀ u, u ∈ K ↔ (ℓ u).2 = 0 := fun u ↦ Iff.rfl
  -- the transition maps
  set τ : E → E := φ ∘ c.symm with hτdef
  set σ : E → E := c ∘ φ.symm with hσdef
  set A := c.target ∩ c.symm ⁻¹' φ.source
  set B := φ.target ∩ φ.symm ⁻¹' c.source
  have hA : IsOpen A := c.isOpen_inter_preimage_symm φ.open_source
  have hB : IsOpen B := φ.isOpen_inter_preimage_symm c.open_source
  have hτs : SmoothMBOn τ A := by
    have h := ((mbGroupoid E).compatible_of_mem_maximalAtlas (hcm x) hφ).1
    rwa [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.coe_trans,
      OpenPartialHomeomorph.symm_source] at h
  have hσs : SmoothMBOn σ B := by
    have h := ((mbGroupoid E).compatible_of_mem_maximalAtlas hφ (hcm x)).1
    rwa [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.coe_trans,
      OpenPartialHomeomorph.symm_source] at h
  have hxc : x ∈ c.source := mem_chart_source E x
  have hcxA : c x ∈ A := ⟨c.map_source hxc, by rw [mem_preimage, c.left_inv hxc]; exact hxφ⟩
  have hστ : ∀ y ∈ A, σ (τ y) = y := fun y hy ↦ by
    simp only [σ, τ, Function.comp_apply, φ.left_inv hy.2, c.right_inv hy.1]
  have hτB : MapsTo τ A B := fun y hy ↦ ⟨φ.map_source hy.2, by
    simp only [mem_preimage, τ, Function.comp_apply, φ.left_inv hy.2]; exact c.map_target hy.1⟩
  have hτcx : τ (c x) = φ x := by simp [τ, c.left_inv hxc]
  -- the domains
  set U' := A ∩ U
  have hU' : IsOpen U' := hA.inter hU
  have hσc : ContinuousOn σ B := hσs 0
  set V' := B ∩ σ ⁻¹' U'
  have hV' : IsOpen V' := hσc.isOpen_inter_preimage hB hU'
  have hτV : MapsTo τ U' V' := fun y hy ↦ ⟨hτB hy.1, by
    simp only [mem_preimage, hστ y hy.1]; exact hy⟩
  have hcxU' : c x ∈ U' := ⟨hcxA, hxU⟩
  -- the fields read in `φ`
  have hfield : ∀ {Z : E → E}, ContDiffMBOn 1 Z U →
      ContDiffMBOn 1 (fun z ↦ dMB τ (σ z, Z (σ z))) V' := by
    intro Z hZ
    have h1 : ContDiffMBOn 1 σ V' := (hσs 1).mono inter_subset_left
    have h2 : ContDiffMBOn 1 (Z ∘ σ) V' :=
      ContDiffMBOn.comp hV' hU hZ h1 fun z hz ↦ hz.2.2
    have h3 : ContDiffMBOn 1 (fun z ↦ (σ z, Z (σ z))) V' := ContDiffMBOn.prodMk hV' h1 h2
    exact ContDiffMBOn.comp (g := dMB τ) (f := fun z ↦ (σ z, Z (σ z))) hV'
      (hA.prod isOpen_univ) (hτs 2).2.2 h3 fun z hz ↦ ⟨hz.2.1, mem_univ _⟩
  set Xj := localRep (prefChart x) X
  set Yj := localRep (prefChart x) Y
  have htrans := localBracket_transition hA hU' hV' inter_subset_left (hτs 2) hτV
    (hX1.mono inter_subset_right) (hY1.mono inter_subset_right) (hfield hX1) (hfield hY1)
    (fun y hy ↦ by rw [hστ y hy.1]) (fun y hy ↦ by rw [hστ y hy.1])
    hcxU'
  -- the fields read in `φ` are tangent to `ℓ⁻¹(E₁ × 0)` near `φ x`
  have htan : ∀ {Z : M → TangentBundle E M}, IsVectorField Z →
      (∀ᶠ x' in 𝓝 x, (show E from (Z x').2) ∈ D x') →
      ∀ᶠ z in 𝓝 (φ x), dMB τ (σ z, localRep (prefChart x) Z (σ z)) ∈ K := by
    intro Z hZv hZD
    have h1 : ∀ᶠ z in 𝓝 (φ x), (show E from (Z (φ.symm z)).2) ∈ D (φ.symm z) := by
      have hcont : ContinuousAt φ.symm (φ x) := φ.continuousAt_symm (φ.map_source hxφ)
      rw [ContinuousAt, φ.left_inv hxφ] at hcont
      exact hcont.eventually hZD
    have h2 : B ∈ 𝓝 (φ x) := hB.mem_nhds ⟨φ.map_source hxφ, by
      rw [mem_preimage, φ.left_inv hxφ]; exact hxc⟩
    filter_upwards [h1, h2] with z hz hzB
    set x' := φ.symm z with hx'def
    have hx'φ : x' ∈ φ.source := φ.map_target hzB.1
    have hx'c : x' ∈ c.source := hzB.2
    have hφx' : φ x' = z := φ.right_inv hzB.1
    have hx'c' : x' ∈ (chartAt E x').source := mem_chart_source E x'
    rw [hK, ← hfl x' hx'φ, hφx']
    have hZj : localRep (prefChart x) Z (σ z) =
        dMB (c ∘ (chartAt E x').symm) (chartAt E x' x', (show E from (Z x').2)) := by
      have hσz : σ z = c x' := rfl
      rw [hσz]
      unfold localRep
      rw [tangentChart_apply]
      change tangentCoordChange _ (prefChart x) (Z (c.symm (c x'))).1 _ = _
      rw [c.left_inv hx'c]
      have hv := hZv x'
      rcases hZpt : Z x' with ⟨p1, p2⟩
      have hp1 : p1 = x' := by rw [hZpt] at hv; exact hv
      subst hp1
      rfl
    rw [hZj]
    have hσz : σ z = c x' := rfl
    rw [hσz, dMB_transition_comp (hcm x') hφ (hcm x) hx'c' hx'φ hx'c,
      ← hφx', dMB_transition_comp (hcm x') (hcm x') hφ hx'c' hx'c' hx'φ,
      dMB_transition_self hx'c']
    exact hz
  -- the bracket in `φ` lies in `K`
  have hbφ : localBracket (fun z ↦ dMB τ (σ z, Xj (σ z))) (fun z ↦ dMB τ (σ z, Yj (σ z)))
      (τ (c x)) ∈ K := by
    rw [hτcx]
    exact localBracket_mem_of_eventually_mem hKc (hτcx ▸ hτV hcxU') (hfield hX1) (hfield hY1)
      (htan hXv hXD) (htan hYv hYD)
  rw [htrans] at hbφ
  -- back to the preferred chart at `x`
  have hkey : dMB σ (φ x, dMB τ (c x, localBracket Xj Yj (c x))) = localBracket Xj Yj (c x) := by
    rw [hσdef, hτdef, dMB_transition_comp (hcm x) (hcm x) hφ hxc hxc hxφ,
      dMB_transition_self hxc]
  change localBracket Xj Yj (c x) ∈ D x
  rw [← hkey]
  exact (hfl x hxφ _).2 ((hK _).1 hbφ)

/-- **The Frobenius theorem as an equivalence** (Lang, Ch. VI, §1, pp. 155–158): a smooth split
distribution with Banach fibre and complement is involutive if and only if it admits flat charts
around every point. -/
theorem isInvolutive_iff_flat [CompleteSpace E₁] [CompleteSpace E₂]
    (hsplit : D.IsSmoothSplit E₁ E₂) :
    D.IsInvolutive ↔ ∀ x₀ : M, ∃ ℓ : E ≃L[ℝ] E₁ × E₂, ∃ φ : OpenPartialHomeomorph M E,
      φ ∈ (mbGroupoid E).maximalAtlas M ∧ x₀ ∈ φ.source ∧ ∀ x ∈ φ.source, ∀ u : E,
        dMB (chartAt E x ∘ φ.symm) (φ x, u) ∈ D x ↔ (ℓ u).2 = 0 := by
  refine ⟨fun hinv x₀ ↦ ?_, isInvolutive_of_flat⟩
  obtain ⟨ℓ, φ, hφ, hx₀, -, h⟩ := hinv.exists_flat_chart hsplit x₀
  exact ⟨ℓ, φ, hφ, hx₀, h⟩

end Distribution

end Distribution

end LocallyConvex.Manifolds
