/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.Flow.Existence

/-!
# The maximal flow of a smooth vector field on a Banach manifold

Let `X` be a smooth vector field on a Hausdorff manifold `M` modeled on a Banach space. By
uniqueness of integral curves (`SmoothVectorField.IsIntegralCurveOn.eqOn`), the integral curves of
`X` starting at `x` glue to a **maximal integral curve**, defined on an open interval `J_x ∋ 0`.

## Main definitions

* `SmoothVectorField.maxInterval`, `SmoothVectorField.flowDomain`, `SmoothVectorField.flow`: the
  maximal interval `J_x`, the domain `D = {(t, x) | t ∈ J_x}` and the **maximal flow**
  `Fl(t, x)`.
* `SmoothVectorField.IsIntegralCurveThrough`: integral curves through a point.

## Main results

* `SmoothVectorField.isIntegralCurveThrough_flow` and
  `SmoothVectorField.IsIntegralCurveThrough.subset_maxInterval`,
  `SmoothVectorField.IsIntegralCurveThrough.flow_eq` (**maximality**): `t ↦ Fl(t, x)` is an
  integral curve through `x` on `J_x`, and every integral curve through `x` on an open interval
  `I ∋ 0` is its restriction to `I`.
* `SmoothVectorField.maxInterval_flow`, `SmoothVectorField.flow_add` (**group law**,
  [Lan99, Ch. IV, §2, Theorem 2.2, p. 91], [GN26, Remark 2.5.24 (c), p. 223]): if
  `t ∈ J_x` then `J_{Fl(t, x)} = J_x - t`, and `Fl(s + t, x) = Fl(s, Fl(t, x))` whenever
  `(t, x) ∈ D` and `(s, Fl(t, x)) ∈ D`; then `(s + t, x) ∈ D`
  (`SmoothVectorField.add_mem_flowDomain`).
* `SmoothVectorField.isOpen_flowDomain`, `SmoothVectorField.smoothMBMOn_flow`: **the domain `D` is
  open in `ℝ × M` and the maximal flow is smooth on `D`** ([Lan99, Ch. IV, §2, Theorem 2.6,
  p. 92], [GN26, Theorem 2.5.18, p. 220], [GN26, Corollary 2.5.21, p. 222]).
* `SmoothVectorField.isLocalFlow_flow`: hence the maximal flow is a local flow in the sense of
  `IsLocalFlow` (compare [GN26, Definition 2.5.23]), and the formula
  `d/dt|₀ (Fl_t)* ω = L_X ω` of `LocallyConvexManifolds.Flow.LieDerivative` holds for it
  (`SmoothVectorField.hasDirDerivAt_pullback_flow`).
* `SmoothVectorField.boxFlowDomain_subset_flowDomain`, `SmoothVectorField.boxFlow_eq_flow`: the
  flow `boxFlow` of `LocallyConvexManifolds.Flow.Existence`, obtained by gluing flow boxes, is the
  restriction of the maximal flow to the open set `boxFlowDomain ⊆ D`.
* `SmoothVectorField.not_mapClusterPt_flow_of_lt_top`,
  `SmoothVectorField.eventually_flow_not_mem_of_isCompact` (**escape lemma**, [Lan99, Ch. IV, §2,
  Theorem 2.3, p. 91]): if the forward maximal time `b` of `x` is finite, then `t ↦ Fl(t, x)` has
  no cluster point as `t → b⁻`; in particular it eventually leaves every compact set. The same
  holds backwards (`SmoothVectorField.not_mapClusterPt_flow_of_bot_lt`,
  `SmoothVectorField.eventually_flow_not_mem_of_isCompact'`).

## Implementation notes

* Hypotheses. `E` is a Banach space: `[CompleteSpace E]` gives the flow boxes
  (`SmoothVectorField.exists_flowBox`, through the Picard–Lindelöf theorem of
  `LocallyConvexAnalysis.ODE.Flow`) and local uniqueness. On manifolds modeled on Fréchet or
  general locally convex spaces smooth vector fields need neither have integral curves nor unique
  ones [GN26, Examples 2.4.2 and 2.4.3], so neither the maximal curve nor its domain need
  make sense. `M` is Hausdorff (`[T2Space M]`): on the line with two origins the constant vector
  field `∂/∂t` has two integral curves through `-1` which agree up to time `1` and then split, so
  there is no maximal integral curve. Both hypotheses are only assumed where they are used.
* Openness and smoothness. We follow the proofs of Lang [Lan99, Theorem IV.2.6] and
  Glöckner–Neeb [GN26, Theorem 2.5.18]: for a fixed `x₀`, the set of `t ∈ J_{x₀}` around which `D`
  contains a neighbourhood of `(t, x₀)` on which `Fl` is smooth is open, contains `0`, and is
  closed in `J_{x₀}`, because near `t` the flow is `Fl(τ, x) = φ(τ - t₁, Fl(t₁, x))` for a flow
  box `φ` at `Fl(t, x₀)` and `t₁` close to `t`. No compactness argument is needed.
* The escape lemma. Lang proves [Lan99, Theorem IV.2.3] with sequences; since we do not assume
  `M` metrizable or first countable at the level of compact sets, we argue with cluster points of
  filters instead. We do not claim this argument is new. [Lan99, Proposition IV.2.5]
  (completeness of vector fields that are uniformly bounded in suitable charts) is in
  `LocallyConvexManifolds.Flow.Complete`.
* `Fl` takes the junk value `Fl(t, x) = x` outside `D`.
* The real analytic case ([GN26, Corollary 2.5.21], last assertion) is
  `LocallyConvexManifolds.Flow.Analytic`.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
* [S. Lang, *Fundamentals of Differential Geometry*][Lan99]
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

/-! ### Integral curves through a point -/

variable (X : SmoothVectorField E M) in
/-- `c` is an **integral curve of `X` through `x` on `I`**: `I` is an open interval containing
`0`, `c` is an integral curve of `X` on `I` and `c 0 = x`. -/
structure IsIntegralCurveThrough (x : M) (c : ℝ → M) (I : Set ℝ) : Prop where
  isOpen : IsOpen I
  ordConnected : OrdConnected I
  zero_mem : (0 : ℝ) ∈ I
  map_zero : c 0 = x
  isIntegralCurveOn : X.IsIntegralCurveOn c I

variable {X : SmoothVectorField E M}

/-- Two integral curves through the same point agree where both are defined
[Lan99, Theorem IV.2.1]. -/
theorem IsIntegralCurveThrough.eqOn [T2Space M] {x : M} {c₁ c₂ : ℝ → M}
    {I₁ I₂ : Set ℝ} (h₁ : X.IsIntegralCurveThrough x c₁ I₁)
    (h₂ : X.IsIntegralCurveThrough x c₂ I₂) : EqOn c₁ c₂ (I₁ ∩ I₂) :=
  IsIntegralCurveOn.eqOn (h₁.isOpen.inter h₂.isOpen)
    (h₁.ordConnected.inter h₂.ordConnected).isPreconnected
    (h₁.isIntegralCurveOn.mono inter_subset_left) (h₂.isIntegralCurveOn.mono inter_subset_right)
    ⟨h₁.zero_mem, h₂.zero_mem⟩ (h₁.map_zero.trans h₂.map_zero.symm)

/-- The curves of a flow box are integral curves through their initial points. -/
theorem FlowBox.isIntegralCurveThrough {z : M} (B : X.FlowBox z) {y : M} (hy : y ∈ B.V) :
    X.IsIntegralCurveThrough y (fun t ↦ B.φ (t, y)) (Ioo (-B.ε) B.ε) where
  isOpen := isOpen_Ioo
  ordConnected := ordConnected_Ioo
  zero_mem := ⟨neg_lt_zero.2 B.ε_pos, B.ε_pos⟩
  map_zero := B.map_zero y hy
  isIntegralCurveOn := B.isIntegralCurveOn y hy

/-! ### The maximal flow -/

variable (X) in
/-- The **maximal interval** `J_x` of the integral curve through `x`: the union of the intervals of
definition of all integral curves of `X` through `x`. -/
def maxInterval (x : M) : Set ℝ :=
  {t | ∃ c I, X.IsIntegralCurveThrough x c I ∧ t ∈ I}

variable (X) in
/-- The **domain of the maximal flow**: the pairs `(t, x)` with `t ∈ J_x`. -/
def flowDomain : Set (ℝ × M) :=
  {p | p.1 ∈ X.maxInterval p.2}

open scoped Classical in
variable (X) in
/-- The **maximal flow** of `X`: `Fl(t, x)` is the value at `t` of any integral curve through `x`
defined at `t`. It is well defined on `flowDomain` by uniqueness of integral curves
(`SmoothVectorField.IsIntegralCurveThrough.flow_eq`); outside `flowDomain` it takes the junk
value `Fl(t, x) = x`. -/
def flow (p : ℝ × M) : M :=
  if h : ∃ c I, X.IsIntegralCurveThrough p.2 c I ∧ p.1 ∈ I then h.choose p.1 else p.2

theorem mem_flowDomain {p : ℝ × M} : p ∈ X.flowDomain ↔ p.1 ∈ X.maxInterval p.2 :=
  Iff.rfl

/-- **Maximality**: every integral curve through `x` is defined on a subinterval of `J_x`. -/
theorem IsIntegralCurveThrough.subset_maxInterval {x : M} {c : ℝ → M} {I : Set ℝ}
    (h : X.IsIntegralCurveThrough x c I) : I ⊆ X.maxInterval x :=
  fun _ ht ↦ ⟨c, I, h, ht⟩

/-- **Maximality**: every integral curve through `x` is a restriction of `t ↦ Fl(t, x)`. -/
theorem IsIntegralCurveThrough.flow_eq [T2Space M] {x : M} {c : ℝ → M}
    {I : Set ℝ} (h : X.IsIntegralCurveThrough x c I) {t : ℝ} (ht : t ∈ I) :
    X.flow (t, x) = c t := by
  have hex : ∃ c I, X.IsIntegralCurveThrough x c I ∧ t ∈ I := ⟨c, I, h, ht⟩
  rw [flow, dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨I', h', ht'⟩ := hex.choose_spec
  exact h'.eqOn h ⟨ht', ht⟩

/-- The maximal interval `J_x` is open. -/
theorem isOpen_maxInterval (x : M) : IsOpen (X.maxInterval x) :=
  isOpen_iff_mem_nhds.2 fun _ ⟨_, _, h, ht⟩ ↦
    Filter.mem_of_superset (h.isOpen.mem_nhds ht) h.subset_maxInterval

/-- The maximal interval `J_x` is an interval. -/
theorem ordConnected_maxInterval (x : M) : OrdConnected (X.maxInterval x) := by
  refine ⟨fun a ⟨c₁, I₁, h₁, ha⟩ b ⟨c₂, I₂, h₂, hb⟩ τ hτ ↦ ?_⟩
  rcases le_total τ 0 with hτ0 | hτ0
  · exact h₁.subset_maxInterval (h₁.ordConnected.out ha h₁.zero_mem ⟨hτ.1, hτ0⟩)
  · exact h₂.subset_maxInterval (h₂.ordConnected.out h₂.zero_mem hb ⟨hτ0, hτ.2⟩)

/-- The maximal interval `J_x` contains `0`. -/
theorem zero_mem_maxInterval [CompleteSpace E] (x : M) : (0 : ℝ) ∈ X.maxInterval x :=
  ⟨_, _, (X.flowBox x).isIntegralCurveThrough
    (X.flowBox x).mem,
    (X.flowBox x).isIntegralCurveThrough
      (X.flowBox x).mem |>.zero_mem⟩

/-- The domain of the maximal flow contains `{0} × M`. -/
theorem zero_mem_flowDomain [CompleteSpace E] (x : M) : ((0 : ℝ), x) ∈ X.flowDomain :=
  X.zero_mem_maxInterval x

/-- `t ↦ Fl(t, x)` is an integral curve of `X` on `J_x`. -/
theorem isIntegralCurveOn_flow [T2Space M] (x : M) :
    X.IsIntegralCurveOn (fun t ↦ X.flow (t, x)) (X.maxInterval x) := by
  rintro t ⟨c, I, h, ht⟩
  exact (h.isIntegralCurveOn.congr h.isOpen fun s hs ↦ (h.flow_eq hs).symm) t ht

/-- `Fl(0, x) = x`. -/
theorem flow_zero [CompleteSpace E] [T2Space M] (x : M) : X.flow (0, x) = x := by
  obtain ⟨c, I, h, -⟩ := X.zero_mem_maxInterval x
  rw [h.flow_eq h.zero_mem, h.map_zero]

/-- **The maximal integral curve**: `t ↦ Fl(t, x)` is an integral curve of `X` through `x` on the
maximal interval `J_x` (compare [GN26, Definition 2.5.23]). -/
theorem isIntegralCurveThrough_flow [CompleteSpace E] [T2Space M] (x : M) :
    X.IsIntegralCurveThrough x (fun t ↦ X.flow (t, x)) (X.maxInterval x) where
  isOpen := X.isOpen_maxInterval x
  ordConnected := X.ordConnected_maxInterval x
  zero_mem := X.zero_mem_maxInterval x
  map_zero := X.flow_zero x
  isIntegralCurveOn := X.isIntegralCurveOn_flow x

/-- On the box of a flow box (around any point), the maximal flow is defined and given by the flow
box. -/
theorem FlowBox.box_subset_flowDomain {z : M} (B : X.FlowBox z) : B.box ⊆ X.flowDomain :=
  fun _ hp ↦ (B.isIntegralCurveThrough hp.2).subset_maxInterval hp.1

/-- On the box of a flow box (around any point), the maximal flow is given by the flow box. -/
theorem FlowBox.flow_eq [T2Space M] {z : M} (B : X.FlowBox z) {p : ℝ × M}
    (hp : p ∈ B.box) : X.flow p = B.φ p :=
  (B.isIntegralCurveThrough hp.2).flow_eq hp.1

/-! ### The group law -/

/-- The time-translated curve `u ↦ Fl(u + t, x)` is an integral curve through `Fl(t, x)` on
`J_x - t`. -/
theorem isIntegralCurveThrough_flow_add [T2Space M] {x : M} {t : ℝ}
    (ht : (t, x) ∈ X.flowDomain) :
    X.IsIntegralCurveThrough (X.flow (t, x)) (fun u ↦ X.flow (u + t, x))
      ((· + t) ⁻¹' X.maxInterval x) where
  isOpen := (X.isOpen_maxInterval x).preimage (continuous_id.add continuous_const)
  ordConnected := ⟨fun a ha b hb c hc ↦ (X.ordConnected_maxInterval x).out ha hb
    ⟨by linarith [hc.1], by linarith [hc.2]⟩⟩
  zero_mem := by
    change (0 : ℝ) + t ∈ X.maxInterval x
    rw [zero_add]
    exact ht
  map_zero := by simp
  isIntegralCurveOn := (X.isIntegralCurveOn_flow x).comp_add t

/-- `Fl(s, Fl(t, x)) = Fl(s + t, x)` whenever `t, s + t ∈ J_x`. -/
theorem flow_flow_of_add_mem [CompleteSpace E] [T2Space M] {x : M} {s t : ℝ}
    (ht : (t, x) ∈ X.flowDomain) (hst : (s + t, x) ∈ X.flowDomain) :
    X.flow (s, X.flow (t, x)) = X.flow (s + t, x) :=
  (X.isIntegralCurveThrough_flow_add ht).flow_eq (show s + t ∈ X.maxInterval x from hst)

/-- **Translation of the maximal interval** [Lan99, Theorem IV.2.2], [GN26, Remark 2.5.24 (c)]: if
`t ∈ J_x`, then `J_{Fl(t, x)} = J_x - t`. -/
theorem maxInterval_flow [CompleteSpace E] [T2Space M] {x : M} {t : ℝ}
    (ht : (t, x) ∈ X.flowDomain) :
    X.maxInterval (X.flow (t, x)) = (· + t) ⁻¹' X.maxInterval x := by
  set y := X.flow (t, x)
  refine Subset.antisymm (fun s hs ↦ ?_) (X.isIntegralCurveThrough_flow_add ht).subset_maxInterval
  -- glue `u ↦ Fl(u, x)` on `J_x` and `u ↦ Fl(u - t, y)` on `J_y + t`
  set A := X.maxInterval x
  set B : Set ℝ := (· + -t) ⁻¹' X.maxInterval y
  open scoped Classical in
  set c : ℝ → M := fun u ↦ if u ∈ A then X.flow (u, x) else X.flow (u + -t, y)
  have hA : IsOpen A := X.isOpen_maxInterval x
  have hB : IsOpen B := (X.isOpen_maxInterval y).preimage (continuous_id.add continuous_const)
  have hcA : EqOn (fun u ↦ X.flow (u, x)) c A := fun u hu ↦ by simp [c, hu]
  have hcB : EqOn (fun u ↦ X.flow (u + -t, y)) c B := fun u hu ↦ by
    by_cases huA : u ∈ A
    · simp only [c, huA, ite_true]
      have := X.flow_flow_of_add_mem (s := u + -t) ht
        (show u + -t + t ∈ X.maxInterval x by simpa using huA)
      simpa using this
    · simp [c, huA]
  have hc : X.IsIntegralCurveThrough x c (A ∪ B) :=
  { isOpen := hA.union hB
    ordConnected := by
      refine isPreconnected_iff_ordConnected.1 ((X.ordConnected_maxInterval x).isPreconnected.union
        t ht ?_ (OrdConnected.isPreconnected ⟨fun a ha b hb τ hτ ↦
          (X.ordConnected_maxInterval y).out ha hb ⟨by linarith [hτ.1], by linarith [hτ.2]⟩⟩))
      simpa [B] using X.zero_mem_maxInterval y
    zero_mem := Or.inl (X.zero_mem_maxInterval x)
    map_zero := by
      have h0 : (0 : ℝ) ∈ A := X.zero_mem_maxInterval x
      simp [c, h0, X.flow_zero]
    isIntegralCurveOn := by
      rintro u (hu | hu)
      · exact ((X.isIntegralCurveOn_flow x).congr hA hcA) u hu
      · exact ((((X.isIntegralCurveOn_flow y).comp_add (-t))).congr hB hcB) u hu }
  exact hc.subset_maxInterval (Or.inr (by simpa [B] using hs))

/-- If `(t, x)` and `(s, Fl(t, x))` lie in the domain of the maximal flow, so does `(s + t, x)`. -/
theorem add_mem_flowDomain [CompleteSpace E] [T2Space M] {x : M} {s t : ℝ}
    (ht : (t, x) ∈ X.flowDomain) (hs : (s, X.flow (t, x)) ∈ X.flowDomain) :
    (s + t, x) ∈ X.flowDomain := by
  have : s ∈ X.maxInterval (X.flow (t, x)) := hs
  rw [X.maxInterval_flow ht] at this
  exact this

/-- If `(t, x)` lies in the domain of the maximal flow, then `(s, Fl(t, x))` lies in it if and only
if `(s + t, x)` does [GN26, Remark 2.5.24 (c)]. -/
theorem mem_flowDomain_flow_iff [CompleteSpace E] [T2Space M] {x : M} {s t : ℝ}
    (ht : (t, x) ∈ X.flowDomain) :
    (s, X.flow (t, x)) ∈ X.flowDomain ↔ (s + t, x) ∈ X.flowDomain := by
  change s ∈ X.maxInterval (X.flow (t, x)) ↔ s + t ∈ X.maxInterval x
  rw [X.maxInterval_flow ht]
  rfl

/-- **The group law** `Fl(s + t, x) = Fl(s, Fl(t, x))` whenever `(t, x)` and `(s, Fl(t, x))` lie in
the domain of the maximal flow [Lan99, Theorem IV.2.2], [GN26, Remark 2.5.24 (c)]; then `(s + t, x)`
lies in it by `SmoothVectorField.add_mem_flowDomain`. -/
theorem flow_add [CompleteSpace E] [T2Space M] {x : M} {s t : ℝ} (ht : (t, x) ∈ X.flowDomain)
    (hs : (s, X.flow (t, x)) ∈ X.flowDomain) :
    X.flow (s + t, x) = X.flow (s, X.flow (t, x)) :=
  (X.flow_flow_of_add_mem ht (X.add_mem_flowDomain ht hs)).symm

/-- Following a flow box from a point of a maximal curve: if `Fl(t, x) ∈ V` for a flow box
`φ : (-ε, ε) × V → M`, then `Fl(s + t, x) = φ(s, Fl(t, x))` for `|s| < ε`. -/
theorem FlowBox.flow_add [CompleteSpace E] [T2Space M] {z : M} (B : X.FlowBox z) {x : M}
    {t s : ℝ} (ht : (t, x) ∈ X.flowDomain) (hV : X.flow (t, x) ∈ B.V)
    (hs : s ∈ Ioo (-B.ε) B.ε) :
    (s + t, x) ∈ X.flowDomain ∧ X.flow (s + t, x) = B.φ (s, X.flow (t, x)) := by
  have hbox : (s, X.flow (t, x)) ∈ B.box := ⟨hs, hV⟩
  exact ⟨X.add_mem_flowDomain ht (B.box_subset_flowDomain hbox),
    (X.flow_add ht (B.box_subset_flowDomain hbox)).trans (B.flow_eq hbox)⟩

/-! ### Openness of the domain and smoothness of the maximal flow -/

omit [MBManifold E M] in
/-- If `f : ℝ × M → M` is smooth on an open set `W`, then `(τ, x) ↦ (τ - a, f(b, x))` is smooth on
`{(τ, x) | (b, x) ∈ W}`. -/
theorem smoothMBMOn_sub_prod_slice {f : ℝ × M → M} {W : Set (ℝ × M)} (hW : IsOpen W)
    (hf : SmoothMBMOn (ModelProd ℝ E) E f W) (a b : ℝ) :
    SmoothMBMOn (ModelProd ℝ E) (ModelProd ℝ E) (fun p : ℝ × M ↦ ((p.1 - a, f (b, p.2)) : ℝ × M))
      {p : ℝ × M | (b, p.2) ∈ W} := by
  intro k
  have hsl : Continuous fun p : ℝ × M ↦ ((b, p.2) : ℝ × M) :=
    continuous_const.prodMk continuous_snd
  have hcont : ContinuousOn (fun p : ℝ × M ↦ ((p.1 - a, f (b, p.2)) : ℝ × M))
      {p : ℝ × M | (b, p.2) ∈ W} :=
    (continuous_fst.sub continuous_const).continuousOn.prodMk
      ((hf 0).1.comp hsl.continuousOn fun _ hp ↦ hp)
  refine ⟨hcont, fun p hp ↦ ?_⟩
  -- the local representative of `f` at `(b, p.2)`, in the charts `id × c` and `e`
  set c := chartAt E p.2
  set e := chartAt E (f (b, p.2))
  set R : ModelProd ℝ E → E := e ∘ f ∘ (chartAt (ModelProd ℝ E) ((b, p.2) : ℝ × M)).symm
  set D := chartDomain f W (chartAt (ModelProd ℝ E) ((b, p.2) : ℝ × M)) e
  have hD : IsOpen D := isOpen_chartDomain hW (hf k).1 _ _
  have hR : ContDiffMBOn k R D := (hf k).2 (b, p.2) hp
  -- `q ↦ (b, q.2)` and `q ↦ q.1 - a` are affine
  set L : ModelProd ℝ E → ModelProd ℝ E := fun q ↦ ((b, q.2) : ℝ × E)
  have hL : ContDiffMBOn k L univ :=
    (contDiffMBOn_const k b univ).prodMk isOpen_univ
      ((ContinuousLinearMap.snd ℝ ℝ E).contDiffMBOn k univ)
  have hLc : Continuous L := continuous_const.prodMk continuous_snd
  have hD' : IsOpen (L ⁻¹' D) := hD.preimage hLc
  have hRL : ContDiffMBOn k (R ∘ L) (L ⁻¹' D) :=
    hR.comp hD' hD (hL.mono (subset_univ _)) fun q hq ↦ hq
  have hsub : ContDiffMBOn k (fun q : ModelProd ℝ E ↦ q.1 - a) univ := by
    refine ContDiffMBOn.congr_of_isOpen isOpen_univ (fun q _ ↦ ?_)
      ((contDiffMBOn_const k (-a) univ).add isOpen_univ
        ((ContinuousLinearMap.fst ℝ ℝ E).contDiffMBOn k univ))
    simp [sub_eq_add_neg, add_comm]
  have hpair : ContDiffMBOn k (fun q : ModelProd ℝ E ↦ ((q.1 - a, R (L q)) : ℝ × E)) (L ⁻¹' D) :=
    (hsub.mono (subset_univ _)).prodMk hD' hRL
  refine (hpair.mono ?_).congr_of_isOpen (isOpen_chartDomain (hsl.isOpen_preimage _ hW) hcont _ _)
    fun q _ ↦ rfl
  rintro q ⟨hq₁, hq₂, hq₃⟩
  exact ⟨⟨mem_univ _, hq₁.2⟩, hq₂, hq₃.2⟩

variable [CompleteSpace E] [T2Space M]

/-- The flow is smooth near `(t, x₀)` and its domain is a neighbourhood of `(t, x₀)`. -/
private def GoodTime (X : SmoothVectorField E M) (x₀ : M) (t : ℝ) : Prop :=
  ∃ W : Set (ℝ × M), IsOpen W ∧ (t, x₀) ∈ W ∧ W ⊆ X.flowDomain ∧
    SmoothMBMOn (ModelProd ℝ E) E X.flow W

/-- **Propagation along a flow box.** If the flow is smooth near `(t, x₀)` and `Fl(t, x₀)` lies in
the domain `V` of a flow box `φ : (-ε, ε) × V → M`, then it is smooth near `(τ, x₀)` for
`|τ - t| < ε`, being `Fl(τ, x) = φ(τ - t, Fl(t, x))` there. -/
private theorem goodTime_of_flowBox {x₀ : M} {t τ : ℝ} (ht : GoodTime X x₀ t) {z : M}
    (B : X.FlowBox z) (hV : X.flow (t, x₀) ∈ B.V) (hτ : τ - t ∈ Ioo (-B.ε) B.ε) :
    GoodTime X x₀ τ := by
  obtain ⟨W, hW, htW, hWD, hsm⟩ := ht
  set W₁ : Set (ℝ × M) := {p | (t, p.2) ∈ W}
  have hsl : Continuous fun p : ℝ × M ↦ ((t, p.2) : ℝ × M) :=
    continuous_const.prodMk continuous_snd
  have hW₁ : IsOpen W₁ := hW.preimage hsl
  set G : ℝ × M → ℝ × M := fun p ↦ (p.1 - t, X.flow (t, p.2))
  have hG : SmoothMBMOn (ModelProd ℝ E) (ModelProd ℝ E) G W₁ :=
    smoothMBMOn_sub_prod_slice hW hsm t t
  set W' : Set (ℝ × M) := W₁ ∩ G ⁻¹' B.box
  have hW' : IsOpen W' := (hG 0).1.isOpen_inter_preimage hW₁ B.isOpen_box
  have hrep : ∀ p ∈ W', p ∈ X.flowDomain ∧ X.flow p = B.φ (G p) := fun p hp ↦ by
    have h := B.flow_add (hWD hp.1) hp.2.2 hp.2.1
    rwa [sub_add_cancel] at h
  refine ⟨W', hW', ⟨htW, hτ, hV⟩, fun p hp ↦ (hrep p hp).1, ?_⟩
  refine SmoothMBMOn.congr_of_isOpen ?_ hW' fun p hp ↦ ((hrep p hp).2).symm
  exact B.smooth.comp hW' B.isOpen_box (hG.mono_of_isOpen hW₁ hW' inter_subset_left)
    fun p hp ↦ hp.2

/-- Every `t ∈ J_{x₀}` is a good time. -/
private theorem goodTime_of_mem {x₀ : M} {t : ℝ} (ht : t ∈ X.maxInterval x₀) :
    GoodTime X x₀ t := by
  set S := {τ | GoodTime X x₀ τ}
  have hS : IsOpen S := isOpen_iff_mem_nhds.2 fun τ ⟨W, hW, hτW, hWD, hsm⟩ ↦
    Filter.mem_of_superset
      ((hW.preimage (continuous_id.prodMk continuous_const)).mem_nhds hτW)
      fun σ hσ ↦ ⟨W, hW, hσ, hWD, hsm⟩
  have h0 : (0 : ℝ) ∈ S := by
    set B := X.flowBox x₀
    refine ⟨B.box, B.isOpen_box, ⟨⟨neg_lt_zero.2 B.ε_pos, B.ε_pos⟩, B.mem⟩,
      B.box_subset_flowDomain, ?_⟩
    exact B.smooth.congr_of_isOpen B.isOpen_box fun p hp ↦ (B.flow_eq hp).symm
  have hsub : X.maxInterval x₀ ⊆ S := by
    refine (X.ordConnected_maxInterval x₀).isPreconnected.subset_of_closure_inter_subset hS
      ⟨0, X.zero_mem_maxInterval x₀, h0⟩ ?_
    rintro τ ⟨hτc, hτ⟩
    set B := X.flowBox (X.flow (τ, x₀))
    -- near `τ`, the maximal curve stays in the domain of the flow box at `Fl(τ, x₀)`
    have hcont : ContinuousAt (fun σ ↦ X.flow (σ, x₀)) τ := (X.isIntegralCurveOn_flow x₀ τ hτ).1
    have hN : Ioo (τ - B.ε) (τ + B.ε) ∩ (fun σ ↦ X.flow (σ, x₀)) ⁻¹' B.V ∈ 𝓝 τ :=
      inter_mem (Ioo_mem_nhds (by linarith [B.ε_pos]) (by linarith [B.ε_pos]))
        (hcont.preimage_mem_nhds (B.isOpen.mem_nhds B.mem))
    obtain ⟨σ, ⟨hσ, hσV⟩, hσS⟩ := mem_closure_iff_nhds.1 hτc _ hN
    exact goodTime_of_flowBox hσS B hσV ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  exact hsub ht

/-- Around every point of its domain, the maximal flow is defined and smooth on an open set. -/
theorem exists_isOpen_smoothMBMOn_flow {p : ℝ × M} (hp : p ∈ X.flowDomain) :
    ∃ W : Set (ℝ × M), IsOpen W ∧ p ∈ W ∧ W ⊆ X.flowDomain ∧
      SmoothMBMOn (ModelProd ℝ E) E X.flow W :=
  goodTime_of_mem hp

/-- **The domain of the maximal flow is open** in `ℝ × M` [Lan99, Theorem IV.2.6], [GN26,
Corollary 2.5.21 (b)]. -/
theorem isOpen_flowDomain : IsOpen X.flowDomain :=
  isOpen_iff_forall_mem_open.2 fun _ hp ↦
    let ⟨W, hW, hpW, hWD, _⟩ := X.exists_isOpen_smoothMBMOn_flow hp
    ⟨W, hWD, hW, hpW⟩

/-- **The maximal flow is smooth** on its domain [Lan99, Theorem IV.2.6], [GN26, Corollary 2.5.21
(c)]. -/
theorem smoothMBMOn_flow : SmoothMBMOn (ModelProd ℝ E) E X.flow X.flowDomain := fun k ↦
  ContMDiffMBOn.of_local X.isOpen_flowDomain fun _ hp ↦
    let ⟨W, hW, hpW, _, hsm⟩ := X.exists_isOpen_smoothMBMOn_flow hp
    ⟨W, hW, hpW, hsm k⟩

/-- **The maximal flow is a local flow** in the sense of `IsLocalFlow`, on its open domain
`flowDomain ⊇ {0} × M` (compare [GN26, Corollary 2.5.21 and Definition 2.5.23]). -/
theorem isLocalFlow_flow : IsLocalFlow X X.flow X.flowDomain where
  isOpen := X.isOpen_flowDomain
  zero_mem := X.zero_mem_flowDomain
  map_zero := X.flow_zero
  contMDiffMBOn := X.smoothMBMOn_flow 2
  hasDirDerivAt := by
    rintro ⟨t, x⟩ hp i hi
    have h := (((X.isIntegralCurveOn_flow x) t hp).2 i hi).hasFDerivAt.hasDirDerivAt 1
    simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at h
    exact h

/-- **The Lie derivative along the flow on Banach manifolds.** On a Hausdorff manifold modeled on
a Banach space, Glöckner–Neeb's formula (3.36), `d/dt|₀ (Fl_t)* ω = L_X ω`, holds for the maximal
flow of every smooth vector field (`IsLocalFlow.hasDirDerivAt_pullback` applied to
`SmoothVectorField.isLocalFlow_flow`). -/
theorem hasDirDerivAt_pullback_flow {F : Type u} [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
    [T2Space F] {n : ℕ} (ω : DifferentialForm E M F n) (i : atlas E M) {x : M}
    (hx : x ∈ i.1.source) (v : Fin n → E) :
    HasDirDerivAt (fun t : ℝ ↦ ω.localRep i (i.1 (X.flow (t, x)),
        fun k ↦ dMB (fun z ↦ i.1 (X.flow (t, i.1.symm z))) (i.1 x, v k))) 0 1
      ((DifferentialForm.lieDeriv X ω).localRep i (i.1 x, v)) :=
  X.isLocalFlow_flow.hasDirDerivAt_pullback ω i hx v

/-! ### The flow obtained by gluing flow boxes -/

/-- The curves of `boxFlow` are integral curves through their initial points. -/
theorem isIntegralCurveThrough_boxFlow (x : M) :
    X.IsIntegralCurveThrough x (fun t ↦ X.boxFlow (t, x)) {t | (t, x) ∈ X.boxFlowDomain} where
  isOpen := X.isOpen_boxFlowDomain_slice x
  ordConnected := X.ordConnected_boxFlowDomain_slice x
  zero_mem := X.zero_mem_boxFlowDomain x
  map_zero := X.boxFlow_zero x
  isIntegralCurveOn := X.isIntegralCurveOn_boxFlow x

/-- The domain of the flow glued from the chosen flow boxes is contained in the maximal one. -/
theorem boxFlowDomain_subset_flowDomain : X.boxFlowDomain ⊆ X.flowDomain :=
  fun p hp ↦ (X.isIntegralCurveThrough_boxFlow p.2).subset_maxInterval hp

/-- The flow glued from the chosen flow boxes is the restriction of the maximal flow. -/
theorem boxFlow_eq_flow {p : ℝ × M} (hp : p ∈ X.boxFlowDomain) : X.boxFlow p = X.flow p :=
  ((X.isIntegralCurveThrough_boxFlow p.2).flow_eq hp).symm

/-! ### The escape lemma -/

/-- **Escape lemma, forward.** If the forward maximal time `b` of `x` is finite,
i.e. `J_x ∩ [0, ∞) = [0, b)`, then the curve `t ↦ Fl(t, x)` has no cluster point as `t → b⁻`
(compare [Lan99, Theorem IV.2.3]). -/
theorem not_mapClusterPt_flow_of_lt_top {x : M} {b : ℝ}
    (hb : X.maxInterval x ∩ Ici 0 = Ico 0 b) (y : M) :
    ¬ MapClusterPt y (𝓝[<] b) (fun t ↦ X.flow (t, x)) := by
  intro hy
  have hb0 : 0 < b := by
    have : (0 : ℝ) ∈ Ico 0 b := hb ▸ ⟨X.zero_mem_maxInterval x, mem_Ici.2 le_rfl⟩
    exact this.2
  set B := X.flowBox y
  have hev : ∀ᶠ t in 𝓝[<] b, t ∈ Ioo (max 0 (b - B.ε)) b :=
    Ioo_mem_nhdsLT (max_lt hb0 (by linarith [B.ε_pos]))
  obtain ⟨t, htV, ht⟩ := ((hy.frequently (B.isOpen.mem_nhds B.mem)).and_eventually hev).exists
  have htJ : t ∈ X.maxInterval x := by
    have : t ∈ Ico 0 b := ⟨(le_max_left _ _).trans ht.1.le, ht.2⟩
    rw [← hb] at this
    exact this.1
  have h := (B.flow_add (s := b - t) htJ htV
    ⟨by linarith [ht.2, B.ε_pos], by linarith [(le_max_right 0 (b - B.ε)).trans_lt ht.1]⟩).1
  rw [sub_add_cancel] at h
  have : b ∈ Ico 0 b := hb ▸ ⟨h, hb0.le⟩
  exact lt_irrefl b this.2

/-- **Escape lemma, backward.** If the backward maximal time `a` of `x` is finite,
i.e. `J_x ∩ (-∞, 0] = (a, 0]`, then the curve `t ↦ Fl(t, x)` has no cluster point as `t → a⁺`. -/
theorem not_mapClusterPt_flow_of_bot_lt {x : M} {a : ℝ}
    (ha : X.maxInterval x ∩ Iic 0 = Ioc a 0) (y : M) :
    ¬ MapClusterPt y (𝓝[>] a) (fun t ↦ X.flow (t, x)) := by
  intro hy
  have ha0 : a < 0 := by
    have : (0 : ℝ) ∈ Ioc a 0 := ha ▸ ⟨X.zero_mem_maxInterval x, mem_Iic.2 le_rfl⟩
    exact this.1
  set B := X.flowBox y
  have hev : ∀ᶠ t in 𝓝[>] a, t ∈ Ioo a (min 0 (a + B.ε)) :=
    Ioo_mem_nhdsGT (lt_min ha0 (by linarith [B.ε_pos]))
  obtain ⟨t, htV, ht⟩ := ((hy.frequently (B.isOpen.mem_nhds B.mem)).and_eventually hev).exists
  have htJ : t ∈ X.maxInterval x := by
    have : t ∈ Ioc a 0 := ⟨ht.1, ht.2.le.trans (min_le_left _ _)⟩
    rw [← ha] at this
    exact this.1
  have h := (B.flow_add (s := a - t) htJ htV
    ⟨by linarith [ht.2.trans_le (min_le_right 0 (a + B.ε))], by linarith [ht.1, B.ε_pos]⟩).1
  rw [sub_add_cancel] at h
  have : a ∈ Ioc a 0 := ha ▸ ⟨h, ha0.le⟩
  exact lt_irrefl a this.1

/-- **Escape from compact sets, forward** [Lan99, Theorem IV.2.3]: if `J_x ∩ [0, ∞) = [0, b)` with
`b` finite, then for every compact `K ⊆ M`, `Fl(t, x) ∉ K` for all `t < b` close enough to `b`. In
infinite dimensions compact sets have empty interior, so this is much weaker than in finite
dimensions. -/
theorem eventually_flow_not_mem_of_isCompact {x : M} {b : ℝ}
    (hb : X.maxInterval x ∩ Ici 0 = Ico 0 b) {K : Set M} (hK : IsCompact K) :
    ∀ᶠ t in 𝓝[<] b, X.flow (t, x) ∉ K := by
  by_contra h
  rw [Filter.not_eventually] at h
  simp only [not_not] at h
  obtain ⟨y, -, hy⟩ := hK.exists_clusterPt_of_frequently (Filter.frequently_map.2 h)
  exact X.not_mapClusterPt_flow_of_lt_top hb y hy

/-- **Escape from compact sets, backward**: if `J_x ∩ (-∞, 0] = (a, 0]` with `a` finite, then for
every compact `K ⊆ M`, `Fl(t, x) ∉ K` for all `t > a` close enough to `a`. -/
theorem eventually_flow_not_mem_of_isCompact' {x : M} {a : ℝ}
    (ha : X.maxInterval x ∩ Iic 0 = Ioc a 0) {K : Set M} (hK : IsCompact K) :
    ∀ᶠ t in 𝓝[>] a, X.flow (t, x) ∉ K := by
  by_contra h
  rw [Filter.not_eventually] at h
  simp only [not_not] at h
  obtain ⟨y, -, hy⟩ := hK.exists_clusterPt_of_frequently (Filter.frequently_map.2 h)
  exact X.not_mapClusterPt_flow_of_bot_lt ha y hy

end SmoothVectorField

end LocallyConvex.Manifolds
