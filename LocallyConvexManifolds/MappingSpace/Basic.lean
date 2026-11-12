/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.MappingSpace.Pushforward
public import LocallyConvexAnalysis.Calculus.ExponentialLaw
public import LocallyConvexAnalysis.MappingSpace.CkSuperposition
public import LocallyConvexManifolds.LocalAddition.Basic

/-!
# The manifold of continuous maps from a compact space

Reference: H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups* (arXiv:2602.12362),
4.1.30, Lemma 4.1.31 and Theorem 4.2.2, in the case `ℓ = 0`.

Let `K` be a compact Hausdorff space and `N` a manifold modeled on a Hausdorff locally convex
space `E`, with a local addition `Σ : Ω → N`, `θ = (π, Σ) : Ω → θ(Ω) ⊆ N × N`. Then `C(K, N)`, with
the compact-open topology, is a smooth manifold modeled on the spaces
`Γ_f = {τ ∈ C(K, TN) : π ∘ τ = f}`:

* `Sec E f` is the space `Γ_f`. Its topology is the initial topology with respect to the fiber
  coordinates `τ ↦ (x ↦ τ(x) in the chart i) ∈ C(L, E)`, for charts `i` of `N` and compact sets
  `L ⊆ K` with `f(L)` in the domain of `i`. It is a Hausdorff locally convex space
  (Lemma 4.1.31), and it carries the topology induced by `C(K, TN)` (`Sec.isInducing_toTangent`).
* `LocalAddition.chart f : C(K, N) ⊇ O'_f → O_f ⊆ Γ_f`, `g ↦ θ⁻¹ ∘ (f, g)`, with inverse
  `τ ↦ Σ ∘ τ`, where `O'_f = {g : (f, g)(K) ⊆ θ(Ω)}` and `O_f = Γ_f ∩ C(K, Ω)`.
* `LocalAddition.smoothMBOn_transition`: the transition maps `φ_g ∘ φ_f⁻¹` are smooth.
* `LocalAddition.mappingAtlas`: the charts form an atlas of `C(K, N)` with varying models
  (`VaryingAtlas`) and smooth transitions (Theorem 4.2.2(a), (b) for `ℓ = 0`).
* `LocalAddition.smoothMBMOn_eval_chart_symm`: the point evaluations are smooth
  (Theorem 4.2.2(c), `ℓ = 0`).

## Implementation notes

* **Manifolds with varying models.** Mathlib's `ChartedSpace` has a single model space, while the
  chart of `C(K, N)` at `f` is modeled on `Γ_f`. The structure `VaryingAtlas` records an atlas
  whose charts have their own model spaces, with smooth transition maps.
* **The space `Γ_f`.** Sections are written in the fiber coordinates of `TN` (in this library the
  fibers of `TN` are copies of `E`), so `Γ_f` is a submodule of `K → E`. Glöckner–Neeb identify
  `Γ_f` with the space of sections of the pullback bundle `f*(TN)` (Lemma 4.1.31); here the
  locally convex topology is defined directly by the fiber coordinates over compact sets, and
  shown to coincide with the topology induced by `C(K, TN)`.
* **Smoothness of the transition maps.** Glöckner–Neeb deduce it from Proposition 4.1.34 (the
  exponential law for sections). Here: the fiber coordinates of `Γ_g` form a closed linear
  embedding into a product (`Sec.isClosed_range_toPi`), so a map into `Γ_g` is smooth as soon as
  its coordinates are (`LocalAddition.Sec.contDiffMBOn_of_coordFun`, using `contDiffMBOn_pi` and
  `contDiffMBOn_of_isClosedEmbedding`, in lc-analysis); the coordinates over a compact set are
  determined by those over the pieces of a finite cover adapted to charts of `N`
  (`restrictPieces`, in lc-analysis); and over
  such a piece the transition map is the superposition operator of a smooth map
  (`transMap`), smooth by Glöckner–Neeb, Proposition 1.7.1 (`smoothMBOn_pushforward` in
  lc-analysis). We do not claim these arguments are new.
* Only the case `ℓ = 0` (continuous maps) is treated here; `K` lives in the universe of `E`. The
  cases `ℓ ≥ 1` are in `LocallyConvexManifolds.MappingSpace.Ck`.
-/

@[expose] public section

open Set Filter Bundle TopologicalSpace
open scoped Topology Manifold
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe u

/-! ### Fiber coordinates of tangent vectors -/

section Coordinates

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [MBManifold E N]

/-- The fiber coordinate of a tangent vector in the chart `i`. -/
def coordAt (i : atlas E N) (v : TangentBundle E N) : E :=
  tangentCoordChange ⟨chartAt E v.proj, chart_mem_atlas E _⟩ i v.proj v.vec

/-- The chart `tangentChart i i` of `TN` is `v ↦ (i (π v), v in the chart i)`. -/
theorem tangentChart_self_apply (i : atlas E N) (v : TangentBundle E N) :
    tangentChart i i.1 v = (i.1 v.proj, coordAt i v) :=
  rfl

/-- The tangent coordinate changes are additive. -/
theorem tangentCoordChange_map_add (i j : atlas E N) {x : N} (hx : x ∈ i.1.source ∩ j.1.source)
    (a b : E) : tangentCoordChange i j x (a + b) =
      tangentCoordChange i j x a + tangentCoordChange i j x b :=
  ((smoothMBOn_transition' i j) 1).dMB_add (isOpen_transition_domain i j)
    ⟨i.1.map_source hx.1, by simp [i.1.left_inv hx.1, hx.2]⟩ a b

/-- The tangent coordinate changes are homogeneous. -/
theorem tangentCoordChange_map_smul (i j : atlas E N) {x : N} (hx : x ∈ i.1.source ∩ j.1.source)
    (c : ℝ) (a : E) : tangentCoordChange i j x (c • a) = c • tangentCoordChange i j x a :=
  ((smoothMBOn_transition' i j) 1).dMB_smul
    ⟨i.1.map_source hx.1, by simp [i.1.left_inv hx.1, hx.2]⟩ c a

/-- The source of `tangentChart i i` is the part of `TN` over the source of `i`. -/
theorem mem_tangentChart_self_source (i : atlas E N) (v : TangentBundle E N) :
    v ∈ (tangentChart i i.1).source ↔ v.proj ∈ i.1.source := by
  rw [mem_tangentChart_source, and_self]

/-- The fiber coordinate in the chart `i` is continuous over the source of `i`. -/
theorem continuousOn_coordAt (i : atlas E N) :
    ContinuousOn (coordAt i) {v : TangentBundle E N | v.proj ∈ i.1.source} := by
  have h := (tangentChart i i.1).continuousOn
  refine (continuous_snd.comp_continuousOn h).mono fun v hv ↦ ?_
  exact (mem_tangentChart_self_source i v).2 hv

/-- **Continuity of maps into `TN`**: near a point whose image lies over the source of the chart
`i`, a map into `TN` is continuous if and only if its projection and its fiber coordinate in
the chart `i` are. -/
theorem continuousAt_iff_coordAt {X : Type*} [TopologicalSpace X] {s : X → TangentBundle E N}
    {x₀ : X} (i : atlas E N) (hx₀ : (s x₀).proj ∈ i.1.source) :
    ContinuousAt s x₀ ↔ ContinuousAt (fun x ↦ (s x).proj) x₀ ∧
      ContinuousAt (fun x ↦ coordAt i (s x)) x₀ := by
  set κ := tangentChart i i.1
  have hκ : s x₀ ∈ κ.source := (mem_tangentChart_self_source i _).2 hx₀
  constructor
  · intro h
    refine ⟨((tangentBundleCore E N).continuous_proj.continuousAt).comp h, ?_⟩
    exact (continuous_snd.continuousAt.comp ((κ.continuousAt hκ).comp h))
  · rintro ⟨h₁, h₂⟩
    have hev : ∀ᶠ x in 𝓝 x₀, (s x).proj ∈ i.1.source :=
      h₁.preimage_mem_nhds (i.1.open_source.mem_nhds hx₀)
    have hc : ContinuousAt (fun x ↦ ((i.1 (s x).proj, coordAt i (s x)) : E × E)) x₀ :=
      (ContinuousAt.comp (f := fun x ↦ (s x).proj) (i.1.continuousAt hx₀) h₁).prodMk h₂
    have h := ContinuousAt.comp (f := fun x ↦ ((i.1 (s x).proj, coordAt i (s x)) : E × E))
      (x := x₀) (κ.continuousAt_symm (κ.map_source hκ)) hc
    refine h.congr (hev.mono fun x hx ↦ ?_)
    change κ.symm (κ (s x)) = s x
    exact κ.left_inv ((mem_tangentChart_self_source i _).2 hx)

/-- The fiber coordinates are additive. -/
theorem coordAt_add (i : atlas E N) {y : N} (hy : y ∈ i.1.source) (a b : E) :
    coordAt i (⟨y, a + b⟩ : TangentBundle E N) =
      coordAt i (⟨y, a⟩ : TangentBundle E N) + coordAt i (⟨y, b⟩ : TangentBundle E N) :=
  tangentCoordChange_map_add _ i ⟨mem_chart_source E y, hy⟩ a b

/-- The fiber coordinates are homogeneous. -/
theorem coordAt_smul (i : atlas E N) {y : N} (hy : y ∈ i.1.source) (c : ℝ) (a : E) :
    coordAt i (⟨y, c • a⟩ : TangentBundle E N) = c • coordAt i (⟨y, a⟩ : TangentBundle E N) :=
  tangentCoordChange_map_smul _ i ⟨mem_chart_source E y, hy⟩ c a

/-- In the preferred chart at its base point, the fiber coordinate of `⟨y, a⟩` is `a`. -/
theorem coordAt_chartAt (y : N) (a : E) :
    coordAt ⟨chartAt E y, chart_mem_atlas E y⟩ (⟨y, a⟩ : TangentBundle E N) = a :=
  tangentCoordChange_self _ (mem_chart_source E y) a

/-- The tangent coordinate changes are continuous in the vector. -/
theorem continuous_tangentCoordChange (i j : atlas E N) {x : N}
    (hx : x ∈ i.1.source ∩ j.1.source) : Continuous (tangentCoordChange i j x) :=
  ((smoothMBOn_transition' i j) 1).continuous_dMB
    ⟨i.1.map_source hx.1, by simp [i.1.left_inv hx.1, hx.2]⟩

/-- The fiber coordinate in the preferred chart at its base point is the vector itself. -/
theorem coordAt_chartAt_of_proj_eq {y : N} {v : TangentBundle E N} (h : v.proj = y) :
    coordAt ⟨chartAt E y, chart_mem_atlas E y⟩ v = v.vec := by
  obtain ⟨y', w⟩ := v
  simp only at h
  subst h
  exact coordAt_chartAt (E := E) y' w

end Coordinates

/-! ### The space `Γ_f` of continuous sections along `f` -/

section Sections

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [MBManifold E N]
  {K : Type u} [TopologicalSpace K]

/-- Linear operations on continuous sections: if `x ↦ ⟨f x, u x⟩` and `x ↦ ⟨f x, w x⟩` are
continuous, so is `x ↦ ⟨f x, a • u x + b • w x⟩`. -/
theorem continuous_section_linearCombination (f : C(K, N)) {u w : K → E}
    (hu : Continuous fun x ↦ (⟨f x, u x⟩ : TangentBundle E N))
    (hw : Continuous fun x ↦ (⟨f x, w x⟩ : TangentBundle E N)) (a b : ℝ) :
    Continuous fun x ↦ (⟨f x, a • u x + b • w x⟩ : TangentBundle E N) := by
  refine continuous_iff_continuousAt.2 fun x₀ ↦ ?_
  set i : atlas E N := ⟨chartAt E (f x₀), chart_mem_atlas E _⟩
  have hx₀ : f x₀ ∈ i.1.source := mem_chart_source E _
  have hu' := ((continuousAt_iff_coordAt i hx₀).1 hu.continuousAt).2
  have hw' := ((continuousAt_iff_coordAt i hx₀).1 hw.continuousAt).2
  refine (continuousAt_iff_coordAt (s := fun x ↦ (⟨f x, a • u x + b • w x⟩ : TangentBundle E N))
    i hx₀).2 ⟨f.continuous.continuousAt, ?_⟩
  have hev : ∀ᶠ x in 𝓝 x₀, f x ∈ i.1.source :=
    f.continuous.continuousAt.preimage_mem_nhds (i.1.open_source.mem_nhds hx₀)
  refine ((hu'.const_smul a).add (hw'.const_smul b)).congr (hev.mono fun x hx ↦ ?_)
  change a • coordAt i ⟨f x, u x⟩ + b • coordAt i ⟨f x, w x⟩ = coordAt i ⟨f x, a • u x + b • w x⟩
  rw [coordAt_add i hx, coordAt_smul i hx, coordAt_smul i hx]

/-- The zero section along `f` is continuous. -/
theorem continuous_zero_section (f : C(K, N)) :
    Continuous fun x ↦ (⟨f x, (0 : E)⟩ : TangentBundle E N) := by
  refine continuous_iff_continuousAt.2 fun x₀ ↦ ?_
  set i : atlas E N := ⟨chartAt E (f x₀), chart_mem_atlas E _⟩
  have hx₀ : f x₀ ∈ i.1.source := mem_chart_source E _
  refine (continuousAt_iff_coordAt (s := fun x ↦ (⟨f x, (0 : E)⟩ : TangentBundle E N))
    i hx₀).2 ⟨f.continuous.continuousAt, ?_⟩
  have hev : ∀ᶠ x in 𝓝 x₀, f x ∈ i.1.source :=
    f.continuous.continuousAt.preimage_mem_nhds (i.1.open_source.mem_nhds hx₀)
  refine (continuousAt_const (y := (0 : E))).congr (hev.mono fun x hx ↦ ?_)
  change (0 : E) = coordAt i ⟨f x, (0 : E)⟩
  have h := coordAt_smul i hx 0 0
  rw [zero_smul, zero_smul] at h
  exact h.symm

variable (E) in
/-- The continuous sections along `f`, written in fiber coordinates: the maps `u : K → E` such
that `x ↦ u(x) ∈ T_{f(x)}N` is continuous. -/
def sectionSubmodule (f : C(K, N)) : Submodule ℝ (K → E) where
  carrier := {u | Continuous fun x ↦ (⟨f x, u x⟩ : TangentBundle E N)}
  add_mem' {u w} hu hw := by
    simpa using continuous_section_linearCombination f hu hw 1 1
  zero_mem' := continuous_zero_section f
  smul_mem' c u hu := by
    simpa using continuous_section_linearCombination f hu hu c 0

variable (E) in
/-- **The space `Γ_f`** of continuous sections of `TN` along `f : K → N` (Glöckner–Neeb, 4.1.30
and 4.2.1 for `ℓ = 0`), written in the fiber coordinates of `TN`. Its topology, defined below,
is the initial topology with respect to the fiber coordinates in the charts of `N` over compact
subsets of `K`; it coincides with the topology induced by `C(K, TN)`
(`Sec.isInducing_toTangent`). -/
def Sec (f : C(K, N)) : Type u := sectionSubmodule E f

namespace Sec

variable {f : C(K, N)}

/-- The vector space operations of `Γ_f` are pointwise. -/
instance : AddCommGroup (Sec E f) := inferInstanceAs (AddCommGroup (sectionSubmodule E f))

/-- The vector space operations of `Γ_f` are pointwise. -/
instance : Module ℝ (Sec E f) := inferInstanceAs (Module ℝ (sectionSubmodule E f))

/-- A section is given by its fiber coordinates `K → E`. -/
instance : FunLike (Sec E f) K E where
  coe u := Subtype.val (u : sectionSubmodule E f)
  coe_injective := Subtype.val_injective

/-- Sections are equal if their coordinates agree. -/
@[ext]
theorem ext {u w : Sec E f} (h : ∀ x, u x = w x) : u = w :=
  DFunLike.ext _ _ h

/-- The section built from fiber coordinates `u` with `x ↦ ⟨f x, u x⟩` continuous. -/
def mk (u : K → E) (hu : Continuous fun x ↦ (⟨f x, u x⟩ : TangentBundle E N)) : Sec E f :=
  ⟨u, hu⟩

/-- The coordinates of `Sec.mk u hu` are `u`. -/
@[simp]
theorem coe_mk (u : K → E) (hu : Continuous fun x ↦ (⟨f x, u x⟩ : TangentBundle E N)) :
    ⇑(mk u hu) = u :=
  rfl

/-- Addition is pointwise. -/
@[simp]
theorem coe_add (u w : Sec E f) : ⇑(u + w) = u + w :=
  rfl

/-- Scalar multiplication is pointwise. -/
@[simp]
theorem coe_smul (c : ℝ) (u : Sec E f) : ⇑(c • u) = c • ⇑u :=
  rfl

/-- The zero section. -/
@[simp]
theorem coe_zero : ⇑(0 : Sec E f) = 0 :=
  rfl

/-- A section as a continuous map `K → TN` along `f`. -/
def toTangent (u : Sec E f) : C(K, TangentBundle E N) :=
  ⟨fun x ↦ ⟨f x, u x⟩, (u : sectionSubmodule E f).2⟩

/-- `toTangent u x = ⟨f x, u x⟩`. -/
@[simp]
theorem toTangent_apply (u : Sec E f) (x : K) :
    toTangent u x = (⟨f x, u x⟩ : TangentBundle E N) :=
  rfl

/-- The section of `TN` along `f` given by a continuous lift `s` of `f`. -/
def ofTangent (s : C(K, TangentBundle E N)) (hs : ∀ x, (s x).proj = f x) : Sec E f :=
  mk (E := E) (fun x ↦ coordAt ⟨chartAt E (f x), chart_mem_atlas E _⟩ (s x)) (by
    have e : (fun x ↦ (⟨f x, coordAt (E := E) ⟨chartAt E (f x), chart_mem_atlas E _⟩ (s x)⟩ :
        TangentBundle E N)) = ⇑s :=
      funext fun x ↦ TangentBundle.ext_vec (hs x).symm (coordAt_chartAt_of_proj_eq (hs x))
    rw [e]
    exact s.continuous)

/-- `toTangent (ofTangent s hs) = s`. -/
theorem toTangent_ofTangent (s : C(K, TangentBundle E N)) (hs : ∀ x, (s x).proj = f x) :
    toTangent (ofTangent s hs) = s :=
  ContinuousMap.ext fun x ↦ TangentBundle.ext_vec (hs x).symm (coordAt_chartAt_of_proj_eq (hs x))

/-- `ofTangent (toTangent u) = u`. -/
theorem ofTangent_toTangent (u : Sec E f) : ofTangent (toTangent u) (fun _ ↦ rfl) = u :=
  ext fun x ↦ coordAt_chartAt (f x) (u x)

variable (f) in
/-- The indices of the fiber coordinates of `Γ_f`: a chart `i` of `N` and a compact `L ⊆ K` with
`f(L) ⊆` source of `i`. -/
def CoordIdx : Type _ :=
  {p : atlas E N × Set K // IsCompact p.2 ∧ ∀ x ∈ p.2, f x ∈ p.1.1.source}

/-- The fiber coordinates of a section on `L`, in the chart `i`. -/
def coordFun (a : CoordIdx (E := E) f) (u : Sec E f) : C(a.1.2, E) where
  toFun x := coordAt a.1.1 (toTangent u x)
  continuous_toFun := (continuousOn_coordAt a.1.1).comp_continuous
    ((toTangent u).continuous.comp continuous_subtype_val) fun x ↦ a.2.2 x x.2

/-- The fiber coordinates in a chart, as a linear map. -/
def coordL (a : CoordIdx (E := E) f) : Sec E f →ₗ[ℝ] C(a.1.2, E) where
  toFun := coordFun a
  map_add' u w := ContinuousMap.ext fun x ↦ coordAt_add a.1.1 (a.2.2 x x.2) (u x) (w x)
  map_smul' c u := ContinuousMap.ext fun x ↦ by
    change coordAt a.1.1 (⟨f x, c • u x⟩ : TangentBundle E N) =
      c • coordAt a.1.1 (⟨f x, u x⟩ : TangentBundle E N)
    exact coordAt_smul a.1.1 (a.2.2 x x.2) c (u x)

/-- All the fiber coordinates. -/
def toPi : Sec E f →ₗ[ℝ] ∀ a : CoordIdx (E := E) f, C(a.1.2, E) :=
  LinearMap.pi coordL

/-- The fiber coordinates separate the sections. -/
theorem toPi_injective : Function.Injective (toPi (E := E) (f := f)) := by
  intro u w h
  ext x
  let a : CoordIdx (E := E) f := ⟨(⟨chartAt E (f x), chart_mem_atlas E _⟩, {x}),
    isCompact_singleton, fun y hy ↦ by rw [hy]; exact mem_chart_source E _⟩
  have h1 := congrArg (fun φ ↦ φ a ⟨x, rfl⟩) h
  change coordAt _ (⟨f x, u x⟩ : TangentBundle E N) = coordAt _ (⟨f x, w x⟩ : TangentBundle E N)
    at h1
  rwa [coordAt_chartAt, coordAt_chartAt] at h1

/-- The index of the fiber coordinate at `x` in the preferred chart at `f x`. -/
def singletonIdx (x : K) : CoordIdx (E := E) f :=
  ⟨(⟨chartAt E (f x), chart_mem_atlas E _⟩, {x}), isCompact_singleton, fun y hy ↦ by
    rw [hy]; exact mem_chart_source E _⟩

section Closed

variable [CompactSpace K] [T2Space K]

/-- **The fiber coordinates of `Γ_f` have closed range**: the families of coordinates of sections
are the families compatible under the coordinate changes. -/
theorem isClosed_range_toPi : IsClosed (range (toPi (E := E) (f := f))) := by
  let S : Set (∀ a : CoordIdx (E := E) f, C(a.1.2, E)) := {φ | ∀ (a b : CoordIdx (E := E) f)
    (x : K) (hxa : x ∈ a.1.2) (hxb : x ∈ b.1.2),
      tangentCoordChange a.1.1 b.1.1 (f x) (φ a ⟨x, hxa⟩) = φ b ⟨x, hxb⟩}
  have hS : IsClosed S := by
    simp only [S, ofPred_forall]
    refine isClosed_iInter fun a ↦ isClosed_iInter fun b ↦ isClosed_iInter fun x ↦
      isClosed_iInter fun hxa ↦ isClosed_iInter fun hxb ↦ isClosed_eq ?_ ?_
    · exact (continuous_tangentCoordChange a.1.1 b.1.1 ⟨a.2.2 x hxa, b.2.2 x hxb⟩).comp
        ((continuous_eval_const _).comp (continuous_apply a))
    · exact (continuous_eval_const _).comp (continuous_apply b)
  convert hS using 1
  ext φ
  constructor
  · rintro ⟨u, rfl⟩ a b x hxa hxb
    change tangentCoordChange a.1.1 b.1.1 (f x)
      (tangentCoordChange ⟨chartAt E (f x), chart_mem_atlas E _⟩ a.1.1 (f x) (u x)) =
      tangentCoordChange ⟨chartAt E (f x), chart_mem_atlas E _⟩ b.1.1 (f x) (u x)
    exact tangentCoordChange_comp _ _ _ ⟨⟨mem_chart_source E _, a.2.2 x hxa⟩, b.2.2 x hxb⟩ _
  · intro hφ
    let u : K → E := fun x ↦ φ (singletonIdx x) ⟨x, rfl⟩
    have key : ∀ (b : CoordIdx (E := E) f) (x : K) (hx : x ∈ b.1.2),
        coordAt b.1.1 (⟨f x, u x⟩ : TangentBundle E N) = φ b ⟨x, hx⟩ :=
      fun b x hx ↦ hφ (singletonIdx x) b x rfl hx
    have hu : Continuous fun x ↦ (⟨f x, u x⟩ : TangentBundle E N) := by
      refine continuous_iff_continuousAt.2 fun x₀ ↦ ?_
      set i : atlas E N := ⟨chartAt E (f x₀), chart_mem_atlas E _⟩
      have hx₀ : f x₀ ∈ i.1.source := mem_chart_source E _
      obtain ⟨C, hCn, hCs, hC⟩ := local_compact_nhds
        (f.continuous.continuousAt.preimage_mem_nhds (i.1.open_source.mem_nhds hx₀))
      let b : CoordIdx (E := E) f := ⟨(i, C), hC, fun x hx ↦ hCs hx⟩
      refine (continuousAt_iff_coordAt (s := fun x ↦ (⟨f x, u x⟩ : TangentBundle E N)) i
        hx₀).2 ⟨f.continuous.continuousAt, ?_⟩
      have hcont : ContinuousOn (fun x ↦ coordAt i (⟨f x, u x⟩ : TangentBundle E N)) C := by
        rw [continuousOn_iff_continuous_domRestrict]
        exact (φ b).continuous.congr fun x ↦ (key b x x.2).symm
      exact hcont.continuousAt hCn
    refine ⟨mk u hu, funext fun a ↦ ContinuousMap.ext fun x ↦ ?_⟩
    exact key a x x.2

end Closed

/-- **The topology of `Γ_f`**: the initial topology with respect to the fiber coordinates. -/
instance : TopologicalSpace (Sec E f) := .induced toPi inferInstance

/-- `Γ_f` embeds in the product of the spaces of fiber coordinates. -/
theorem isEmbedding_toPi : Topology.IsEmbedding (toPi (E := E) (f := f)) :=
  ⟨⟨rfl⟩, toPi_injective⟩

/-- `Γ_f` is a topological vector space (Glöckner–Neeb, Lemma 4.1.31). -/
instance : IsTopologicalAddGroup (Sec E f) := isTopologicalAddGroup_induced toPi

/-- `Γ_f` is a topological vector space (Glöckner–Neeb, Lemma 4.1.31). -/
instance : ContinuousSMul ℝ (Sec E f) := continuousSMul_induced toPi

/-- `Γ_f` is locally convex (Glöckner–Neeb, Lemma 4.1.31). -/
instance : LocallyConvexSpace ℝ (Sec E f) := LocallyConvexSpace.induced toPi

/-- `Γ_f` is Hausdorff. -/
instance : T2Space (Sec E f) := isEmbedding_toPi.t2Space

/-- The fiber coordinates are continuous. -/
theorem continuous_coordFun (a : CoordIdx (E := E) f) :
    Continuous (coordFun (E := E) (f := f) a) :=
  (continuous_apply a).comp (continuous_induced_dom : Continuous (toPi (E := E) (f := f)))

/-- All the fiber coordinates, as a continuous linear map. -/
def toPiCLM : Sec E f →L[ℝ] ∀ a : CoordIdx (E := E) f, C(a.1.2, E) :=
  ⟨toPi, continuous_induced_dom⟩

/-- `toPiCLM` is a topological embedding. -/
theorem isEmbedding_toPiCLM : Topology.IsEmbedding (toPiCLM (E := E) (f := f)) :=
  isEmbedding_toPi

/-- `toPiCLM` has closed range. -/
theorem isClosed_range_toPiCLM [CompactSpace K] [T2Space K] :
    IsClosed (range (toPiCLM (E := E) (f := f))) :=
  isClosed_range_toPi

/-- A map into `Γ_f` is continuous if and only if all its fiber coordinates are. -/
theorem continuous_iff {X : Type*} [tX : TopologicalSpace X] {φ : X → Sec E f} :
    Continuous φ ↔ ∀ a, Continuous fun x ↦ coordFun a (φ x) :=
  ⟨fun h a ↦ (continuous_coordFun a).comp h, fun h ↦ continuous_induced_rng.2
    (continuous_pi fun a ↦ h a)⟩

section Compact

variable [CompactSpace K] [T2Space K]

omit [CompactSpace K] in
/-- If `φ : X → Γ_f` is continuous as a map into `C(K, TN)`, then so are its fiber
coordinates. -/
theorem continuous_toPi_of_continuous_toTangent {X : Type*} [tX : TopologicalSpace X]
    {φ : X → Sec E f} (hφ : Continuous fun x ↦ toTangent (φ x)) :
    Continuous fun x ↦ toPi (φ x) := by
  refine continuous_pi fun a ↦ ?_
  refine ContinuousMap.continuous_of_continuous_uncurry_restrict _ fun L hL ↦ ?_
  have he := (ContinuousMap.continuous_eval_comp_restrict (W := TangentBundle E N)
    continuous_subtype_val hL).comp ((hφ.comp continuous_fst).prodMk continuous_snd)
  exact (continuousOn_coordAt a.1.1).comp_continuous he fun q ↦ a.2.2 _ q.2.1.2

omit [CompactSpace K] in
/-- If `φ : X → Γ_f` is continuous as a map into `C(K, TN)`, then it is continuous. -/
theorem continuous_of_continuous_toTangent {X : Type*} [TopologicalSpace X]
    {φ : X → Sec E f} (hφ : Continuous fun x ↦ toTangent (φ x)) : Continuous φ :=
  continuous_induced_rng.2 (continuous_toPi_of_continuous_toTangent hφ)

/-- The inclusion `Γ_f → C(K, TN)` is continuous. -/
theorem continuous_toTangent : Continuous (toTangent (E := E) (f := f)) := by
  refine ContinuousMap.continuous_of_continuous_uncurry_restrict _ fun L _ ↦ ?_
  refine continuous_iff_continuousAt.2 fun q₀ ↦ ?_
  set i : atlas E N := ⟨chartAt E (f q₀.2), chart_mem_atlas E _⟩
  have hx₀ : f q₀.2 ∈ i.1.source := mem_chart_source E _
  obtain ⟨C, hCn, hCs, hC⟩ := local_compact_nhds
    (f.continuous.continuousAt.preimage_mem_nhds (i.1.open_source.mem_nhds hx₀))
  let a : CoordIdx (E := E) f := ⟨(i, C), hC, fun x hx ↦ hCs hx⟩
  refine (continuousAt_iff_coordAt (s := fun q : Sec E f × L ↦ toTangent q.1 q.2) i hx₀).2
    ⟨(f.continuous.comp (continuous_subtype_val.comp continuous_snd)).continuousAt, ?_⟩
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hS : {q : Sec E f × L | (q.2 : K) ∈ C} ∈ 𝓝 q₀ :=
    (continuous_subtype_val.comp continuous_snd).continuousAt.preimage_mem_nhds hCn
  have hh : Continuous fun p : Sec E f × C ↦ coordFun a p.1 p.2 :=
    continuous_eval.comp ((continuous_coordFun a).prodMap continuous_id)
  have hcont : ContinuousOn (fun q : Sec E f × L ↦ coordAt i (toTangent q.1 q.2))
      {q : Sec E f × L | (q.2 : K) ∈ C} := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (hh.comp (continuous_subtype_val.fst.prodMk
      ((continuous_subtype_val.comp continuous_subtype_val.snd).subtype_mk fun q ↦ q.2))).congr
      fun q ↦ rfl
  exact hcont.continuousAt hS

/-- **`Γ_f` carries the topology induced by `C(K, TN)`** (Glöckner–Neeb, 4.1.30, `ℓ = 0`). -/
theorem isInducing_toTangent : Topology.IsInducing (toTangent (E := E) (f := f)) := by
  refine (Topology.isInducing_iff _).2 (le_antisymm
    (continuous_iff_le_induced.1 continuous_toTangent) ?_)
  exact continuous_iff_le_induced.1 (continuous_toPi_of_continuous_toTangent (X := Sec E f)
    (tX := TopologicalSpace.induced toTangent inferInstance) (φ := id) continuous_induced_dom)

/-- `Γ_f → C(K, TN)` is a topological embedding. -/
theorem isEmbedding_toTangent : Topology.IsEmbedding (toTangent (E := E) (f := f)) :=
  ⟨isInducing_toTangent, fun u w h ↦ by
    rw [← ofTangent_toTangent u, ← ofTangent_toTangent w]
    simp only [h]⟩

end Compact

end Sec

end Sections

/-! ### Smoothness of charts -/

section ChartSmooth

variable {H : Type u} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [IsTopologicalAddGroup H]
  [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MBManifold H M]

/-- Charts are smooth on their sources. -/
theorem smoothMBMOn_of_mem_atlas {e : OpenPartialHomeomorph M H} (he : e ∈ atlas H M) :
    SmoothMBMOn H H e e.source := by
  intro k
  refine ⟨e.continuousOn, fun x _ ↦ ?_⟩
  have h := smoothMBOn_transition (chart_mem_atlas H x) he k
  exact h.mono fun y hy ↦ ⟨hy.1, hy.2.1⟩

/-- Inverses of charts are smooth on their targets. -/
theorem smoothMBMOn_symm_of_mem_atlas {e : OpenPartialHomeomorph M H} (he : e ∈ atlas H M) :
    SmoothMBMOn H H e.symm e.target := by
  intro k
  refine ⟨e.continuousOn_symm, fun y _ ↦ ?_⟩
  have h := smoothMBOn_transition he (chart_mem_atlas H (e.symm y)) k
  exact h.mono fun z (hz : z ∈ chartDomain e.symm e.target (chartAt H y)
    (chartAt H (e.symm y))) ↦ hz.2

/-- Restriction of smooth maps to smaller open sets. -/
theorem SmoothMBMOn.mono_of_isOpen {H' : Type u} [AddCommGroup H'] [Module ℝ H']
    [TopologicalSpace H'] [IsTopologicalAddGroup H'] [ContinuousSMul ℝ H']
    [LocallyConvexSpace ℝ H'] [T2Space H'] {M' : Type*} [TopologicalSpace M']
    [ChartedSpace H' M'] [MBManifold H' M'] {g : M → M'} {U V : Set M} (hU : IsOpen U)
    (hV : IsOpen V) (hg : SmoothMBMOn H H' g U) (hVU : V ⊆ U) : SmoothMBMOn H H' g V :=
  fun k ↦ (hg k).comp hV hU (smoothMBMOn_id hV k) hVU

omit [MBManifold H M] in
/-- `C^k` maps only depend on their values on the open set. -/
theorem ContMDiffMBOn.congr_of_isOpen {H' : Type u} [AddCommGroup H'] [Module ℝ H']
    [TopologicalSpace H'] [IsTopologicalAddGroup H'] [ContinuousSMul ℝ H']
    [LocallyConvexSpace ℝ H'] [T2Space H'] {M' : Type*} [TopologicalSpace M']
    [ChartedSpace H' M'] [MBManifold H' M'] {k : ℕ} {f g : M → M'} {U : Set M}
    (hf : ContMDiffMBOn (E := H) (F := H') k f U) (hU : IsOpen U) (heq : EqOn f g U) :
    ContMDiffMBOn (E := H) (F := H') k g U := by
  refine ⟨hf.1.congr fun x hx ↦ (heq hx).symm, fun x hx ↦ ?_⟩
  have hD : chartDomain g U (chartAt H x) (chartAt H' (g x)) =
      chartDomain f U (chartAt H x) (chartAt H' (f x)) := by
    ext y
    simp only [chartDomain, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by rw [heq h2, heq hx]; exact h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by rw [← heq h2, ← heq hx]; exact h3⟩
  rw [hD, ← heq hx]
  refine (hf.2 x hx).congr_of_isOpen (isOpen_chartDomain hU hf.1 _ _) fun y hy ↦ ?_
  simp only [Function.comp_apply, heq hy.2.1]

omit [MBManifold H M] in
/-- Smooth maps only depend on their values on the open set. -/
theorem SmoothMBMOn.congr_of_isOpen {H' : Type u} [AddCommGroup H'] [Module ℝ H']
    [TopologicalSpace H'] [IsTopologicalAddGroup H'] [ContinuousSMul ℝ H']
    [LocallyConvexSpace ℝ H'] [T2Space H'] {M' : Type*} [TopologicalSpace M']
    [ChartedSpace H' M'] [MBManifold H' M'] {f g : M → M'} {U : Set M}
    (hf : SmoothMBMOn H H' f U) (hU : IsOpen U) (heq : EqOn f g U) : SmoothMBMOn H H' g U :=
  fun k ↦ (hf k).congr_of_isOpen hU heq

end ChartSmooth

section TangentChartAtlas

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [MBManifold E N]

/-- The charts `tangentChart i i` belong to the atlas of `TN`. -/
theorem tangentChart_self_mem_atlas (i : atlas E N) :
    tangentChart i i.1 ∈ atlas (E × E) (TangentBundle E N) :=
  ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, _, ⟨i.1, i.2, OpenPartialHomeomorph.refl E,
    by simp [chartedSpaceSelf_atlas], rfl⟩, rfl⟩

end TangentChartAtlas

/-! ### Postcomposition with maps continuous on open sets -/

section CompOn

variable {K : Type*} [TopologicalSpace K] {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]

/-- Postcomposition `s ↦ h ∘ s` of a continuous map `s` with values in `W` with a map `h`
continuous on `W`. -/
def compOn (h : Y → Z) {W : Set Y} (hh : ContinuousOn h W) (s : C(K, Y)) (hs : ∀ x, s x ∈ W) :
    C(K, Z) :=
  ⟨h ∘ s, hh.comp_continuous s.continuous hs⟩

/-- `compOn h hh s hs x = h (s x)`. -/
@[simp]
theorem compOn_apply (h : Y → Z) {W : Set Y} (hh : ContinuousOn h W) (s : C(K, Y))
    (hs : ∀ x, s x ∈ W) (x : K) : compOn h hh s hs x = h (s x) :=
  rfl

/-- Postcomposition with a map continuous on `W` is continuous on the maps with values in `W`
(compact-open topologies, `K` Hausdorff). -/
theorem continuous_compOn [T2Space K] (h : Y → Z) {W : Set Y} (hh : ContinuousOn h W) :
    Continuous fun s : {s : C(K, Y) // ∀ x, s x ∈ W} ↦ compOn h hh s.1 s.2 := by
  refine ContinuousMap.continuous_of_continuous_uncurry_restrict _ fun L hL ↦ ?_
  have h1 : Continuous fun q : {s : C(K, Y) // ∀ x, s x ∈ W} × L ↦ (q.1.1, q.2) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have he := (ContinuousMap.continuous_eval_restrict (A := Y) hL).comp h1
  exact hh.comp_continuous he fun q ↦ q.1.2 q.2

end CompOn

/-! ### The charts of `C(K, N)` -/

section Charts

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [MBManifold E N]
  {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  (A : LocalAddition E N)

namespace LocalAddition

/-- The domain `O'_f = {g : (f, g)(K) ⊆ θ(Ω)}` of the chart at `f` (Glöckner–Neeb, proof of
Theorem 4.2.2). -/
def chartSource (f : C(K, N)) : Set C(K, N) :=
  {g | ∀ x, (f x, g x) ∈ A.toOpenPartialHomeomorph.target}

/-- The range `O_f = Γ_f ∩ C(K, Ω)` of the chart at `f`. -/
def chartTarget (f : C(K, N)) : Set (Sec E f) :=
  {u | ∀ x, Sec.toTangent u x ∈ A.toOpenPartialHomeomorph.source}

/-- `O'_f` is open in `C(K, N)`. -/
theorem isOpen_chartSource (f : C(K, N)) : IsOpen (A.chartSource f) := by
  have h : Continuous fun g : C(K, N) ↦ f.prodMk g :=
    ContinuousMap.continuous_prodMk_pair.comp (continuous_const.prodMk continuous_id)
  have := (ContinuousMap.isOpen_setOfPred_mapsTo (K := univ) isCompact_univ
    A.toOpenPartialHomeomorph.open_target).preimage h
  convert this using 1
  ext g
  simp [chartSource, MapsTo]

/-- `O_f` is open in `Γ_f`. -/
theorem isOpen_chartTarget (f : C(K, N)) : IsOpen (A.chartTarget f) := by
  have := (ContinuousMap.isOpen_setOfPred_mapsTo (K := univ) isCompact_univ
    A.toOpenPartialHomeomorph.open_source).preimage (Sec.continuous_toTangent (E := E) (f := f))
  convert this using 1
  ext u
  simp [chartTarget, MapsTo]

/-- `θ⁻¹ ∘ (f, g)` for `g ∈ O'_f`, as a continuous map `K → TN`. -/
def chartTangent (f g : C(K, N)) (hg : g ∈ A.chartSource f) : C(K, TangentBundle E N) :=
  compOn A.toOpenPartialHomeomorph.symm A.toOpenPartialHomeomorph.continuousOn_symm
    (f.prodMk g) hg

omit [CompactSpace K] [T2Space K] in
/-- `θ⁻¹ ∘ (f, g)` is a lift of `f`. -/
theorem chartTangent_proj (f g : C(K, N)) (hg : g ∈ A.chartSource f) (x : K) :
    (A.chartTangent f g hg x).proj = f x := by
  have h := A.fst_eq _ (A.toOpenPartialHomeomorph.map_target (hg x))
  rw [A.toOpenPartialHomeomorph.right_inv (hg x)] at h
  exact h.symm

/-- `Σ ∘ τ` for `τ ∈ O_f`, as a continuous map `K → N`. -/
def chartInvFun (f : C(K, N)) (u : Sec E f) (hu : u ∈ A.chartTarget f) : C(K, N) :=
  compOn (fun v ↦ (A.toOpenPartialHomeomorph v).2)
    (continuous_snd.comp_continuousOn A.toOpenPartialHomeomorph.continuousOn) (Sec.toTangent u) hu

open scoped Classical in
/-- **The chart of `C(K, N)` at `f`** (Glöckner–Neeb, proof of Theorem 4.2.2):
`φ_f : O'_f → O_f ⊆ Γ_f`, `g ↦ θ⁻¹ ∘ (f, g)`, with inverse `τ ↦ Σ ∘ τ`. It is modeled on `Γ_f`. -/
def chart (f : C(K, N)) : OpenPartialHomeomorph C(K, N) (Sec E f) where
  toFun g := if hg : g ∈ A.chartSource f then Sec.ofTangent (A.chartTangent f g hg)
    (A.chartTangent_proj f g hg) else 0
  invFun u := if hu : u ∈ A.chartTarget f then A.chartInvFun f u hu else f
  source := A.chartSource f
  target := A.chartTarget f
  map_source' g hg := by
    simp only [hg, dite_true]
    intro x
    rw [Sec.toTangent_ofTangent]
    exact A.toOpenPartialHomeomorph.map_target (hg x)
  map_target' u hu := by
    simp only [hu, dite_true]
    intro x
    have h := A.toOpenPartialHomeomorph.map_source (hu x)
    rw [A.toOpenPartialHomeomorph_apply (hu x)] at h
    exact h
  left_inv' g hg := by
    have h : Sec.ofTangent (A.chartTangent f g hg) (A.chartTangent_proj f g hg) ∈
        A.chartTarget f := fun x ↦ by
      rw [Sec.toTangent_ofTangent]; exact A.toOpenPartialHomeomorph.map_target (hg x)
    simp only [hg, h, dite_true]
    ext x
    change (A.toOpenPartialHomeomorph (Sec.toTangent (Sec.ofTangent _ _) x)).2 = g x
    rw [Sec.toTangent_ofTangent]
    change (A.toOpenPartialHomeomorph (A.toOpenPartialHomeomorph.symm (f x, g x))).2 = g x
    rw [A.toOpenPartialHomeomorph.right_inv (hg x)]
  right_inv' u hu := by
    have h : A.chartInvFun f u hu ∈ A.chartSource f := fun x ↦ by
      have h := A.toOpenPartialHomeomorph.map_source (hu x)
      rw [A.toOpenPartialHomeomorph_apply (hu x)] at h
      exact h
    simp only [hu, h, dite_true]
    apply Sec.isEmbedding_toTangent.injective
    rw [Sec.toTangent_ofTangent]
    ext x : 1
    change A.toOpenPartialHomeomorph.symm (f x, (A.toOpenPartialHomeomorph
      (Sec.toTangent u x)).2) = Sec.toTangent u x
    have e : ((f x, (A.toOpenPartialHomeomorph (Sec.toTangent u x)).2) : N × N) =
        A.toOpenPartialHomeomorph (Sec.toTangent u x) := Prod.ext (A.fst_eq _ (hu x)).symm rfl
    rw [e]
    exact A.toOpenPartialHomeomorph.left_inv (hu x)
  open_source := A.isOpen_chartSource f
  open_target := A.isOpen_chartTarget f
  continuousOn_toFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine Sec.continuous_of_continuous_toTangent ?_
    have hp : Continuous fun g : A.chartSource f ↦ f.prodMk g.1 :=
      ContinuousMap.continuous_prodMk_pair.comp (continuous_const.prodMk continuous_subtype_val)
    refine ((continuous_compOn A.toOpenPartialHomeomorph.symm
      A.toOpenPartialHomeomorph.continuousOn_symm).comp
      (hp.subtype_mk fun g ↦ g.2)).congr fun g ↦ ?_
    simp only [domRestrict_apply, g.2, dite_true, Sec.toTangent_ofTangent]
    rfl
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine ((continuous_compOn _ (continuous_snd.comp_continuousOn
      A.toOpenPartialHomeomorph.continuousOn)).comp
      ((Sec.continuous_toTangent.comp continuous_subtype_val).subtype_mk fun u ↦ u.2)).congr
      fun u ↦ ?_
    simp only [domRestrict_apply, u.2, dite_true]
    rfl

/-- The chart at `f` contains `f` in its domain. -/
theorem mem_chart_source (f : C(K, N)) : f ∈ (A.chart f).source := fun x ↦ by
  have h := A.toOpenPartialHomeomorph.map_source (A.zero_mem (f x))
  rw [A.toOpenPartialHomeomorph_apply (A.zero_mem (f x))] at h
  simpa [LocalAddition.toFun_zero] using h

open scoped Classical in
/-- In the chart at `f`, `g` has fiber coordinates `x ↦ θ⁻¹(f x, g x)`. -/
theorem toTangent_chart (f g : C(K, N)) (hg : g ∈ (A.chart f).source) (x : K) :
    Sec.toTangent (A.chart f g) x = A.toOpenPartialHomeomorph.symm (f x, g x) := by
  change Sec.toTangent (if hg : g ∈ A.chartSource f then Sec.ofTangent (A.chartTangent f g hg)
    (A.chartTangent_proj f g hg) else 0) x = _
  have hg' : g ∈ A.chartSource f := hg
  simp only [hg', dite_true, Sec.toTangent_ofTangent]
  rfl

open scoped Classical in
/-- The inverse of the chart at `f` is `τ ↦ Σ ∘ τ`. -/
theorem chart_symm_apply (f : C(K, N)) {u : Sec E f} (hu : u ∈ (A.chart f).target) (x : K) :
    (A.chart f).symm u x = A.toFun (Sec.toTangent u x) := by
  change (if hu : u ∈ A.chartTarget f then A.chartInvFun f u hu else f) x = _
  have hu' : u ∈ A.chartTarget f := hu
  simp only [hu', dite_true]
  rfl

end LocalAddition

end Charts

/-! ### The transition maps in coordinates -/

section Transition

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [MBManifold E N]
  (A : LocalAddition E N)

namespace LocalAddition

/-- The domain `{(y, z, v) : …}` of the transition maps in the charts `i` (for the source) and
`j` (for the target) of `N`, first stage: `y ∈ i(Uᵢ)`, `z ∈ j(Uⱼ)`. -/
def transDom₁ (i j : atlas E N) : Set (E × E × E) := {q | q.1 ∈ i.1.target ∧ q.2.1 ∈ j.1.target}

/-- `(y, z, v) ↦ (i⁻¹ y, v) ∈ TN`. -/
def transVec (i : atlas E N) (q : E × E × E) : TangentBundle E N :=
  (tangentChart i i.1).symm (q.1, q.2.2)

/-- Second stage: the vector lies in `Ω`. -/
def transDom₂ (i j : atlas E N) : Set (E × E × E) :=
  transDom₁ i j ∩ transVec i ⁻¹' A.source

/-- `(y, z, v) ↦ (j⁻¹ z, Σ(i⁻¹ y, v)) ∈ N × N`. -/
def transPair (i j : atlas E N) (q : E × E × E) : N × N :=
  (j.1.symm q.2.1, A.toFun (transVec i q))

/-- The domain of the transition maps in the charts `i`, `j`. -/
def transDom (i j : atlas E N) : Set (E × E × E) :=
  A.transDom₂ i j ∩ A.transPair i j ⁻¹' A.toOpenPartialHomeomorph.target

/-- **The transition maps in charts**: `(y, z, v) ↦ θ⁻¹(j⁻¹ z, Σ(i⁻¹ y, v))`, in the fiber
coordinates of the chart `j`. -/
def transMap (i j : atlas E N) (q : E × E × E) : E :=
  coordAt j (A.toOpenPartialHomeomorph.symm (A.transPair i j q))

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] [MBManifold E N] in
/-- The first-stage domain is open. -/
theorem isOpen_transDom₁ (i j : atlas E N) : IsOpen (transDom₁ i j) :=
  (i.1.open_target.preimage continuous_fst).inter
    (j.1.open_target.preimage (continuous_fst.comp continuous_snd))

/-- `(y, z, v) ↦ (y, v)` maps the first-stage domain into the target of the chart of `TN`. -/
theorem mapsTo_transDom₁ (i j : atlas E N) :
    MapsTo (fun q : E × E × E ↦ (q.1, q.2.2)) (transDom₁ i j) (tangentChart i i.1).target :=
  fun _ hq ↦ (mem_tangentChart_target i i.1 _).2 ⟨hq.1, i.1.map_target hq.1⟩

/-- `(y, z, v) ↦ (i⁻¹ y, v)` is smooth. -/
theorem smoothMBMOn_transVec (i j : atlas E N) :
    SmoothMBMOn (E × E × E) (E × E) (transVec i) (transDom₁ i j) := fun k ↦
  ((smoothMBMOn_symm_of_mem_atlas (tangentChart_self_mem_atlas i)) k).comp
    (isOpen_transDom₁ i j) (tangentChart i i.1).open_target
    ((contMDiffMBOn_iff_contDiffMBOn (isOpen_transDom₁ i j)).2
      ((((ContinuousLinearMap.fst ℝ E (E × E)).prod
        ((ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.snd ℝ E (E × E)))).contDiffMBOn
          k univ).mono (subset_univ _)))
    (mapsTo_transDom₁ i j)

/-- The second-stage domain is open. -/
theorem isOpen_transDom₂ (i j : atlas E N) : IsOpen (A.transDom₂ i j) :=
  ((smoothMBMOn_transVec i j) 0).continuousOn.isOpen_inter_preimage (isOpen_transDom₁ i j)
    A.isOpen_source

/-- `(y, z, v) ↦ (j⁻¹ z, Σ(i⁻¹ y, v))` is smooth. -/
theorem smoothMBMOn_transPair (i j : atlas E N) :
    SmoothMBMOn (E × E × E) (ModelProd E E) (A.transPair i j) (A.transDom₂ i j) := by
  intro k
  have h₂ := A.isOpen_transDom₂ i j
  have hsub : A.transDom₂ i j ⊆ transDom₁ i j := inter_subset_left
  have hz : ContMDiffMBOn (E := E × E × E) (F := E) k (fun q : E × E × E ↦ q.2.1)
      (A.transDom₂ i j) := (contMDiffMBOn_iff_contDiffMBOn h₂).2
    ((((ContinuousLinearMap.fst ℝ E E).comp (ContinuousLinearMap.snd ℝ E (E × E))).contDiffMBOn
      k univ).mono (subset_univ _))
  have h1 := ((smoothMBMOn_symm_of_mem_atlas j.2) k).comp h₂ j.1.open_target hz
    fun q hq ↦ (hsub hq).2
  have h2 := (A.smoothMBMOn_toFun k).comp h₂ A.isOpen_source
    ((SmoothMBMOn.mono_of_isOpen (isOpen_transDom₁ i j) h₂ (smoothMBMOn_transVec i j) hsub) k)
    fun q hq ↦ hq.2
  exact ContMDiffMBOn.prodMk h₂ h1 h2

/-- The domain of the transition maps in charts is open. -/
theorem isOpen_transDom (i j : atlas E N) : IsOpen (A.transDom i j) :=
  ((A.smoothMBMOn_transPair i j) 0).continuousOn.isOpen_inter_preimage (A.isOpen_transDom₂ i j)
    A.toOpenPartialHomeomorph.open_target

/-- The transition maps in charts are smooth. -/
theorem smoothMBOn_transMap (i j : atlas E N) : SmoothMBOn (A.transMap i j) (A.transDom i j) := by
  intro k
  have hD := A.isOpen_transDom i j
  have h1 := ((A.smoothMBMOn_symm) k).comp hD A.toOpenPartialHomeomorph.open_target
    (((SmoothMBMOn.mono_of_isOpen (A.isOpen_transDom₂ i j) hD (A.smoothMBMOn_transPair i j)
      inter_subset_left)) k) fun q hq ↦ hq.2
  have hmaps : MapsTo (A.toOpenPartialHomeomorph.symm ∘ A.transPair i j) (A.transDom i j)
      (tangentChart j j.1).source := by
    intro q hq
    rw [mem_tangentChart_self_source]
    have h := A.fst_eq _ (A.toOpenPartialHomeomorph.map_target hq.2)
    rw [A.toOpenPartialHomeomorph.right_inv hq.2] at h
    change (A.toOpenPartialHomeomorph.symm (A.transPair i j q)).proj ∈ j.1.source
    rw [← h]
    exact j.1.map_target hq.1.1.2
  have h2 := ((smoothMBMOn_of_mem_atlas (tangentChart_self_mem_atlas j)) k).comp hD
    (tangentChart j j.1).open_source h1 hmaps
  have h3 := ((contMDiffMBOn_iff_contDiffMBOn (E := E × E) (F := E) isOpen_univ).2
    ((ContinuousLinearMap.snd ℝ E E).contDiffMBOn k univ)).comp hD isOpen_univ h2
    (mapsTo_univ _ _)
  exact (contMDiffMBOn_iff_contDiffMBOn hD).1 h3

end LocalAddition

end Transition

/-! ### Smoothness of the transition maps -/

section TransitionSmooth

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [MBManifold E N]
  {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  (A : LocalAddition E N)

namespace LocalAddition

/-- The domain of the transition map from the chart at `f` to the chart at `g`. -/
def transitionDomain (f g : C(K, N)) : Set (Sec E f) :=
  (A.chart f).target ∩ (A.chart f).symm ⁻¹' (A.chart g).source

/-- The domain of the transition map is open. -/
theorem isOpen_transitionDomain (f g : C(K, N)) : IsOpen (A.transitionDomain f g) :=
  (A.chart f).isOpen_inter_preimage_symm (A.chart g).open_source

/-- The transition map `φ_g ∘ φ_f⁻¹ : Γ_f ⊇ ψ_f⁻¹(O'_f ∩ O'_g) → Γ_g`. -/
def transition (f g : C(K, N)) (u : Sec E f) : Sec E g := A.chart g ((A.chart f).symm u)

/-- In coordinates over a compact set adapted to charts `i` and `j` of `N`, the transition map is
the superposition operator of `transMap i j`. -/
theorem coordFun_transition (f g : C(K, N)) (a : Sec.CoordIdx (E := E) g) (i : atlas E N)
    (hi : ∀ x ∈ a.1.2, f x ∈ i.1.source) {u : Sec E f} (hu : u ∈ A.transitionDomain f g)
    (x : a.1.2) :
    (A.transDom i a.1.1).indicator (A.transMap i a.1.1) (i.1 (f x), a.1.1.1 (g x),
      Sec.coordFun ⟨(i, a.1.2), a.2.1, hi⟩ u x) = Sec.coordFun a (A.transition f g u) x ∧
    ((i.1 (f x), a.1.1.1 (g x), Sec.coordFun ⟨(i, a.1.2), a.2.1, hi⟩ u x) : E × E × E) ∈
      A.transDom i a.1.1 := by
  set j := a.1.1
  have hfx : f x ∈ i.1.source := hi x x.2
  have hgx : g x ∈ j.1.source := a.2.2 x x.2
  have hvec : transVec i (i.1 (f x), j.1 (g x), Sec.coordFun ⟨(i, a.1.2), a.2.1, hi⟩ u x) =
      Sec.toTangent u x := by
    change (tangentChart i i.1).symm (i.1 (f x), coordAt i (Sec.toTangent u x)) = _
    have h := (tangentChart i i.1).left_inv
      ((mem_tangentChart_self_source i (Sec.toTangent u x)).2 hfx)
    rw [tangentChart_self_apply] at h
    exact h
  have hpair : A.transPair i j (i.1 (f x), j.1 (g x), Sec.coordFun ⟨(i, a.1.2), a.2.1, hi⟩ u x) =
      (g x, (A.chart f).symm u x) := by
    rw [transPair, hvec, j.1.left_inv hgx, A.chart_symm_apply f hu.1]
  have hmem : ((i.1 (f x), j.1 (g x), Sec.coordFun ⟨(i, a.1.2), a.2.1, hi⟩ u x) : E × E × E) ∈
      A.transDom i j := by
    refine ⟨⟨⟨i.1.map_source hfx, j.1.map_source hgx⟩, ?_⟩, ?_⟩
    · change transVec i _ ∈ A.source
      rw [hvec]
      exact hu.1 x
    · change A.transPair i j _ ∈ A.toOpenPartialHomeomorph.target
      rw [hpair]
      exact hu.2 x
  refine ⟨?_, hmem⟩
  rw [indicator_of_mem hmem, transMap, hpair]
  change _ = coordAt j (Sec.toTangent (A.chart g ((A.chart f).symm u)) x)
  rw [A.toTangent_chart g _ hu.2]

/-- **Smoothness in adapted coordinates**: over a compact set `L` with `f(L)` in the chart `i` and
`g(L)` in the chart `j`, the coordinates of the transition map are smooth. -/
theorem contDiffMBOn_coordFun_transition_of_adapted (f g : C(K, N)) (a : Sec.CoordIdx (E := E) g)
    (i : atlas E N) (hi : ∀ x ∈ a.1.2, f x ∈ i.1.source) (k : ℕ) :
    ContDiffMBOn k (fun u ↦ Sec.coordFun a (A.transition f g u)) (A.transitionDomain f g) := by
  set L := a.1.2
  set j := a.1.1
  have : CompactSpace L := isCompact_iff_compactSpace.mp a.2.1
  let b : Sec.CoordIdx (E := E) f := ⟨(i, L), a.2.1, hi⟩
  -- the curve `x ↦ (i (f x), j (g x), u x in the chart i)` depends affinely on `u`
  let γ₀ : C(L, E × E × E) := ⟨fun x ↦ (i.1 (f x), j.1 (g x), 0), by
    refine Continuous.prodMk ?_ (Continuous.prodMk ?_ continuous_const)
    · exact i.1.continuousOn.comp_continuous (f.continuous.comp continuous_subtype_val)
        fun x ↦ hi x x.2
    · exact j.1.continuousOn.comp_continuous (g.continuous.comp continuous_subtype_val)
        fun x ↦ a.2.2 x x.2⟩
  let Λ : Sec E f →L[ℝ] C(L, E × E × E) :=
    (ContinuousLinearMap.compLeftContinuous ℝ L ((ContinuousLinearMap.inr ℝ E (E × E)).comp
      (ContinuousLinearMap.inr ℝ E E))).comp ⟨Sec.coordL b, Sec.continuous_coordFun b⟩
  have hγ : ContDiffMBOn k (fun u ↦ Λ u + γ₀) univ :=
    (Λ.contDiffMBOn k univ).add isOpen_univ (contDiffMBOn_const k γ₀ univ)
  have hγx : ∀ u x, (Λ u + γ₀) x = (i.1 (f x), j.1 (g x), Sec.coordFun b u x) := fun u x ↦ by
    simp [Λ, γ₀, Sec.coordL]
  have hP := (smoothMBOn_pushforward (K := L) (A.isOpen_transDom i j)
    (A.smoothMBOn_transMap i j)) k
  have hmaps : MapsTo (fun u ↦ Λ u + γ₀) (A.transitionDomain f g) (valuedIn L (A.transDom i j)) :=
    fun u hu x ↦ by rw [hγx]; exact (A.coordFun_transition f g a i hi hu x).2
  have hc := hP.comp (A.isOpen_transitionDomain f g) (isOpen_valuedIn (A.isOpen_transDom i j))
    (hγ.mono (subset_univ _)) hmaps
  refine ContDiffMBOn.congr_of_isOpen (A.isOpen_transitionDomain f g) (fun u hu ↦ ?_) hc
  ext x
  rw [Function.comp_apply, pushforward_apply ((A.smoothMBOn_transMap i j) 0).continuousOn
    (hmaps hu) x, hγx]
  have h := (A.coordFun_transition f g a i hi hu x).1
  rwa [indicator_of_mem (A.coordFun_transition f g a i hi hu x).2] at h

/-- **`C^k` maps into `Γ_f`**: a map into `Γ_f` is `C^k` if all its fiber coordinates are. -/
theorem Sec.contDiffMBOn_of_coordFun {V : Type u} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [LocallyConvexSpace ℝ V]
    [T2Space V] {f : C(K, N)} {k : ℕ} {h : V → Sec E f} {W : Set V} (hW : IsOpen W)
    (hh : ∀ a, ContDiffMBOn k (fun x ↦ Sec.coordFun a (h x)) W) : ContDiffMBOn k h W :=
  contDiffMBOn_of_isClosedEmbedding Sec.toPiCLM Sec.isEmbedding_toPiCLM
    Sec.isClosed_range_toPiCLM hW (contDiffMBOn_pi hW hh)

/-- **The transition maps are smooth** (Glöckner–Neeb, proof of Theorem 4.2.2, `ℓ = 0`):
`φ_g ∘ φ_f⁻¹` is smooth on its open domain in `Γ_f`. In coordinates over compact sets adapted to
charts of `N`, it is a superposition operator, smooth by Glöckner–Neeb, Proposition 1.7.1
(`smoothMBOn_pushforward`). -/
theorem smoothMBOn_transition (f g : C(K, N)) :
    SmoothMBOn (A.transition f g) (A.transitionDomain f g) := by
  intro k
  refine Sec.contDiffMBOn_of_coordFun (A.isOpen_transitionDomain f g) fun a ↦ ?_
  set L := a.1.2
  set j := a.1.1
  -- a finite cover of `L` by compact sets on which `f` lies in a chart of `N`
  have hC : ∀ x : K, ∃ C ∈ 𝓝 x, C ⊆ f ⁻¹' (chartAt E (f x)).source ∧ IsCompact C := fun x ↦
    local_compact_nhds (f.continuous.continuousAt.preimage_mem_nhds
      ((chartAt E (f x)).open_source.mem_nhds (_root_.mem_chart_source E (f x))))
  choose C hCn hCs hCc using hC
  obtain ⟨t, -, ht⟩ := a.2.1.elim_nhds_subcover C fun x _ ↦ hCn x
  let Lb : t → Set K := fun b ↦ L ∩ C b
  have hsub : ∀ b, Lb b ⊆ L := fun _ ↦ inter_subset_left
  have hcpt : ∀ b, IsCompact (Lb b) := fun b ↦ a.2.1.inter_right (hCc b).isClosed
  have hcov : L ⊆ ⋃ b, Lb b := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (ht hx)
    exact mem_iUnion.2 ⟨⟨y, hy⟩, hx, hxy⟩
  let ab : t → Sec.CoordIdx (E := E) g := fun b ↦
    ⟨(j, Lb b), hcpt b, fun x hx ↦ a.2.2 x hx.1⟩
  have hpiece : ∀ b, ContDiffMBOn k (fun u ↦ restrictPieces (G := E) hsub
      (Sec.coordFun a (A.transition f g u)) b) (A.transitionDomain f g) := fun b ↦
    (A.contDiffMBOn_coordFun_transition_of_adapted f g (ab b)
      ⟨chartAt E (f b), _root_.chart_mem_atlas E _⟩ (fun x hx ↦ hCs b hx.2) k).congr_of_isOpen
      (A.isOpen_transitionDomain f g) (fun u _ ↦ rfl)
  exact contDiffMBOn_of_isClosedEmbedding (restrictPieces hsub)
    (isEmbedding_restrictPieces hsub hcpt hcov) (isClosed_range_restrictPieces hsub hcpt hcov)
    (A.isOpen_transitionDomain f g) (contDiffMBOn_pi (A.isOpen_transitionDomain f g) hpiece)

end LocalAddition

end TransitionSmooth

/-! ### Atlases with varying models and the manifold `C(K, N)` -/

/-- **An atlas with varying models** (compare Glöckner–Neeb, Definition 3.2.13): a family of
charts `φᵢ : X ⊇ Uᵢ → Vᵢ ⊆ Eᵢ`, each modeled on its own Hausdorff locally convex space `Eᵢ`,
whose domains cover `X` and whose transition maps `φⱼ ∘ φᵢ⁻¹` are smooth in the sense of
Michal–Bastiani. Mathlib's `ChartedSpace` has a single model space, which does not fit
manifolds of mappings: the chart of `C(K, N)` at `f` is modeled on `Γ_f`. -/
structure VaryingAtlas (X : Type*) [TopologicalSpace X] where
  /-- The index set of the charts. -/
  ι : Type*
  /-- The model space of each chart. -/
  model : ι → Type u
  [addCommGroup : ∀ i, AddCommGroup (model i)]
  [module : ∀ i, Module ℝ (model i)]
  [topologicalSpace : ∀ i, TopologicalSpace (model i)]
  [isTopologicalAddGroup : ∀ i, IsTopologicalAddGroup (model i)]
  [continuousSMul : ∀ i, ContinuousSMul ℝ (model i)]
  [locallyConvexSpace : ∀ i, LocallyConvexSpace ℝ (model i)]
  [t2Space : ∀ i, T2Space (model i)]
  /-- The charts. -/
  chart : ∀ i, OpenPartialHomeomorph X (model i)
  /-- A preferred chart at each point. -/
  chartAt : X → ι
  /-- The preferred chart at `x` contains `x` in its domain. -/
  mem_chartAt_source : ∀ x, x ∈ (chart (chartAt x)).source
  /-- The transition maps are smooth. -/
  smoothMBOn_transition : ∀ i j, SmoothMBOn (chart j ∘ (chart i).symm)
    ((chart i).target ∩ (chart i).symm ⁻¹' (chart j).source)

section MappingManifold

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [MBManifold E N]
  {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  (A : LocalAddition E N)

namespace LocalAddition

/-- **The manifold of continuous maps** `C(K, N)` (Glöckner–Neeb, Theorem 4.2.2(a) and (b), for
`ℓ = 0`): for `K` compact Hausdorff and `N` admitting a local addition, the charts
`φ_f : O'_f → O_f ⊆ Γ_f`, `g ↦ θ⁻¹ ∘ (f, g)`, form an atlas of `C(K, N)` with varying models
`Γ_f` and smooth transition maps. The charts are partial homeomorphisms for the compact-open
topology of `C(K, N)`, so the topology of this manifold is the compact-open topology
(Theorem 4.2.2(b)). -/
def mappingAtlas : VaryingAtlas C(K, N) where
  ι := C(K, N)
  model f := Sec E f
  chart := A.chart
  chartAt g := g
  mem_chartAt_source g := A.mem_chart_source g
  smoothMBOn_transition f g := A.smoothMBOn_transition f g

/-- `u ↦ u(x) ∈ T_{f(x)} N` is smooth on `Γ_f`. -/
theorem smoothMBM_evalTangent (f : C(K, N)) (x : K) :
    SmoothMBM (Sec E f) (E × E) (fun u : Sec E f ↦ Sec.toTangent u x) := by
  intro k
  refine ⟨((continuous_eval_const x).comp Sec.continuous_toTangent).continuousOn, fun u _ ↦ ?_⟩
  set i : atlas E N := ⟨chartAt E (f x), _root_.chart_mem_atlas E _⟩
  let a : Sec.CoordIdx (E := E) f := Sec.singletonIdx x
  let L : Sec E f →L[ℝ] E := (ContinuousMap.evalCLM ℝ (⟨x, rfl⟩ : ({x} : Set K))).comp
    ⟨Sec.coordL a, Sec.continuous_coordFun a⟩
  have hsmooth : ContDiffMBOn k (fun w : Sec E f ↦ ((chartAt E (f x) (f x), L w) : E × E)) univ :=
    (contDiffMBOn_const k _ univ).prodMk isOpen_univ (L.contDiffMBOn k univ)
  refine ContDiffMBOn.congr_of_isOpen (isOpen_chartDomain isOpen_univ
    ((continuous_eval_const x).comp Sec.continuous_toTangent).continuousOn _ _)
    (fun w _ ↦ ?_) (hsmooth.mono (subset_univ _))
  rfl

/-- **Point evaluations are smooth** (Glöckner–Neeb, Theorem 4.2.2(c), `ℓ = 0`): in the chart at
`f`, the evaluation `ε_x : g ↦ g(x)` reads `τ ↦ Σ(τ(x))`, which is smooth on `O_f`. -/
theorem smoothMBMOn_eval_chart_symm (f : C(K, N)) (x : K) :
    SmoothMBMOn (Sec E f) E (fun u ↦ (A.chart f).symm u x) (A.chart f).target := by
  intro k
  have h := (A.smoothMBMOn_toFun k).comp (A.chart f).open_target A.isOpen_source
    ((smoothMBM_evalTangent f x k).comp (A.chart f).open_target isOpen_univ
      (smoothMBMOn_id (A.chart f).open_target k) (mapsTo_univ _ _)) fun u hu ↦ hu x
  exact h.congr_of_isOpen (A.chart f).open_target fun u hu ↦ (A.chart_symm_apply f hu x).symm

end LocalAddition

end MappingManifold

/-- The domains of the charts of an atlas with varying models cover the space. -/
theorem VaryingAtlas.exists_mem_source {X : Type*} [TopologicalSpace X] (A : VaryingAtlas X)
    (x : X) : ∃ i, x ∈ (A.chart i).source :=
  ⟨A.chartAt x, A.mem_chartAt_source x⟩

end LocallyConvex.Manifolds
