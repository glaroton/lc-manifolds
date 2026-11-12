/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Calculus.SmoothExponentialLaw
public import LocallyConvexManifolds.Manifold.CkSuperposition
public import LocallyConvexManifolds.Manifold.VaryingAtlas

/-!
# `C^{k,ℓ}` maps between manifolds

Let `L` be a space with an atlas with varying models `B` (for instance a manifold of the library,
through `VaryingAtlas.ofChartedSpace`, or a manifold of mappings) and `M`, `N` manifolds modeled on
Hausdorff locally convex spaces `H`, `F`. A map
`f : L × M → N` is `C^{k,ℓ}` if, around each point, its local representatives in charts are
`C^{k,ℓ}` on products of open sets (H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*,
arXiv:2602.12362, Definition 3.5.24; the `C^{k,ℓ}` maps on open sets are those of lc-analysis,
Definition 1.7.17). These maps are the subject of the exponential law for manifolds of mappings,
Theorem 4.2.2(a).

## Main definitions

* `IsChartBox f e e' c U V`: `U × V` is a product of open sets in the targets of the charts `e`,
  `e'`, with `f(e⁻¹ U × e'⁻¹ V)` in the source of the chart `c`; `localRep₂ f e e' c`: the local
  representative `(a, b) ↦ c(f(e⁻¹ a, e'⁻¹ b))`.
* `ContMDiffMB₂ H F B k ℓ f`: `f` is `C^{k,ℓ}` (Definition 3.5.24).

## Main results

* The `C^{k,ℓ}` calculus on open sets (locality, currying and the chain rule
  `ContDiffMBOn₂.comp_prodMap`) is in lc-analysis, `Calculus/SmoothExponentialLaw.lean`.
* `ContMDiffMB₂.continuous`: `C^{k,ℓ}` maps are continuous (remark after Definition 3.5.24).
* `ContMDiffMB₂.contDiffMBOn₂`: chart independence, the local representatives on every box in
  every chart are `C^{k,ℓ}` (Remark 3.5.26(a)).
* `ContMDiffMB₂.contMDiffOn_left`: the partial maps `x ↦ f(x, y)` of a `C^{k,ℓ}` map are `C^k`.
* The local compactness hypotheses hold for compact manifolds `M`
  (`locallyCompactSpace_of_compactSpace`, in `Manifold/CkSuperposition.lean`).

## Implementation notes

* Manifolds with rough boundary are out of scope; `M`, `N` are manifolds of the library (smooth,
  without boundary), and `k`, `ℓ` are finite (`∞` is "for all finite orders"). Glöckner–Neeb
  remark (Remark 3.5.28) that the definition extends to non-pure manifolds; this is why the first
  factor is an atlas with varying models.
* All the model spaces live in one universe.
-/

@[expose] public section

open Set Filter Function TopologicalSpace
open scoped Topology
open LocallyConvex.Analysis

noncomputable section

universe u

namespace LocallyConvex.Manifolds

/-! ### `C^{k,ℓ}` maps on products of manifolds -/

section Manifolds

variable {G H F : Type u} [TopologicalSpace G]
  [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [IsTopologicalAddGroup H]
  [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {L : Type*} [TopologicalSpace L]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N]

/-- The local representative `(a, b) ↦ c(f(e⁻¹ a, e'⁻¹ b))` of a map `f : L × M → N` in charts
`e`, `e'` of `L`, `M` and `c` of `N`. -/
def localRep₂ (f : L × M → N) (e : OpenPartialHomeomorph L G) (e' : OpenPartialHomeomorph M H)
    (c : OpenPartialHomeomorph N F) (p : G × H) : F :=
  c (f (e.symm p.1, e'.symm p.2))

/-- `U × V` is a box for the charts `e`, `e'`, `c`: `U` and `V` are open subsets of the targets
of `e` and `e'`, and `f(e⁻¹ U × e'⁻¹ V)` lies in the source of `c`. -/
structure IsChartBox (f : L × M → N) (e : OpenPartialHomeomorph L G)
    (e' : OpenPartialHomeomorph M H) (c : OpenPartialHomeomorph N F) (U : Set G) (V : Set H) :
    Prop where
  /-- `U` is open. -/
  isOpen_left : IsOpen U
  /-- `V` is open. -/
  isOpen_right : IsOpen V
  /-- `U` lies in the target of `e`. -/
  subset_left : U ⊆ e.target
  /-- `V` lies in the target of `e'`. -/
  subset_right : V ⊆ e'.target
  /-- `f(e⁻¹ U × e'⁻¹ V)` lies in the source of `c`. -/
  mapsTo : ∀ a ∈ U, ∀ b ∈ V, f (e.symm a, e'.symm b) ∈ c.source

variable (H F) in
/-- **`C^{k,ℓ}` maps** `L × M → N` (Glöckner–Neeb, Definition 3.5.24), for `L` given by an atlas
with varying models `B` (for instance a manifold of the library, `VaryingAtlas.ofChartedSpace`, or
a manifold of mappings): around each point `(x, y)` there are charts `φ_i` of `B` at `x`, `e'` of
`M` at `y` and `c` of `N`, and a box `U × V ∋ (φ_i x, e' y)` on which the local representative of
`f` is `C^{k,ℓ}`. -/
def ContMDiffMB₂ (B : VaryingAtlas.{u, _, _} L) (k ℓ : ℕ) (f : L × M → N) : Prop :=
  ∀ x y, ∃ i : B.ι, ∃ e' ∈ atlas H M, ∃ c ∈ atlas F N, ∃ (U : Set (B.model i)) (V : Set H),
    x ∈ (B.chart i).source ∧ y ∈ e'.source ∧ B.chart i x ∈ U ∧ e' y ∈ V ∧
    IsChartBox f (B.chart i) e' c U V ∧ ContDiffMBOn₂ k ℓ (localRep₂ f (B.chart i) e' c) U V

omit [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- `C^{k,ℓ}` maps are continuous. -/
theorem ContMDiffMB₂.continuous {B : VaryingAtlas.{u, _, _} L} {k ℓ : ℕ} {f : L × M → N}
    (hf : ContMDiffMB₂ H F B k ℓ f) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun ⟨x, y⟩ ↦ ?_
  obtain ⟨i, e', -, c, -, U, V, hx, hy, hxU, hyV, hbox, hrep⟩ := hf x y
  set e := B.chart i
  have hrc : ContinuousOn (localRep₂ f e e' c) (U ×ˢ V) := by
    have h := hrep.continuousOn 0 (Nat.zero_le k) 0 (Nat.zero_le ℓ)
    have hj : Continuous fun p : B.model i × H ↦
        (p, ((Fin.elim0 : Fin 0 → B.model i), (Fin.elim0 : Fin 0 → H))) := by fun_prop
    exact (h.comp hj.continuousOn fun p hp ↦ ⟨hp, mem_univ _⟩ :)
  set S := (e.source ∩ e ⁻¹' U) ×ˢ (e'.source ∩ e' ⁻¹' V)
  have hS : S ∈ 𝓝 (x, y) :=
    ((e.continuousOn.isOpen_inter_preimage e.open_source hbox.isOpen_left).prod
      (e'.continuousOn.isOpen_inter_preimage e'.open_source hbox.isOpen_right)).mem_nhds
      ⟨⟨hx, hxU⟩, ⟨hy, hyV⟩⟩
  have hpair : ContinuousAt (fun q : L × M ↦ ((e q.1, e' q.2) : B.model i × H)) (x, y) :=
    ((e.continuousAt hx).comp continuousAt_fst).prodMk ((e'.continuousAt hy).comp continuousAt_snd)
  have hrep' : ContinuousAt (fun q : L × M ↦ localRep₂ f e e' c (e q.1, e' q.2)) (x, y) :=
    (hrc.continuousAt ((hbox.isOpen_left.prod hbox.isOpen_right).mem_nhds ⟨hxU, hyV⟩)).comp
      hpair
  have hfc : f (x, y) ∈ c.source := by
    have := hbox.mapsTo _ hxU _ hyV
    rwa [e.left_inv hx, e'.left_inv hy] at this
  have hval : localRep₂ f e e' c (e x, e' y) = c (f (x, y)) := by
    simp only [localRep₂, e.left_inv hx, e'.left_inv hy]
  have hsymm := c.continuousAt_symm (hval ▸ c.map_source hfc : localRep₂ f e e' c (e x, e' y) ∈
    c.target)
  refine (ContinuousAt.comp (f := fun q : L × M ↦ localRep₂ f e e' c (e q.1, e' q.2))
    hsymm hrep').congr (Filter.eventually_of_mem hS fun q hq ↦ ?_)
  have hq1 : e.symm (e q.1) = q.1 := e.left_inv hq.1.1
  have hq2 : e'.symm (e' q.2) = q.2 := e'.left_inv hq.2.1
  have hqc : f q ∈ c.source := by
    have := hbox.mapsTo _ hq.1.2 _ hq.2.2
    rwa [hq1, hq2] at this
  simp only [Function.comp_apply, localRep₂, hq1, hq2]
  exact c.left_inv hqc

variable [MBManifold H M] [MBManifold F N]

/-- **Chart independence** (Glöckner–Neeb, Remark 3.5.26(a)): the local representatives of a
`C^{k,ℓ}` map on any box, in any charts, are `C^{k,ℓ}`. The model of the second factor is
assumed locally compact (this holds when `M` is compact and nonempty,
`locallyCompactSpace_of_compactSpace`; the model is then finite-dimensional); see
`ContDiffMBOn₂.comp_prodMap`. -/
theorem ContMDiffMB₂.contDiffMBOn₂ [LocallyCompactSpace H] {B : VaryingAtlas.{u, _, _} L}
    {k ℓ : ℕ} {f : L × M → N} (hf : ContMDiffMB₂ H F B k ℓ f) (i : B.ι)
    {e' : OpenPartialHomeomorph M H} (he' : e' ∈ atlas H M) {c : OpenPartialHomeomorph N F}
    (hc : c ∈ atlas F N) {U : Set (B.model i)} {V : Set H}
    (hbox : IsChartBox f (B.chart i) e' c U V) :
    ContDiffMBOn₂ k ℓ (localRep₂ f (B.chart i) e' c) U V := by
  set e := B.chart i
  refine ContDiffMBOn₂.of_local hbox.isOpen_left hbox.isOpen_right fun a ha b hb ↦ ?_
  obtain ⟨i₁, e₁', he₁', c₁, hc₁, U₁, V₁, hx, hy, hxU, hyV, hbox₁, hrep⟩ :=
    hf (e.symm a) (e'.symm b)
  set e₁ := B.chart i₁
  have hα := B.smoothMBOn_transition i i₁
  have hβ := smoothMBOn_transition he' he₁'
  have hγ := smoothMBOn_transition hc₁ hc
  set U₂ := (e.target ∩ e.symm ⁻¹' e₁.source) ∩ (e₁ ∘ e.symm) ⁻¹' U₁ ∩ U
  set V₂ := (e'.target ∩ e'.symm ⁻¹' e₁'.source) ∩ (e₁' ∘ e'.symm) ⁻¹' V₁ ∩ V
  have hU₂ : IsOpen U₂ := ((hα 0).continuousOn.isOpen_inter_preimage
    (e.isOpen_inter_preimage_symm e₁.open_source) hbox₁.isOpen_left).inter hbox.isOpen_left
  have hV₂ : IsOpen V₂ := ((hβ 0).continuousOn.isOpen_inter_preimage
    (e'.isOpen_inter_preimage_symm e₁'.open_source) hbox₁.isOpen_right).inter hbox.isOpen_right
  have hO := c₁.isOpen_inter_preimage_symm c.open_source
  have hfO : ∀ a' ∈ U₂, ∀ b' ∈ V₂,
      localRep₂ f e₁ e₁' c₁ ((e₁ ∘ e.symm) a', (e₁' ∘ e'.symm) b') ∈
        c₁.target ∩ c₁.symm ⁻¹' c.source := fun a' ha' b' hb' ↦ by
    have h1 : e₁.symm (e₁ (e.symm a')) = e.symm a' := e₁.left_inv ha'.1.1.2
    have h2 : e₁'.symm (e₁' (e'.symm b')) = e'.symm b' := e₁'.left_inv hb'.1.1.2
    have hs := hbox₁.mapsTo _ ha'.1.2 _ hb'.1.2
    simp only [Function.comp_apply, h1, h2] at hs
    simp only [localRep₂, Function.comp_apply, h1, h2]
    refine ⟨c₁.map_source hs, ?_⟩
    rw [mem_preimage, c₁.left_inv hs]
    exact hbox.mapsTo _ ha'.2 _ hb'.2
  have h := hrep.comp_prodMap hbox₁.isOpen_left hbox₁.isOpen_right hU₂ hV₂
    ((hα k).mono fun _ h ↦ h.1.1) ((hβ ℓ).mono fun _ h ↦ h.1.1) (fun _ h ↦ h.1.2)
    (fun _ h ↦ h.1.2) hO hγ hfO
  refine ⟨U₂, V₂, hU₂, hV₂, ⟨⟨⟨hbox.subset_left ha, hx⟩, ?_⟩, ha⟩,
    ⟨⟨⟨hbox.subset_right hb, hy⟩, ?_⟩, hb⟩, h.congr hU₂ hV₂ fun p hp ↦ ?_⟩
  · exact hxU
  · exact hyV
  · have h1 : e₁.symm (e₁ (e.symm p.1)) = e.symm p.1 := e₁.left_inv hp.1.1.1.2
    have h2 : e₁'.symm (e₁' (e'.symm p.2)) = e'.symm p.2 := e₁'.left_inv hp.2.1.1.2
    have hs : f (e.symm p.1, e'.symm p.2) ∈ c₁.source := by
      have := hbox₁.mapsTo _ hp.1.1.2 _ hp.2.1.2
      simp only [Function.comp_apply, h1, h2] at this
      exact this
    change c (c₁.symm (c₁ (f (e₁.symm (e₁ (e.symm p.1)), e₁'.symm (e₁' (e'.symm p.2)))))) =
      c (f (e.symm p.1, e'.symm p.2))
    rw [h1, h2, c₁.left_inv hs]

omit [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  [MBManifold H M] in
/-- **Partial maps of `C^{k,ℓ}` maps are `C^k`**: if `f : L × M → N` is `C^{k,ℓ}`, then
`x ↦ f(x, y)` is `C^k` for every `y ∈ M`. -/
theorem ContMDiffMB₂.contMDiffOn_left {B : VaryingAtlas.{u, _, _} L} {k ℓ : ℕ} {f : L × M → N}
    (hf : ContMDiffMB₂ H F B k ℓ f) (y : M) :
    B.ContMDiffOn (VaryingAtlas.ofChartedSpace F N) k (fun x ↦ f (x, y)) univ := by
  refine VaryingAtlas.contMDiffOn_of_local isOpen_univ
    (hf.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn fun x _ ↦ ?_
  obtain ⟨i, e', -, c, hc, U, V, hx, hy, hxU, hyV, hbox, hrep⟩ := hf x y
  have hey : e'.symm (e' y) = y := e'.left_inv hy
  refine ⟨i, ⟨c, hc⟩, U, hx, hbox.isOpen_left, hxU, fun a ha ↦ ⟨hbox.subset_left ha, mem_univ _,
    ?_⟩, ?_⟩
  · have := hbox.mapsTo a ha _ hyV
    rwa [hey] at this
  · change ContDiffMBOn k (c ∘ (fun x ↦ f (x, y)) ∘ (B.chart i).symm) U
    refine ContDiffMBOn.congr_of_isOpen hbox.isOpen_left (fun a _ ↦ ?_)
      (hrep.contDiffMBOn_left 0 (Nat.zero_le ℓ) (e' y) hyV Fin.elim0)
    change c (f ((B.chart i).symm a, e'.symm (e' y))) = c (f ((B.chart i).symm a, y))
    rw [hey]

end Manifolds

end LocallyConvex.Manifolds
