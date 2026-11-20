/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.Manifold.Ckl

/-!
# Restriction of atlases with varying models to open subsets

An open subset `U` of a space `X` with an atlas with varying models `A` inherits an atlas: the
restrictions of the charts of `A` to `U` (`VaryingAtlas.restrict`). This is how an open subset
of a manifold of mappings, such as the group `Diff(K)` of diffeomorphisms of a compact manifold
`K` in `C^∞(K, K)`, becomes a manifold in its own right ([GN26, Proposition 13.1.10]).

## Main definitions

* `VaryingAtlas.restrict A U hU`: the restriction of `A` to the open set `U`, an atlas on the
  subtype `U`.

## Main results

* `VaryingAtlas.restrict_chart_apply`, `VaryingAtlas.restrict_chart_symm_apply`: the charts of
  the restriction.
* `ContMDiffMB₂.restrict`: restrictions of `C^{k,ℓ}` maps `X × M → N` to `U × M` are `C^{k,ℓ}`.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set TopologicalSpace
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe u

namespace VaryingAtlas

variable {X : Type*} [TopologicalSpace X]

/-- **The restriction of an atlas with varying models to an open subset** `U`: the charts are the
restrictions `φ_i|_U` (`OpenPartialHomeomorph.subtypeRestr`), indexed by pairs `(i, x)` with
`x ∈ U` (a point of `U` is needed to restrict a chart to a subtype). It is reducible, so that
instance search sees the models. -/
abbrev restrict (A : VaryingAtlas.{u, _, _} X) (U : Set X) (hU : IsOpen U) :
    VaryingAtlas.{u, _, _} U where
  ι := A.ι × U
  model p := A.model p.1
  chart p := (A.chart p.1).subtypeRestr (s := ⟨U, hU⟩) ⟨p.2⟩
  chartAt x := (A.chartAt x.1, x)
  mem_chartAt_source x := by
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact A.mem_chartAt_source x.1
  smoothMBOn_transition p q := by
    set e := A.chart p.1
    set e' := A.chart q.1
    set s := e.subtypeRestr (s := ⟨U, hU⟩) ⟨p.2⟩
    set s' := e'.subtypeRestr (s := ⟨U, hU⟩) ⟨q.2⟩
    have hsymm : ∀ a ∈ s.target, (s.symm a : X) = e.symm a := fun a ha ↦
      e.subtypeRestr_symm_apply ⟨p.2⟩ ha
    have hsub : s.target ∩ s.symm ⁻¹' s'.source ⊆ e.target ∩ e.symm ⁻¹' e'.source := by
      rintro a ⟨ha, ha'⟩
      refine ⟨ha.1, ?_⟩
      rw [mem_preimage, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage, hsymm a ha] at ha'
      exact ha'
    have heq : EqOn (e' ∘ e.symm) (s' ∘ s.symm) (s.target ∩ s.symm ⁻¹' s'.source) := by
      intro a ha
      change e' (e.symm a) = e' (s.symm a : X)
      rw [hsymm a ha.1]
    intro n
    exact ((A.smoothMBOn_transition p.1 q.1 n).mono hsub).congr_of_isOpen
      (s.isOpen_inter_preimage_symm s'.open_source) heq

variable (A : VaryingAtlas.{u, _, _} X) {U : Set X} (hU : IsOpen U)

@[simp]
theorem restrict_chart_apply (p : (A.restrict U hU).ι) (x : U) :
    (A.restrict U hU).chart p x = A.chart p.1 x :=
  rfl

theorem restrict_chart_symm_apply (p : (A.restrict U hU).ι) {a : (A.restrict U hU).model p}
    (ha : a ∈ ((A.restrict U hU).chart p).target) :
    (((A.restrict U hU).chart p).symm a : X) = (A.chart p.1).symm a :=
  (A.chart p.1).subtypeRestr_symm_apply ⟨p.2⟩ ha

theorem restrict_chart_source (p : (A.restrict U hU).ι) :
    ((A.restrict U hU).chart p).source = (↑) ⁻¹' (A.chart p.1).source :=
  OpenPartialHomeomorph.subtypeRestr_source _ _

theorem restrict_chart_target_subset (p : (A.restrict U hU).ι) :
    ((A.restrict U hU).chart p).target ⊆ (A.chart p.1).target := fun _ ha ↦ ha.1

end VaryingAtlas

section Ckl

variable {H F : Type u}
  [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [IsTopologicalAddGroup H]
  [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {X : Type*} [TopologicalSpace X]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N]

omit [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] in
/-- **Restrictions of `C^{k,ℓ}` maps** to open subsets of the first factor are `C^{k,ℓ}`. -/
theorem ContMDiffMB₂.restrict {B : VaryingAtlas.{u, _, _} X} {k ℓ : ℕ} {f : X × M → N}
    (hf : ContMDiffMB₂ H F B k ℓ f) {U : Set X} (hU : IsOpen U) :
    ContMDiffMB₂ H F (B.restrict U hU) k ℓ (fun p : U × M ↦ f (p.1, p.2)) := by
  intro x y
  obtain ⟨i, e', he', c, hc, V₁, V₂, hx, hy, hxV, hyV, hbox, hrep⟩ := hf x y
  set s := (B.restrict U hU).chart (i, x)
  have hsymm : ∀ a ∈ s.target, (s.symm a : X) = (B.chart i).symm a := fun a ha ↦
    B.restrict_chart_symm_apply hU (i, x) ha
  have hxs : x ∈ s.source := by
    rw [B.restrict_chart_source hU]
    exact hx
  refine ⟨(i, x), e', he', c, hc, V₁ ∩ s.target, V₂, hxs, hy, ⟨hxV, s.map_source hxs⟩, hyV,
    ⟨hbox.isOpen_left.inter s.open_target, hbox.isOpen_right, fun _ ha ↦ ha.2,
      hbox.subset_right, fun a ha b hb ↦ ?_⟩, ?_⟩
  · change f ((s.symm a : X), e'.symm b) ∈ c.source
    rw [hsymm a ha.2]
    exact hbox.mapsTo a ha.1 b hb
  · refine (hrep.mono inter_subset_left subset_rfl).congr
      (hbox.isOpen_left.inter s.open_target) hbox.isOpen_right fun q hq ↦ ?_
    change c (f ((B.chart i).symm q.1, e'.symm q.2)) = c (f ((s.symm q.1 : X), e'.symm q.2))
    rw [hsymm q.1 hq.1.2]

end Ckl

end LocallyConvex.Manifolds
