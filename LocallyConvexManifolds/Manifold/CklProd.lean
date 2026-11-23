/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.Manifold.Ckl
public import LocallyConvexManifolds.Manifold.Product
public import LocallyConvexAnalysis.Calculus.SmoothExponentialLaw

/-!
# `C^{k,ℓ}` maps and smooth maps on products

For manifolds `L` and `M` (with single models), a map `f : L × M → N` is smooth on the product
manifold if and only if it is `C^{k,ℓ}` for all `k, ℓ` ([GN26, Proposition 1.7.33(a), (b)] in
charts):
`C^{k+ℓ}` maps are `C^{k,ℓ}` (lc-analysis, `ContDiffMBOn.contDiffMBOn₂`), and `C^{k,k}` maps are
`C^k` (lc-analysis, `ContDiffMBOn₂.contDiffMBOn_prod`).

## Main results

* `ContMDiffMB.contMDiffMB₂`: a `C^{k+ℓ}` map on `L × M` is `C^{k,ℓ}`.
* `ContMDiffMB₂.contMDiffMB`: a `C^{k,k}` map is `C^k` on `L × M`.
* `smoothMBM_iff_contMDiffMB₂`: smooth maps on `L × M` are the maps that are `C^{k,ℓ}` for all
  `k, ℓ`.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Function TopologicalSpace
open scoped Topology
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe u

attribute [local instance] VaryingAtlas.addCommGroup VaryingAtlas.module
  VaryingAtlas.topologicalSpace VaryingAtlas.isTopologicalAddGroup VaryingAtlas.continuousSMul
  VaryingAtlas.locallyConvexSpace VaryingAtlas.t2Space

variable {G H F : Type u}
  [AddCommGroup G] [Module ℝ G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G]
  [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [IsTopologicalAddGroup H]
  [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {L : Type*} [TopologicalSpace L] [ChartedSpace G L] [MBManifold G L]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MBManifold H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N] [MBManifold F N]

omit [MBManifold H M] [MBManifold F N] in
/-- **`C^{k+ℓ}` maps on a product are `C^{k,ℓ}`.** -/
theorem ContMDiffMB.contMDiffMB₂ {k ℓ : ℕ} {f : L × M → N}
    (hf : ContMDiffMB (ModelProd G H) F (k + ℓ) f) :
    ContMDiffMB₂ H F (VaryingAtlas.ofChartedSpace G L) k ℓ f := by
  intro x y
  set e := chartAt G x
  set e' := chartAt H y
  set c := chartAt F (f (x, y))
  set D := chartDomain f univ (chartAt (ModelProd G H) (x, y)) c
  have hD : IsOpen D := isOpen_chartDomain isOpen_univ hf.1 _ _
  have hxy : (e x, e' y) ∈ D :=
    ⟨⟨e.map_source (mem_chart_source G x), e'.map_source (mem_chart_source H y)⟩, mem_univ _, by
      change f (e.symm (e x), e'.symm (e' y)) ∈ c.source
      rw [e.left_inv (mem_chart_source G x), e'.left_inv (mem_chart_source H y)]
      exact mem_chart_source F _⟩
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := isOpen_prod_iff.1 hD _ _ hxy
  have hrep : ContDiffMBOn (k + ℓ) (c ∘ f ∘ (chartAt (ModelProd G H) (x, y)).symm) D :=
    hf.2 (x, y) (mem_univ _)
  refine ⟨(VaryingAtlas.ofChartedSpace G L).chartAt x, e', chart_mem_atlas H y, c,
    chart_mem_atlas F _, U, V,
    mem_chart_source G x, mem_chart_source H y, hxU, hyV,
    ⟨hU, hV, fun a ha ↦ (hUV (show (a, e' y) ∈ U ×ˢ V from ⟨ha, hyV⟩)).1.1,
      fun b hb ↦ (hUV (show (e x, b) ∈ U ×ˢ V from ⟨hxU, hb⟩)).1.2,
      fun a ha b hb ↦ (hUV (show (a, b) ∈ U ×ˢ V from ⟨ha, hb⟩)).2.2⟩, ?_⟩
  exact (hrep.mono hUV).contDiffMBOn₂ hU hV

/-- **`C^{k,k}` maps on a product are `C^k`.** -/
theorem ContMDiffMB₂.contMDiffMB {k : ℕ} {f : L × M → N}
    (hf : ContMDiffMB₂ H F (VaryingAtlas.ofChartedSpace G L) k k f) :
    ContMDiffMB (ModelProd G H) F k f := by
  have hc : Continuous f := hf.continuous
  have h := (VaryingAtlas.contMDiffOn_ofChartedSpace_iff (G := ModelProd G H) (F := F)
    (M := L × M) (N := N) (k := k) (f := f) isOpen_univ).1
  refine h (VaryingAtlas.contMDiffOn_of_local isOpen_univ hc.continuousOn fun p _ ↦ ?_)
  obtain ⟨i, e', he', c, hc', U, V, hx, hy, hxU, hyV, hbox, hrep⟩ := hf p.1 p.2
  set e : OpenPartialHomeomorph L G := i.1
  have hprod : e.prod e' ∈ atlas (ModelProd G H) (L × M) := ⟨e, i.2, e', he', rfl⟩
  refine ⟨show (VaryingAtlas.ofChartedSpace (ModelProd G H) (L × M)).ι from ⟨e.prod e', hprod⟩,
    show (VaryingAtlas.ofChartedSpace F N).ι from ⟨c, hc'⟩, U ×ˢ V, ⟨hx, hy⟩,
    hbox.isOpen_left.prod hbox.isOpen_right,
    ⟨hxU, hyV⟩, fun ab hab ↦ ⟨⟨hbox.subset_left hab.1, hbox.subset_right hab.2⟩, mem_univ _,
      hbox.mapsTo _ hab.1 _ hab.2⟩, ?_⟩
  exact hrep.contDiffMBOn_prod hbox.isOpen_left hbox.isOpen_right

/-- **Smooth maps on a product are the maps that are `C^{k,ℓ}` for all `k, ℓ`.** -/
theorem smoothMBM_iff_contMDiffMB₂ {f : L × M → N} :
    SmoothMBM (ModelProd G H) F f ↔
      ∀ k ℓ, ContMDiffMB₂ H F (VaryingAtlas.ofChartedSpace G L) k ℓ f :=
  ⟨fun hf k ℓ ↦ (hf (k + ℓ)).contMDiffMB₂, fun hf k ↦ (hf k k).contMDiffMB⟩

end LocallyConvex.Manifolds
