/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.Manifold.VaryingAtlas

/-!
# Products of atlases with varying models

For atlases with varying models `A` on `X` and `B` on `Y`, the charts `φ_i × ψ_j` form an atlas
with varying models on `X × Y`, modeled on the products `E_i × F_j` (`VaryingAtlas.prod`). For
manifolds of mappings this is the manifold structure on products such as
`C^{ℓ+k}(L, M) × C^ℓ(K, L)`, the domain of the composition map ([GN26, Proposition 13.1.2]).

## Main definitions

* `VaryingAtlas.prod A B`: the product atlas.

## Main results

* `VaryingAtlas.prod_chart_apply`, `VaryingAtlas.prod_chart_symm_apply`,
  `VaryingAtlas.prod_chart_source`, `VaryingAtlas.prod_chart_target`: the charts of the product.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe u

namespace VaryingAtlas

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **The product of two atlases with varying models**: the charts of `X × Y` are the products
`φ_i × ψ_j` of charts of `A` and `B`, modeled on `E_i × F_j`; the transition maps are products of
transition maps, hence smooth. It is reducible, so that instance search sees the models
`E_i × F_j` and their structure through `VaryingAtlas.topologicalSpace`, .... -/
abbrev prod (A : VaryingAtlas.{u, _, _} X) (B : VaryingAtlas.{u, _, _} Y) :
    VaryingAtlas.{u, _, _} (X × Y) where
  ι := A.ι × B.ι
  model p := A.model p.1 × B.model p.2
  chart p := (A.chart p.1).prod (B.chart p.2)
  chartAt x := (A.chartAt x.1, B.chartAt x.2)
  mem_chartAt_source x := ⟨A.mem_chartAt_source x.1, B.mem_chartAt_source x.2⟩
  smoothMBOn_transition p q := by
    have h := SmoothMBOn.prodMap
      ((A.chart p.1).isOpen_inter_preimage_symm (A.chart q.1).open_source)
      ((B.chart p.2).isOpen_inter_preimage_symm (B.chart q.2).open_source)
      (A.smoothMBOn_transition p.1 q.1) (B.smoothMBOn_transition p.2 q.2)
    have hset : ((A.chart p.1).prod (B.chart p.2)).target ∩
        ((A.chart p.1).prod (B.chart p.2)).symm ⁻¹' ((A.chart q.1).prod (B.chart q.2)).source =
        ((A.chart p.1).target ∩ (A.chart p.1).symm ⁻¹' (A.chart q.1).source) ×ˢ
          ((B.chart p.2).target ∩ (B.chart p.2).symm ⁻¹' (B.chart q.2).source) := by
      ext r
      simp only [OpenPartialHomeomorph.prod_target, OpenPartialHomeomorph.prod_symm,
        OpenPartialHomeomorph.prod_source, mem_inter_iff, mem_prod, mem_preimage,
        OpenPartialHomeomorph.prod_apply]
      tauto
    rw [hset]
    exact h

variable (A : VaryingAtlas.{u, _, _} X) (B : VaryingAtlas.{u, _, _} Y)

@[simp]
theorem prod_chart_apply (p : (A.prod B).ι) (x : X × Y) :
    (A.prod B).chart p x = (A.chart p.1 x.1, B.chart p.2 x.2) :=
  rfl

@[simp]
theorem prod_chart_symm_apply (p : (A.prod B).ι) (a : (A.prod B).model p) :
    ((A.prod B).chart p).symm a = ((A.chart p.1).symm a.1, (B.chart p.2).symm a.2) :=
  rfl

@[simp]
theorem prod_chart_source (p : (A.prod B).ι) :
    ((A.prod B).chart p).source = (A.chart p.1).source ×ˢ (B.chart p.2).source :=
  rfl

@[simp]
theorem prod_chart_target (p : (A.prod B).ι) :
    ((A.prod B).chart p).target = (A.chart p.1).target ×ˢ (B.chart p.2).target :=
  rfl

end VaryingAtlas

end LocallyConvex.Manifolds
