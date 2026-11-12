/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.MappingSpace.CkSuperposition
public import LocallyConvexManifolds.MappingSpace.Basic

/-!
# Compact manifolds have finite-dimensional models

The superposition operators on spaces of `C^r` maps and the restrictions to covers
(`ContDiffMBMap.contDiffMBOn_compLeftOn`, `ContDiffMBMap.isClosed_range_restrictCover`,
`isClosed_range_restrictCompacts`), first proved here, now live in lc-analysis
(`LocallyConvexAnalysis.MappingSpace.CkSuperposition`); this file re-exports them for the manifolds
of `C^ℓ` maps (`LocallyConvexManifolds.MappingSpace.Ck`) and keeps the facts about compact
manifolds.

## Main results

* `locallyCompactSpace_of_compactSpace`: a nonempty compact manifold has a locally compact
  model space;
* `finiteDimensional_of_compactSpace`: hence (Riesz) a finite-dimensional one.
-/

@[expose] public section

open Set Filter Function TopologicalSpace
open scoped Topology
open LocallyConvex.Analysis

noncomputable section

universe u

namespace LocallyConvex.Manifolds

/-! ### Compact manifolds have finite-dimensional models -/

section CompactModel

variable {H : Type u} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [IsTopologicalAddGroup H]
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] [T2Space M] [Nonempty M]

include M in
omit [Module ℝ H] in
/-- **A nonempty compact manifold has a locally compact model space**: a chart sends a compact
neighborhood of a point onto a compact neighborhood in the model, and a topological group with a
compact neighborhood is locally compact. This is the local compactness used, through the
exponential law (uncurrying), in the theory of the manifolds of mappings `C^ℓ(M, N)`. -/
theorem locallyCompactSpace_of_compactSpace : LocallyCompactSpace H := by
  obtain ⟨x⟩ := ‹Nonempty M›
  set e := chartAt H x
  obtain ⟨K, hKn, hKs, hKc⟩ :=
    local_compact_nhds (e.open_source.mem_nhds (mem_chart_source H x))
  exact (hKc.image_of_continuousOn (e.continuousOn.mono hKs))
    |>.locallyCompactSpace_of_mem_nhds_of_addGroup (e.image_mem_nhds (mem_chart_source H x) hKn)

include M in
/-- **A nonempty compact manifold is finite-dimensional**: its model is locally compact, hence
finite-dimensional by Riesz's theorem (`FiniteDimensional.of_locallyCompactSpace`). So `M` is
modeled on some `ℝⁿ`; in the manifolds of mappings `C^ℓ(M, N)`, only the target `N` may be
infinite-dimensional. -/
theorem finiteDimensional_of_compactSpace [ContinuousSMul ℝ H] [T2Space H] :
    FiniteDimensional ℝ H :=
  have := locallyCompactSpace_of_compactSpace (H := H) M
  FiniteDimensional.of_locallyCompactSpace ℝ

end CompactModel

end LocallyConvex.Manifolds
