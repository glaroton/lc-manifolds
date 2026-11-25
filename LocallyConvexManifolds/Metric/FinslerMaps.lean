/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.Metric.FinslerQuotient

/-!
# Lipschitz maps between Finsler manifolds

Let `f : M → N` be a `C¹` map between manifolds with Finsler length structures `μ` and `μ'`. If
the differential of `f` is bounded, `μ'(T f v) ≤ C μ(v)` for every tangent vector `v`, then `f`
shortens lengths and distances by the factor `C`. This is the argument of [Lar19, Prop. 2.10(3)]
for left translations, written for an arbitrary map.

## Main results

* `IsCkCurve.comp`: a `C^k` map takes `C^k` curves to `C^k` curves.
* `FinslerLengthStructure.length_comp_le`: `L'(f ∘ γ) ≤ C L(γ)`.
* `FinslerLengthStructure.Reach.map`: chains of arcs are mapped to chains, with lengths
  multiplied by at most `C`.
* `FinslerLengthStructure.dist_map_le`: `d'(f x, f y) ≤ C d(x, y)` for `C > 0`.
* `FinslerLengthStructure.dist_map_le_of_le`: the case `C = 1`, maps that do not increase the
  Finsler seminorms.

## References

* [G. Larotonda, *The metric geometry of infinite dimensional Lie groups and their homogeneous
  spaces*][Lar19]
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology ENNReal
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe u

variable {E F : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N] [MBManifold F N]

/-- **A `C^k` map takes `C^k` curves to `C^k` curves.** Near each time `t`, the local
representative of `f ∘ γ` in a chart `j` of `N` is `(j ∘ f ∘ c⁻¹) ∘ (c ∘ γ)`, where `c` is the
preferred chart at `γ t`. -/
theorem IsCkCurve.comp {k : ℕ} {f : M → N} (hf : ContMDiffMB E F k f) {γ : ℝ → M}
    (hγ : IsCkCurve E k γ) : IsCkCurve F k (f ∘ γ) := by
  have hfc : Continuous f := continuousOn_univ.mp hf.1
  refine ⟨hfc.comp hγ.1, fun j ↦ ?_⟩
  have hU : IsOpen ((f ∘ γ) ⁻¹' j.1.source) := j.1.open_source.preimage (hfc.comp hγ.1)
  refine ContDiffMBOn.of_local hU fun t ht ↦ ?_
  set c := chartAt E (γ t)
  set O := γ ⁻¹' (c.source ∩ f ⁻¹' j.1.source)
  have hO : IsOpen O := (c.open_source.inter (j.1.open_source.preimage hfc)).preimage hγ.1
  refine ⟨O, hO, ⟨mem_chart_source E _, ht⟩, ?_⟩
  have hD : IsOpen (chartDomain f univ c j.1) := isOpen_chartDomain isOpen_univ hf.1 c j.1
  have hh : ContDiffMBOn k (j.1 ∘ f ∘ c.symm) (chartDomain f univ c j.1) :=
    ContMDiffMBOn.contDiffMBOn_chart isOpen_univ hf (chart_mem_atlas E _) j.2
  have hcγ : ContDiffMBOn k (c ∘ γ) O :=
    (hγ.2 ⟨c, chart_mem_atlas E _⟩).mono fun s hs ↦ hs.1
  have hmaps : MapsTo (c ∘ γ) O (chartDomain f univ c j.1) := fun s hs ↦
    ⟨c.map_source hs.1, by simp [c.left_inv hs.1, hs.2]⟩
  have hcomp : ContDiffMBOn k ((j.1 ∘ f ∘ c.symm) ∘ (c ∘ γ)) O :=
    ContDiffMBOn.comp hO hD hh hcγ hmaps
  have hUO : IsOpen ((f ∘ γ) ⁻¹' j.1.source ∩ O) := hU.inter hO
  refine ContDiffMBOn.congr_of_isOpen hUO (fun s hs ↦ ?_)
    (hcomp.mono inter_subset_right)
  simp [c.left_inv hs.2.1]

namespace FinslerLengthStructure

variable (μ : FinslerLengthStructure E M) (μ' : FinslerLengthStructure F N)
  {f : M → N} {C : ℝ}

/-- **A map with bounded differential shortens lengths by its bound**: if
`μ'(T f v) ≤ C μ(v)` for every tangent vector, then `L'(f ∘ γ) ≤ C L(γ)`. -/
theorem length_comp_le (hf : ContMDiffMB E F 1 f)
    (hC : ∀ p : TangentBundle E M, μ'.toFun (tangentMap E F f p) ≤ C * μ.toFun p)
    {γ : ℝ → M} (hγ : IsCkCurve E 1 γ) {a b : ℝ} (hab : a ≤ b) :
    μ'.length (f ∘ γ) a b ≤ C * μ.length γ a b := by
  have hfγ : IsCkCurve F 1 (f ∘ γ) := hγ.comp hf
  unfold length
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hab
    ((μ'.continuous_velocity hfγ).intervalIntegrable _ _)
    ((continuous_const.mul (μ.continuous_velocity hγ)).intervalIntegrable _ _) fun t _ ↦ ?_
  rw [← tangentMap_velocity hf hγ t]
  exact hC _

/-- **Lengths are preserved by maps that preserve the Finsler seminorms.** -/
theorem length_comp_eq (hf : ContMDiffMB E F 1 f)
    (hC : ∀ p : TangentBundle E M, μ'.toFun (tangentMap E F f p) = μ.toFun p)
    {γ : ℝ → M} (hγ : IsCkCurve E 1 γ) (a b : ℝ) :
    μ'.length (f ∘ γ) a b = μ.length γ a b := by
  unfold length
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  rw [← tangentMap_velocity hf hγ t]
  exact hC _

variable {μ μ'} in
/-- **Chains of arcs are mapped to chains of arcs**, with lengths multiplied by at most `C`. -/
theorem Reach.map (hf : ContMDiffMB E F 1 f)
    (hC : ∀ p : TangentBundle E M, μ'.toFun (tangentMap E F f p) ≤ C * μ.toFun p)
    {x y : M} {L : ℝ} (h : μ.Reach x y L) :
    ∃ L', L' ≤ C * L ∧ μ'.Reach (f x) (f y) L' := by
  induction h with
  | refl x => exact ⟨0, by simp, Reach.refl _⟩
  | @cons γ a b y L hγ hab _ ih =>
    obtain ⟨L', hL', h'⟩ := ih
    refine ⟨μ'.length (f ∘ γ) a b + L', ?_, Reach.cons (hγ.comp hf) hab h'⟩
    rw [mul_add]
    exact add_le_add (length_comp_le μ μ' hf hC hγ hab) hL'

/-- **A map with differential bounded by `C > 0` is `C`-Lipschitz for the Finsler distances**:
`d'(f x, f y) ≤ C d(x, y)` ([Lar19, Prop. 2.10(3)], for an arbitrary map). -/
theorem dist_map_le (hf : ContMDiffMB E F 1 f) (hC0 : 0 < C)
    (hC : ∀ p : TangentBundle E M, μ'.toFun (tangentMap E F f p) ≤ C * μ.toFun p) (x y : M) :
    μ'.dist (f x) (f y) ≤ ENNReal.ofReal C * μ.dist x y := by
  change _ ≤ ENNReal.ofReal C * ⨅ L : {L : ℝ // μ.Reach x y L}, ENNReal.ofReal L.1
  rw [ENNReal.mul_iInf_of_ne (by simpa using hC0) ENNReal.ofReal_ne_top]
  refine le_iInf fun L ↦ ?_
  obtain ⟨L', hL', h'⟩ := L.2.map hf hC
  calc μ'.dist (f x) (f y) ≤ ENNReal.ofReal L' := μ'.dist_le_of_reach h'
    _ ≤ ENNReal.ofReal (C * L.1) := ENNReal.ofReal_le_ofReal hL'
    _ = ENNReal.ofReal C * ENNReal.ofReal L.1 := ENNReal.ofReal_mul hC0.le

/-- **A map that does not increase the Finsler seminorms does not increase distances.** -/
theorem dist_map_le_of_le (hf : ContMDiffMB E F 1 f)
    (hC : ∀ p : TangentBundle E M, μ'.toFun (tangentMap E F f p) ≤ μ.toFun p) (x y : M) :
    μ'.dist (f x) (f y) ≤ μ.dist x y := by
  simpa using μ.dist_map_le μ' hf one_pos (fun p ↦ by simpa using hC p) x y

end FinslerLengthStructure

end LocallyConvex.Manifolds
