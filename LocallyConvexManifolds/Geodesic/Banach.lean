/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.Connection.CovariantCurve
public import LocallyConvexAnalysis.Calculus.MBFrechet

/-!
# Geodesics on Banach manifolds: the geodesic equation in charts

On a manifold modeled on a **normed** space the geodesic equation of a connection can be written
with Fréchet derivatives: in a chart `i`, a curve `c = φᵢ ∘ α` is a geodesic when
`c' = c₁` and `c₁' = Γᵢ(c)(c₁, c₁)`. This file proves that the equation does not depend on the
chart (`geodesicEq_comp`): if `c` solves it in the chart `i`, then `τ ∘ c` solves it in the chart
`j`, `τ = φⱼ ∘ φᵢ⁻¹`. The computation is `(τ ∘ c)'' = D²τ(c', c') + Dτ(c'')`, combined with the
change of charts law of the symbols, `Γⱼ(τ y)(Dτ a, Dτ b) = Dτ Γᵢ(y)(a, b) + D²τ(a, b)`. We follow
[Lan99, Ch. IV and VIII] and [Lar26, Cap. 6].

## Main definitions

* `Connection.GeodesicEqAt`: the geodesic equation at a time, in a chart.
* `Connection.IsGeodesicOn`: geodesics on a set of times.

## Main results

* `geodesicEq_comp`: the geodesic equation does not depend on the chart.
* `Connection.geodesicEqAt_of_chart`: a curve that solves the geodesic equation at `t` in one chart
  solves it in every chart around `α t`.

## Implementation notes

The Michal–Bastiani derivatives of the change of charts law are first identified with Fréchet
derivatives (`dMB_eq_fderiv`, `dMB_dMB_eq_fderiv_fderiv`, in lc-analysis [LCA]).

## References

* [S. Lang, *Fundamentals of Differential Geometry*][Lan99]
* [G. Larotonda, *Estructuras geométricas para las variedades de Banach*][Lar26]
* [glaroton, *lc-analysis: Michal–Bastiani calculus on locally convex spaces*][LCA]
-/

@[expose] public section

open Set Filter
open scoped Topology ContDiff
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The geodesic equation does not depend on the chart.** Let `τ` be `C²` on the open set `T`,
and let the symbols `Γᵢ, Γⱼ` obey the change of charts law along `τ`. If `c` solves the geodesic
equation of `Γᵢ` near `t` (`c' = c₁`, `c₁'(t) = Γᵢ(c t)(c₁ t, c₁ t)`), then `τ ∘ c` solves the
geodesic equation of `Γⱼ` at `t`, with velocity `Dτ(c)(c₁)`. -/
theorem geodesicEq_comp {τ : E → E} {T : Set E} (hT : IsOpen T) (hτ : ContDiffOn ℝ 2 τ T)
    {Γi Γj : E → E → E → E}
    (htrans : ∀ y ∈ T, ∀ a b, Γj (τ y) (dMB τ (y, a)) (dMB τ (y, b)) =
      dMB τ (y, Γi y a b) + dMB (dMB τ) ((y, b), (a, 0)))
    {c c₁ : ℝ → E} {t : ℝ} (hcT : ∀ᶠ s in 𝓝 t, c s ∈ T)
    (hc : ∀ᶠ s in 𝓝 t, HasDerivAt c (c₁ s) s)
    (hc₁ : HasDerivAt c₁ (Γi (c t) (c₁ t) (c₁ t)) t) :
    (∀ᶠ s in 𝓝 t, HasDerivAt (τ ∘ c) (fderiv ℝ τ (c s) (c₁ s)) s) ∧
      HasDerivAt (fun s ↦ fderiv ℝ τ (c s) (c₁ s))
        (Γj (τ (c t)) (fderiv ℝ τ (c t) (c₁ t)) (fderiv ℝ τ (c t) (c₁ t))) t := by
  have hτ1 : ContDiffOn ℝ 1 τ T := hτ.of_le (by norm_num)
  have hDτ : ∀ y ∈ T, HasFDerivAt τ (fderiv ℝ τ y) y := fun y hy ↦
    ((hτ1.contDiffAt (hT.mem_nhds hy)).differentiableAt one_ne_zero).hasFDerivAt
  refine ⟨?_, ?_⟩
  · filter_upwards [hcT, hc] with s hs hcs
    exact (hDτ _ hs).comp_hasDerivAt s hcs
  · have htT : c t ∈ T := hcT.self_of_nhds
    have hct : HasDerivAt c (c₁ t) t := hc.self_of_nhds
    have hτy : ContDiffAt ℝ 2 τ (c t) := hτ.contDiffAt (hT.mem_nhds htT)
    have hD2 : HasFDerivAt (fderiv ℝ τ) (fderiv ℝ (fderiv ℝ τ) (c t)) (c t) :=
      ((hτy.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
    have hL : HasDerivAt (fun s ↦ fderiv ℝ τ (c s)) (fderiv ℝ (fderiv ℝ τ) (c t) (c₁ t)) t :=
      hD2.comp_hasDerivAt t hct
    have happ := hL.clm_apply hc₁
    convert happ using 1
    have h := htrans (c t) htT (c₁ t) (c₁ t)
    simp only [dMB_eq_fderiv hT hτ1 htT, dMB_dMB_eq_fderiv_fderiv hT hτ htT] at h
    rw [h, add_comm]

/-! ### Geodesics on intervals -/

section Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]
  (C : Connection E M)

/-- If the representative of `α` in the preferred chart at `α t` has derivative `v` at `t`, then
the velocity of `α` at `t` is `v`. -/
theorem velocity_eq_of_hasDerivAt {α : ℝ → M} {t : ℝ} {v : E}
    (h : HasDerivAt (chartAt E (α t) ∘ α) v t) : velocity E α t = ⟨α t, v⟩ := by
  have hd : dMB (chartAt E (α t) ∘ α) (t, 1) = v := by
    simpa using (h.hasFDerivAt.hasDirDerivAt (1 : ℝ)).dMB_eq
  unfold velocity
  rw [hd]

/-- The geodesic equation at `t`, read in the chart `j`: `c = φⱼ ∘ α` has a velocity `c₁` near
`t` and `c₁'(t) = Γⱼ(c t)(c₁ t, c₁ t)`. -/
def Connection.GeodesicEqAt (α : ℝ → M) (j : atlas E M) (t : ℝ) : Prop :=
  ∃ c₁ : ℝ → E, (∀ᶠ s in 𝓝 t, HasDerivAt (j.1 ∘ α) (c₁ s) s) ∧
    HasDerivAt c₁ (C.Γ j (j.1 (α t)) (c₁ t) (c₁ t)) t

/-- `α` is a **geodesic on the open set `I`**: it is continuous on `I` and satisfies the geodesic
equation, in the preferred chart, at every `t ∈ I`. By `Connection.geodesicEqAt_of_chart` it then
satisfies it in every chart around `α t`. -/
def Connection.IsGeodesicOn (α : ℝ → M) (I : Set ℝ) : Prop :=
  IsOpen I ∧ ContinuousOn α I ∧ ∀ t ∈ I, C.GeodesicEqAt α ⟨chartAt E (α t), chart_mem_atlas E _⟩ t

/-- **The geodesic equation in any chart.** If `α` is continuous at `t` and satisfies the
geodesic equation at `t` in the chart `i`, it satisfies it in every chart `j` around `α t`. -/
theorem Connection.geodesicEqAt_of_chart {α : ℝ → M} {t : ℝ} (hα : ContinuousAt α t)
    {i j : atlas E M} (hi : α t ∈ i.1.source) (hj : α t ∈ j.1.source)
    (h : C.GeodesicEqAt α i t) : C.GeodesicEqAt α j t := by
  obtain ⟨c₁, hc, hc₁⟩ := h
  set T := i.1.target ∩ i.1.symm ⁻¹' j.1.source
  have hT : IsOpen T := isOpen_transition_domain i j
  have hτ : ContDiffOn ℝ 2 (j.1 ∘ i.1.symm) T :=
    ((smoothMBOn_iff_contDiffOn hT).mp (smoothMBOn_transition' i j)).of_le (by simp)
  have hnear : ∀ᶠ s in 𝓝 t, α s ∈ i.1.source ∩ j.1.source :=
    hα.preimage_mem_nhds ((i.1.open_source.inter j.1.open_source).mem_nhds ⟨hi, hj⟩)
  have hcT : ∀ᶠ s in 𝓝 t, (i.1 ∘ α) s ∈ T := by
    filter_upwards [hnear] with s hs
    exact ⟨i.1.map_source hs.1, by simp [i.1.left_inv hs.1, hs.2]⟩
  have htrans : ∀ y ∈ T, ∀ a b, C.Γ j ((j.1 ∘ i.1.symm) y) (dMB (j.1 ∘ i.1.symm) (y, a))
      (dMB (j.1 ∘ i.1.symm) (y, b)) =
      dMB (j.1 ∘ i.1.symm) (y, C.Γ i y a b) + dMB (dMB (j.1 ∘ i.1.symm)) ((y, b), (a, 0)) :=
    fun y hy a b ↦ C.transition i j y hy a b
  obtain ⟨h1, h2⟩ := geodesicEq_comp hT hτ htrans hcT hc hc₁
  have heq : (j.1 ∘ i.1.symm) ∘ (i.1 ∘ α) =ᶠ[𝓝 t] j.1 ∘ α := by
    filter_upwards [hnear] with s hs
    simp [i.1.left_inv hs.1]
  refine ⟨fun s ↦ fderiv ℝ (j.1 ∘ i.1.symm) ((i.1 ∘ α) s) (c₁ s), ?_, ?_⟩
  · filter_upwards [h1, heq.eventually_nhds] with s hs hs'
    exact hs.congr_of_eventuallyEq (Filter.EventuallyEq.symm hs')
  · have hval : (j.1 ∘ i.1.symm) ((i.1 ∘ α) t) = j.1 (α t) := by simp [i.1.left_inv hi]
    rw [hval] at h2
    exact h2

end Manifold

end LocallyConvex.Manifolds
