/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Uniform injectivity of maps with nearby derivatives

Let `f` be a map on a Banach space `E` whose derivative is continuous at `x₀` and invertible
there. Then there are `r > 0` and `ε > 0` such that every map `g` whose derivative stays within
`ε` of the derivative of `f` on the ball `B(x₀, r)` is injective on that ball, with invertible
derivative at each of its points. This is the analytic core of [GN26, Lemma 13.1.5], which
Glöckner–Neeb state for `E = ℝⁿ` and `f'(x₀) = id`.

## Main results

* `exists_injOn_of_fderiv_near`: the statement above.

## Implementation notes

The proof is Glöckner–Neeb's: by the mean value theorem, `g - A` is `c`-Lipschitz on the ball,
`A = f'(x₀)`, so `g` approximates `A` there (`ApproximatesLinearOn`) and is injective for
`c < ‖A⁻¹‖⁻¹`; the derivatives of `g` lie in a ball around `A` contained in the open set of
invertible operators (`ContinuousLinearEquiv.isOpen`).

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Metric
open scoped Topology NNReal

namespace LocallyConvex.Manifolds

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Uniform injectivity** ([GN26, Lemma 13.1.5]): if the derivative of `f` is continuous at
`x₀` and `f'(x₀) = A` is invertible, there are `r, ε > 0` such that, for `r' ≤ r`, every map `g`
with derivatives `g'(y)` on `B(x₀, r')` satisfying `‖g'(y) - f'(y)‖ < ε` is injective on
`B(x₀, r')`, and its derivatives there are invertible. -/
theorem exists_injOn_of_fderiv_near {f : E → E} {x₀ : E} (A : E ≃L[ℝ] E)
    (hA : fderiv ℝ f x₀ = A) (hfc : ContinuousAt (fderiv ℝ f) x₀) :
    ∃ r > 0, ∃ ε > 0, ∀ r' ≤ r, ∀ (g : E → E) (g' : E → E →L[ℝ] E),
      (∀ y ∈ ball x₀ r', HasFDerivAt g (g' y) y) →
      (∀ y ∈ ball x₀ r', ‖g' y - fderiv ℝ f y‖ < ε) →
      InjOn g (ball x₀ r') ∧ ∀ y ∈ ball x₀ r', g' y ∈ range ((↑) : (E ≃L[ℝ] E) → E →L[ℝ] E) := by
  -- a ball around `A` of invertible operators
  obtain ⟨δ, hδ, hδA⟩ := isOpen_iff.1 ContinuousLinearEquiv.isOpen (A : E →L[ℝ] E)
    (mem_range_self A)
  -- the Lipschitz constant `c`: below `δ`, and below `‖A⁻¹‖⁻¹` unless `E` is trivial
  obtain ⟨c, hc0, hcδ, hcN⟩ : ∃ c : ℝ≥0, 0 < c ∧ (c : ℝ) < δ ∧
      (Subsingleton E ∨ c < ‖(A.symm : E →L[ℝ] E)‖₊⁻¹) := by
    rcases subsingleton_or_nontrivial E with hE | hE
    · refine ⟨(δ / 2).toNNReal, Real.toNNReal_pos.2 (by positivity), ?_, Or.inl hE⟩
      rw [Real.coe_toNNReal _ (by positivity)]
      linarith
    · have hN : 0 < ‖(A.symm : E →L[ℝ] E)‖₊ := by
        rw [nnnorm_pos]
        intro h0
        obtain ⟨x, hx⟩ := exists_ne (0 : E)
        have : A.symm (A x) = 0 := by
          change (A.symm : E →L[ℝ] E) (A x) = 0
          rw [h0]
          rfl
        exact hx (by simpa using this)
      set c' : ℝ≥0 := min δ.toNNReal ‖(A.symm : E →L[ℝ] E)‖₊⁻¹
      have hc' : 0 < c' := lt_min (Real.toNNReal_pos.2 hδ) (inv_pos.2 hN)
      refine ⟨c' / 2, by positivity, ?_, Or.inr ?_⟩
      · have : c' / 2 < c' := NNReal.half_lt_self hc'.ne'
        refine (NNReal.coe_lt_coe.2 this).trans_le ?_
        calc (c' : ℝ) ≤ (δ.toNNReal : ℝ) := NNReal.coe_le_coe.2 (min_le_left _ _)
          _ = δ := Real.coe_toNNReal _ hδ.le
      · exact (NNReal.half_lt_self hc'.ne').trans_le (min_le_right _ _)
  -- `f'` stays within `c / 2` of `A` on a ball
  obtain ⟨r, hr, hrf⟩ := Metric.continuousAt_iff.1 hfc (c / 2) (by positivity)
  refine ⟨r, hr, c / 2, by positivity, fun r' hr' g g' hg hg' ↦ ?_⟩
  have hclose : ∀ y ∈ ball x₀ r', ‖g' y - A‖ < c := fun y hy ↦ by
    have h1 := hg' y hy
    have h2 : ‖fderiv ℝ f y - A‖ < c / 2 := by
      have := hrf (mem_ball.1 (ball_subset_ball hr' hy))
      rwa [dist_eq_norm, hA] at this
    calc ‖g' y - A‖ = ‖(g' y - fderiv ℝ f y) + (fderiv ℝ f y - A)‖ := by abel_nf
      _ ≤ ‖g' y - fderiv ℝ f y‖ + ‖fderiv ℝ f y - A‖ := norm_add_le _ _
      _ < c / 2 + c / 2 := add_lt_add h1 h2
      _ = c := add_halves _
  refine ⟨?_, fun y hy ↦ hδA ?_⟩
  · have hL : LipschitzOnWith c (g - ⇑(A : E →L[ℝ] E)) (ball x₀ r') :=
      (convex_ball x₀ r').lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
        (f' := fun y ↦ g' y - (A : E →L[ℝ] E))
        (fun y hy ↦ ((hg y hy).sub (A : E →L[ℝ] E).hasFDerivAt).hasFDerivWithinAt)
        fun y hy ↦ by
          rw [← NNReal.coe_le_coe, coe_nnnorm]
          exact (hclose y hy).le
    exact (ApproximatesLinearOn.approximatesLinearOn_iff_lipschitzOnWith.2 hL).injOn hcN
  · rw [mem_ball, dist_eq_norm]
    exact (hclose y hy).trans hcδ

end LocallyConvex.Manifolds
