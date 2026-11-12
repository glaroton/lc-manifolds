/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.Flow.Maximal

/-!
# A completeness criterion for vector fields on Banach manifolds

Let `X` be a smooth vector field on a Hausdorff manifold `M` modeled on a Banach space `E`.
Lang [Lan99, Ch. IV, §2, Proposition 2.5, p. 92] proves that `X` is **complete**, i.e. its
maximal flow is defined on all of `ℝ × M`, if there are `a > 0` and `K > 0` such that every point
`x` admits a chart `(U, φ)` at `x` with `φ(U) ⊇ B(φ x, a)` in which the local representative `f`
of `X` and its derivative `f'` are bounded by `K`.

## Main results

* `SmoothVectorField.not_mapClusterPt_flow_of_notMem`: a two-sided form of the escape lemma: if
  `t ∉ J_x`, the maximal curve `s ↦ Fl(s, x)` has no cluster point as `s → t` within `J_x`.
* `SmoothVectorField.Ioo_subset_maxInterval_of_norm_rep_le` (**uniform existence time**): if
  `B(φ x, a) ⊆ φ(U)` and `‖f‖ ≤ K` on `B(φ x, a)`, then `J_x ⊇ (-a / (K + 1), a / (K + 1))`.
* `SmoothVectorField.flowDomain_eq_univ_of_forall_norm_rep_le` ([Lan99, Proposition IV.2.5]):
  under Lang's hypotheses, without the bound on `f'`, the maximal flow is global.

## Implementation notes

* **Hypotheses.** We only bound the local representative on the ball `B(φ x, a)` (Lang bounds
  it on the whole chart), and we do not bound its derivative. Lang derives the uniform existence
  time from his Proposition IV.1.1, the local existence theorem with explicit constants, whose
  proof by the contraction principle uses a Lipschitz constant, hence the bound on `f'`. We argue
  instead with the maximal flow: as long as the maximal curve stays in the ball, its
  representative is `K`-Lipschitz, hence Cauchy when time approaches a finite end of `J_x`
  (here the completeness of `E` is used); its limit lies in the closed ball of radius
  `K a / (K + 1) < a`, so the curve has a cluster point in `M`, which the escape lemma forbids.
  We do not claim this argument is new.
* **Infinite-dimensional subtlety.** In finite dimensions a vector field with compact support is
  complete by the escape lemma [Lan99, Corollary IV.2.4]. On Banach manifolds compact sets have
  empty interior, so the escape lemma gives no such criterion, and uniform bounds in charts of a
  fixed size play the role of compactness. The uniform radius `a` cannot be dropped: the
  constant vector field `1` on the open interval `(0, 1)` is bounded, but not complete.
* As for the maximal flow, `E` is a Banach space (`[CompleteSpace E]`) and `M` is Hausdorff.

## References

* [S. Lang, *Fundamentals of Differential Geometry*][Lan99]
-/

@[expose] public section

open Set Filter Function Metric
open LocallyConvex.Analysis
open scoped Topology NNReal

noncomputable section

namespace LocallyConvex.Manifolds

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

namespace SmoothVectorField

variable {X : SmoothVectorField E M} [CompleteSpace E] [T2Space M]

/-- **Escape lemma, two-sided form.** If `t ∉ J_x`, the maximal curve `s ↦ Fl(s, x)` has no cluster
point as `s → t` within `J_x` (compare [Lan99, Theorem IV.2.3]): a flow box around a cluster point
would continue the curve beyond `t`. -/
theorem not_mapClusterPt_flow_of_notMem {x : M} {t : ℝ} (ht : t ∉ X.maxInterval x) (y : M) :
    ¬ MapClusterPt y (𝓝[X.maxInterval x] t) (fun s ↦ X.flow (s, x)) := by
  intro hy
  set B := X.flowBox y
  have hev : ∀ᶠ s in 𝓝[X.maxInterval x] t,
      s ∈ X.maxInterval x ∧ s ∈ Ioo (t - B.ε) (t + B.ε) :=
    (eventually_mem_nhdsWithin).and (mem_nhdsWithin_of_mem_nhds
      (Ioo_mem_nhds (by linarith [B.ε_pos]) (by linarith [B.ε_pos])))
  obtain ⟨s, hsV, hsJ, hs⟩ :=
    ((hy.frequently (B.isOpen.mem_nhds B.mem)).and_eventually hev).exists
  have h := (B.flow_add (s := t - s) hsJ hsV ⟨by linarith [hs.2], by linarith [hs.1]⟩).1
  rw [sub_add_cancel] at h
  exact ht h

/-- **Uniform existence time.** Let `(U, φ)` be a chart at `x` with `B(φ x, a) ⊆ φ(U)` such that
the local representative of `X` is bounded by `K` on `B(φ x, a)`. Then the maximal interval of
`x` contains `(-a / (K + 1), a / (K + 1))`, and the maximal curve stays in the ball meanwhile. -/
theorem Ioo_subset_maxInterval_of_norm_rep_le {a K : ℝ} (ha : 0 < a) {x : M} (i : atlas E M)
    (hx : x ∈ i.1.source) (hball : ball (i.1 x) a ⊆ i.1.target)
    (hK : ∀ y ∈ ball (i.1 x) a, ‖X.rep i y‖ ≤ K) :
    Ioo (-(a / (K + 1))) (a / (K + 1)) ⊆ X.maxInterval x := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK _ (mem_ball_self ha))
  set δ := a / (K + 1) with hδ_def
  have hδ : 0 < δ := by positivity
  have hKδ : K * δ < a := by
    rw [hδ_def, mul_div_assoc', div_lt_iff₀ (by linarith)]
    nlinarith
  set J := X.maxInterval x
  set c : ℝ → M := fun s ↦ X.flow (s, x)
  set D : Set ℝ := Ioo (-δ) δ
  have hcJ : ContinuousOn c J := fun s hs ↦ ((X.isIntegralCurveOn_flow x) s hs).1.continuousWithinAt
  set S : Set ℝ := D ∩ (J ∩ c ⁻¹' (i.1.source ∩ i.1 ⁻¹' ball (i.1 x) a))
  have hS : IsOpen S := isOpen_Ioo.inter
    (hcJ.isOpen_inter_preimage (X.isOpen_maxInterval x) (i.1.isOpen_inter_preimage isOpen_ball))
  have hc0 : c 0 = x := X.flow_zero x
  have h0D : (0 : ℝ) ∈ D := ⟨neg_lt_zero.2 hδ, hδ⟩
  have h0S : (0 : ℝ) ∈ S :=
    ⟨h0D, X.zero_mem_maxInterval x, by rw [hc0]; exact hx,
      by rw [mem_preimage, hc0]; exact mem_ball_self ha⟩
  set I := connectedComponentIn S 0
  have hIo : IsOpen I := hS.connectedComponentIn
  have hIS : I ⊆ S := connectedComponentIn_subset S 0
  have h0I : (0 : ℝ) ∈ I := mem_connectedComponentIn h0S
  have hIconv : Convex ℝ I :=
    (isPreconnected_iff_ordConnected.1 isPreconnected_connectedComponentIn).convex
  -- the representative `γ = φ ∘ c` of the curve is `K`-Lipschitz on `I`
  set γ : ℝ → E := i.1 ∘ c
  have hd : ∀ s ∈ I, HasDerivWithinAt γ (X.rep i (i.1 (c s))) I s := fun s hs ↦
    (((X.isIntegralCurveOn_flow x) s (hIS hs).2.1).2 i (hIS hs).2.2.1).hasDerivWithinAt
  have hb : ∀ s ∈ I, ‖X.rep i (i.1 (c s))‖ ≤ K := fun s hs ↦ hK _ (hIS hs).2.2.2
  have hLip : LipschitzOnWith K.toNNReal γ I :=
    hIconv.lipschitzOnWith_of_nnnorm_hasDerivWithin_le hd fun s hs ↦ by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hK0]
      exact hb s hs
  have hγ0 : γ 0 = i.1 x := by simp [γ, hc0]
  have hγI : ∀ s ∈ I, γ s ∈ closedBall (i.1 x) (K * δ) := fun s hs ↦ by
    have h := hIconv.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb h0I hs
    rw [hγ0, sub_zero, Real.norm_eq_abs] at h
    rw [mem_closedBall, dist_eq_norm]
    exact h.trans (mul_le_mul_of_nonneg_left (abs_lt.2 (hIS hs).1).le hK0)
  -- the closure step
  refine (isPreconnected_Ioo.subset_of_closure_inter_subset hIo ⟨0, h0D, h0I⟩ ?_).trans
    (hIS.trans fun s hs ↦ hs.2.1)
  rintro t ⟨htc, htD⟩
  have : (𝓝[I] t).NeBot := mem_closure_iff_nhdsWithin_neBot.1 htc
  have hcau : Cauchy (map γ (𝓝[I] t)) :=
    (cauchy_nhds.mono nhdsWithin_le_nhds).map_of_le hLip.uniformContinuousOn
      (le_principal_iff.2 self_mem_nhdsWithin)
  obtain ⟨z, hz⟩ := cauchy_map_iff_exists_tendsto.1 hcau
  have hzb : z ∈ closedBall (i.1 x) (K * δ) :=
    isClosed_closedBall.mem_of_tendsto hz (mem_of_superset self_mem_nhdsWithin hγI)
  have hzT : z ∈ i.1.target := hball (closedBall_subset_ball hKδ hzb)
  have hcz : Tendsto c (𝓝[I] t) (𝓝 (i.1.symm z)) := by
    refine ((i.1.continuousAt_symm hzT).tendsto.comp hz).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact i.1.left_inv (hIS hs).2.2.1
  have htJ : t ∈ J := by
    by_contra htJ
    exact X.not_mapClusterPt_flow_of_notMem htJ (i.1.symm z)
      (hcz.mapClusterPt.mono (nhdsWithin_mono _ fun s hs ↦ (hIS hs).2.1))
  have hct : c t = i.1.symm z :=
    tendsto_nhds_unique ((((X.isIntegralCurveOn_flow x) t htJ).1).mono_left nhdsWithin_le_nhds)
      hcz
  have htS : t ∈ S := by
    refine ⟨htD, htJ, ?_, ?_⟩
    · rw [hct]; exact i.1.map_target hzT
    · rw [mem_preimage, hct, i.1.right_inv hzT]
      exact closedBall_subset_ball hKδ hzb
  obtain ⟨ε, hε, hεS⟩ := Metric.isOpen_iff.1 hS t htS
  have hne : (I ∩ ball t ε).Nonempty := by
    obtain ⟨s, hs1, hs2⟩ := mem_closure_iff.1 htc _ isOpen_ball (mem_ball_self hε)
    exact ⟨s, hs2, hs1⟩
  have hU : IsPreconnected (I ∪ ball t ε) :=
    isPreconnected_connectedComponentIn.union' hne (convex_ball t ε).isPreconnected
  exact hU.subset_connectedComponentIn (Or.inl h0I) (union_subset hIS hεS)
    (Or.inr (mem_ball_self hε))

/-- **A completeness criterion for vector fields** [Lan99, Proposition IV.2.5, p. 92]. Let `X` be a
smooth vector field on a Hausdorff manifold modeled on a Banach space, and `a > 0`, `K` such that
every point `x` admits a chart `φ` at `x` whose target contains the ball `B(φ x, a)`, on which the
local representative of `X` is bounded by `K`. Then the maximal flow of `X` is defined on all of
`ℝ × M`. Unlike Lang, we bound neither the derivative of the local representative, nor the local
representative outside the ball. -/
theorem flowDomain_eq_univ_of_forall_norm_rep_le {a K : ℝ} (ha : 0 < a)
    (h : ∀ x : M, ∃ i : atlas E M, x ∈ i.1.source ∧ ball (i.1 x) a ⊆ i.1.target ∧
      ∀ y ∈ ball (i.1 x) a, ‖X.rep i y‖ ≤ K) :
    X.flowDomain = univ := by
  set K' := max K 0
  set δ := a / (K' + 1)
  have hδ : 0 < δ := by positivity
  have h1 : ∀ x : M, Ioo (-δ) δ ⊆ X.maxInterval x := fun x ↦ by
    obtain ⟨i, hx, hball, hK⟩ := h x
    exact Ioo_subset_maxInterval_of_norm_rep_le ha i hx hball fun y hy ↦
      (hK y hy).trans (le_max_left _ _)
  have hn : ∀ n : ℕ, ∀ x : M, Ioo (-((n + 1) * δ)) ((n + 1) * δ) ⊆ X.maxInterval x := by
    intro n
    induction n with
    | zero => intro x; simpa using h1 x
    | succ n ih =>
      intro x t ht
      have hn1 : (0 : ℝ) < n + 2 := by positivity
      set t₂ := t / (n + 2)
      set t₁ := t * ((n + 1) / (n + 2))
      have hsum : t₂ + t₁ = t := by
        simp only [t₁, t₂]; field_simp; ring
      have ht' : -((n + 2) * δ) < t ∧ t < (n + 2) * δ := by
        obtain ⟨h₁, h₂⟩ := ht; push_cast at h₁ h₂; constructor <;> linarith
      have ht₁ : t₁ ∈ X.maxInterval x := by
        refine ih x ⟨?_, ?_⟩
        · simp only [t₁, mul_div_assoc']
          rw [lt_div_iff₀ hn1]; nlinarith [ht'.1]
        · simp only [t₁, mul_div_assoc']
          rw [div_lt_iff₀ hn1]; nlinarith [ht'.2]
      have ht₂ : t₂ ∈ X.maxInterval (X.flow (t₁, x)) := by
        refine h1 _ ⟨?_, ?_⟩
        · rw [lt_div_iff₀ hn1]; linarith [ht'.1]
        · rw [div_lt_iff₀ hn1]; linarith [ht'.2]
      have := X.add_mem_flowDomain (s := t₂) (t := t₁) ht₁ ht₂
      rwa [hsum] at this
  refine eq_univ_of_forall fun p ↦ ?_
  obtain ⟨n, hn'⟩ := exists_nat_gt (|p.1| / δ)
  rw [div_lt_iff₀ hδ] at hn'
  refine hn n p.2 (abs_lt.1 ?_)
  nlinarith [abs_nonneg p.1]

/-- Under the hypotheses of `flowDomain_eq_univ_of_forall_norm_rep_le`, every maximal integral
curve is defined on all of `ℝ`. -/
theorem maxInterval_eq_univ_of_forall_norm_rep_le {a K : ℝ} (ha : 0 < a)
    (h : ∀ x : M, ∃ i : atlas E M, x ∈ i.1.source ∧ ball (i.1 x) a ⊆ i.1.target ∧
      ∀ y ∈ ball (i.1 x) a, ‖X.rep i y‖ ≤ K) (x : M) :
    X.maxInterval x = univ :=
  eq_univ_of_forall fun t ↦ by
    have : (t, x) ∈ X.flowDomain := by
      rw [flowDomain_eq_univ_of_forall_norm_rep_le ha h]; trivial
    exact this

end SmoothVectorField

end LocallyConvex.Manifolds
