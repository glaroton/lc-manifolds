/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.Geodesic.Maximal
public import LocallyConvexManifolds.Metric.FinslerGeodesics

/-!
# Complete Finsler manifolds are geodesically complete

[Lar24, Cap. 9, §9.2 *Variedades de Finsler con spray*, Proposición 9.2.1 (p. 253)] states that,
for a strong Finsler manifold `M` with spray, each of the following assertions implies the next:

1. `(M, d_b)` is complete;
2. every geodesic of `M` is defined on all of `ℝ`;
3. `M` is geodesically complete: `D(exp) = TM`;
4. there is `p ∈ M` with `Dom(exp_p) = T_pM`.

With the maximal geodesics and the exponential map of `LocallyConvexManifolds.Geodesic.Maximal`,
all of them can now be stated. The implications `2 ⇒ 3 ⇒ 4` are proved there
(`Connection.expDomain_eq_univ_of_maxInterval_eq_univ`, `Connection.exists_expDomainAt_eq_univ`).
This file proves the implications that start from `1`.

## Main results

* `Connection.maxInterval_eq_univ_of_complete` (**`1 ⇒ 2`**): every maximal geodesic is defined
  on `ℝ`;
* `Connection.expDomain_eq_univ_of_complete` (**`1 ⇒ 3`**) and
  `Connection.exists_expDomainAt_eq_univ_of_complete` (**`1 ⇒ 4`**).

The proof of `1 ⇒ 2`: if `J_v` were bounded above, with `b = sup J_v`, the maximal geodesic on
`(a, b) ⊆ J_v` would extend past `b` by `Connection.IsGeodesicOn.exists_extend_right_of_complete`,
and the extension would be a geodesic with initial velocity `v` on an interval reaching beyond
`b`, against maximality. Boundedness below reduces to boundedness above through
`J_{-v} = -J_v`. We do not claim this argument is new.

## Hypotheses, compared with [Lar24]

The hypotheses are those of `Connection.IsGeodesicOn.exists_extend_of_complete`, whose docstring
compares them with the book in detail:

* `M` is Hausdorff and modeled on a **Banach** space; the connection plays the role of the spray.
* `μ` is a Finsler length structure **bounded below** (the upper bound of a *strong* Finsler
  structure is not used), and `(M, d_b)` is complete for the **symmetrized** distance
  `max (d_b(x, y), d_b(y, x))`.
* **Speed.** In the book the metric is invariant under the parallel transport of the spray, so
  geodesics have constant speed. We only assume that **every geodesic on a bounded open interval
  `(a, b)` has bounded speed `μ(α̇)` and bounded backward speed `μ(-α̇)`** there (hypothesis
  `hL`). Under invariance both are constant along the geodesic, so `hL` holds; it is needed for
  all geodesics, not only for maximal ones, but only on bounded intervals.

## Infinite-dimensional subtleties

* No local compactness is available. The extension past a finite end does not use compactness of
  closed balls (which fails in infinite dimension): it rests on the **uniform existence time** of
  geodesics with initial velocities bounded in a chart (`Connection.exists_isGeodesicOn_uniform`,
  a consequence of the Picard–Lindelöf theorem on Banach spaces), and on the lower bound of `μ`,
  which transfers the bound on `μ(α̇)` to a chart. In infinite dimension a Finsler norm need not be
  equivalent to the norm of the model, and without the lower bound a `μ`-bounded velocity may be
  unbounded in every chart.
* The converse implications are **not** claimed. In finite dimension the Hopf–Rinow theorem
  makes `1`–`4` equivalent for Riemannian (and reversible Finsler) manifolds, and adds that `exp_p`
  is onto. In infinite dimension the surjectivity of `exp_p` fails: [Atk75, Lemma 6, p. 265]
  shows that on the unit sphere `M` of `ℝ × ℓ²`, with the Riemannian metric induced by the inner
  product `|ξ|² + ⟨T x, x⟩` for a suitable strictly positive operator `T` ([Atk75, (3), p. 262]),
  a complete Riemannian Hilbert manifold, the poles `(±1, 0)` are joined by no geodesic (see also
  [Eke78, p. 288]). Atkin leaves without proof the Hilbert manifold structure of the space of
  `H¹` paths and the characterization of geodesics as critical points of the energy (Lemmas 3
  and 4, p. 263, adaptations of Palais). Even the existence of shortest curves fails: in the
  ellipsoid `M = A(S)` of a Hilbert space, image of the unit sphere by
  `A = diag(1, 1 + 2⁻¹, 1 + 2⁻², …)`, a complete Riemannian Hilbert manifold, `e₀` and `-e₀` are at
  distance `π` but every curve joining them is strictly longer ([McA65], as presented
  in [Lar24, Ejemplo 10.4.2, pp. 297–298]).

## References

* [C. J. Atkin, *The Hopf–Rinow theorem is false in infinite dimensions*][Atk75]
* [I. Ekeland, *The Hopf–Rinow theorem in infinite dimension*][Eke78]
* [G. Larotonda, *Estructuras geométricas para las variedades de Banach*][Lar24]
* [J. McAlpin, *Infinite dimensional manifolds and Morse theory*][McA65]
-/

@[expose] public section

open Set Filter
open scoped Topology

noncomputable section

namespace LocallyConvex.Manifolds

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

namespace Connection

variable {C : Connection E M}

/-- The velocity at `0` of the maximal geodesic `γ_v` is `v`. -/
theorem velocity_maxGeodesic_zero [CompleteSpace E] [T2Space M] (v : TangentBundle E M) :
    velocity E (C.maxGeodesic v) 0 = v := by
  obtain ⟨p, w⟩ := v
  have h0 : C.maxGeodesic ⟨p, w⟩ 0 = p := C.maxGeodesic_zero _
  have hd : HasDerivAt (chartAt E (C.maxGeodesic ⟨p, w⟩ 0) ∘ C.maxGeodesic ⟨p, w⟩) w 0 := by
    rw [h0]; exact C.hasDerivAt_maxGeodesic_zero (⟨p, w⟩ : TangentBundle E M)
  rw [velocity_eq_of_hasDerivAt hd, h0]

variable [CompleteSpace E] [T2Space M] (μ : FinslerLengthStructure E M)
  [CompleteSpace μ.FinslerSpace]

/-- Under the hypotheses of Proposición 9.2.1 (`1 ⇒ 2`), the maximal interval `J_v` is not
bounded above. -/
theorem not_bddAbove_maxInterval_of_complete (hb : μ.toFinslerSeminormField.IsBoundedBelow)
    (hL : ∀ (α : ℝ → M) (a b : ℝ), C.IsGeodesicOn α (Ioo a b) → ∃ L, ∀ τ ∈ Ioo a b,
      μ.toFun (velocity E α τ) ≤ L ∧ μ.toFun (velocity E (fun σ ↦ α (-σ)) (-τ)) ≤ L)
    (v : TangentBundle E M) : ¬ BddAbove (C.maxInterval v) := by
  intro hbdd
  set J := C.maxInterval v
  set b := sSup J
  have hJ := C.isGeodesicThrough_maxGeodesic v
  -- `J` contains a neighborhood `(-ε, ε)` of `0`
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hJ.isOpen.mem_nhds hJ.zero_mem)
  rw [Real.ball_eq_Ioo, zero_sub, zero_add] at hball
  set a := -(ε / 2)
  have ha : a ∈ J := hball ⟨by simp only [a]; linarith, by simp only [a]; linarith⟩
  have hεb : ε / 2 ≤ b := le_csSup hbdd (hball ⟨by linarith, by linarith⟩)
  have ha0 : a < 0 := by simp only [a]; linarith
  have hab : a < b := by linarith
  -- `(a, b) ⊆ J`
  have hsub : Ioo a b ⊆ J := fun t ht ↦ by
    obtain ⟨t', ht', htt'⟩ := exists_lt_of_lt_csSup ⟨0, hJ.zero_mem⟩ ht.2
    exact hJ.ordConnected.out ha ht' ⟨ht.1.le, htt'.le⟩
  have hα : C.IsGeodesicOn (C.maxGeodesic v) (Ioo a b) := hJ.isGeodesicOn.mono isOpen_Ioo hsub
  obtain ⟨L, hL⟩ := hL _ a b hα
  obtain ⟨b', hb', β, hβ, hEq⟩ := hα.exists_extend_right_of_complete μ hb hab
    (fun τ hτ ↦ (hL τ hτ).1) (fun τ hτ ↦ (hL τ hτ).2)
  -- the extension is a geodesic with initial velocity `v` on `(a, b')`
  have h0 : (0 : ℝ) ∈ Ioo a b := ⟨ha0, by linarith⟩
  have hβ0 : HasDerivAt (chartAt E v.proj ∘ β) (v.2 : E) 0 := by
    refine hJ.hasDerivAt_zero.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds h0] with s hs
    simp [hEq hs]
  have hβv : C.IsGeodesicThrough v β (Ioo a b') :=
    ⟨isOpen_Ioo, ordConnected_Ioo, ⟨ha0, by linarith⟩, by rw [hEq h0, hJ.map_zero], hβ0, hβ⟩
  have hmem : (b + b') / 2 ∈ J := hβv.subset_maxInterval ⟨by linarith, by linarith⟩
  have := le_csSup hbdd hmem
  linarith

/-- **Proposición 9.2.1 (`1 ⇒ 2`)** ([Lar24, §9.2, p. 253]). Let `M` be a Hausdorff manifold modeled
on a Banach space, with a connection and a Finsler length structure `μ` bounded below, such that
`(M, d_b)` is complete (for the symmetrized distance). Assume that every geodesic on a bounded open
interval has bounded speed `μ(α̇)` and bounded backward speed `μ(-α̇)` there (as when geodesics have
constant speed). Then **every maximal geodesic is defined on all of `ℝ`**: `J_v = ℝ` for every
`v ∈ TM`. -/
theorem maxInterval_eq_univ_of_complete (hb : μ.toFinslerSeminormField.IsBoundedBelow)
    (hL : ∀ (α : ℝ → M) (a b : ℝ), C.IsGeodesicOn α (Ioo a b) → ∃ L, ∀ τ ∈ Ioo a b,
      μ.toFun (velocity E α τ) ≤ L ∧ μ.toFun (velocity E (fun σ ↦ α (-σ)) (-τ)) ≤ L)
    (v : TangentBundle E M) : C.maxInterval v = univ := by
  have habove := C.not_bddAbove_maxInterval_of_complete μ hb hL v
  -- `J_v` is not bounded below, since `J_{-v} = -J_v` is not bounded above
  have hbelow : ¬ BddBelow (C.maxInterval v) := by
    rintro ⟨m, hm⟩
    refine C.not_bddAbove_maxInterval_of_complete μ hb hL (tangentSMul (-1) v) ⟨-m, fun t ht ↦ ?_⟩
    rw [C.maxInterval_smul v (by norm_num), mem_preimage] at ht
    have := hm ht
    linarith
  refine eq_univ_of_forall fun x ↦ ?_
  obtain ⟨a, ha, hax⟩ := not_bddBelow_iff.1 hbelow x
  obtain ⟨b, hb, hxb⟩ := not_bddAbove_iff.1 habove x
  exact (C.ordConnected_maxInterval v).out ha hb ⟨hax.le, hxb.le⟩

/-- **Proposición 9.2.1 (`1 ⇒ 3`)**: under the hypotheses of
`Connection.maxInterval_eq_univ_of_complete`, `M` is geodesically complete: `D(exp) = TM`. -/
theorem expDomain_eq_univ_of_complete (hb : μ.toFinslerSeminormField.IsBoundedBelow)
    (hL : ∀ (α : ℝ → M) (a b : ℝ), C.IsGeodesicOn α (Ioo a b) → ∃ L, ∀ τ ∈ Ioo a b,
      μ.toFun (velocity E α τ) ≤ L ∧ μ.toFun (velocity E (fun σ ↦ α (-σ)) (-τ)) ≤ L) :
    C.expDomain = univ :=
  expDomain_eq_univ_of_maxInterval_eq_univ (C.maxInterval_eq_univ_of_complete μ hb hL)

/-- **Proposición 9.2.1 (`1 ⇒ 4`)**: under the hypotheses of
`Connection.maxInterval_eq_univ_of_complete`, if `M` is nonempty there is `p ∈ M` with
`Dom(exp_p) = T_pM` (indeed this holds for every `p`, by `Connection.expDomainAt_eq_univ`). -/
theorem exists_expDomainAt_eq_univ_of_complete [Nonempty M]
    (hb : μ.toFinslerSeminormField.IsBoundedBelow)
    (hL : ∀ (α : ℝ → M) (a b : ℝ), C.IsGeodesicOn α (Ioo a b) → ∃ L, ∀ τ ∈ Ioo a b,
      μ.toFun (velocity E α τ) ≤ L ∧ μ.toFun (velocity E (fun σ ↦ α (-σ)) (-τ)) ≤ L) :
    ∃ p : M, C.expDomainAt p = univ :=
  exists_expDomainAt_eq_univ (C.expDomain_eq_univ_of_complete μ hb hL)

end Connection

end LocallyConvex.Manifolds
