/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.Geodesic.Existence

/-!
# Maximal geodesics and the exponential map on Banach manifolds

References: S. Lang, *Fundamentals of Differential Geometry*, Springer GTM 191 (1999), Ch. IV §3
(Sprays, p. 96) and §4 (The Flow of a Spray and the Exponential Map, p. 105), Ch. VIII §5
(p. 215); G. Larotonda, *Estructuras geométricas para las variedades de Banach* (version of
29 November 2023), §9.2.

Let `C` be a connection on a **Hausdorff** manifold `M` modeled on a **Banach** space `E`. A
tangent vector `v ∈ T_pM` is a pair `⟨p, w⟩`, with `w ∈ E` read in the preferred chart at `p`.
By local existence (`Connection.exists_isGeodesicOn`) and uniqueness
(`Connection.IsGeodesicOn.eqOn`) of geodesics, the geodesics with initial velocity `v` glue to a
**maximal geodesic** `γ_v`, defined on an open interval `J_v ∋ 0`. We prove:

* `Connection.IsGeodesicThrough`, `Connection.maxInterval`, `Connection.maxGeodesic`: geodesics
  with initial velocity `v` on open intervals containing `0`, the maximal interval `J_v` and the
  maximal geodesic `γ_v`.
* `Connection.isGeodesicThrough_maxGeodesic`, `Connection.IsGeodesicThrough.subset_maxInterval`,
  `Connection.IsGeodesicThrough.maxGeodesic_eq` (**maximality**): `γ_v` is a geodesic with
  initial velocity `v` on `J_v`, and every geodesic with initial velocity `v` on an open interval
  `I ∋ 0` is its restriction to `I`.
* `Connection.maxInterval_smul`, `Connection.maxGeodesic_smul` (**homogeneity**): for `s ≠ 0`,
  `J_{sv} = s⁻¹ J_v` and `γ_{sv}(t) = γ_v(st)`; `Connection.maxInterval_zero_smul`: the
  geodesic with zero initial velocity is constant and defined on `ℝ`.
* `Connection.expDomain`, `Connection.exp`, `Connection.expDomainAt`, `Connection.expAt`: the
  **exponential map** `exp v = γ_v(1)`, defined on `D(exp) = {v | 1 ∈ J_v}`, and its restriction
  `exp_p` to `T_pM`. `Connection.smul_mem_expDomain_iff`, `Connection.exp_smul`: `tv ∈ D(exp)`
  if and only if `t ∈ J_v`, and then `exp(tv) = γ_v(t)`, so the maximal geodesic is
  `t ↦ exp(tv)`, as in *Estructuras*.
* `Connection.expDomain_eq_univ_of_maxInterval_eq_univ`,
  `Connection.exists_expDomainAt_eq_univ` (**Proposición 9.2.1 of *Estructuras*, `2 ⇒ 3 ⇒ 4`**):
  if every maximal geodesic is defined on `ℝ` then `D(exp) = TM`, and then
  `Dom(exp_p) = T_pM` for some (indeed every) `p`. The implication `1 ⇒ 2` is in
  `LocallyConvexManifolds.Metric.FinslerExp`.

## Implementation notes

* Hypotheses. Completeness of `E` is used by local existence (Picard–Lindelöf) and local
  uniqueness; on manifolds modeled on Fréchet spaces geodesics need neither exist nor be unique.
  The Hausdorff property is used by uniqueness: on the line with two origins the two copies of a
  line through the origins are geodesics of the flat connection with the same initial data, so
  there is no maximal geodesic. Both hypotheses are only assumed where they are used.
* The direct route. The maximal geodesic is built directly from the geodesics of `C`, mimicking
  the construction of the maximal flow in `LocallyConvexManifolds.Flow.Maximal`, and not as the
  projection of the maximal flow of the geodesic spray on `TM`, which keeps the basic theory free
  of the double tangent bundle. We do not claim this argument is new.
* Openness of `D(exp)` in `TM` and smoothness of `exp` on it (Lang, Ch. IV §4) are proved in
  `LocallyConvexManifolds.Geodesic.GeodesicSpray`, which identifies `γ_v` with the projection of the
  maximal flow of the geodesic spray (`Connection.maxGeodesic_eq_proj_flow`).
* `γ_v` takes the junk value `γ_v(t) = p` (the base point of `v`) for `t ∉ J_v`, and so
  `exp v = p` for `v ∉ D(exp)`.
-/

@[expose] public section

open Set Filter
open scoped Topology

noncomputable section

namespace LocallyConvex.Manifolds

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

/-- The product `s • v` of a scalar and a tangent vector `v ∈ T_pM`: the vector `s • v ∈ T_pM`. -/
def tangentSMul (s : ℝ) (v : TangentBundle E M) : TangentBundle E M :=
  ⟨v.proj, s • v.2⟩

@[simp] theorem tangentSMul_proj (s : ℝ) (v : TangentBundle E M) :
    (tangentSMul s v).proj = v.proj := rfl

theorem tangentSMul_snd (s : ℝ) (v : TangentBundle E M) :
    (tangentSMul s v).2 = s • v.2 := rfl

theorem tangentSMul_tangentSMul (s r : ℝ) (v : TangentBundle E M) :
    tangentSMul s (tangentSMul r v) = tangentSMul (s * r) v := by
  unfold tangentSMul
  congr 1
  exact smul_smul s r (v.2 : E)

theorem tangentSMul_one (v : TangentBundle E M) : tangentSMul 1 v = v := by
  simp [tangentSMul]

/-- The preimage of an interval under `t ↦ s t` is an interval. -/
theorem ordConnected_preimage_mul {I : Set ℝ} (hI : OrdConnected I) (s : ℝ) :
    OrdConnected ((s * ·) ⁻¹' I) := by
  refine ⟨fun x hx y hy z hz ↦ hI.uIcc_subset hx hy ?_⟩
  rcases le_total 0 s with hs | hs
  · exact Set.Icc_subset_uIcc
      ⟨mul_le_mul_of_nonneg_left hz.1 hs, mul_le_mul_of_nonneg_left hz.2 hs⟩
  · exact Set.Icc_subset_uIcc'
      ⟨mul_le_mul_of_nonpos_left hz.2 hs, mul_le_mul_of_nonpos_left hz.1 hs⟩

namespace Connection

variable {C : Connection E M}

/-! ### Uniqueness on intervals; rescaled geodesics -/

/-- **Uniqueness of geodesics on an interval.** On a Hausdorff manifold modeled on a Banach space,
two geodesics on an open interval `I` (possibly unbounded) with the same position and velocity at
`t₀ ∈ I` agree on `I`. This reduces to `Connection.IsGeodesicOn.eqOn` on bounded subintervals. -/
theorem IsGeodesicOn.eqOn_of_ordConnected [CompleteSpace E] [T2Space M] {α β : ℝ → M}
    {I : Set ℝ} (hα : C.IsGeodesicOn α I) (hβ : C.IsGeodesicOn β I) (hI : OrdConnected I)
    {t₀ : ℝ} (ht₀ : t₀ ∈ I) (heq : α t₀ = β t₀) (i : atlas E M) (hi : α t₀ ∈ i.1.source)
    (hv : deriv (i.1 ∘ α) t₀ = deriv (i.1 ∘ β) t₀) : EqOn α β I := by
  intro t ht
  have hmin : min t₀ t ∈ I := by rcases min_choice t₀ t with h | h <;> rw [h] <;> assumption
  have hmax : max t₀ t ∈ I := by rcases max_choice t₀ t with h | h <;> rw [h] <;> assumption
  obtain ⟨ε₁, hε₁, h₁⟩ := Metric.mem_nhds_iff.1 (hα.1.mem_nhds hmin)
  obtain ⟨ε₂, hε₂, h₂⟩ := Metric.mem_nhds_iff.1 (hα.1.mem_nhds hmax)
  rw [Real.ball_eq_Ioo] at h₁ h₂
  have ha : min t₀ t - ε₁ / 2 ∈ I := h₁ ⟨by linarith, by linarith⟩
  have hb : max t₀ t + ε₂ / 2 ∈ I := h₂ ⟨by linarith, by linarith⟩
  have hsub : Ioo (min t₀ t - ε₁ / 2) (max t₀ t + ε₂ / 2) ⊆ I :=
    Ioo_subset_Icc_self.trans (hI.out ha hb)
  have ht₀' : t₀ ∈ Ioo (min t₀ t - ε₁ / 2) (max t₀ t + ε₂ / 2) :=
    ⟨by linarith [min_le_left t₀ t], by linarith [le_max_left t₀ t]⟩
  have ht' : t ∈ Ioo (min t₀ t - ε₁ / 2) (max t₀ t + ε₂ / 2) :=
    ⟨by linarith [min_le_right t₀ t], by linarith [le_max_right t₀ t]⟩
  exact IsGeodesicOn.eqOn (hα.mono isOpen_Ioo hsub) (hβ.mono isOpen_Ioo hsub) ht₀' heq i hi hv ht'

omit [MBManifold E M] in
/-- **A rescaled geodesic is a geodesic**: if `α` is a geodesic on `I`, then `t ↦ α (s t)` is a
geodesic on `s⁻¹ I = {t | s t ∈ I}`. The symbols are bilinear, so
`Γ(s v, s v) = s² Γ(v, v)`. -/
theorem IsGeodesicOn.comp_mul {α : ℝ → M} {I : Set ℝ} (h : C.IsGeodesicOn α I) (s : ℝ) :
    C.IsGeodesicOn (fun t ↦ α (s * t)) ((s * ·) ⁻¹' I) := by
  have hcont : Continuous fun t : ℝ ↦ s * t := continuous_const.mul continuous_id
  have hd : ∀ r : ℝ, HasDerivAt (fun t : ℝ ↦ s * t) s r := fun r ↦ by
    simpa using (hasDerivAt_id r).const_mul s
  refine ⟨h.1.preimage hcont, h.2.1.comp hcont.continuousOn (mapsTo_preimage _ _), fun t ht ↦ ?_⟩
  obtain ⟨c₁, hc, hc₁⟩ := h.2.2 _ ht
  have htend : Tendsto (fun r : ℝ ↦ s * r) (𝓝 t) (𝓝 (s * t)) := hcont.continuousAt
  refine ⟨fun r ↦ s • c₁ (s * r), ?_, ?_⟩
  · filter_upwards [htend.eventually hc] with r hr
    exact hr.scomp r (hd r)
  · have h2 : HasDerivAt (fun r ↦ s • c₁ (s * r)) _ t := (hc₁.scomp t (hd t)).const_smul s
    convert h2 using 1
    rw [C.smul_left, C.smul_right, smul_smul]

/-! ### Geodesics with given initial velocity -/

variable (C) in
/-- `α` is a **geodesic with initial velocity `v ∈ T_pM` on `I`**: `I` is an open interval
containing `0`, `α` is a geodesic on `I`, `α 0 = p`, and the derivative at `0` of `α` read in the
preferred chart at `p` is the fiber coordinate of `v`. -/
structure IsGeodesicThrough (v : TangentBundle E M) (α : ℝ → M) (I : Set ℝ) : Prop where
  isOpen : IsOpen I
  ordConnected : OrdConnected I
  zero_mem : (0 : ℝ) ∈ I
  map_zero : α 0 = v.proj
  hasDerivAt_zero : HasDerivAt (chartAt E v.proj ∘ α) (v.2 : E) 0
  isGeodesicOn : C.IsGeodesicOn α I

/-- Two geodesics with the same initial velocity agree where both are defined. -/
theorem IsGeodesicThrough.eqOn [CompleteSpace E] [T2Space M] {v : TangentBundle E M}
    {α β : ℝ → M} {I₁ I₂ : Set ℝ} (h₁ : C.IsGeodesicThrough v α I₁)
    (h₂ : C.IsGeodesicThrough v β I₂) : EqOn α β (I₁ ∩ I₂) :=
  IsGeodesicOn.eqOn_of_ordConnected
    (h₁.isGeodesicOn.mono (h₁.isOpen.inter h₂.isOpen) inter_subset_left)
    (h₂.isGeodesicOn.mono (h₁.isOpen.inter h₂.isOpen) inter_subset_right)
    (h₁.ordConnected.inter h₂.ordConnected) ⟨h₁.zero_mem, h₂.zero_mem⟩
    (h₁.map_zero.trans h₂.map_zero.symm) ⟨chartAt E v.proj, chart_mem_atlas E _⟩
    (by rw [h₁.map_zero]; exact mem_chart_source E _)
    (by rw [h₁.hasDerivAt_zero.deriv, h₂.hasDerivAt_zero.deriv])

variable (C) in
/-- **Local existence**: every tangent vector is the initial velocity of a geodesic on some
`(-ε, ε)`. -/
theorem exists_isGeodesicThrough [CompleteSpace E] (v : TangentBundle E M) :
    ∃ ε > (0 : ℝ), ∃ α : ℝ → M, C.IsGeodesicThrough v α (Ioo (-ε) ε) := by
  obtain ⟨ε, hε, α, h0, hv, hα⟩ :=
    C.exists_isGeodesicOn ⟨chartAt E v.proj, chart_mem_atlas E _⟩ (mem_chart_source E v.proj)
      (v.2 : E)
  exact ⟨ε, hε, α, isOpen_Ioo, ordConnected_Ioo, ⟨neg_lt_zero.2 hε, hε⟩, h0, hv, hα⟩

/-- A rescaled geodesic with initial velocity `v` is a geodesic with initial velocity `s v`. -/
theorem IsGeodesicThrough.comp_mul {v : TangentBundle E M} {α : ℝ → M} {I : Set ℝ}
    (h : C.IsGeodesicThrough v α I) (s : ℝ) :
    C.IsGeodesicThrough (tangentSMul s v) (fun t ↦ α (s * t)) ((s * ·) ⁻¹' I) where
  isOpen := h.isOpen.preimage (continuous_const.mul continuous_id)
  ordConnected := ordConnected_preimage_mul h.ordConnected s
  zero_mem := by simpa using h.zero_mem
  map_zero := by simpa using h.map_zero
  hasDerivAt_zero := by
    have hd : HasDerivAt (fun t : ℝ ↦ s * t) s 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul s
    exact h.hasDerivAt_zero.scomp_of_eq 0 hd (by simp)
  isGeodesicOn := h.isGeodesicOn.comp_mul s

/-! ### The maximal geodesic -/

variable (C) in
/-- The **maximal interval** `J_v` of the geodesic with initial velocity `v`: the union of the
intervals of definition of all geodesics with initial velocity `v`. -/
def maxInterval (v : TangentBundle E M) : Set ℝ :=
  {t | ∃ α I, C.IsGeodesicThrough v α I ∧ t ∈ I}

open scoped Classical in
variable (C) in
/-- The **maximal geodesic** `γ_v` with initial velocity `v ∈ T_pM`: `γ_v(t)` is the value at `t`
of any geodesic with initial velocity `v` defined at `t`. It is well defined on `J_v` by
uniqueness (`Connection.IsGeodesicThrough.maxGeodesic_eq`); for `t ∉ J_v` it takes the junk
value `p`. -/
def maxGeodesic (v : TangentBundle E M) (t : ℝ) : M :=
  if h : ∃ α I, C.IsGeodesicThrough v α I ∧ t ∈ I then h.choose t else v.proj

/-- **Maximality**: every geodesic with initial velocity `v` is defined on a subinterval of
`J_v`. -/
theorem IsGeodesicThrough.subset_maxInterval {v : TangentBundle E M} {α : ℝ → M} {I : Set ℝ}
    (h : C.IsGeodesicThrough v α I) : I ⊆ C.maxInterval v :=
  fun _ ht ↦ ⟨α, I, h, ht⟩

/-- **Maximality**: every geodesic with initial velocity `v` is a restriction of `γ_v`. -/
theorem IsGeodesicThrough.maxGeodesic_eq [CompleteSpace E] [T2Space M] {v : TangentBundle E M}
    {α : ℝ → M} {I : Set ℝ} (h : C.IsGeodesicThrough v α I) {t : ℝ} (ht : t ∈ I) :
    C.maxGeodesic v t = α t := by
  have hex : ∃ α I, C.IsGeodesicThrough v α I ∧ t ∈ I := ⟨α, I, h, ht⟩
  rw [maxGeodesic, dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨I', h', ht'⟩ := hex.choose_spec
  exact h'.eqOn h ⟨ht', ht⟩

/-- Outside `J_v`, `γ_v` takes the junk value `p`. -/
theorem maxGeodesic_of_notMem {v : TangentBundle E M} {t : ℝ} (ht : t ∉ C.maxInterval v) :
    C.maxGeodesic v t = v.proj := by
  have ht' : ¬ ∃ α I, C.IsGeodesicThrough v α I ∧ t ∈ I := ht
  exact dite_eq_right_of_eq_false (eq_false ht')

/-- The maximal interval `J_v` is open. -/
theorem isOpen_maxInterval (v : TangentBundle E M) : IsOpen (C.maxInterval v) :=
  isOpen_iff_mem_nhds.2 fun _ ⟨_, _, h, ht⟩ ↦
    Filter.mem_of_superset (h.isOpen.mem_nhds ht) h.subset_maxInterval

/-- The maximal interval `J_v` is an interval. -/
theorem ordConnected_maxInterval (v : TangentBundle E M) : OrdConnected (C.maxInterval v) := by
  refine ⟨fun a ⟨_, _, h₁, ha⟩ b ⟨_, _, h₂, hb⟩ τ hτ ↦ ?_⟩
  rcases le_total τ 0 with hτ0 | hτ0
  · exact h₁.subset_maxInterval (h₁.ordConnected.out ha h₁.zero_mem ⟨hτ.1, hτ0⟩)
  · exact h₂.subset_maxInterval (h₂.ordConnected.out h₂.zero_mem hb ⟨hτ0, hτ.2⟩)

/-- The maximal interval `J_v` contains `0`. -/
theorem zero_mem_maxInterval [CompleteSpace E] (v : TangentBundle E M) :
    (0 : ℝ) ∈ C.maxInterval v := by
  obtain ⟨ε, -, α, h⟩ := C.exists_isGeodesicThrough v
  exact h.subset_maxInterval h.zero_mem

/-- `γ_v` is a geodesic on `J_v`. -/
theorem isGeodesicOn_maxGeodesic [CompleteSpace E] [T2Space M] (v : TangentBundle E M) :
    C.IsGeodesicOn (C.maxGeodesic v) (C.maxInterval v) :=
  isGeodesicOn_of_local (C.isOpen_maxInterval v) fun _ ⟨α, I, h, ht⟩ ↦
    ⟨α, I, ht, h.isGeodesicOn, fun _ hs ↦ h.maxGeodesic_eq hs⟩

/-- `γ_v(0) = p`. -/
theorem maxGeodesic_zero [CompleteSpace E] [T2Space M] (v : TangentBundle E M) :
    C.maxGeodesic v 0 = v.proj := by
  obtain ⟨ε, -, α, h⟩ := C.exists_isGeodesicThrough v
  rw [h.maxGeodesic_eq h.zero_mem, h.map_zero]

/-- The initial velocity of `γ_v` is `v`. -/
theorem hasDerivAt_maxGeodesic_zero [CompleteSpace E] [T2Space M] (v : TangentBundle E M) :
    HasDerivAt (chartAt E v.proj ∘ C.maxGeodesic v) (v.2 : E) 0 := by
  obtain ⟨ε, -, α, h⟩ := C.exists_isGeodesicThrough v
  refine h.hasDerivAt_zero.congr_of_eventuallyEq ?_
  filter_upwards [h.isOpen.mem_nhds h.zero_mem] with s hs
  simp [h.maxGeodesic_eq hs]

/-- **The maximal geodesic**: `γ_v` is a geodesic with initial velocity `v` on the maximal
interval `J_v`. -/
theorem isGeodesicThrough_maxGeodesic [CompleteSpace E] [T2Space M] (v : TangentBundle E M) :
    C.IsGeodesicThrough v (C.maxGeodesic v) (C.maxInterval v) where
  isOpen := C.isOpen_maxInterval v
  ordConnected := C.ordConnected_maxInterval v
  zero_mem := C.zero_mem_maxInterval v
  map_zero := C.maxGeodesic_zero v
  hasDerivAt_zero := C.hasDerivAt_maxGeodesic_zero v
  isGeodesicOn := C.isGeodesicOn_maxGeodesic v

/-! ### Homogeneity -/

/-- The rescaled maximal geodesic `t ↦ γ_v(s t)` is defined on `s⁻¹ J_v ⊆ J_{sv}`. -/
theorem preimage_maxInterval_subset [CompleteSpace E] [T2Space M] (v : TangentBundle E M)
    (s : ℝ) : (s * ·) ⁻¹' C.maxInterval v ⊆ C.maxInterval (tangentSMul s v) :=
  ((C.isGeodesicThrough_maxGeodesic v).comp_mul s).subset_maxInterval

/-- `γ_{sv}(t) = γ_v(s t)` whenever `s t ∈ J_v`. -/
theorem maxGeodesic_smul_of_mem [CompleteSpace E] [T2Space M] (v : TangentBundle E M)
    {s t : ℝ} (ht : s * t ∈ C.maxInterval v) :
    C.maxGeodesic (tangentSMul s v) t = C.maxGeodesic v (s * t) :=
  ((C.isGeodesicThrough_maxGeodesic v).comp_mul s).maxGeodesic_eq ht

/-- **Homogeneity of the maximal interval**: for `s ≠ 0`, `J_{sv} = s⁻¹ J_v`. -/
theorem maxInterval_smul [CompleteSpace E] [T2Space M] (v : TangentBundle E M) {s : ℝ}
    (hs : s ≠ 0) : C.maxInterval (tangentSMul s v) = (s * ·) ⁻¹' C.maxInterval v := by
  refine (Subset.antisymm ?_ (C.preimage_maxInterval_subset v s))
  intro t ht
  have h := C.preimage_maxInterval_subset (tangentSMul s v) s⁻¹
  rw [tangentSMul_tangentSMul, inv_mul_cancel₀ hs, tangentSMul_one] at h
  exact h (show s⁻¹ * (s * t) ∈ _ by rwa [← mul_assoc, inv_mul_cancel₀ hs, one_mul])

/-- **Homogeneity of the maximal geodesic**: for `s ≠ 0`, `γ_{sv}(t) = γ_v(s t)` for all `t`
(both sides take the junk value `p` when `s t ∉ J_v`). -/
theorem maxGeodesic_smul [CompleteSpace E] [T2Space M] (v : TangentBundle E M) {s : ℝ}
    (hs : s ≠ 0) (t : ℝ) : C.maxGeodesic (tangentSMul s v) t = C.maxGeodesic v (s * t) := by
  by_cases ht : s * t ∈ C.maxInterval v
  · exact C.maxGeodesic_smul_of_mem v ht
  · have ht' : t ∉ C.maxInterval (tangentSMul s v) := by rwa [C.maxInterval_smul v hs]
    rw [maxGeodesic_of_notMem ht', maxGeodesic_of_notMem ht, tangentSMul_proj]

/-- The geodesic with zero initial velocity is defined on `ℝ`. -/
theorem maxInterval_zero_smul [CompleteSpace E] [T2Space M] (v : TangentBundle E M) :
    C.maxInterval (tangentSMul 0 v) = univ :=
  eq_univ_of_univ_subset fun t _ ↦
    C.preimage_maxInterval_subset v 0 (by simpa using C.zero_mem_maxInterval v)

/-- The geodesic with zero initial velocity is constant. -/
theorem maxGeodesic_zero_smul [CompleteSpace E] [T2Space M] (v : TangentBundle E M) (t : ℝ) :
    C.maxGeodesic (tangentSMul 0 v) t = v.proj := by
  rw [C.maxGeodesic_smul_of_mem v (by simpa using C.zero_mem_maxInterval v), zero_mul,
    C.maxGeodesic_zero]

/-! ### The exponential map -/

variable (C) in
/-- The **domain of the exponential map**: `D(exp) = {v ∈ TM | 1 ∈ J_v}`. -/
def expDomain : Set (TangentBundle E M) :=
  {v | (1 : ℝ) ∈ C.maxInterval v}

variable (C) in
/-- The **exponential map** `exp v = γ_v(1)`, meaningful on `D(exp)`; outside `D(exp)` it takes
the junk value `exp v = p` for `v ∈ T_pM`. -/
def exp (v : TangentBundle E M) : M :=
  C.maxGeodesic v 1

variable (C) in
/-- The **domain of `exp_p`**: the vectors `w ∈ T_pM = E` with `⟨p, w⟩ ∈ D(exp)`. -/
def expDomainAt (p : M) : Set E :=
  {w | (⟨p, w⟩ : TangentBundle E M) ∈ C.expDomain}

variable (C) in
/-- The **exponential map at `p`**, `exp_p w = exp ⟨p, w⟩`. -/
def expAt (p : M) (w : E) : M :=
  C.exp ⟨p, w⟩

theorem mem_expDomain {v : TangentBundle E M} : v ∈ C.expDomain ↔ (1 : ℝ) ∈ C.maxInterval v :=
  Iff.rfl

/-- `t v ∈ D(exp)` if and only if `t ∈ J_v`. -/
theorem smul_mem_expDomain_iff [CompleteSpace E] [T2Space M] (v : TangentBundle E M) (t : ℝ) :
    tangentSMul t v ∈ C.expDomain ↔ t ∈ C.maxInterval v := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [mem_expDomain, C.maxInterval_zero_smul, C.zero_mem_maxInterval]
  · rw [mem_expDomain, C.maxInterval_smul v ht, mem_preimage, mul_one]

/-- **The maximal geodesic is `t ↦ exp(t v)`**: for `t ∈ J_v`, `exp(t v) = γ_v(t)`. -/
theorem exp_smul [CompleteSpace E] [T2Space M] (v : TangentBundle E M) {t : ℝ}
    (ht : t ∈ C.maxInterval v) : C.exp (tangentSMul t v) = C.maxGeodesic v t := by
  rw [exp, C.maxGeodesic_smul_of_mem v (by rwa [mul_one]), mul_one]

/-- `exp(0_p) = p`. -/
theorem exp_zero_smul [CompleteSpace E] [T2Space M] (v : TangentBundle E M) :
    C.exp (tangentSMul 0 v) = v.proj :=
  C.maxGeodesic_zero_smul v 1

/-- Every geodesic with initial velocity `v` defined at `1` has endpoint `exp v`. -/
theorem IsGeodesicThrough.exp_eq [CompleteSpace E] [T2Space M] {v : TangentBundle E M}
    {α : ℝ → M} {I : Set ℝ} (h : C.IsGeodesicThrough v α I) (h1 : (1 : ℝ) ∈ I) :
    v ∈ C.expDomain ∧ C.exp v = α 1 :=
  ⟨h.subset_maxInterval h1, h.maxGeodesic_eq h1⟩

/-! ### Proposición 9.2.1 of *Estructuras*, `2 ⇒ 3 ⇒ 4` -/

/-- **Proposición 9.2.1 (`2 ⇒ 3`)**: if every maximal geodesic is defined on `ℝ`, then `M` is
geodesically complete: `D(exp) = TM`. -/
theorem expDomain_eq_univ_of_maxInterval_eq_univ (h : ∀ v : TangentBundle E M,
    C.maxInterval v = univ) : C.expDomain = univ :=
  eq_univ_of_forall fun v ↦ by simp [mem_expDomain, h v]

/-- **Proposición 9.2.1 (`3 ⇒ 4`)**: if `D(exp) = TM`, then `Dom(exp_p) = T_pM` for every `p`. -/
theorem expDomainAt_eq_univ (h : C.expDomain = univ) (p : M) : C.expDomainAt p = univ :=
  eq_univ_of_forall fun w ↦ by simp [expDomainAt, h]

/-- **Proposición 9.2.1 (`3 ⇒ 4`)**: if `M` is nonempty and `D(exp) = TM`, there is `p ∈ M` with
`Dom(exp_p) = T_pM`. -/
theorem exists_expDomainAt_eq_univ [Nonempty M] (h : C.expDomain = univ) :
    ∃ p : M, C.expDomainAt p = univ :=
  ⟨Classical.arbitrary M, C.expDomainAt_eq_univ h _⟩

end Connection

end LocallyConvex.Manifolds
