/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.Manifold.VaryingAtlasProd
public import LocallyConvexManifolds.MappingSpace.Composition

/-!
# The composition map of manifolds of mappings

Let `K`, `L` be compact manifolds, `L` with a local addition, and `M` a manifold with a local
addition. The composition map
`Γ : C^{ℓ+k}(L, M) × C^ℓ(K, L) → C^ℓ(K, M)`, `(γ, η) ↦ γ ∘ η`,
is `C^k` for the product of the canonical manifold structures ([GN26, Proposition 13.1.2(a)]);
in particular `C^∞(L, M) × C^ℓ(K, L) → C^ℓ(K, M)` is smooth.

## Main definitions

* `CkMap.comp γ η hm`: the composition `γ ∘ η ∈ C^ℓ(K, M)` of `γ ∈ C^m(L, M)` and
  `η ∈ C^ℓ(K, L)`, for `ℓ ≤ m`; `SmoothMap.comp γ η`: the same for smooth maps.

## Main results

* `ContMDiffMB₂.comp_eval`: for `K` compact, if `ε₁ : P₁ × L → M` is `C^{ℓ+k, ℓ+k}` and
  `ε₂ : P₂ × K → L` is `C^{k,ℓ}`, then `((p₁, p₂), x) ↦ ε₁(p₁, ε₂(p₂, x))` is `C^{k,ℓ}`.
* `LocalAddition.contMDiffOn_comp`: **[GN26, Proposition 13.1.2(a)]**, the composition map
  `C^{ℓ+k}(L, M) × C^ℓ(K, L) → C^ℓ(K, M)` is `C^k`.
* `LocalAddition.smooth_comp_smoothMap`: `C^∞(L, M) × C^ℓ(K, L) → C^ℓ(K, M)` is smooth;
  `LocalAddition.smooth_compSm`: `C^∞(L, M) × C^∞(K, L) → C^∞(K, M)` is smooth.

## Implementation notes

* Products of manifolds of mappings carry the product atlas `VaryingAtlas.prod`.
* **The proof** follows Glöckner–Neeb. By the exponential law ([GN26, Theorem 4.2.2(a)]) it
  suffices that `Γ^∧((γ, η), x) = ε₁(γ, ε₂(η, x))` is `C^{k,ℓ}`, where
  `ε₁ : C^{ℓ+k}(L, M) × L → M` and `ε₂ : C^ℓ(K, L) × K → L` are the evaluation maps. In charts,
  `ε₁` is `C^{ℓ+k, ℓ+k}` ([GN26, Theorem 4.2.2(c)]), hence `C^{ℓ+k}` on products of open sets
  (`ContDiffMBOn₂.contDiffMBOn_prod`); `(a, b) ↦ (a₁, ε₂(a₂, b))` is `C^{k,ℓ}`; and the chain rule
  for `C^{k,ℓ}` maps ([GN26, Proposition 1.7.28], `contDiffMBOn₂_comp_left`) concludes.
* Glöckner–Neeb allow `K` with rough boundary; here `K` and `L` are compact manifolds of the
  library (without boundary).
* Proposition 13.1.2(b) (smoothness of the right translations `η ↦ η ∘ γ`) is only sketched in
  [GN26] and is not formalized here.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set
open LocallyConvex.Analysis

noncomputable section

universe u v

namespace LocallyConvex.Manifolds

variable {HK : Type u} [AddCommGroup HK] [Module ℝ HK] [TopologicalSpace HK]
  [IsTopologicalAddGroup HK] [ContinuousSMul ℝ HK] [LocallyConvexSpace ℝ HK] [T2Space HK]
  {K : Type u} [TopologicalSpace K] [ChartedSpace HK K] [MBManifold HK K]
  {HL : Type u} [AddCommGroup HL] [Module ℝ HL] [TopologicalSpace HL]
  [IsTopologicalAddGroup HL] [ContinuousSMul ℝ HL] [LocallyConvexSpace ℝ HL] [T2Space HL]
  {L : Type u} [TopologicalSpace L] [ChartedSpace HL L] [MBManifold HL L]
  {EM : Type u} [AddCommGroup EM] [Module ℝ EM] [TopologicalSpace EM]
  [IsTopologicalAddGroup EM] [ContinuousSMul ℝ EM] [LocallyConvexSpace ℝ EM] [T2Space EM]
  {M : Type v} [TopologicalSpace M] [ChartedSpace EM M] [MBManifold EM M]

namespace CkMap

/-- The composition `γ ∘ η ∈ C^ℓ(K, M)` of `γ ∈ C^m(L, M)` and `η ∈ C^ℓ(K, L)`, for `ℓ ≤ m`. -/
def comp {ℓ m : ℕ} (γ : CkMap HL EM m L M) (η : CkMap HK HL ℓ K L) (hm : ℓ ≤ m) :
    CkMap HK EM ℓ K M :=
  ⟨γ ∘ η, γ.contMDiffMB.comp_of_le hm η.contMDiffMB⟩

@[simp]
theorem comp_apply {ℓ m : ℕ} (γ : CkMap HL EM m L M) (η : CkMap HK HL ℓ K L) (hm : ℓ ≤ m)
    (x : K) : comp γ η hm x = γ (η x) :=
  rfl

end CkMap

namespace SmoothMap

/-- The composition `γ ∘ η ∈ C^∞(K, M)` of smooth maps `γ ∈ C^∞(L, M)` and `η ∈ C^∞(K, L)`. -/
def comp (γ : SmoothMap HL EM L M) (η : SmoothMap HK HL K L) : SmoothMap HK EM K M :=
  ⟨γ ∘ η, fun ℓ ↦ (γ.2 ℓ).comp_of_le le_rfl (η.2 ℓ)⟩

@[simp]
theorem comp_apply (γ : SmoothMap HL EM L M) (η : SmoothMap HK HL K L) (x : K) :
    comp γ η x = γ (η x) :=
  rfl

end SmoothMap

section Generic

variable [CompactSpace K] [T2Space K] {P₁ P₂ : Type*} [TopologicalSpace P₁] [TopologicalSpace P₂]
  {B₁ : VaryingAtlas.{u, _, _} P₁} {B₂ : VaryingAtlas.{u, _, _} P₂}

omit [MBManifold EM M] in
/-- **Composition of evaluations** (the core of [GN26, Proposition 13.1.2(a)]): if `K` is compact
Hausdorff, `ε₁ : P₁ × L → M` is `C^{ℓ+k, ℓ+k}` and `ε₂ : P₂ × K → L` is `C^{k,ℓ}`, then
`((p₁, p₂), x) ↦ ε₁(p₁, ε₂(p₂, x))` is `C^{k,ℓ}` on `(P₁ × P₂) × K`. -/
theorem ContMDiffMB₂.comp_eval {k ℓ : ℕ} {ε₁ : P₁ × L → M} {ε₂ : P₂ × K → L}
    (hev₁ : ContMDiffMB₂ HL EM B₁ (ℓ + k) (ℓ + k) ε₁) (hev₂ : ContMDiffMB₂ HK HL B₂ k ℓ ε₂) :
    ContMDiffMB₂ HK EM (B₁.prod B₂) k ℓ (fun q ↦ ε₁ (q.1.1, ε₂ (q.1.2, q.2))) := by
  rintro ⟨γ₀, η₀⟩ x₀
  have : Nonempty K := ⟨x₀⟩
  have := locallyCompactSpace_of_compactSpace (H := HK) K
  -- `ε₁` at `(γ₀, ε₂(η₀, x₀))`: a box `U₁ × V₁` in charts `φ₁`, `d`, `c`, on which its local
  -- representative `R₁` is `C^{ℓ+k, ℓ+k}`, hence `C^{ℓ+k}`.
  obtain ⟨i₁, d, hd, c, hc, U₁, V₁, hγ₀, hy₀, hU₁, hV₁, hbox₁, hrep₁⟩ := hev₁ γ₀ (ε₂ (η₀, x₀))
  set φ₁ := B₁.chart i₁
  set R₁ := localRep₂ ε₁ φ₁ d c
  have hR₁ : ContDiffMBOn (k + ℓ) R₁ (U₁ ×ˢ V₁) := by
    rw [Nat.add_comm k ℓ]
    exact hrep₁.contDiffMBOn_prod hbox₁.isOpen_left hbox₁.isOpen_right
  -- `ε₂` in the preferred charts `φ₂` at `η₀`, `e'` at `x₀`, and the chart `d`.
  set i₂ := B₂.chartAt η₀
  set φ₂ := B₂.chart i₂
  have hη₀ : η₀ ∈ φ₂.source := B₂.mem_chartAt_source η₀
  set e' := chartAt HK x₀
  have he' : e' ∈ atlas HK K := _root_.chart_mem_atlas HK x₀
  have hx₀ : x₀ ∈ e'.source := _root_.mem_chart_source HK x₀
  set g : B₂.model i₂ × HK → L := fun p ↦ ε₂ (φ₂.symm p.1, e'.symm p.2)
  have hg : ContinuousOn g (φ₂.target ×ˢ e'.target) :=
    hev₂.continuous.comp_continuousOn
      ((φ₂.continuousOn_symm.comp (continuousOn_fst (s := φ₂.target ×ˢ e'.target))
          fun _ hp ↦ hp.1).prodMk
        (e'.continuousOn_symm.comp (continuousOn_snd (s := φ₂.target ×ˢ e'.target))
          fun _ hp ↦ hp.2))
  set Ω := (φ₂.target ×ˢ e'.target) ∩ g ⁻¹' (d.source ∩ d ⁻¹' V₁)
  have hΩ : IsOpen Ω := hg.isOpen_inter_preimage (φ₂.open_target.prod e'.open_target)
    (d.isOpen_inter_preimage hbox₁.isOpen_right)
  have hgx₀ : g (φ₂ η₀, e' x₀) = ε₂ (η₀, x₀) := by
    simp only [g, φ₂.left_inv hη₀, e'.left_inv hx₀]
  have hpΩ : (φ₂ η₀, e' x₀) ∈ Ω :=
    ⟨⟨φ₂.map_source hη₀, e'.map_source hx₀⟩, by rw [mem_preimage, hgx₀]; exact ⟨hy₀, hV₁⟩⟩
  obtain ⟨U₂', V₂, hU₂', hV₂, hη₀U₂', hx₀V₂, hsub⟩ := isOpen_prod_iff.1 hΩ _ _ hpΩ
  set U₂ := U₂' ∩ φ₂.target
  have hU₂ : IsOpen U₂ := hU₂'.inter φ₂.open_target
  have hΩ' : ∀ a ∈ U₂, ∀ b ∈ V₂, (a, b) ∈ Ω := fun a ha b hb ↦ hsub ⟨ha.1, hb⟩
  have hbox₂ : IsChartBox ε₂ φ₂ e' d U₂ V₂ :=
    ⟨hU₂, hV₂, inter_subset_right, fun b hb ↦ (hΩ' _ (by
      exact ⟨hη₀U₂', φ₂.map_source hη₀⟩) b hb).1.2,
      fun a ha b hb ↦ (hΩ' a ha b hb).2.1⟩
  set R₂ := localRep₂ ε₂ φ₂ e' d
  have hR₂ : ContDiffMBOn₂ k ℓ R₂ U₂ V₂ := hev₂.contDiffMBOn₂ i₂ he' hd hbox₂
  have hR₂V₁ : ∀ a ∈ U₂, ∀ b ∈ V₂, R₂ (a, b) ∈ V₁ := fun a ha b hb ↦ (hΩ' a ha b hb).2.2
  -- The composite `(a, b) ↦ R₁(a₁, R₂(a₂, b))` on `(U₁ × U₂) × V₂`.
  set U := U₁ ×ˢ U₂
  have hU : IsOpen U := hbox₁.isOpen_left.prod hU₂
  set f : (B₁.model i₁ × B₂.model i₂) × HK → B₁.model i₁ × HL :=
    fun q ↦ (q.1.1, R₂ (q.1.2, q.2))
  have hf : ContDiffMBOn₂ k ℓ f U V₂ := by
    have h1 : ContDiffMBOn₂ k ℓ (fun q : (B₁.model i₁ × B₂.model i₂) × HK ↦ q.1.1) U V₂ :=
      ContDiffMBOn.contDiffMBOn₂ hU hV₂ (ContDiffMBOn.congr_of_isOpen (hU.prod hV₂)
        (fun _ _ ↦ rfl) (((ContinuousLinearMap.fst ℝ (B₁.model i₁) (B₂.model i₂)).comp
          (ContinuousLinearMap.fst ℝ (B₁.model i₁ × B₂.model i₂) HK)).contDiffMBOn (k + ℓ) _))
    have h2 : ContDiffMBOn₂ k ℓ (fun q : (B₁.model i₁ × B₂.model i₂) × HK ↦ R₂ (q.1.2, q.2))
        U V₂ :=
      hR₂.comp_prodMap hU₂ hV₂ hU hV₂ (α := Prod.snd) (β := id)
        ((ContinuousLinearMap.snd ℝ _ _).contDiffMBOn k U)
        ((ContinuousLinearMap.id ℝ HK).contDiffMBOn ℓ V₂) (fun _ hq ↦ hq.2) (fun _ hb ↦ hb)
        (γ := id) isOpen_univ (fun n ↦ (ContinuousLinearMap.id ℝ HL).contDiffMBOn n univ)
        fun _ _ _ _ ↦ mem_univ _
    rw [← contDiffLC₂_iff_contDiffMBOn₂ hU hV₂] at h1 h2 ⊢
    exact (contDiffLC₂_prodMk_iff hU.hasDenseInterior hV₂.hasDenseInterior).2 ⟨h1, h2⟩
  have hfW : MapsTo f (U ×ˢ V₂) (U₁ ×ˢ V₁) := fun q hq ↦
    ⟨hq.1.1, hR₂V₁ _ hq.1.2 _ hq.2⟩
  have hF := contDiffMBOn₂_comp_left hU hV₂ (hbox₁.isOpen_left.prod hbox₁.isOpen_right) hf hR₁ hfW
  -- Reading back through the chart `d`.
  have hback : ∀ a ∈ U₂, ∀ b ∈ V₂, d.symm (R₂ (a, b)) = ε₂ (φ₂.symm a, e'.symm b) :=
    fun a ha b hb ↦ d.left_inv (hΩ' a ha b hb).2.1
  refine ⟨(i₁, i₂), e', he', c, hc, U, V₂, ⟨hγ₀, hη₀⟩, hx₀, ⟨hU₁, hη₀U₂', φ₂.map_source hη₀⟩,
    hx₀V₂, ⟨hU, hV₂, ?_, fun b hb ↦ (hΩ' _ ⟨hη₀U₂', φ₂.map_source hη₀⟩ b hb).1.2, ?_⟩, ?_⟩
  · exact prod_mono hbox₁.subset_left inter_subset_right
  · intro a ha b hb
    have := hbox₁.mapsTo a.1 ha.1 _ (hR₂V₁ a.2 ha.2 b hb)
    rw [hback a.2 ha.2 b hb] at this
    exact this
  · refine hF.congr hU hV₂ fun q hq ↦ ?_
    change c (ε₁ (φ₁.symm q.1.1, d.symm (R₂ (q.1.2, q.2)))) =
      c (ε₁ (φ₁.symm q.1.1, ε₂ (φ₂.symm q.1.2, e'.symm q.2)))
    rw [hback _ hq.1.2 _ hq.2]

end Generic

variable [CompactSpace K] [T2Space K] [CompactSpace L] [T2Space L]
  (AL : LocalAddition HL L) (AM : LocalAddition EM M)

namespace LocalAddition

/-- The map `((γ, η), x) ↦ γ(η(x))`, on `(C^{ℓ+k}(L, M) × C^ℓ(K, L)) × K`, is `C^{k,ℓ}`. -/
theorem contMDiffMB₂_comp_uncurry (k ℓ : ℕ) :
    ContMDiffMB₂ HK EM ((AM.mappingAtlasCk (H := HL) (M := L) (ℓ := ℓ + k)).prod
      (AL.mappingAtlasCk (H := HK) (M := K) (ℓ := ℓ))) k ℓ
      (fun q : (CkMap HL EM (ℓ + k) L M × CkMap HK HL ℓ K L) × K ↦ q.1.1 (q.1.2 q.2)) :=
  ContMDiffMB₂.comp_eval (AM.contMDiffMB₂_eval (ℓ + k)) (AL.contMDiffMB₂_eval k)

/-- **[GN26, Proposition 13.1.2(a)]**: the composition map
`Γ : C^{ℓ+k}(L, M) × C^ℓ(K, L) → C^ℓ(K, M)`, `(γ, η) ↦ γ ∘ η`, is `C^k`. -/
theorem contMDiffOn_comp (k ℓ : ℕ) :
    ((AM.mappingAtlasCk (H := HL) (M := L) (ℓ := ℓ + k)).prod
      (AL.mappingAtlasCk (H := HK) (M := K) (ℓ := ℓ))).ContMDiffOn
      (AM.mappingAtlasCk (H := HK) (M := K) (ℓ := ℓ)) k
      (fun p ↦ CkMap.comp p.1 p.2 (Nat.le_add_right ℓ k)) univ :=
  AM.contMDiffOn_mappingAtlasCk_iff.2 (contMDiffMB₂_comp_uncurry AL AM k ℓ)

/-- **[GN26, Proposition 13.1.2(a)]**, `C^∞` in the first factor: the composition map
`C^∞(L, M) × C^ℓ(K, L) → C^ℓ(K, M)`, `(γ, η) ↦ γ ∘ η`, is smooth. -/
theorem smooth_comp_smoothMap (ℓ : ℕ) :
    ((AM.mappingAtlasSm (H := HL) (M := L)).prod
      (AL.mappingAtlasCk (H := HK) (M := K) (ℓ := ℓ))).Smooth
      (AM.mappingAtlasCk (H := HK) (M := K) (ℓ := ℓ))
      (fun p ↦ CkMap.comp (SmoothMap.toCk ℓ p.1) p.2 le_rfl) := fun k ↦
  AM.contMDiffOn_mappingAtlasCk_iff.2
    (ContMDiffMB₂.comp_eval (AM.contMDiffMB₂_evalSm (ℓ + k) (ℓ + k)) (AL.contMDiffMB₂_eval k))

/-- **[GN26, Proposition 13.1.2(a)]**, `ℓ = ∞`: the composition map
`C^∞(L, M) × C^∞(K, L) → C^∞(K, M)`, `(γ, η) ↦ γ ∘ η`, is smooth. -/
theorem smooth_compSm :
    ((AM.mappingAtlasSm (H := HL) (M := L)).prod (AL.mappingAtlasSm (H := HK) (M := K))).Smooth
      (AM.mappingAtlasSm (H := HK) (M := K)) (fun p ↦ SmoothMap.comp p.1 p.2) := fun k ↦
  AM.contMDiffOn_mappingAtlasSm_iff.2 fun ℓ ↦
    ContMDiffMB₂.comp_eval (AM.contMDiffMB₂_evalSm (ℓ + k) (ℓ + k)) (AL.contMDiffMB₂_evalSm k ℓ)

end LocalAddition

end LocallyConvex.Manifolds
