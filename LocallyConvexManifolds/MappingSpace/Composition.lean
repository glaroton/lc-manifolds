/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.MappingSpace.ExponentialLaw

/-!
# Composition on the left in manifolds of mappings

Let `M` be a compact manifold and `N₁`, `N₂` manifolds with local additions. For a map
`h : N₁ → N₂` of class `C^{k+ℓ}`, the pushforward `C^ℓ(M, h) : C^ℓ(M, N₁) → C^ℓ(M, N₂)`,
`f ↦ h ∘ f`, is `C^k` ([GN26, Lemma 4.2.6]); for smooth `h`, it is smooth, on `C^ℓ(M, N₁)` and on
`C^∞(M, N₁)`.

## Main definitions

* `CkMap.compLeft h hh : C^ℓ(M, N₁) → C^ℓ(M, N₂)`, `f ↦ h ∘ f`, for `h` of class `C^ℓ`;
  `SmoothMap.compLeft h hh : C^∞(M, N₁) → C^∞(M, N₂)`, for smooth `h`.

## Main results

* `LocalAddition.contMDiffOn_compLeft`: [GN26, Lemma 4.2.6], `C^ℓ(M, h)` is `C^k` if `h` is
  `C^{k+ℓ}`; `LocalAddition.smooth_compLeft`: it is smooth if `h` is smooth.
* `LocalAddition.smooth_compLeftSm`: the same on `C^∞(M, N₁)`.

## Implementation notes

As in Glöckner–Neeb, the proof is the exponential law ([GN26, Theorem 4.2.2(a)],
`LocalAddition.contMDiffOn_mappingAtlasCk_iff`): `C^ℓ(M, h)^∧ = h ∘ ε` with the evaluation map
`ε`, which is `C^{k,ℓ}` ([GN26, Theorem 4.2.2(c)]), and the chain rule for `C^{k,ℓ}` maps
([GN26, Proposition 3.5.27], `ContMDiffMB₂.comp_left`).

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set
open LocallyConvex.Analysis

noncomputable section

universe u v w

namespace LocallyConvex.Manifolds

variable {H : Type u} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [IsTopologicalAddGroup H]
  [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [MBManifold H M]
  {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁] [IsTopologicalAddGroup E₁]
  [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  {N₁ : Type v} [TopologicalSpace N₁] [ChartedSpace E₁ N₁] [MBManifold E₁ N₁]
  {E₂ : Type u} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂] [IsTopologicalAddGroup E₂]
  [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  {N₂ : Type w} [TopologicalSpace N₂] [ChartedSpace E₂ N₂] [MBManifold E₂ N₂]

/-- `h ∘ f` is `C^ℓ` when `f` and `h` are. -/
theorem ContMDiffMB.comp_of_le {ℓ m : ℕ} {f : M → N₁} {h : N₁ → N₂}
    (hh : ContMDiffMB E₁ E₂ m h) (hm : ℓ ≤ m) (hf : ContMDiffMB H E₁ ℓ f) :
    ContMDiffMB H E₂ ℓ (h ∘ f) :=
  ContMDiffMBOn.comp isOpen_univ isOpen_univ ⟨hh.1, fun x hx ↦ (hh.2 x hx).of_le hm⟩ hf
    (mapsTo_univ _ _)

namespace CkMap

/-- **Composition on the left** `C^ℓ(M, h) : C^ℓ(M, N₁) → C^ℓ(M, N₂)`, `f ↦ h ∘ f`, for a map
`h : N₁ → N₂` of class `C^m` with `ℓ ≤ m`. -/
def compLeft {ℓ m : ℕ} (h : N₁ → N₂) (hh : ContMDiffMB E₁ E₂ m h) (hm : ℓ ≤ m) :
    CkMap H E₁ ℓ M N₁ → CkMap H E₂ ℓ M N₂ :=
  fun f ↦ ⟨h ∘ f, hh.comp_of_le hm f.contMDiffMB⟩

@[simp]
theorem compLeft_apply {ℓ m : ℕ} (h : N₁ → N₂) (hh : ContMDiffMB E₁ E₂ m h) (hm : ℓ ≤ m)
    (f : CkMap H E₁ ℓ M N₁) (x : M) : compLeft h hh hm f x = h (f x) :=
  rfl

end CkMap

namespace SmoothMap

/-- **Composition on the left** `C^∞(M, h) : C^∞(M, N₁) → C^∞(M, N₂)`, `f ↦ h ∘ f`, for a smooth
map `h : N₁ → N₂`. -/
def compLeft (h : N₁ → N₂) (hh : SmoothMBM E₁ E₂ h) :
    SmoothMap H E₁ M N₁ → SmoothMap H E₂ M N₂ :=
  fun f ↦ ⟨h ∘ f, fun ℓ ↦ (hh ℓ).comp_of_le le_rfl (f.2 ℓ)⟩

@[simp]
theorem compLeft_apply (h : N₁ → N₂) (hh : SmoothMBM E₁ E₂ h) (f : SmoothMap H E₁ M N₁) (x : M) :
    compLeft h hh f x = h (f x) :=
  rfl

end SmoothMap

variable [CompactSpace M] [T2Space M] (A₁ : LocalAddition E₁ N₁) (A₂ : LocalAddition E₂ N₂)

namespace LocalAddition

/-- **[GN26, Lemma 4.2.6]**: for `h : N₁ → N₂` of class `C^{k+ℓ}`, composition on the left
`C^ℓ(M, h) : C^ℓ(M, N₁) → C^ℓ(M, N₂)`, `f ↦ h ∘ f`, is `C^k`. -/
theorem contMDiffOn_compLeft {k ℓ : ℕ} {h : N₁ → N₂} (hh : ContMDiffMB E₁ E₂ (k + ℓ) h) :
    A₁.mappingAtlasCk.ContMDiffOn A₂.mappingAtlasCk k
      (CkMap.compLeft (H := H) (M := M) (ℓ := ℓ) h hh (Nat.le_add_left ℓ k)) univ :=
  A₂.contMDiffOn_mappingAtlasCk_iff.2 ((A₁.contMDiffMB₂_eval k).comp_left hh)

/-- **[GN26, Lemma 4.2.6]**, smooth case: for smooth `h : N₁ → N₂`, composition on the left
`C^ℓ(M, N₁) → C^ℓ(M, N₂)` is smooth. -/
theorem smooth_compLeft {ℓ : ℕ} {h : N₁ → N₂} (hh : SmoothMBM E₁ E₂ h) :
    A₁.mappingAtlasCk.Smooth A₂.mappingAtlasCk
      (CkMap.compLeft (H := H) (M := M) (ℓ := ℓ) h (hh ℓ) le_rfl) := fun k ↦
  A₂.contMDiffOn_mappingAtlasCk_iff.2 ((A₁.contMDiffMB₂_eval k).comp_left (hh (k + ℓ)))

/-- **[GN26, Lemma 4.2.6]**, `ℓ = ∞`: for smooth `h : N₁ → N₂`, composition on the left
`C^∞(M, N₁) → C^∞(M, N₂)` is smooth. -/
theorem smooth_compLeftSm {h : N₁ → N₂} (hh : SmoothMBM E₁ E₂ h) :
    A₁.mappingAtlasSm.Smooth A₂.mappingAtlasSm
      (SmoothMap.compLeft (H := H) (M := M) h hh) := fun k ↦
  A₂.contMDiffOn_mappingAtlasSm_iff.2 fun ℓ ↦
    (A₁.contMDiffMB₂_evalSm k ℓ).comp_left (hh (k + ℓ))

end LocalAddition

end LocallyConvex.Manifolds
