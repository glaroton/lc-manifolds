/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.Metric.ProjectorMetric
public import LocallyConvexAnalysis.Krein.OrthoComplemented

/-!
# Orthogonal projector fields on submanifolds of a Krein space

Let `X` be a submanifold of a real Hilbert space `H` with a field of projectors `P`
(`LocallyConvexManifolds.Metric.ProjectorMetric`), and `β(x, y) = ⟪J x, y⟫` the form of a
fundamental symmetry `J`. If `P` is `β`-orthogonal, every tangent space is ortho-complemented in
the Krein space `(H, β)`, hence closed, nondegenerate and (for complete `H`) a Krein space, and the
projectors are continuous (`ProjectorField.isOrthoComplemented_of_isOrthogonal`,
`ProjectorField.isKreinSpace_of_isOrthogonal`, `ProjectorField.continuous_E_of_isOrthogonal`).

The theory of ortho-complemented subspaces of Krein spaces used here (J. Bognár, *Indefinite Inner
Product Spaces*, Springer (1974), Theorem V.3.4, p. 104) is in lc-analysis,
`LocallyConvexAnalysis/Krein/OrthoComplemented.lean`. Conversely, a closed tangent space that is a
Krein space has a continuous `β`-orthogonal projector
(`FundamentalSymmetry.exists_projector_of_kreinDecomposition`); whether these can be chosen
smoothly in `p` is not addressed.
-/

@[expose] public section

open scoped InnerProductSpace

noncomputable section

namespace LocallyConvex.Manifolds

open LocallyConvex.Analysis

/-! ### `β`-orthogonal projector fields on submanifolds of a Krein space -/

namespace ProjectorField

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {X : Set H} {S : Submodule ℝ H} {h : IsEmbeddedSubmanifold X S}

/-- The tangent space `T_p X` as a submodule: the range of the projector `P_p`. -/
def tangentSubmodule (P : ProjectorField h) (p : X) : Submodule ℝ H where
  carrier := h.tangentSpace p
  add_mem' {a b} ha hb := by
    rw [← P.E_eq_self ha, ← P.E_eq_self hb, ← P.map_add]
    exact P.mem_tangentSpace p _
  zero_mem' := by
    have h0 : P.E p 0 = 0 := by simpa using P.map_smul p 0 0
    rw [← h0]
    exact P.mem_tangentSpace p 0
  smul_mem' c a ha := by
    rw [← P.E_eq_self ha, ← P.map_smul]
    exact P.mem_tangentSpace p _

/-- **Orthogonal projector fields and ortho-complemented tangent spaces.** Let
`β(x, y) = ⟪J x, y⟫` be the form of a fundamental symmetry of a real Hilbert space `H`. If the
projector field `P` of a submanifold `X ⊆ H` is `β`-orthogonal, every tangent space `T_p X` is
ortho-complemented in the Krein space `(H, β)`: hence closed, nondegenerate, with bijective Gram
operator, and (if `H` is complete) a Krein space (`isKreinSpace_of_isOrthogonal`; Bognár,
Theorem V.3.4). -/
theorem isOrthoComplemented_of_isOrthogonal (J : FundamentalSymmetry ℝ H) (P : ProjectorField h)
    {β : LinearMap.BilinForm ℝ H} (hβ : ∀ x y, β x y = ⟪J.op x, y⟫_ℝ)
    (hP : P.IsOrthogonal β) (p : X) : J.IsOrthoComplemented (P.tangentSubmodule p) :=
  FundamentalSymmetry.isOrthoComplemented_of_projector (P.E p) (P.mem_tangentSpace p)
    fun w t ht ↦ by rw [← hβ, ← hβ]; exact hP p w t ht

/-- The tangent spaces of a submanifold of a real Krein space (`H` complete) with a
`β`-orthogonal projector field are Krein spaces for the restriction of `β` (Bognár,
Theorem V.3.4, "only if", through the complexification). -/
theorem isKreinSpace_of_isOrthogonal [CompleteSpace H] (J : FundamentalSymmetry ℝ H)
    (P : ProjectorField h) {β : LinearMap.BilinForm ℝ H} (hβ : ∀ x y, β x y = ⟪J.op x, y⟫_ℝ)
    (hP : P.IsOrthogonal β) (p : X) : IsKreinSpace J.form (P.tangentSubmodule p) :=
  (isOrthoComplemented_of_isOrthogonal J P hβ hP p).isKreinSpace

/-- A `β`-orthogonal projector of a submanifold of a Krein space (`H` complete) is continuous:
it is the unique `β`-orthogonal projector onto the ortho-complemented `T_p X`, whose continuity
comes from the closed graph theorem. -/
theorem continuous_E_of_isOrthogonal [CompleteSpace H] (J : FundamentalSymmetry ℝ H)
    (P : ProjectorField h) {β : LinearMap.BilinForm ℝ H} (hβ : ∀ x y, β x y = ⟪J.op x, y⟫_ℝ)
    (hP : P.IsOrthogonal β) (p : X) : Continuous (P.E p) := by
  have hL := isOrthoComplemented_of_isOrthogonal J P hβ hP p
  obtain ⟨Q, hQ, -, hQo⟩ := FundamentalSymmetry.isOrthoComplemented_iff_exists_projector.1 hL
  have : P.E p = Q := hL.eq_of_projector (P.mem_tangentSpace p) hQ
    (fun w t ht ↦ by rw [← hβ, ← hβ]; exact hP p w t ht) hQo
  rw [this]
  exact Q.continuous

end ProjectorField

end LocallyConvex.Manifolds
