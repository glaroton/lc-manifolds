/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.Analytic.Bundle
public import LocallyConvexManifolds.Submanifold.LocalAddition

/-!
# Split real analytic submanifolds and real analytic local additions

Let `F` be a real locally convex space (no completeness) and `S ⊆ F` a *complemented* subspace,
given by a continuous linear projection `P : F → S`. A subset `X ⊆ F` is a *split real analytic
submanifold* modeled on `S` (`IsSplitAnalyticSubmanifold`) if every point of `X` lies in a real
analytic slice chart: a real analytic diffeomorphism `φ` between open subsets of `F` with
`φ(U ∩ X) = φ(U) ∩ S`.

This is the real analytic counterpart of `LocallyConvexManifolds.Submanifold.LocalAddition`; the
proofs follow the same pattern, with `RealAnalyticOn` in place of `ContDiffMBOn`.

## Main definitions

* `IsAnalyticSliceChart`, `IsSplitAnalyticSubmanifold`: real analytic slice charts and split real
  analytic submanifolds.
* `IsSplitAnalyticSubmanifold.chartedSpace`: the restrictions of the real analytic slice charts,
  as an atlas of `X`.
* `AnalyticAmbientAddition`: real analytic maps `σ`, `τ` on open subsets of `F × F` such that
  `w ↦ σ(p, w)` is a bijection from part of `T_p X` onto part of `X` with inverse
  `q ↦ τ(p, q)`; `AnalyticAmbientAddition.toLocalAddition` is the local addition
  `Σ(v) = σ(π v, w)` they define.

## Main results

* `IsSplitAnalyticSubmanifold.realAnalyticManifold`: `X` is a real analytic manifold modeled on
  `S` ([GN26, Definition 3.1.10], with `r = ω`);
* `IsSplitAnalyticSubmanifold.realAnalyticMOn_of_val`,
  `IsSplitAnalyticSubmanifold.realAnalyticMOn_val`: a map into `X` is real analytic iff it is real
  analytic into `F`;
* `IsSplitAnalyticSubmanifold.realAnalyticMOn_ambient`: the ambient map `TX → F × F`,
  `v ↦ (π v, w)` (`w ∈ T_p X ⊆ F` the ambient vector of `v`), is real analytic;
  `IsSplitAnalyticSubmanifold.realAnalyticMOn_of_ambient`: a map into `TX` is real analytic as
  soon as its composition with the ambient map is;
* `AnalyticAmbientAddition.isRealAnalytic_toLocalAddition`: **the local addition of an analytic
  ambient addition is a real analytic local addition** ([GN26, p. 325], after Definition 3.8.11).

## Implementation notes and infinite-dimensional subtleties

* **Corestriction.** For smooth maps, a map with values in a closed subspace `S` is smooth into
  `S` (`ContDiffMBOn.codRestrict`). For real analytic maps in Milnor's sense this is less clear:
  a complex analytic extension to `D_ℂ` of a map with values in `S` need not take values in
  `S_ℂ`; one would need the identity theorem and the Hahn–Banach theorem
  (`S = ⋂ ker λ`). We avoid the issue by assuming `S` complemented: then `g = P ∘ g` for maps
  with values in `S`. In finite dimensions, and for closed subspaces of Hilbert spaces, this is
  no restriction; for general locally convex (even Banach) spaces it is.
* The charted space structure is not an instance (it depends on the proof `h`); the statements
  take an instance `cs : ChartedSpace S X` with the hypothesis `cs = h.chartedSpace`. Its atlas
  consists of the *real analytic* slice charts; it differs from the atlas of all smooth slice
  charts used by `IsEmbeddedSubmanifold.chartedSpace`, so the two tangent bundles are different
  types, although `h.toEmbedded : IsEmbeddedSubmanifold X S` holds and the tangent spaces
  `T_p X ⊆ F` agree (`IsEmbeddedSubmanifold.tangentSpace`).
* Glöckner–Neeb do not discuss ambient formulas for local additions on submanifolds. We do not
  claim this argument is new.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]; the numbers refer to
  arXiv:2602.12362v1.
-/

@[expose] public section

open Set Filter Function TopologicalSpace
open scoped Topology Manifold
open LocallyConvex.Analysis

noncomputable section

universe u

namespace LocallyConvex.Manifolds

variable {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

section Definitions

variable (X : Set F) (S : Submodule ℝ F)

/-- `φ` is a *real analytic slice chart* for `X` with model `S`: a real analytic diffeomorphism
between open subsets of `F` with `φ(U ∩ X) = φ(U) ∩ S`. -/
def IsAnalyticSliceChart (φ : OpenPartialHomeomorph F F) : Prop :=
  φ ∈ realAnalyticGroupoid F ∧ ∀ q ∈ φ.source, (q ∈ X ↔ φ q ∈ S)

/-- `X ⊆ F` is a **split real analytic submanifold** modeled on `S`: `S` is complemented
(there is a continuous linear projection `F → S`), and every point of `X` lies in a real analytic
slice chart. -/
structure IsSplitAnalyticSubmanifold : Prop where
  exists_proj : ∃ P : F →L[ℝ] S, ∀ s : S, P s = s
  exists_sliceChart : ∀ p ∈ X, ∃ φ, IsAnalyticSliceChart X S φ ∧ p ∈ φ.source

end Definitions

variable {X : Set F} {S : Submodule ℝ F}

/-- A real analytic slice chart is a (smooth) slice chart. -/
theorem IsAnalyticSliceChart.isSliceChart {φ : OpenPartialHomeomorph F F}
    (hφ : IsAnalyticSliceChart X S φ) : IsSliceChart X S φ :=
  ⟨StructureGroupoid.mem_maximalAtlas_of_mem_groupoid _
    (StructureGroupoid.le_iff.1 (realAnalyticGroupoid_le_mbGroupoid F) φ hφ.1), hφ.2⟩

/-- A real analytic slice chart is real analytic. -/
theorem IsAnalyticSliceChart.realAnalyticOn {φ : OpenPartialHomeomorph F F}
    (hφ : IsAnalyticSliceChart X S φ) : RealAnalyticOn φ φ.source :=
  hφ.1.1

/-- The inverse of a real analytic slice chart is real analytic. -/
theorem IsAnalyticSliceChart.realAnalyticOn_symm {φ : OpenPartialHomeomorph F F}
    (hφ : IsAnalyticSliceChart X S φ) : RealAnalyticOn φ.symm φ.target :=
  hφ.1.2

/-- The local parametrization `ψ = φ⁻¹|_S` of a real analytic slice chart is real analytic. -/
theorem IsAnalyticSliceChart.realAnalyticOn_param {φ : OpenPartialHomeomorph F F}
    (hφ : IsAnalyticSliceChart X S φ) :
    RealAnalyticOn (ProjectorField.param φ) (Subtype.val ⁻¹' φ.target : Set S) :=
  hφ.realAnalyticOn_symm.comp (S.subtypeL.realAnalyticOn _) fun _ hy ↦ hy

namespace IsSplitAnalyticSubmanifold

variable (h : IsSplitAnalyticSubmanifold X S)

/-- The continuous linear projection `P : F → S`. -/
def proj : F →L[ℝ] S := h.exists_proj.choose

theorem proj_coe (s : S) : h.proj s = s := h.exists_proj.choose_spec s

/-- `x ∈ S` iff `P x = x`. -/
theorem mem_iff_proj (x : F) : x ∈ S ↔ (h.proj x : F) = x :=
  ⟨fun hx ↦ by rw [show x = ((⟨x, hx⟩ : S) : F) from rfl, h.proj_coe], fun hx ↦ hx ▸ (h.proj x).2⟩

include h in
/-- The model space is closed. -/
theorem isClosed : IsClosed (S : Set F) := by
  have : (S : Set F) = {x | (h.proj x : F) = x} := Set.ext h.mem_iff_proj
  rw [this]
  exact isClosed_eq (continuous_subtype_val.comp h.proj.continuous) continuous_id

include h in
/-- A split real analytic submanifold is an embedded submanifold. -/
theorem toEmbedded : IsEmbeddedSubmanifold X S :=
  ⟨h.isClosed, fun p hp ↦
    let ⟨φ, hφ, hpφ⟩ := h.exists_sliceChart p hp; ⟨φ, hφ.isSliceChart, hpφ⟩⟩

include h in
/-- **Corestriction through the projection.** A map into `S` is real analytic as soon as it is
real analytic as a map into `F`. -/
theorem realAnalyticOn_of_coe {D : Type u} [AddCommGroup D] [Module ℝ D] [TopologicalSpace D]
    [IsTopologicalAddGroup D] [ContinuousSMul ℝ D] [LocallyConvexSpace ℝ D] [T2Space D]
    {g : D → S} {V : Set D} (hg : RealAnalyticOn (fun y ↦ (g y : F)) V) :
    RealAnalyticOn g V :=
  realAnalyticOn_congr (fun y _ ↦ h.proj_coe (g y)) (RealAnalyticOn.clm_comp hg h.proj)

/-- The real analytic slice chart of `F` behind the preferred chart of `X` at `p`. -/
def phi (p : X) : OpenPartialHomeomorph F F := (h.exists_sliceChart p p.2).choose

theorem isAnalyticSliceChart_phi (p : X) : IsAnalyticSliceChart X S (h.phi p) :=
  (h.exists_sliceChart p p.2).choose_spec.1

theorem mem_phi_source (p : X) : (p : F) ∈ (h.phi p).source :=
  (h.exists_sliceChart p p.2).choose_spec.2

/-- The charted space structure of a split real analytic submanifold, by the induced real
analytic slice charts. -/
@[instance_reducible]
def chartedSpace : ChartedSpace S X where
  atlas := {e | ∃ (φ : OpenPartialHomeomorph F F) (hφ : IsAnalyticSliceChart X S φ) (p₀ : X),
    e = sliceChart hφ.isSliceChart p₀}
  chartAt p := sliceChart (h.isAnalyticSliceChart_phi p).isSliceChart p
  mem_chart_source p := h.mem_phi_source p
  chart_mem_atlas p := ⟨_, h.isAnalyticSliceChart_phi p, p, rfl⟩

include h in
/-- The transition maps between induced real analytic charts are real analytic. -/
theorem realAnalyticOn_sliceChart_transition {φ ψ : OpenPartialHomeomorph F F}
    (hφ : IsAnalyticSliceChart X S φ) (hψ : IsAnalyticSliceChart X S ψ) (p₀ p₁ : X) :
    RealAnalyticOn ⇑((sliceChart hφ.isSliceChart p₀).symm ≫ₕ sliceChart hψ.isSliceChart p₁)
      ((sliceChart hφ.isSliceChart p₀).symm ≫ₕ sliceChart hψ.isSliceChart p₁).source := by
  set e := sliceChart hφ.isSliceChart p₀
  set e' := sliceChart hψ.isSliceChart p₁
  have hsub : ∀ y ∈ (e.symm ≫ₕ e').source,
      (y : F) ∈ φ.target ∩ φ.symm ⁻¹' ψ.source ∧ ((e.symm y : X) : F) = φ.symm y := by
    rintro y ⟨hy, hy'⟩
    have hy₁ : (y : F) ∈ φ.target := hy
    have hc := sliceChart_symm_apply_coe hφ.isSliceChart p₀ hy₁
    refine ⟨⟨hy₁, ?_⟩, hc⟩
    have : ((e.symm y : X) : F) ∈ ψ.source := hy'
    rwa [hc] at this
  have htr : RealAnalyticOn (ψ ∘ φ.symm) (φ.target ∩ φ.symm ⁻¹' ψ.source) := by
    have := ((realAnalyticGroupoid F).trans ((realAnalyticGroupoid F).symm hφ.1) hψ.1).1
    rwa [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.coe_trans] at this
  have hh : RealAnalyticOn ((ψ ∘ φ.symm) ∘ S.subtypeL) (e.symm ≫ₕ e').source :=
    htr.comp (S.subtypeL.realAnalyticOn _) fun y hy ↦ (hsub y hy).1
  refine h.realAnalyticOn_of_coe (realAnalyticOn_congr (fun y hy ↦ ?_) hh)
  change ψ (φ.symm (y : F)) = ((sliceChart hψ.isSliceChart p₁ (e.symm y) : S) : F)
  rw [sliceChart_apply_coe hψ.isSliceChart p₁ (by rw [(hsub y hy).2]; exact (hsub y hy).1.2),
    (hsub y hy).2]

/-- **A split real analytic submanifold is a real analytic manifold** modeled on `S`. -/
theorem realAnalyticManifold : letI := h.chartedSpace; RealAnalyticManifold S X := by
  let := h.chartedSpace
  refine ⟨?_⟩
  rintro _ _ ⟨φ, hφ, p₀, rfl⟩ ⟨ψ, hψ, p₁, rfl⟩
  refine ⟨h.realAnalyticOn_sliceChart_transition hφ hψ p₀ p₁, ?_⟩
  have h' := h.realAnalyticOn_sliceChart_transition hψ hφ p₁ p₀
  rw [OpenPartialHomeomorph.trans_source] at h'
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm,
    OpenPartialHomeomorph.trans_target, ← OpenPartialHomeomorph.symm_source,
    OpenPartialHomeomorph.symm_target]
  exact h'

variable [cs : ChartedSpace S X] [MBManifold S X]

include h in
/-- **Maps into a split real analytic submanifold.** A map into `X` is real analytic as soon as
it is real analytic as a map into `F`: in a slice chart `φ`, its local representative is
`P ∘ φ ∘ g`. -/
theorem realAnalyticMOn_of_val (hc : cs = h.chartedSpace) {G : Type u} [AddCommGroup G]
    [Module ℝ G] [TopologicalSpace G] [IsTopologicalAddGroup G] [ContinuousSMul ℝ G]
    [LocallyConvexSpace ℝ G] [T2Space G] {Y : Type*} [TopologicalSpace Y] [ChartedSpace G Y]
    {g : Y → X} {U : Set Y} (hg : RealAnalyticMOn (E := G) (F := F) (Subtype.val ∘ g) U) :
    RealAnalyticMOn (E := G) (F := S) g U := by
  subst hc
  let _ : ChartedSpace S X := h.chartedSpace
  refine ⟨Topology.IsInducing.subtypeVal.continuousOn_iff.mpr hg.1, fun x hx ↦ ?_⟩
  have hφ := h.isAnalyticSliceChart_phi (g x)
  set c := chartAt G x
  have hD : chartDomain g U c (chartAt S (g x)) ⊆ chartDomain (Subtype.val ∘ g) U c
      (chartAt F ((Subtype.val ∘ g) x)) := fun y hy ↦ ⟨hy.1, hy.2.1, mem_univ _⟩
  have h1 : RealAnalyticOn (Subtype.val ∘ g ∘ c.symm) (chartDomain g U c (chartAt S (g x))) :=
    (hg.2 x hx).mono hD
  have h2 : RealAnalyticOn (h.phi (g x) ∘ (Subtype.val ∘ g ∘ c.symm))
      (chartDomain g U c (chartAt S (g x))) :=
    hφ.realAnalyticOn.comp h1 fun y hy ↦ hy.2.2
  exact h.realAnalyticOn_of_coe (realAnalyticOn_congr
    (fun y hy ↦ (sliceChart_apply_coe hφ.isSliceChart (g x) hy.2.2).symm) h2)

include h in
/-- The inclusion `X → F` is real analytic. -/
theorem realAnalyticMOn_val (hc : cs = h.chartedSpace) :
    RealAnalyticMOn (E := S) (F := F) (Subtype.val : X → F) univ := by
  subst hc
  let _ : ChartedSpace S X := h.chartedSpace
  refine ⟨continuous_subtype_val.continuousOn, fun p _ ↦ ?_⟩
  have hφ := h.isAnalyticSliceChart_phi p
  refine realAnalyticOn_congr (fun y hy ↦ ?_)
    (hφ.realAnalyticOn_param.mono fun y (hy : y ∈ chartDomain _ _ _ _) ↦ hy.1)
  change (h.phi p).symm (y : F) = ((sliceChart hφ.isSliceChart p).symm y : F)
  rw [sliceChart_symm_apply_coe hφ.isSliceChart p hy.1]

/-! ### Ambient tangent vectors -/

/-- The tangent space `T_p X ⊆ F` (as for embedded submanifolds). -/
abbrev tangentSpace (p : X) : Set F := h.toEmbedded.tangentSpace p

omit cs [MBManifold S X] in
/-- The tangent space can be read in the preferred real analytic slice chart. -/
theorem mem_tangentSpace_iff (p : X) (w : F) :
    w ∈ h.tangentSpace p ↔ dMB (h.phi p) ((p : F), w) ∈ S :=
  h.toEmbedded.mem_tangentSpace_iff p (h.isAnalyticSliceChart_phi p).isSliceChart
    (h.mem_phi_source p) w

/-- The ambient vector `w ∈ T_p X ⊆ F` of a tangent vector `v` of `X` at `p`: in the preferred
slice chart `φ` at `p`, `w = dφ⁻¹(φ p)(v)`. -/
def ambVec (v : TangentBundle S X) : F :=
  dMB (ProjectorField.param (h.phi v.proj)) (chartAt S v.proj v.proj, v.vec)

/-- The tangent vector of `X` at `p` with ambient vector `w` (meant for `w ∈ T_p X`). -/
def ofAmb (p : X) (w : F) : TangentBundle S X :=
  ⟨p, h.proj (dMB (h.phi p) ((p : F), w))⟩

/-- In a real analytic slice chart `φ`, the fiber coordinate of a tangent vector is `dφ` of its
ambient vector. -/
theorem coe_coordAt_slice (hc : cs = h.chartedSpace) {φ : OpenPartialHomeomorph F F}
    (hφ : IsAnalyticSliceChart X S φ) (p₀ : X)
    (hmem : sliceChart hφ.isSliceChart p₀ ∈ atlas S X)
    (v : TangentBundle S X) (hv : (v.proj : F) ∈ φ.source) :
    ((coordAt ⟨sliceChart hφ.isSliceChart p₀, hmem⟩ v : S) : F) =
      dMB φ ((v.proj : F), h.ambVec v) := by
  subst hc
  let _ : ChartedSpace S X := h.chartedSpace
  set p := v.proj
  set ψ := h.phi p
  have hψ : IsSliceChart X S ψ := (h.isAnalyticSliceChart_phi p).isSliceChart
  set i : atlas S X := ⟨sliceChart hφ.isSliceChart p₀, hmem⟩
  set c : atlas S X := ⟨chartAt S p, chart_mem_atlas S p⟩
  set W := c.1.target ∩ c.1.symm ⁻¹' i.1.source
  have hW : IsOpen W := isOpen_transition_domain c i
  have hpc : p ∈ c.1.source := mem_chart_source S p
  have hcp : c.1 p ∈ W := ⟨c.1.map_source hpc, by
    rw [mem_preimage, c.1.left_inv hpc]; exact hv⟩
  have hcpψ : ((c.1 p : S) : F) = ψ p := sliceChart_apply_coe hψ p (h.mem_phi_source p)
  have hW' : ∀ y ∈ W, (y : F) ∈ ψ.target ∧
      ProjectorField.param ψ y ∈ φ.source ∧
      ((i.1 (c.1.symm y) : S) : F) = φ (ProjectorField.param ψ y) := by
    intro y hy
    have hyψ : (y : F) ∈ ψ.target := hy.1
    have h1 : ((c.1.symm y : X) : F) = ψ.symm y := sliceChart_symm_apply_coe hψ p hyψ
    have h2 : ((c.1.symm y : X) : F) ∈ φ.source := hy.2
    refine ⟨hyψ, ?_, ?_⟩
    · change ψ.symm (y : F) ∈ φ.source
      rw [← h1]; exact h2
    · rw [sliceChart_apply_coe hφ.isSliceChart p₀ h2, h1]; rfl
  have hτ : ContDiffMBOn 1 (i.1 ∘ c.1.symm) W := smoothMBOn_transition' c i 1
  have hev : Subtype.val ∘ (i.1 ∘ c.1.symm) =ᶠ[𝓝 (c.1 p)] φ ∘ ProjectorField.param ψ :=
    Filter.eventuallyEq_of_mem (hW.mem_nhds hcp) fun y hy ↦ (hW' y hy).2.2
  have hpar : ContDiffMBOn 1 (ProjectorField.param ψ) W :=
    ((ProjectorField.smoothMBOn_param hψ) 1).mono fun y hy ↦ (hW' y hy).1
  change ((dMB (i.1 ∘ c.1.symm) (c.1 p, v.vec) : S) : F) = _
  rw [ProjectorField.coe_dMB_of_subtype hτ hcp, dMB_congr_of_eventuallyEq hev,
    ContDiffMBOn.dMB_comp φ.open_source
      ((smoothMBOn_of_mem_maximalAtlas hφ.isSliceChart.1) 1) hpar
      (fun y hy ↦ (hW' y hy).2.1) hcp]
  have hpp : ProjectorField.param ψ (c.1 p) = p := by
    change ψ.symm ((c.1 p : S) : F) = p
    rw [hcpψ, ψ.left_inv (h.mem_phi_source p)]
  rw [hpp]
  rfl

/-- The fiber coordinate in the preferred chart is `dφ` of the ambient vector. -/
theorem dMB_phi_ambVec (hc : cs = h.chartedSpace) (v : TangentBundle S X) :
    dMB (h.phi v.proj) ((v.proj : F), h.ambVec v) = (v.vec : F) := by
  subst hc
  let _ : ChartedSpace S X := h.chartedSpace
  have := h.coe_coordAt_slice rfl (h.isAnalyticSliceChart_phi v.proj) v.proj
    (chart_mem_atlas S v.proj) v (h.mem_phi_source v.proj)
  rw [← this]
  exact congrArg Subtype.val (coordAt_chartAt_of_proj_eq (E := S) rfl)

/-- Ambient vectors are tangent. -/
theorem ambVec_mem_tangentSpace (hc : cs = h.chartedSpace) (v : TangentBundle S X) :
    h.ambVec v ∈ h.tangentSpace v.proj := by
  rw [mem_tangentSpace_iff, h.dMB_phi_ambVec hc v]
  exact (v.vec).2

/-- The ambient vector of `ofAmb p w` is `w`, for `w ∈ T_p X`. -/
theorem ambVec_ofAmb (hc : cs = h.chartedSpace) {p : X} {w : F} (hw : w ∈ h.tangentSpace p) :
    h.ambVec (h.ofAmb p w) = w := by
  subst hc
  let _ : ChartedSpace S X := h.chartedSpace
  have hψ := (h.isAnalyticSliceChart_phi p).isSliceChart
  have hw' : dMB (h.phi p) ((p : F), w) ∈ S := (h.mem_tangentSpace_iff p w).1 hw
  have hcp : ((chartAt S p p : S) : F) = h.phi p p :=
    sliceChart_apply_coe hψ p (h.mem_phi_source p)
  have hy : ((chartAt S p p : S) : F) ∈ (h.phi p).target := by
    rw [hcp]; exact (h.phi p).map_source (h.mem_phi_source p)
  change dMB (ProjectorField.param (h.phi p))
    (chartAt S p p, h.proj (dMB (h.phi p) ((p : F), w))) = w
  rw [ProjectorField.dMB_param hψ hy, hcp, show ((h.proj (dMB (h.phi p) ((p : F), w)) : S) : F) =
    dMB (h.phi p) ((p : F), w) from (h.mem_iff_proj _).1 hw']
  exact dMB_symm_dMB_chart hψ.1 (h.mem_phi_source p) w

/-- A tangent vector is recovered from its ambient vector. -/
theorem ofAmb_ambVec (hc : cs = h.chartedSpace) (v : TangentBundle S X) :
    h.ofAmb v.proj (h.ambVec v) = v := by
  refine TangentBundle.ext_vec rfl ?_
  change h.proj (dMB (h.phi v.proj) ((v.proj : F), h.ambVec v)) = v.vec
  rw [h.dMB_phi_ambVec hc v, h.proj_coe]

/-- The ambient map `TX → F × F`, `v ↦ (π v, ambVec v)`. -/
def ambient (v : TangentBundle S X) : F × F := ((v.proj : F), h.ambVec v)

omit [MBManifold S X] cs in
/-- The local formula `(y, s) ↦ (ψ y, dψ(y) s)` of the ambient map in a real analytic slice chart
is real analytic. -/
theorem realAnalyticOn_ambientLocal {φ : OpenPartialHomeomorph F F}
    (hφ : IsAnalyticSliceChart X S φ) :
    RealAnalyticOn (IsEmbeddedSubmanifold.ambientLocal φ)
      ((Subtype.val ⁻¹' φ.target : Set S) ×ˢ (univ : Set S)) :=
  RealAnalyticOn.prodMk
    (hφ.realAnalyticOn_param.comp ((ContinuousLinearMap.fst ℝ S S).realAnalyticOn _)
      fun _ hq ↦ hq.1)
    (RealAnalyticOn.dMB hφ.realAnalyticOn_param (ProjectorField.isOpen_dom φ))

/-- Over a real analytic slice chart, `ambient` is `ambientLocal` composed with the tangent
chart. -/
theorem ambient_eq_ambientLocal (hc : cs = h.chartedSpace) {φ : OpenPartialHomeomorph F F}
    (hφ : IsAnalyticSliceChart X S φ) (p₀ : X) (hmem : sliceChart hφ.isSliceChart p₀ ∈ atlas S X)
    (v : TangentBundle S X) (hv : (v.proj : F) ∈ φ.source) :
    h.ambient v = IsEmbeddedSubmanifold.ambientLocal φ
      (tangentChart ⟨sliceChart hφ.isSliceChart p₀, hmem⟩ (sliceChart hφ.isSliceChart p₀) v) := by
  rw [tangentChart_self_apply (E := S) ⟨sliceChart hφ.isSliceChart p₀, hmem⟩ v]
  refine Prod.ext ?_ ?_
  · change ((v.proj : X) : F) = φ.symm ((sliceChart hφ.isSliceChart p₀ v.proj : S) : F)
    rw [sliceChart_apply_coe hφ.isSliceChart p₀ hv, φ.left_inv hv]
  · have hy : ((sliceChart hφ.isSliceChart p₀ v.proj : S) : F) ∈ φ.target := by
      rw [sliceChart_apply_coe hφ.isSliceChart p₀ hv]; exact φ.map_source hv
    change h.ambVec v = dMB (ProjectorField.param φ) (sliceChart hφ.isSliceChart p₀ v.proj,
      coordAt ⟨sliceChart hφ.isSliceChart p₀, hmem⟩ v)
    rw [ProjectorField.dMB_param hφ.isSliceChart hy, h.coe_coordAt_slice hc hφ p₀ hmem v hv,
      sliceChart_apply_coe hφ.isSliceChart p₀ hv, dMB_symm_dMB_chart hφ.isSliceChart.1 hv]

/-- **The ambient map `TX → F × F` is real analytic.** -/
theorem realAnalyticMOn_ambient (hc : cs = h.chartedSpace) :
    RealAnalyticMOn (E := S × S) (F := F × F) h.ambient univ := by
  subst hc
  let _ : ChartedSpace S X := h.chartedSpace
  have key : ∀ v₀ : TangentBundle S X, ∃ φ : OpenPartialHomeomorph F F,
      IsAnalyticSliceChart X S φ ∧
      (∀ v ∈ (chartAt (S × S) v₀).source,
        h.ambient v = IsEmbeddedSubmanifold.ambientLocal φ (chartAt (S × S) v₀ v)) ∧
      (chartAt (S × S) v₀).target ⊆ (Subtype.val ⁻¹' φ.target : Set S) ×ˢ univ := by
    intro v₀
    refine ⟨h.phi v₀.proj, h.isAnalyticSliceChart_phi v₀.proj, fun v hv ↦ ?_, fun q hq ↦ ?_⟩
    · have hv' : v.proj ∈ (chartAt S v₀.proj).source :=
        ((mem_tangentChart_source _ _ v).1 hv).1
      exact h.ambient_eq_ambientLocal rfl (h.isAnalyticSliceChart_phi v₀.proj) v₀.proj
        (chart_mem_atlas S _) v hv'
    · exact ⟨((mem_tangentChart_target _ _ q).1 hq).1, mem_univ _⟩
  have hcont : Continuous h.ambient := by
    refine continuous_iff_continuousAt.2 fun v₀ ↦ ?_
    obtain ⟨φ, hφ, heq, hsub⟩ := key v₀
    set κ := chartAt (S × S) v₀
    have hv₀ : v₀ ∈ κ.source := mem_chart_source (S × S) v₀
    have hR : ContinuousAt (IsEmbeddedSubmanifold.ambientLocal φ) (κ v₀) :=
      (((realAnalyticOn_ambientLocal hφ).smoothMBOn ((ProjectorField.isOpen_dom φ).prod
        isOpen_univ) 0).continuousOn).continuousAt
        (((ProjectorField.isOpen_dom φ).prod isOpen_univ).mem_nhds (hsub (κ.map_source hv₀)))
    refine (hR.comp (κ.continuousAt hv₀)).congr ?_
    filter_upwards [κ.open_source.mem_nhds hv₀] with v hv
    exact (heq v hv).symm
  refine ⟨hcont.continuousOn, fun v₀ _ ↦ ?_⟩
  obtain ⟨φ, hφ, heq, hsub⟩ := key v₀
  set κ := chartAt (S × S) v₀
  refine realAnalyticOn_congr (f := IsEmbeddedSubmanifold.ambientLocal φ) (fun q hq ↦ ?_)
    ((realAnalyticOn_ambientLocal hφ).mono fun q hq ↦ hsub hq.1)
  change IsEmbeddedSubmanifold.ambientLocal φ q = h.ambient (κ.symm q)
  rw [heq _ (κ.map_target hq.1), κ.right_inv hq.1]

include h in
/-- **Maps into the tangent bundle of a split real analytic submanifold.** A map into `TX` is
real analytic as soon as its composition with the ambient map `TX → F × F` is real analytic: in
a slice chart `φ`, its local representative is `(a, b) ↦ (P φ a, P dφ(a) b)` applied to the
ambient map. -/
theorem realAnalyticMOn_of_ambient (hc : cs = h.chartedSpace) {G : Type u} [AddCommGroup G]
    [Module ℝ G] [TopologicalSpace G] [IsTopologicalAddGroup G] [ContinuousSMul ℝ G]
    [LocallyConvexSpace ℝ G] [T2Space G] {Y : Type*} [TopologicalSpace Y] [ChartedSpace G Y]
    {g : Y → TangentBundle S X} {U : Set Y} (hU : IsOpen U)
    (hg : RealAnalyticMOn (E := G) (F := F × F) (h.ambient ∘ g) U) :
    RealAnalyticMOn (E := G) (F := S × S) g U := by
  subst hc
  let _ : ChartedSpace S X := h.chartedSpace
  -- `g` is continuous on `U`
  have hcont : ContinuousOn g U := by
    intro x hx
    refine ContinuousAt.continuousWithinAt ?_
    set p := (g x).proj
    set φ := h.phi p
    have hφ : IsAnalyticSliceChart X S φ := h.isAnalyticSliceChart_phi p
    set i : atlas S X := ⟨chartAt S p, chart_mem_atlas S p⟩
    have hA : ContinuousAt (h.ambient ∘ g) x := hg.1.continuousAt (hU.mem_nhds hx)
    have hpx : (g x).proj ∈ i.1.source := mem_chart_source S p
    have hproj : ContinuousAt (fun y ↦ (g y).proj) x :=
      Topology.IsInducing.subtypeVal.continuousAt_iff.mpr (continuous_fst.continuousAt.comp hA)
    refine (continuousAt_iff_coordAt i hpx).2 ⟨hproj, ?_⟩
    have hev : ∀ᶠ y in 𝓝 x, (g y).proj ∈ i.1.source :=
      hproj.preimage_mem_nhds (i.1.open_source.mem_nhds hpx)
    have hdφ : ContinuousOn (dMB φ) (φ.source ×ˢ univ) :=
      ((smoothMBOn_of_mem_maximalAtlas hφ.isSliceChart.1) 1).2.2
    have hd : ContinuousAt (fun y ↦ dMB φ (h.ambient (g y))) x :=
      (hdφ.continuousAt ((φ.open_source.prod isOpen_univ).mem_nhds
        ⟨h.mem_phi_source p, mem_univ _⟩)).comp hA
    refine Topology.IsInducing.subtypeVal.continuousAt_iff.mpr (hd.congr ?_)
    filter_upwards [hev] with y hy
    exact (h.coe_coordAt_slice rfl hφ p (chart_mem_atlas S p) (g y) hy).symm
  refine ⟨hcont, fun x hx ↦ ?_⟩
  set p := (g x).proj
  set φ := h.phi p
  have hφ : IsAnalyticSliceChart X S φ := h.isAnalyticSliceChart_phi p
  set i : atlas S X := ⟨chartAt S p, chart_mem_atlas S p⟩
  set c := chartAt G x
  set D := chartDomain g U c (tangentChart i i.1)
  set A := h.ambient ∘ g ∘ c.symm
  have hA : RealAnalyticOn A D := by
    have h1 : RealAnalyticOn A (chartDomain (h.ambient ∘ g) U c
        (chartAt (F × F) (h.ambient (g x)))) := hg.2 x hx
    exact h1.mono fun y hy ↦ ⟨hy.1, hy.2.1, mem_univ _⟩
  have hsrc : ∀ y ∈ D, ((g (c.symm y)).proj : F) ∈ φ.source := fun y hy ↦
    ((mem_tangentChart_source _ _ _).1 hy.2.2).1
  have h1 : RealAnalyticOn (φ ∘ Prod.fst ∘ A) D :=
    hφ.realAnalyticOn.comp (((ContinuousLinearMap.fst ℝ F F).realAnalyticOn univ).comp hA
      (mapsTo_univ _ _)) hsrc
  have h2 : RealAnalyticOn (dMB φ ∘ A) D :=
    (RealAnalyticOn.dMB hφ.realAnalyticOn φ.open_source).comp hA
      fun y hy ↦ ⟨hsrc y hy, mem_univ _⟩
  have h1' : RealAnalyticOn (fun y ↦ i.1 (g (c.symm y)).proj) D :=
    h.realAnalyticOn_of_coe (realAnalyticOn_congr (fun y hy ↦
      (sliceChart_apply_coe hφ.isSliceChart p (hsrc y hy)).symm) h1)
  have h2' : RealAnalyticOn (fun y ↦ coordAt i (g (c.symm y))) D :=
    h.realAnalyticOn_of_coe (realAnalyticOn_congr (fun y hy ↦
      (h.coe_coordAt_slice rfl hφ p (chart_mem_atlas S p) _ (hsrc y hy)).symm) h2)
  exact RealAnalyticOn.prodMk h1' h2'

/-- The ambient vector of a zero vector is `0`. -/
theorem ambVec_zero (hc : cs = h.chartedSpace) (p : X) :
    h.ambVec (⟨p, 0⟩ : TangentBundle S X) = 0 := by
  subst hc
  let _ : ChartedSpace S X := h.chartedSpace
  have hψ := (h.isAnalyticSliceChart_phi p).isSliceChart
  have hy : ((chartAt S p p : S) : F) ∈ (h.phi p).target := by
    rw [show ((chartAt S p p : S) : F) = h.phi p p from
      sliceChart_apply_coe hψ p (h.mem_phi_source p)]
    exact (h.phi p).map_source (h.mem_phi_source p)
  exact ProjectorField.dMB_param_zero hψ hy

/-- The ambient map sends `0_p` to `(p, 0)`. -/
theorem ambient_zero (hc : cs = h.chartedSpace) (p : X) :
    h.ambient (⟨p, 0⟩ : TangentBundle S X) = ((p : F), 0) :=
  Prod.ext rfl (h.ambVec_zero hc p)

end IsSplitAnalyticSubmanifold

/-! ### Real analytic local additions from ambient formulas -/

/-- **Ambient data for a real analytic local addition** on a split real analytic submanifold
`X ⊆ F`: real analytic maps `σ : Ω → F` and `τ : V → F` on open subsets of `F × F` such that, for
`p ∈ X`, `σ(p, 0) = p` and `w ↦ σ(p, w)` is a bijection from `{w ∈ T_p X : (p, w) ∈ Ω}` onto
`{q ∈ X : (p, q) ∈ V}`, with inverse `q ↦ τ(p, q)`. -/
structure AnalyticAmbientAddition (h : IsSplitAnalyticSubmanifold X S) where
  /-- The domain of `σ`. -/
  Ω : Set (F × F)
  /-- `Ω` is open. -/
  isOpen_Ω : IsOpen Ω
  /-- The ambient formula of the local addition. -/
  σ : F × F → F
  /-- `σ` is real analytic on `Ω`. -/
  realAnalyticOn_σ : RealAnalyticOn σ Ω
  /-- The domain of `τ`. -/
  V : Set (F × F)
  /-- `V` is open. -/
  isOpen_V : IsOpen V
  /-- The ambient formula of the inverse. -/
  τ : F × F → F
  /-- `τ` is real analytic on `V`. -/
  realAnalyticOn_τ : RealAnalyticOn τ V
  /-- `Ω` contains the zero section. -/
  zero_mem : ∀ p : X, ((p : F), (0 : F)) ∈ Ω
  /-- `σ(p, 0) = p`. -/
  σ_zero : ∀ p : X, σ ((p : F), 0) = p
  /-- `σ` maps tangent vectors into `X`. -/
  σ_mem : ∀ p : X, ∀ w ∈ h.tangentSpace p, ((p : F), w) ∈ Ω → σ ((p : F), w) ∈ X
  /-- `(p, σ(p, w))` lies in `V`. -/
  mem_V : ∀ p : X, ∀ w ∈ h.tangentSpace p, ((p : F), w) ∈ Ω → ((p : F), σ ((p : F), w)) ∈ V
  /-- `τ` inverts `σ`. -/
  τ_σ : ∀ p : X, ∀ w ∈ h.tangentSpace p, ((p : F), w) ∈ Ω → τ ((p : F), σ ((p : F), w)) = w
  /-- `τ(p, q)` is tangent at `p`. -/
  τ_mem : ∀ p q : X, ((p : F), (q : F)) ∈ V → τ ((p : F), (q : F)) ∈ h.tangentSpace p
  /-- `(p, τ(p, q))` lies in `Ω`. -/
  mem_Ω : ∀ p q : X, ((p : F), (q : F)) ∈ V → ((p : F), τ ((p : F), (q : F))) ∈ Ω
  /-- `σ` inverts `τ`. -/
  σ_τ : ∀ p q : X, ((p : F), (q : F)) ∈ V → σ ((p : F), τ ((p : F), (q : F))) = q

namespace AnalyticAmbientAddition

variable {h : IsSplitAnalyticSubmanifold X S} (D : AnalyticAmbientAddition h)
  [cs : ChartedSpace S X] [MBManifold S X]

open scoped Classical in
/-- The local addition `Σ(v) = σ(π v, v)` on `TX` (junk value `π v` off its domain). -/
def sigma (v : TangentBundle S X) : X :=
  if hm : D.σ (h.ambient v) ∈ X then ⟨_, hm⟩ else v.proj

/-- The domain `Ω_X = {v ∈ TX : (π v, v) ∈ Ω}` of the local addition. -/
def source : Set (TangentBundle S X) := h.ambient ⁻¹' D.Ω

/-- The image `{(p, q) ∈ X × X : (p, q) ∈ V}` of `θ = (π, Σ)`. -/
def target : Set (X × X) := (fun z : X × X ↦ ((z.1 : F), (z.2 : F))) ⁻¹' D.V

/-- On its domain, `Σ(v) = σ(π v, w)`, with `w` the ambient vector of `v`. -/
theorem coe_sigma (hc : cs = h.chartedSpace) {v : TangentBundle S X} (hv : v ∈ D.source) :
    ((D.sigma v : X) : F) = D.σ (h.ambient v) := by
  have hm : D.σ (h.ambient v) ∈ X :=
    D.σ_mem v.proj (h.ambVec v) (h.ambVec_mem_tangentSpace hc v) hv
  unfold sigma
  rw [dite_eq_left hm]

/-- The inverse `θ⁻¹(p, q) = (p, τ(p, q))`. -/
def thetaInv (z : X × X) : TangentBundle S X := h.ofAmb z.1 (D.τ ((z.1 : F), (z.2 : F)))

/-- The ambient map sends `θ⁻¹(p, q)` to `(p, τ(p, q))`. -/
theorem ambient_thetaInv (hc : cs = h.chartedSpace) {z : X × X} (hz : z ∈ D.target) :
    h.ambient (D.thetaInv z) = ((z.1 : F), D.τ ((z.1 : F), (z.2 : F))) :=
  Prod.ext rfl (h.ambVec_ofAmb hc (D.τ_mem z.1 z.2 hz))

/-- The domain of the local addition is open. -/
theorem isOpen_source (hc : cs = h.chartedSpace) : IsOpen D.source :=
  D.isOpen_Ω.preimage (continuousOn_univ.1 (h.realAnalyticMOn_ambient hc).1)

omit cs [MBManifold S X] in
/-- The image of `θ` is open. -/
theorem isOpen_target : IsOpen D.target :=
  D.isOpen_V.preimage (by fun_prop)

/-- `θ = (π, Σ)` is real analytic on its domain. -/
theorem realAnalyticMOn_theta (hc : cs = h.chartedSpace) :
    RealAnalyticMOn (E := S × S) (F := ModelProd S S) (fun v ↦ (v.proj, D.sigma v)) D.source := by
  have hamb := (h.realAnalyticMOn_ambient hc).mono (subset_univ D.source)
  have : RealAnalyticManifold S X := by subst hc; exact h.realAnalyticManifold
  have hRM : RealAnalyticManifold (F × F) (F × F) := hasGroupoid_model_space _ _
  refine RealAnalyticMOn.prodMk ?_ ?_
  · refine h.realAnalyticMOn_of_val hc ?_
    have hfst : RealAnalyticMOn (E := F × F) (F := F) Prod.fst univ :=
      (realAnalyticMOn_iff_realAnalyticOn isOpen_univ).2
        ((ContinuousLinearMap.fst ℝ F F).realAnalyticOn univ)
    exact (RealAnalyticMOn.comp (f := h.ambient) (g := Prod.fst) (D.isOpen_source hc)
      isOpen_univ hfst hamb (mapsTo_univ _ _)).congr fun v _ ↦ rfl
  · refine h.realAnalyticMOn_of_val hc ?_
    have hσ : RealAnalyticMOn (E := F × F) (F := F) D.σ D.Ω :=
      (realAnalyticMOn_iff_realAnalyticOn D.isOpen_Ω).2 D.realAnalyticOn_σ
    refine (RealAnalyticMOn.comp (D.isOpen_source hc) D.isOpen_Ω hσ hamb
      fun v hv ↦ hv).congr fun v hv ↦ ?_
    exact (D.coe_sigma hc hv).symm

/-- `θ⁻¹` is real analytic on its domain. -/
theorem realAnalyticMOn_thetaInv (hc : cs = h.chartedSpace) :
    RealAnalyticMOn (E := ModelProd S S) (F := S × S) D.thetaInv D.target := by
  have hT := D.isOpen_target
  refine h.realAnalyticMOn_of_ambient hc hT ?_
  subst hc
  let _ : ChartedSpace S X := h.chartedSpace
  have _ := h.realAnalyticManifold
  have hRM : RealAnalyticManifold (F × F) (F × F) := hasGroupoid_model_space _ _
  have hRF : RealAnalyticManifold F F := hasGroupoid_model_space _ _
  have hval := h.realAnalyticMOn_val rfl
  have h1 : RealAnalyticMOn (E := ModelProd S S) (F := F)
      (fun z : X × X ↦ ((z.1 : X) : F)) D.target :=
    RealAnalyticMOn.comp (f := Prod.fst) (g := Subtype.val) hT isOpen_univ hval
      ((realAnalyticMOn_fst (E := S) (F := S)).mono (subset_univ _)) (mapsTo_univ _ _)
  have h2 : RealAnalyticMOn (E := ModelProd S S) (F := F)
      (fun z : X × X ↦ ((z.2 : X) : F)) D.target :=
    RealAnalyticMOn.comp (f := Prod.snd) (g := Subtype.val) hT isOpen_univ hval
      ((realAnalyticMOn_snd (E := S) (F := S)).mono (subset_univ _)) (mapsTo_univ _ _)
  have hΨ := RealAnalyticMOn.prodMk_model h1 h2
  have hτ : RealAnalyticMOn (E := F × F) (F := F) D.τ D.V :=
    (realAnalyticMOn_iff_realAnalyticOn D.isOpen_V).2 D.realAnalyticOn_τ
  have h3 := RealAnalyticMOn.comp hT D.isOpen_V hτ hΨ fun z hz ↦ hz
  exact (RealAnalyticMOn.prodMk_model h1 h3).congr fun z hz ↦
    (D.ambient_thetaInv rfl hz).symm

/-- `θ⁻¹` maps the image of `θ` into the domain. -/
theorem thetaInv_mem_source (hc : cs = h.chartedSpace) {z : X × X} (hz : z ∈ D.target) :
    D.thetaInv z ∈ D.source := by
  change h.ambient (D.thetaInv z) ∈ D.Ω
  rw [D.ambient_thetaInv hc hz]
  exact D.mem_Ω _ _ hz

/-- **The local addition defined by real analytic ambient formulas.** -/
def toLocalAddition (hc : cs = h.chartedSpace) : LocalAddition S X where
  toOpenPartialHomeomorph :=
    { toFun := fun v ↦ (v.proj, D.sigma v)
      invFun := D.thetaInv
      source := D.source
      target := D.target
      map_source' := fun v hv ↦ by
        change (((v.proj : X) : F), ((D.sigma v : X) : F)) ∈ D.V
        rw [D.coe_sigma hc hv]
        exact D.mem_V _ _ (h.ambVec_mem_tangentSpace hc v) hv
      map_target' := fun z hz ↦ D.thetaInv_mem_source hc hz
      left_inv' := fun v hv ↦ by
        change h.ofAmb v.proj (D.τ (((v.proj : X) : F), ((D.sigma v : X) : F))) = v
        rw [D.coe_sigma hc hv]
        change h.ofAmb v.proj (D.τ (((v.proj : X) : F), D.σ (((v.proj : X) : F),
          h.ambVec v))) = v
        rw [D.τ_σ _ _ (h.ambVec_mem_tangentSpace hc v) hv, h.ofAmb_ambVec hc v]
      right_inv' := fun z hz ↦ by
        refine Prod.ext rfl (Subtype.ext ?_)
        change ((D.sigma (D.thetaInv z) : X) : F) = z.2
        rw [D.coe_sigma hc (D.thetaInv_mem_source hc hz), D.ambient_thetaInv hc hz,
          D.σ_τ _ _ hz]
      open_source := D.isOpen_source hc
      open_target := D.isOpen_target
      continuousOn_toFun := (D.realAnalyticMOn_theta hc).1
      continuousOn_invFun := (D.realAnalyticMOn_thetaInv hc).1 }
  fst_eq := fun _ _ ↦ rfl
  smoothMBMOn := (D.realAnalyticMOn_theta hc).smoothMBMOn (D.isOpen_source hc)
  smoothMBMOn_symm := (D.realAnalyticMOn_thetaInv hc).smoothMBMOn D.isOpen_target
  zero_mem := fun p ↦ by
    change h.ambient ⟨p, 0⟩ ∈ D.Ω
    rw [h.ambient_zero hc p]
    exact D.zero_mem p
  snd_zero := fun p ↦ by
    have hp : (⟨p, 0⟩ : TangentBundle S X) ∈ D.source := by
      change h.ambient ⟨p, 0⟩ ∈ D.Ω
      rw [h.ambient_zero hc p]
      exact D.zero_mem p
    refine Subtype.ext ?_
    change ((D.sigma ⟨p, 0⟩ : X) : F) = p
    rw [D.coe_sigma hc hp, h.ambient_zero hc p, D.σ_zero p]

/-- The local addition reads `Σ(v) = σ(π v, w)`, with `w` the ambient vector of `v`. -/
theorem toLocalAddition_toFun (hc : cs = h.chartedSpace) {v : TangentBundle S X}
    (hv : v ∈ D.source) :
    (((D.toLocalAddition hc).toFun v : X) : F) = D.σ ((v.proj : F), h.ambVec v) :=
  D.coe_sigma hc hv

/-- **The local addition defined by real analytic ambient formulas is a real analytic local
addition**: `θ = (π, Σ)` is a real analytic diffeomorphism onto its open image. -/
theorem isRealAnalytic_toLocalAddition (hc : cs = h.chartedSpace) :
    letI : RealAnalyticManifold S X := hc ▸ h.realAnalyticManifold
    (D.toLocalAddition hc).IsRealAnalytic :=
  ⟨D.realAnalyticMOn_theta hc, D.realAnalyticMOn_thetaInv hc⟩

end AnalyticAmbientAddition

end LocallyConvex.Manifolds
