/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.LocalAddition.Normalize
public import LocallyConvexManifolds.Connection.Projector

/-!
# Local additions on embedded submanifolds from ambient formulas

Let `X ⊆ F` be an embedded submanifold of a locally convex space, modeled on a closed subspace
`S` (`IsEmbeddedSubmanifold`), with the charted space structure given by its slice charts. We
describe smooth maps into `X` and into `TX` through the ambient space, and use this to build
local additions ([GN26, Definition 3.8.11]) on `X` from formulas in `F`.

## Main results

* `IsEmbeddedSubmanifold.contMDiffMBOn_of_val`: a map into `X` is `C^k` as soon as it is `C^k`
  as a map into `F`.
* `IsEmbeddedSubmanifold.ambVec`, `IsEmbeddedSubmanifold.ofAmb`: the ambient vector `w ∈ T_p X ⊆ F`
  of a tangent vector of `X`, and back; `IsEmbeddedSubmanifold.coe_coordAt_slice`: in a slice chart
  `φ`, the fiber coordinate of a tangent vector is `dφ(p) w`.
* `IsEmbeddedSubmanifold.smoothMBM_ambient`: the ambient map `TX → F × F`, `v ↦ (π v, w)`, is
  smooth; `IsEmbeddedSubmanifold.contMDiffMBOn_of_ambient`: a map into `TX` is `C^k` as soon as
  its composition with the ambient map is.
* `AmbientAddition`: smooth maps `σ`, `τ` on open subsets of `F × F` such that `w ↦ σ(p, w)` is
  a bijection from part of `T_p X` onto part of `X` with inverse `q ↦ τ(p, q)`;
  `AmbientAddition.toLocalAddition`: the local addition `Σ(v) = σ(π v, w)` they define;
  `AmbientAddition.isNormalized_toLocalAddition`: it is normalized when
  `d(σ(p, ·))(0) = id` on `T_p X`.

## Implementation notes

* The charted space structure of `X` is not an instance (it depends on the proof `h` of
  `IsEmbeddedSubmanifold X S`). The statements take an instance `cs : ChartedSpace S X` together
  with the hypothesis `cs = h.chartedSpace`, used with `rfl`.
* Glöckner–Neeb obtain local additions from sprays ([GN26, Proposition 3.8.13], for smoothly
  paracompact Banach manifolds) and from Lie group structures ([GN26, Proposition 3.8.12]); they do
  not discuss ambient formulas on submanifolds. We do not claim this argument is new.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function TopologicalSpace
open scoped Topology
open LocallyConvex.Analysis

noncomputable section

universe u

namespace LocallyConvex.Manifolds

/-- A pair of `C^k` maps into model spaces `A`, `B` is a `C^k` map into the model space `A × B`
(with its own chart, not the product structure `ModelProd A B`). -/
theorem ContMDiffMBOn.prodMk_model {G A B : Type u} [AddCommGroup G] [Module ℝ G]
    [TopologicalSpace G] [AddCommGroup A] [Module ℝ A] [TopologicalSpace A] [T2Space A]
    [AddCommGroup B] [Module ℝ B] [TopologicalSpace B] [T2Space B]
    [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G]
    {P : Type*} [TopologicalSpace P] [ChartedSpace G P] {k : ℕ} {f : P → A} {g : P → B}
    {U : Set P} (hU : IsOpen U) (hf : ContMDiffMBOn (E := G) (F := A) k f U)
    (hg : ContMDiffMBOn (E := G) (F := B) k g U) :
    ContMDiffMBOn (E := G) (F := A × B) k (fun p ↦ (f p, g p)) U := by
  refine ⟨hf.1.prodMk hg.1, fun x hx ↦ ?_⟩
  set c := chartAt G x
  have hD := isOpen_chartDomain hU (hf.1.prodMk hg.1) c (chartAt (A × B) (f x, g x))
  have h1 : ContDiffMBOn k (f ∘ c.symm) (chartDomain f U c (chartAt A (f x))) := hf.2 x hx
  have h2 : ContDiffMBOn k (g ∘ c.symm) (chartDomain g U c (chartAt B (g x))) := hg.2 x hx
  exact ContDiffMBOn.prodMk hD (h1.mono fun y hy ↦ ⟨hy.1, hy.2.1, mem_univ _⟩)
    (h2.mono fun y hy ↦ ⟨hy.1, hy.2.1, mem_univ _⟩)

namespace IsEmbeddedSubmanifold

variable {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {X : Set F} {S : Submodule ℝ F} (h : IsEmbeddedSubmanifold X S)

/-- The slice chart of `F` behind the preferred chart of `X` at `p`. -/
def phi (p : X) : OpenPartialHomeomorph F F := (h.exists_sliceChart p p.2).choose

/-- The preferred slice chart at `p` is a slice chart. -/
theorem isSliceChart_phi (p : X) : IsSliceChart X S (h.phi p) :=
  (h.exists_sliceChart p p.2).choose_spec.1

/-- `p` lies in the source of its preferred slice chart. -/
theorem mem_phi_source (p : X) : (p : F) ∈ (h.phi p).source :=
  (h.exists_sliceChart p p.2).choose_spec.2

variable [cs : ChartedSpace S X] [MBManifold S X]

include h in
/-- **Maps into an embedded submanifold.** A map into `X` is `C^k` as soon as it is `C^k` as a
map into `F`: in a slice chart `φ`, its local representative is the corestriction to `S` of the
local representative of the map into `F`. -/
theorem contMDiffMBOn_of_val (hc : cs = h.chartedSpace) {G : Type u} [AddCommGroup G]
    [Module ℝ G] [TopologicalSpace G] [IsTopologicalAddGroup G] [ContinuousSMul ℝ G]
    [LocallyConvexSpace ℝ G] [T2Space G] {Y : Type*} [TopologicalSpace Y] [ChartedSpace G Y]
    [MBManifold G Y] {k : ℕ} {g : Y → X} {U : Set Y} (hU : IsOpen U)
    (hg : ContMDiffMBOn (E := G) (F := F) k (Subtype.val ∘ g) U) :
    ContMDiffMBOn (E := G) (F := S) k g U := by
  subst hc
  let _ : ChartedSpace S X := h.chartedSpace
  refine ⟨Topology.IsInducing.subtypeVal.continuousOn_iff.mpr hg.1, fun x hx ↦ ?_⟩
  have hφ := h.isSliceChart_phi (g x)
  have hh := hg.contDiffMBOn_chart_of_mem_maximalAtlas hU
    ((mbGroupoid G).chart_mem_maximalAtlas x) hφ.1
  exact ContDiffMBOn.codRestrict h.isClosed
    (isOpen_chartDomain hU hg.1 (chartAt G x) (h.phi (g x))) hh
    fun y hy ↦ sliceChart_apply_coe hφ (g x) hy.2.2

include h in
/-- Smooth version of `contMDiffMBOn_of_val`. -/
theorem smoothMBMOn_of_val (hc : cs = h.chartedSpace) {G : Type u} [AddCommGroup G]
    [Module ℝ G] [TopologicalSpace G] [IsTopologicalAddGroup G] [ContinuousSMul ℝ G]
    [LocallyConvexSpace ℝ G] [T2Space G] {Y : Type*} [TopologicalSpace Y] [ChartedSpace G Y]
    [MBManifold G Y] {g : Y → X} {U : Set Y} (hU : IsOpen U)
    (hg : SmoothMBMOn G F (Subtype.val ∘ g) U) : SmoothMBMOn G S g U :=
  fun k ↦ h.contMDiffMBOn_of_val hc hU (hg k)

/-! ### Ambient tangent vectors -/

/-- The ambient vector `w ∈ T_p X ⊆ F` of a tangent vector `v` of `X` at `p`: in the preferred
slice chart `φ` at `p`, `w = dφ⁻¹(φ p)(v)`. -/
def ambVec (v : TangentBundle S X) : F :=
  dMB (ProjectorField.param (h.phi v.proj)) (chartAt S v.proj v.proj, v.vec)

open scoped Classical in
/-- The tangent vector of `X` at `p` with ambient vector `w` (meant for `w ∈ T_p X`; junk value
`0` otherwise). -/
def ofAmb (p : X) (w : F) : TangentBundle S X :=
  ⟨p, if hw : dMB (h.phi p) ((p : F), w) ∈ S then (⟨_, hw⟩ : S) else 0⟩

/-- `ofAmb p w` lies over `p`. -/
theorem ofAmb_proj (p : X) (w : F) : (h.ofAmb p w).proj = p := rfl

/-- In a slice chart `φ`, the fiber coordinate of a tangent vector is `dφ` of its ambient
vector. -/
theorem coe_coordAt_slice (hc : cs = h.chartedSpace) {φ : OpenPartialHomeomorph F F}
    (hφ : IsSliceChart X S φ) (p₀ : X) (hmem : sliceChart hφ p₀ ∈ atlas S X)
    (v : TangentBundle S X) (hv : (v.proj : F) ∈ φ.source) :
    ((coordAt ⟨sliceChart hφ p₀, hmem⟩ v : S) : F) = dMB φ ((v.proj : F), h.ambVec v) := by
  subst hc
  let _ : ChartedSpace S X := h.chartedSpace
  set p := v.proj
  set ψ := h.phi p
  have hψ : IsSliceChart X S ψ := h.isSliceChart_phi p
  set i : atlas S X := ⟨sliceChart hφ p₀, hmem⟩
  set c : atlas S X := ⟨chartAt S p, chart_mem_atlas S p⟩
  have hc' : c.1 = sliceChart hψ p := rfl
  set W := c.1.target ∩ c.1.symm ⁻¹' i.1.source
  have hW : IsOpen W := isOpen_transition_domain c i
  have hpc : p ∈ c.1.source := mem_chart_source S p
  have hcp : c.1 p ∈ W := ⟨c.1.map_source hpc, by
    rw [mem_preimage, c.1.left_inv hpc]; exact hv⟩
  have hcpψ : ((c.1 p : S) : F) = ψ p := sliceChart_apply_coe hψ p (h.mem_phi_source p)
  -- on `W`, `i ∘ c⁻¹` reads `φ ∘ ψ⁻¹` in `F`
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
    · rw [sliceChart_apply_coe hφ p₀ h2, h1]; rfl
  have hτ : ContDiffMBOn 1 (i.1 ∘ c.1.symm) W := smoothMBOn_transition' c i 1
  have hev : Subtype.val ∘ (i.1 ∘ c.1.symm) =ᶠ[𝓝 (c.1 p)] φ ∘ ProjectorField.param ψ :=
    Filter.eventuallyEq_of_mem (hW.mem_nhds hcp) fun y hy ↦ (hW' y hy).2.2
  have hpar : ContDiffMBOn 1 (ProjectorField.param ψ) W :=
    ((ProjectorField.smoothMBOn_param hψ) 1).mono fun y hy ↦ (hW' y hy).1
  change ((dMB (i.1 ∘ c.1.symm) (c.1 p, v.vec) : S) : F) = _
  rw [ProjectorField.coe_dMB_of_subtype hτ hcp, dMB_congr_of_eventuallyEq hev,
    ContDiffMBOn.dMB_comp φ.open_source ((smoothMBOn_of_mem_maximalAtlas hφ.1) 1) hpar
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
  have := h.coe_coordAt_slice rfl (h.isSliceChart_phi v.proj) v.proj
    (chart_mem_atlas S v.proj) v (h.mem_phi_source v.proj)
  rw [← this]
  exact congrArg Subtype.val (coordAt_chartAt_of_proj_eq (E := S) rfl)

/-- Ambient vectors are tangent. -/
theorem ambVec_mem_tangentSpace (hc : cs = h.chartedSpace) (v : TangentBundle S X) :
    h.ambVec v ∈ h.tangentSpace v.proj := by
  change dMB (h.phi v.proj) ((v.proj : F), h.ambVec v) ∈ S
  rw [h.dMB_phi_ambVec hc v]
  exact (v.vec).2

/-- In a slice chart `φ`, the ambient vector is `dφ⁻¹` of the fiber coordinate. -/
theorem ambVec_eq_slice (hc : cs = h.chartedSpace) {φ : OpenPartialHomeomorph F F}
    (hφ : IsSliceChart X S φ) (p₀ : X) (hmem : sliceChart hφ p₀ ∈ atlas S X)
    (v : TangentBundle S X) (hv : (v.proj : F) ∈ φ.source) :
    h.ambVec v = dMB (ProjectorField.param φ)
      (sliceChart hφ p₀ v.proj, coordAt ⟨sliceChart hφ p₀, hmem⟩ v) := by
  have hy : ((sliceChart hφ p₀ v.proj : S) : F) ∈ φ.target := by
    rw [sliceChart_apply_coe hφ p₀ hv]; exact φ.map_source hv
  rw [ProjectorField.dMB_param hφ hy, h.coe_coordAt_slice hc hφ p₀ hmem v hv,
    sliceChart_apply_coe hφ p₀ hv, dMB_symm_dMB_chart hφ.1 hv]

open scoped Classical in
/-- The ambient vector of `ofAmb p w` is `w`, for `w ∈ T_p X`. -/
theorem ambVec_ofAmb (hc : cs = h.chartedSpace) {p : X} {w : F} (hw : w ∈ h.tangentSpace p) :
    h.ambVec (h.ofAmb p w) = w := by
  subst hc
  let _ : ChartedSpace S X := h.chartedSpace
  have hψ := h.isSliceChart_phi p
  have hw' : dMB (h.phi p) ((p : F), w) ∈ S := hw
  have hcp : ((chartAt S p p : S) : F) = h.phi p p :=
    sliceChart_apply_coe hψ p (h.mem_phi_source p)
  have hy : ((chartAt S p p : S) : F) ∈ (h.phi p).target := by
    rw [hcp]; exact (h.phi p).map_source (h.mem_phi_source p)
  change dMB (ProjectorField.param (h.phi p)) (chartAt S p p,
    (if hw : dMB (h.phi p) ((p : F), w) ∈ S then (⟨_, hw⟩ : S) else 0)) = w
  rw [dite_eq_left hw', ProjectorField.dMB_param hψ hy, hcp]
  exact dMB_symm_dMB_chart hψ.1 (h.mem_phi_source p) w

open scoped Classical in
/-- A tangent vector is recovered from its ambient vector. -/
theorem ofAmb_ambVec (hc : cs = h.chartedSpace) (v : TangentBundle S X) :
    h.ofAmb v.proj (h.ambVec v) = v := by
  have hm : dMB (h.phi v.proj) ((v.proj : F), h.ambVec v) ∈ S := h.ambVec_mem_tangentSpace hc v
  refine TangentBundle.ext_vec rfl ?_
  change (if hw : dMB (h.phi v.proj) ((v.proj : F), h.ambVec v) ∈ S then (⟨_, hw⟩ : S)
    else 0) = v.vec
  rw [dite_eq_left hm]
  exact Subtype.ext (h.dMB_phi_ambVec hc v)

/-- The ambient map `TX → F × F`, `v ↦ (π v, ambVec v)`. -/
def ambient (v : TangentBundle S X) : F × F := ((v.proj : F), h.ambVec v)

/-- The local formula `(y, s) ↦ (ψ y, dψ(y) s)` of `ambient` in a slice chart `φ`, with
`ψ = φ⁻¹|_S`. -/
def ambientLocal (φ : OpenPartialHomeomorph F F) (q : S × S) : F × F :=
  (ProjectorField.param φ q.1, dMB (ProjectorField.param φ) q)

omit cs [MBManifold S X] in
/-- The local formula of the ambient map is smooth. -/
theorem contDiffMBOn_ambientLocal {φ : OpenPartialHomeomorph F F} (hφ : IsSliceChart X S φ)
    (k : ℕ) : ContDiffMBOn k (ambientLocal φ)
      ((Subtype.val ⁻¹' φ.target : Set S) ×ˢ (univ : Set S)) := by
  have hD : IsOpen ((Subtype.val ⁻¹' φ.target : Set S) ×ˢ (univ : Set S)) :=
    (ProjectorField.isOpen_dom φ).prod isOpen_univ
  refine ContDiffMBOn.prodMk hD ?_ ((ProjectorField.smoothMBOn_param hφ (k + 1)).2.2)
  have h1 : ContDiffMBOn k (ProjectorField.param φ ∘ (ContinuousLinearMap.fst ℝ S S))
      ((Subtype.val ⁻¹' φ.target : Set S) ×ˢ (univ : Set S)) :=
    ContDiffMBOn.comp (g := ProjectorField.param φ) hD (ProjectorField.isOpen_dom φ)
      ((ProjectorField.smoothMBOn_param hφ) k)
      (((ContinuousLinearMap.fst ℝ S S).contDiffMBOn k univ).mono (subset_univ _))
      fun q hq ↦ hq.1
  exact h1

/-- Over a slice chart, `ambient` is `ambientLocal` composed with the tangent chart. -/
theorem ambient_eq_ambientLocal (hc : cs = h.chartedSpace) {φ : OpenPartialHomeomorph F F}
    (hφ : IsSliceChart X S φ) (p₀ : X) (hmem : sliceChart hφ p₀ ∈ atlas S X)
    (v : TangentBundle S X) (hv : (v.proj : F) ∈ φ.source) :
    h.ambient v = ambientLocal φ (tangentChart ⟨sliceChart hφ p₀, hmem⟩ (sliceChart hφ p₀) v) := by
  rw [tangentChart_self_apply (E := S) ⟨sliceChart hφ p₀, hmem⟩ v]
  refine Prod.ext ?_ (h.ambVec_eq_slice hc hφ p₀ hmem v hv)
  change ((v.proj : X) : F) = φ.symm ((sliceChart hφ p₀ v.proj : S) : F)
  rw [sliceChart_apply_coe hφ p₀ hv, φ.left_inv hv]

/-- **The ambient map `TX → F × F` is smooth.** -/
theorem smoothMBM_ambient (hc : cs = h.chartedSpace) :
    SmoothMBM (S × S) (F × F) h.ambient := by
  subst hc
  let _ : ChartedSpace S X := h.chartedSpace
  -- the data at a base point
  have key : ∀ v₀ : TangentBundle S X, ∃ φ : OpenPartialHomeomorph F F,
      IsSliceChart X S φ ∧ chartAt (S × S) v₀ = tangentChart
        ⟨chartAt S v₀.proj, chart_mem_atlas S _⟩ (chartAt S v₀.proj) ∧
      (∀ v ∈ (chartAt (S × S) v₀).source,
        h.ambient v = ambientLocal φ (chartAt (S × S) v₀ v)) ∧
      (chartAt (S × S) v₀).target ⊆ (Subtype.val ⁻¹' φ.target : Set S) ×ˢ univ := by
    intro v₀
    refine ⟨h.phi v₀.proj, h.isSliceChart_phi v₀.proj, rfl, fun v hv ↦ ?_, fun q hq ↦ ?_⟩
    · have hv' : v.proj ∈ (chartAt S v₀.proj).source :=
        ((mem_tangentChart_source _ _ v).1 hv).1
      exact h.ambient_eq_ambientLocal rfl (h.isSliceChart_phi v₀.proj) v₀.proj
        (chart_mem_atlas S _) v hv'
    · exact ⟨((mem_tangentChart_target _ _ q).1 hq).1, mem_univ _⟩
  have hcont : Continuous h.ambient := by
    refine continuous_iff_continuousAt.2 fun v₀ ↦ ?_
    obtain ⟨φ, hφ, -, heq, hsub⟩ := key v₀
    set κ := chartAt (S × S) v₀
    have hv₀ : v₀ ∈ κ.source := mem_chart_source (S × S) v₀
    have hR : ContinuousAt (ambientLocal φ) (κ v₀) :=
      ((contDiffMBOn_ambientLocal hφ 0).continuousOn).continuousAt
        ((((ProjectorField.isOpen_dom φ).prod isOpen_univ)).mem_nhds (hsub (κ.map_source hv₀)))
    refine (hR.comp (κ.continuousAt hv₀)).congr ?_
    filter_upwards [κ.open_source.mem_nhds hv₀] with v hv
    exact (heq v hv).symm
  intro k
  refine ⟨hcont.continuousOn, fun v₀ _ ↦ ?_⟩
  obtain ⟨φ, hφ, -, heq, hsub⟩ := key v₀
  set κ := chartAt (S × S) v₀
  have hD := isOpen_chartDomain isOpen_univ hcont.continuousOn κ (chartAt (F × F) (h.ambient v₀))
  refine ContDiffMBOn.congr_of_isOpen hD (f₁ := ambientLocal φ) (fun q hq ↦ ?_)
    ((contDiffMBOn_ambientLocal hφ k).mono fun q hq ↦ hsub hq.1)
  change ambientLocal φ q = h.ambient (κ.symm q)
  rw [heq _ (κ.map_target hq.1), κ.right_inv hq.1]

include h in
/-- **Maps into the tangent bundle of an embedded submanifold.** A map into `TX` is `C^k` as soon
as its composition with the ambient map `TX → F × F` is `C^k`: in a slice chart `φ`, its local
representative is the corestriction of `(a, b) ↦ (φ a, dφ(a) b)` applied to the ambient map. -/
theorem contMDiffMBOn_of_ambient (hc : cs = h.chartedSpace) {G : Type u} [AddCommGroup G]
    [Module ℝ G] [TopologicalSpace G] [IsTopologicalAddGroup G] [ContinuousSMul ℝ G]
    [LocallyConvexSpace ℝ G] [T2Space G] {Y : Type*} [TopologicalSpace Y] [ChartedSpace G Y]
    {k : ℕ} {g : Y → TangentBundle S X} {U : Set Y} (hU : IsOpen U)
    (hg : ContMDiffMBOn (E := G) (F := F × F) k (h.ambient ∘ g) U) :
    ContMDiffMBOn (E := G) (F := S × S) k g U := by
  subst hc
  let _ : ChartedSpace S X := h.chartedSpace
  -- `g` is continuous on `U`
  have hcont : ContinuousOn g U := by
    intro x hx
    refine ContinuousAt.continuousWithinAt ?_
    set p := (g x).proj
    set φ := h.phi p
    have hφ : IsSliceChart X S φ := h.isSliceChart_phi p
    set i : atlas S X := ⟨chartAt S p, chart_mem_atlas S p⟩
    have hA : ContinuousAt (h.ambient ∘ g) x := hg.1.continuousAt (hU.mem_nhds hx)
    have hpx : (g x).proj ∈ i.1.source := mem_chart_source S p
    have hproj : ContinuousAt (fun y ↦ (g y).proj) x :=
      Topology.IsInducing.subtypeVal.continuousAt_iff.mpr (continuous_fst.continuousAt.comp hA)
    refine (continuousAt_iff_coordAt i hpx).2 ⟨hproj, ?_⟩
    have hev : ∀ᶠ y in 𝓝 x, (g y).proj ∈ i.1.source :=
      hproj.preimage_mem_nhds (i.1.open_source.mem_nhds hpx)
    have hdφ : ContinuousOn (dMB φ) (φ.source ×ˢ univ) :=
      ((smoothMBOn_of_mem_maximalAtlas hφ.1) 1).2.2
    have hd : ContinuousAt (fun y ↦ dMB φ (h.ambient (g y))) x :=
      (hdφ.continuousAt ((φ.open_source.prod isOpen_univ).mem_nhds
        ⟨h.mem_phi_source p, mem_univ _⟩)).comp hA
    refine Topology.IsInducing.subtypeVal.continuousAt_iff.mpr (hd.congr ?_)
    filter_upwards [hev] with y hy
    exact (h.coe_coordAt_slice rfl hφ p (chart_mem_atlas S p) (g y) hy).symm
  refine ⟨hcont, fun x hx ↦ ?_⟩
  set p := (g x).proj
  set φ := h.phi p
  have hφ : IsSliceChart X S φ := h.isSliceChart_phi p
  set i : atlas S X := ⟨chartAt S p, chart_mem_atlas S p⟩
  set c := chartAt G x
  set D := chartDomain g U c (tangentChart i i.1)
  have hD : IsOpen D := isOpen_chartDomain hU hcont c (tangentChart i i.1)
  set A := h.ambient ∘ g ∘ c.symm
  have hA : ContDiffMBOn k A D := by
    have h1 : ContDiffMBOn k A (chartDomain (h.ambient ∘ g) U c
        (chartAt (F × F) (h.ambient (g x)))) := hg.2 x hx
    exact h1.mono fun y hy ↦ ⟨hy.1, hy.2.1, mem_univ _⟩
  have hsrc : ∀ y ∈ D, ((g (c.symm y)).proj : F) ∈ φ.source := fun y hy ↦
    ((mem_tangentChart_source _ _ _).1 hy.2.2).1
  have hAsrc : ∀ y ∈ D, (A y).1 ∈ φ.source := hsrc
  have h1 : ContDiffMBOn k (φ ∘ Prod.fst ∘ A) D :=
    ((smoothMBOn_of_mem_maximalAtlas hφ.1) k).comp hD φ.open_source
      (((ContinuousLinearMap.fst ℝ F F).contDiffMBOn k univ).comp hD isOpen_univ
        (hA) (mapsTo_univ _ _)) hAsrc
  have h2 : ContDiffMBOn k (dMB φ ∘ A) D :=
    (((smoothMBOn_of_mem_maximalAtlas hφ.1) (k + 1)).2.2).comp hD
      (φ.open_source.prod isOpen_univ) hA fun y hy ↦ ⟨hAsrc y hy, mem_univ _⟩
  have h1' : ContDiffMBOn k (fun y ↦ i.1 (g (c.symm y)).proj) D :=
    ContDiffMBOn.codRestrict h.isClosed hD h1 fun y hy ↦
      sliceChart_apply_coe hφ p (hsrc y hy)
  have h2' : ContDiffMBOn k (fun y ↦ coordAt i (g (c.symm y))) D :=
    ContDiffMBOn.codRestrict h.isClosed hD h2 fun y hy ↦
      h.coe_coordAt_slice rfl hφ p (chart_mem_atlas S p) _ (hsrc y hy)
  exact ContDiffMBOn.prodMk hD h1' h2'

/-- The ambient vector of a zero vector is `0`. -/
theorem ambVec_zero (hc : cs = h.chartedSpace) (p : X) :
    h.ambVec (⟨p, 0⟩ : TangentBundle S X) = 0 := by
  subst hc
  let _ : ChartedSpace S X := h.chartedSpace
  have hψ := h.isSliceChart_phi p
  have hy : ((chartAt S p p : S) : F) ∈ (h.phi p).target := by
    rw [show ((chartAt S p p : S) : F) = h.phi p p from
      sliceChart_apply_coe hψ p (h.mem_phi_source p)]
    exact (h.phi p).map_source (h.mem_phi_source p)
  exact ProjectorField.dMB_param_zero hψ hy

/-- The ambient map sends `0_p` to `(p, 0)`. -/
theorem ambient_zero (hc : cs = h.chartedSpace) (p : X) :
    h.ambient (⟨p, 0⟩ : TangentBundle S X) = ((p : F), 0) :=
  Prod.ext rfl (h.ambVec_zero hc p)

/-- The ambient vector map `TX → F` is smooth. -/
theorem smoothMBM_ambVec (hc : cs = h.chartedSpace) : SmoothMBM (S × S) F h.ambVec := by
  intro k
  have hs : ContMDiffMBOn (E := F × F) (F := F) k Prod.snd univ :=
    (contMDiffMBOn_iff_contDiffMBOn isOpen_univ).2
      ((ContinuousLinearMap.snd ℝ F F).contDiffMBOn k univ)
  exact ContMDiffMBOn.comp (f := h.ambient) (g := Prod.snd) isOpen_univ isOpen_univ hs
    (h.smoothMBM_ambient hc k) (mapsTo_univ _ _)

/-- The ambient projection `TX → F` is smooth. -/
theorem smoothMBM_val_proj (hc : cs = h.chartedSpace) :
    SmoothMBM (S × S) F (fun v : TangentBundle S X ↦ ((v.proj : X) : F)) := by
  intro k
  have hs : ContMDiffMBOn (E := F × F) (F := F) k Prod.fst univ :=
    (contMDiffMBOn_iff_contDiffMBOn isOpen_univ).2
      ((ContinuousLinearMap.fst ℝ F F).contDiffMBOn k univ)
  exact ContMDiffMBOn.comp (f := h.ambient) (g := Prod.fst) isOpen_univ isOpen_univ hs
    (h.smoothMBM_ambient hc k) (mapsTo_univ _ _)

end IsEmbeddedSubmanifold

/-! ### Local additions from ambient formulas -/

section Ambient

variable {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {X : Set F} {S : Submodule ℝ F}

/-- **Ambient data for a local addition** on an embedded submanifold `X ⊆ F`: smooth maps
`σ : Ω → F` and `τ : V → F` on open subsets of `F × F` such that, for `p ∈ X`, `σ(p, 0) = p` and
`w ↦ σ(p, w)` is a bijection from `{w ∈ T_p X : (p, w) ∈ Ω}` onto `{q ∈ X : (p, q) ∈ V}`, with
inverse `q ↦ τ(p, q)`. -/
structure AmbientAddition (h : IsEmbeddedSubmanifold X S) where
  /-- The domain of `σ`. -/
  Ω : Set (F × F)
  /-- `Ω` is open. -/
  isOpen_Ω : IsOpen Ω
  /-- The ambient formula of the local addition. -/
  σ : F × F → F
  /-- `σ` is smooth on `Ω`. -/
  smoothMBOn_σ : SmoothMBOn σ Ω
  /-- The domain of `τ`. -/
  V : Set (F × F)
  /-- `V` is open. -/
  isOpen_V : IsOpen V
  /-- The ambient formula of the inverse. -/
  τ : F × F → F
  /-- `τ` is smooth on `V`. -/
  smoothMBOn_τ : SmoothMBOn τ V
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

namespace AmbientAddition

variable {h : IsEmbeddedSubmanifold X S} (D : AmbientAddition h)
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
  D.isOpen_Ω.preimage (continuousOn_univ.1 (h.smoothMBM_ambient hc 0).1)

omit cs [MBManifold S X] in
/-- The image of `θ` is open. -/
theorem isOpen_target : IsOpen D.target :=
  D.isOpen_V.preimage (by fun_prop)

/-- `θ = (π, Σ)` is smooth on its domain. -/
theorem smoothMBMOn_theta (hc : cs = h.chartedSpace) :
    SmoothMBMOn (S × S) (ModelProd S S) (fun v ↦ (v.proj, D.sigma v)) D.source := by
  have := h.mbManifold
  intro k
  have hU := D.isOpen_source hc
  refine ContMDiffMBOn.prodMk hU ?_ ?_
  · exact h.contMDiffMBOn_of_val hc hU (SmoothMBMOn.mono_of_isOpen isOpen_univ hU
      (h.smoothMBM_val_proj hc) (subset_univ _) k)
  · refine h.contMDiffMBOn_of_val hc hU ?_
    have hσ : ContMDiffMBOn (E := F × F) (F := F) k D.σ D.Ω :=
      (contMDiffMBOn_iff_contDiffMBOn D.isOpen_Ω).2 (D.smoothMBOn_σ k)
    refine (hσ.comp hU D.isOpen_Ω (SmoothMBMOn.mono_of_isOpen isOpen_univ hU
      (h.smoothMBM_ambient hc) (subset_univ _) k)
      fun v hv ↦ hv).congr_of_isOpen hU fun v hv ↦ ?_
    exact (D.coe_sigma hc hv).symm

/-- `θ⁻¹` is smooth on its domain. -/
theorem smoothMBMOn_thetaInv (hc : cs = h.chartedSpace) :
    SmoothMBMOn (ModelProd S S) (S × S) D.thetaInv D.target := by
  intro k
  have hT := D.isOpen_target
  refine h.contMDiffMBOn_of_ambient hc hT ?_
  subst hc
  let _ : ChartedSpace S X := h.chartedSpace
  have hval := h.smoothMBM_val
  have h1 : ContMDiffMBOn (E := ModelProd S S) (F := F) k
      (fun z : X × X ↦ ((z.1 : X) : F)) D.target :=
    ContMDiffMBOn.comp (f := Prod.fst) (g := Subtype.val) hT isOpen_univ (hval k)
      (SmoothMBMOn.mono_of_isOpen isOpen_univ hT (smoothMBM_fst (E := S) (F := S))
        (subset_univ _) k) (mapsTo_univ _ _)
  have h2 : ContMDiffMBOn (E := ModelProd S S) (F := F) k
      (fun z : X × X ↦ ((z.2 : X) : F)) D.target :=
    ContMDiffMBOn.comp (f := Prod.snd) (g := Subtype.val) hT isOpen_univ (hval k)
      (SmoothMBMOn.mono_of_isOpen isOpen_univ hT (smoothMBM_snd (E := S) (F := S))
        (subset_univ _) k) (mapsTo_univ _ _)
  have hΨ := ContMDiffMBOn.prodMk_model hT h1 h2
  have hτ : ContMDiffMBOn (E := F × F) (F := F) k D.τ D.V :=
    (contMDiffMBOn_iff_contDiffMBOn D.isOpen_V).2 (D.smoothMBOn_τ k)
  have h3 := ContMDiffMBOn.comp hT D.isOpen_V hτ hΨ fun z hz ↦ hz
  exact (ContMDiffMBOn.prodMk_model hT h1 h3).congr_of_isOpen hT fun z hz ↦
    (D.ambient_thetaInv rfl hz).symm

/-- `θ⁻¹` maps the image of `θ` into the domain. -/
theorem thetaInv_mem_source (hc : cs = h.chartedSpace) {z : X × X} (hz : z ∈ D.target) :
    D.thetaInv z ∈ D.source := by
  change h.ambient (D.thetaInv z) ∈ D.Ω
  rw [D.ambient_thetaInv hc hz]
  exact D.mem_Ω _ _ hz

/-- **The local addition defined by ambient formulas.** -/
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
      continuousOn_toFun := (D.smoothMBMOn_theta hc 0).1
      continuousOn_invFun := (D.smoothMBMOn_thetaInv hc 0).1 }
  fst_eq := fun _ _ ↦ rfl
  smoothMBMOn := D.smoothMBMOn_theta hc
  smoothMBMOn_symm := D.smoothMBMOn_thetaInv hc
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

/-- **Normalization.** If `w ↦ σ(p, w)` has derivative the identity at `0` along `T_p X`, the
local addition defined by `σ` is normalized. -/
theorem isNormalized_toLocalAddition (hc : cs = h.chartedSpace)
    (hσ : ∀ p : X, ∀ w ∈ h.tangentSpace p, dMB (fun u ↦ D.σ ((p : F), u)) (0, w) = w) :
    (D.toLocalAddition hc).IsNormalized := by
  subst hc
  let _ : ChartedSpace S X := h.chartedSpace
  intro x w
  set ψ := h.phi x
  have hψ : IsSliceChart X S ψ := h.isSliceChart_phi x
  have hxψ : (x : F) ∈ ψ.source := h.mem_phi_source x
  set y₀ : S := chartAt S x x
  have hy₀ : (y₀ : F) ∈ ψ.target := by
    rw [show (y₀ : F) = ψ x from sliceChart_apply_coe hψ x hxψ]
    exact ψ.map_source hxψ
  obtain ⟨Lc, hL⟩ := ((ProjectorField.smoothMBOn_param hψ) 1).exists_clm
    (ProjectorField.isOpen_dom ψ) hy₀
  have hamb : ∀ v : S, h.ambVec (⟨x, v⟩ : TangentBundle S X) = Lc v := fun v ↦ (hL v).symm
  set a : S → F × F := fun v ↦ ((x : F), Lc v)
  have ha : ∀ k, ContDiffMBOn k a univ := fun k ↦
    ContDiffMBOn.prodMk isOpen_univ (contDiffMBOn_const k _ univ) (Lc.contDiffMBOn k univ)
  set O : Set S := a ⁻¹' (D.Ω ∩ D.σ ⁻¹' ψ.source)
  have hO : IsOpen O :=
    ((D.smoothMBOn_σ 0).continuousOn.isOpen_inter_preimage D.isOpen_Ω ψ.open_source).preimage
      (continuousOn_univ.1 (ha 0).continuousOn)
  have ha0 : a 0 = ((x : F), 0) := by simp [a]
  have hσ0 : D.σ (a 0) = x := by rw [ha0]; exact D.σ_zero x
  have h0O : (0 : S) ∈ O := ⟨by rw [ha0]; exact D.zero_mem x, by
    change D.σ (a 0) ∈ ψ.source; rw [hσ0]; exact hxψ⟩
  have hamb' : ∀ v : S, h.ambient (⟨x, v⟩ : TangentBundle S X) = a v := fun v ↦
    Prod.ext rfl (hamb v)
  set g : S → F := ψ ∘ D.σ ∘ a
  have hσa : ContDiffMBOn 1 (D.σ ∘ a) O :=
    (D.smoothMBOn_σ 1).comp hO D.isOpen_Ω ((ha 1).mono (subset_univ _)) fun v hv ↦ hv.1
  have hg : ContDiffMBOn 1 g O :=
    ((smoothMBOn_of_mem_maximalAtlas hψ.1) 1).comp hO ψ.open_source hσa fun v hv ↦ hv.2
  set f : S → S := fun v ↦ chartAt S x ((D.toLocalAddition rfl).toFun ⟨x, v⟩)
  have hfeq : ∀ v ∈ O, (f v : F) = g v := by
    intro v hv
    have hsrc : (⟨x, v⟩ : TangentBundle S X) ∈ D.source := by
      change h.ambient ⟨x, v⟩ ∈ D.Ω; rw [hamb' v]; exact hv.1
    have hval : (((D.toLocalAddition rfl).toFun ⟨x, v⟩ : X) : F) = D.σ (a v) := by
      rw [D.toLocalAddition_toFun rfl hsrc]; rw [← hamb' v]; rfl
    have hmem : (((D.toLocalAddition rfl).toFun ⟨x, v⟩ : X) : F) ∈ ψ.source := by
      rw [hval]; exact hv.2
    change ((sliceChart hψ x ((D.toLocalAddition rfl).toFun ⟨x, v⟩) : S) : F) = _
    rw [sliceChart_apply_coe hψ x hmem, hval]
    rfl
  have hf : ContDiffMBOn 1 f O := ContDiffMBOn.codRestrict h.isClosed hO hg hfeq
  have hev : Subtype.val ∘ f =ᶠ[𝓝 0] g :=
    Filter.eventuallyEq_of_mem (hO.mem_nhds h0O) hfeq
  have hda : dMB a (0, w) = (0, Lc w) := by
    refine HasDirDerivAt.dMB_eq (HasDirDerivAt.prodMk ?_ (Lc.hasDirDerivAt 0 w))
    unfold HasDirDerivAt
    simp only [sub_self, smul_zero]
    exact tendsto_const_nhds
  have hTw : Lc w ∈ h.tangentSpace x := by
    rw [← hamb w]; exact h.ambVec_mem_tangentSpace rfl ⟨x, w⟩
  have h1 : dMB g (0, w) = dMB ψ ((D.σ ∘ a) 0, dMB (D.σ ∘ a) (0, w)) :=
    ContDiffMBOn.dMB_comp ψ.open_source ((smoothMBOn_of_mem_maximalAtlas hψ.1) 1) hσa
      (fun v (hv : v ∈ O) ↦ hv.2) h0O w
  have h2 : dMB (D.σ ∘ a) (0, w) = dMB D.σ (a 0, dMB a (0, w)) :=
    ContDiffMBOn.dMB_comp D.isOpen_Ω (D.smoothMBOn_σ 1) ((ha 1).mono (subset_univ O))
      (fun v (hv : v ∈ O) ↦ hv.1) h0O w
  apply Subtype.ext
  change ((dMB f (0, w) : S) : F) = w
  rw [ProjectorField.coe_dMB_of_subtype hf h0O w, dMB_congr_of_eventuallyEq hev, h1, h2,
    Function.comp_apply, hda, hσ0, ha0, LocalAddition.dMB_slice_snd (E := F),
    hσ x (Lc w) hTw, ← hamb w]
  exact h.dMB_phi_ambVec rfl ⟨x, w⟩

end AmbientAddition

end Ambient

end LocallyConvex.Manifolds
