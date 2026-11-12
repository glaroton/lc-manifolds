/-
Prints the axioms used by the main theorems on manifolds of mappings in LocallyConvex.Manifolds.
Run with `lake env lean scripts/Axioms.lean`; every line should read
`[propext, Classical.choice, Quot.sound]` (the standard axioms of Lean and Mathlib).
-/
import LocallyConvexManifolds

open LocallyConvex.Manifolds LocallyConvex.Analysis

-- Local additions (`LocalAddition/Basic.lean`)
#print axioms LocalAddition.prod
-- The manifold `C(K, N)` (`MappingSpace/Basic.lean`)
#print axioms LocalAddition.mappingAtlas
#print axioms LocalAddition.smoothMBMOn_eval_chart_symm
-- Superposition operators (`LocallyConvexAnalysis/MappingSpace/CkSuperposition.lean`, used here)
#print axioms ContDiffMBMap.contDiffMBOn_compLeftOn
#print axioms ContDiffMBMap.isClosed_range_restrictCover
-- The manifolds `C^ℓ(M, N)` (`MappingSpace/Ck.lean`)
#print axioms LocalAddition.mappingAtlasCk
#print axioms LocalAddition.smoothMBMOn_eval_chartCk_symm
#print axioms LocalAddition.mappingAtlasSm
#print axioms LocalAddition.smoothMBMOn_eval_chartSm_symm
-- Atlases with varying models (`Manifold/VaryingAtlas.lean`)
#print axioms VaryingAtlas.contMDiffOn_iff_local
#print axioms VaryingAtlas.ContMDiffOn.comp
#print axioms VaryingAtlas.contMDiffOn_ofChartedSpace_iff
#print axioms VaryingAtlas.smoothOn_chart
#print axioms VaryingAtlas.smoothOn_chart_symm
#print axioms VaryingAtlas.equivalent_iff_compatible
#print axioms VaryingAtlas.union
-- `C^{k,ℓ}` maps (`Manifold/Ckl.lean`)
#print axioms ContDiffMBOn₂.comp_prodMap
#print axioms contDiffMBOn₂_of_curry
#print axioms ContMDiffMB₂.continuous
#print axioms ContMDiffMB₂.contDiffMBOn₂
#print axioms locallyCompactSpace_of_compactSpace
#print axioms finiteDimensional_of_compactSpace
-- The exponential law (`MappingSpace/ExponentialLaw.lean`)
#print axioms LocalAddition.contMDiffOn_mappingAtlasCk_iff
#print axioms LocalAddition.equivalent_mappingAtlasCk_of_expLaw
#print axioms LocalAddition.contMDiffOn_mappingAtlasSm_iff
#print axioms LocalAddition.equivalent_mappingAtlasSm_of_expLaw
#print axioms LocalAddition.contMDiffMB₂_eval
#print axioms LocalAddition.smooth_eval
#print axioms LocalAddition.contMDiffMB₂_evalSm
#print axioms LocalAddition.smooth_evalSm
#print axioms VaryingAtlas.tangentCoordChangeEquiv
#print axioms VaryingAtlas.dMB_chart_eq_tangentMapAt
-- Normalization of local additions (`LocalAddition/Normalize.lean`)
#print axioms LocalAddition.alpha_beta
#print axioms LocalAddition.smoothMBM_normMap
#print axioms LocalAddition.smoothMBM_normMapInv
#print axioms LocalAddition.isNormalized_normalize
-- Tangent spaces of `C^ℓ(M, N)` (`MappingSpace/Tangent.lean`)
#print axioms LocalAddition.tangentMapAt_eval
#print axioms LocalAddition.coe_tangentEquivSecCk
#print axioms LocalAddition.tangentMapAt_evalSm
#print axioms LocalAddition.coe_tangentEquivSecSm
#print axioms LocalAddition.coe_tangentEquivSecCkOf
#print axioms LocalAddition.coe_tangentEquivSecSmOf
#print axioms LocalAddition.mappingAtlasCk_equivalent
#print axioms LocalAddition.mappingAtlasSm_equivalent
-- Iterated tangent bundles (`Tangent/Iterated.lean`)
#print axioms MBMfld.contMDiffMB_iterMap
#print axioms MBMfld.gnTopology_succ
#print axioms MBMfld.gnTopologySm_eq
-- The chart topology and the tangent map (`MappingSpace/Topology.lean`)
#print axioms continuous_tangentCk
#print axioms chartTopology_zero
#print axioms chartTopology_succ
-- The chart topology and the jet topology (`MappingSpace/Ck.lean`)
#print axioms CkMap.jetTopology_le_chartTopology
#print axioms CkMap.chartTopology_eq_jetTopology
#print axioms CkMap.topology_eq_chartTopology_of_compactSpace
#print axioms SmoothMap.chartTopologySm_eq_jetTopologySm
#print axioms SmoothMap.topology_eq_chartTopologySm_of_compactSpace
-- The chart topology and Definition 4.1.2 (`MappingSpace/TopologyGN.lean`)
#print axioms chartTopology_eq_gnTopology
#print axioms chartTopologySm_eq_gnTopologySm
-- The jet topology of `C^ℓ(M, N)` (`MappingSpace/TopologyJet.lean`)
#print axioms CkMap.continuous_jetTopology_iff
#print axioms MBMfld.gnTopology_le_jetTopology
#print axioms MBMfld.jetTopology_le_gnTopology
#print axioms CkMap.jetTopology_eq_gnTopology
#print axioms CkMap.jetTopology_eq_gnTopology_of_locallyCompactSpace
#print axioms SmoothMap.jetTopologySm_eq_gnTopologySm
#print axioms MBMfld.jetTopology_eq_chartTopology
-- Theorem 4.2.2(b), for every Hausdorff `M` (`MappingSpace/TopologyJet.lean`)
#print axioms CkMap.topology_eq_gnTopology
#print axioms SmoothMap.topology_eq_gnTopologySm
-- Targets in any universe, through `ULift` (`MappingSpace/TopologyULift.lean`)
#print axioms MBMfld.iterMap_comp
#print axioms MBMfld.gnTopology_eq_induced
#print axioms MBMfld.gnTopologySm_eq_induced
#print axioms MBMfld.jetTopologySm_eq_gnTopologySm
#print axioms CkMap.uliftHomeomorph
#print axioms SmoothMap.uliftHomeomorph
#print axioms CkMap.gnTopology_eq
#print axioms SmoothMap.gnTopologySm_eq
#print axioms CkMap.chartTopology_eq_gnTopology
#print axioms SmoothMap.chartTopologySm_eq_gnTopologySm
#print axioms SmoothMap.jetTopologySm_eq_gnTopologySm_of_locallyCompactSpace
-- Local additions on embedded submanifolds (`Submanifold/LocalAddition.lean`)
#print axioms IsEmbeddedSubmanifold.contMDiffMBOn_of_val
#print axioms IsEmbeddedSubmanifold.smoothMBM_ambient
#print axioms IsEmbeddedSubmanifold.contMDiffMBOn_of_ambient
#print axioms AmbientAddition.toLocalAddition
#print axioms AmbientAddition.isNormalized_toLocalAddition
-- A local addition on the sphere (`Examples/SphereLocalAddition.lean`)
#print axioms sphereLocalAddition
#print axioms sphereLocalAddition_toFun
#print axioms isNormalized_sphereLocalAddition
-- Local diffeomorphisms injective on compact sets (`Manifold/LocalDiffeo.lean`)
#print axioms exists_isOpen_injOn_of_isCompact
#print axioms IsLocalHomeomorph.exists_openPartialHomeomorph_of_isCompact
#print axioms exists_contMDiffMB_diffeo_of_isCompact
#print axioms exists_smoothMBM_diffeo_of_isCompact
#print axioms exists_realAnalyticMOn_diffeo_of_isCompact
-- Local diffeomorphisms near σ-compact sets (`Manifold/LocalDiffeo.lean`, GN 3.8.20–3.8.21)
#print axioms exists_isOpen_injOn_of_isSigmaCompact_image
#print axioms exists_isOpen_injOn_of_isSigmaCompact
#print axioms exists_openPartialHomeomorph_of_isSigmaCompact
#print axioms exists_contMDiffMB_diffeo_of_isSigmaCompact
#print axioms exists_smoothMBM_diffeo_of_isSigmaCompact
#print axioms exists_realAnalyticMOn_diffeo_of_isSigmaCompact
#print axioms locallyCompactSpace_of_finiteDimensional
#print axioms realAnalyticMOn_of_local
-- Real analytic tangent bundles, products, local additions (`Analytic/Bundle.lean`)
#print axioms TangentBundle.realAnalyticManifold
#print axioms Prod.realAnalyticManifold
#print axioms RealAnalyticMOn.prodMk
-- Split real analytic submanifolds (`Analytic/Submanifold.lean`)
#print axioms IsSplitAnalyticSubmanifold.realAnalyticManifold
#print axioms IsSplitAnalyticSubmanifold.realAnalyticMOn_of_val
#print axioms IsSplitAnalyticSubmanifold.realAnalyticMOn_ambient
#print axioms IsSplitAnalyticSubmanifold.realAnalyticMOn_of_ambient
#print axioms AnalyticAmbientAddition.toLocalAddition
#print axioms AnalyticAmbientAddition.isRealAnalytic_toLocalAddition
-- The real analytic local addition on the sphere (`Examples/SphereAnalytic.lean`)
#print axioms ScalarAnalytic.realAnalyticOn_of_differentiableOn
#print axioms ScalarAnalytic.realAnalyticOn_sqrt
#print axioms isSplitAnalyticSubmanifold_sphere
#print axioms realAnalyticManifold_sphere
#print axioms sphereAnalyticLocalAddition
#print axioms sphereAnalyticLocalAddition_toFun
#print axioms isRealAnalytic_sphereAnalyticLocalAddition
-- de Rham cohomology of `M × G` (`DifferentialForm/Homotopy.lean`)
#print axioms deRhamProdEquiv
-- Complex analytic extensions to complexifications (`Analytic/ComplexExtension.lean`)
#print axioms exists_glue_of_paracompact
#print axioms complexAnalyticMOn_of_local
#print axioms IsComplexification.exists_complexAnalytic_extension
-- The Lie derivative along a local flow (`Flow/LieDerivative.lean`)
#print axioms IsLocalForm.hasDirDerivAt_flow
#print axioms IsLocalFlow.hasDirDerivAt_pullback
-- Local flows on Banach manifolds (`Flow/Existence.lean`)
#print axioms SmoothVectorField.hasDerivAt_rep_of_chart
#print axioms SmoothVectorField.IsIntegralCurveOn.eqOn
#print axioms SmoothVectorField.exists_flowBox
#print axioms SmoothVectorField.smoothMBMOn_boxFlow
#print axioms SmoothVectorField.isLocalFlow_boxFlow
#print axioms SmoothVectorField.boxFlow_add
-- The maximal flow on Banach manifolds (`Flow/Maximal.lean`)
#print axioms SmoothVectorField.isIntegralCurveThrough_flow
#print axioms SmoothVectorField.IsIntegralCurveThrough.flow_eq
#print axioms SmoothVectorField.maxInterval_flow
#print axioms SmoothVectorField.add_mem_flowDomain
#print axioms SmoothVectorField.flow_add
#print axioms SmoothVectorField.isOpen_flowDomain
#print axioms SmoothVectorField.smoothMBMOn_flow
#print axioms SmoothVectorField.isLocalFlow_flow
#print axioms SmoothVectorField.hasDirDerivAt_pullback_flow
#print axioms SmoothVectorField.boxFlowDomain_subset_flowDomain
#print axioms SmoothVectorField.boxFlow_eq_flow
#print axioms SmoothVectorField.eventually_flow_not_mem_of_isCompact
#print axioms SmoothVectorField.eventually_flow_not_mem_of_isCompact'
-- A completeness criterion for vector fields (`Flow/Complete.lean`)
#print axioms SmoothVectorField.not_mapClusterPt_flow_of_notMem
#print axioms SmoothVectorField.Ioo_subset_maxInterval_of_norm_rep_le
#print axioms SmoothVectorField.flowDomain_eq_univ_of_forall_norm_rep_le
-- The maximal flow of a real analytic vector field (`Flow/Analytic.lean`)
#print axioms realAnalyticMOn_coe_chart
#print axioms realAnalyticMOn_chart_symm
#print axioms SmoothVectorField.exists_flowBox_realAnalyticMOn
#print axioms SmoothVectorField.realAnalyticMOn_flow
-- The Darboux theorem for strong symplectic forms (`Symplectic/Darboux.lean`)
#print axioms Darboux.exists_flow_of_stationary
#print axioms Darboux.exists_primitive
#print axioms Darboux.exists_darboux_local'
#print axioms Darboux.exists_darboux_local
#print axioms DifferentialForm.exists_darboux_chart
#print axioms SymplecticForm.IsStrong.exists_darboux_chart
#print axioms Darboux.exists_darboux_local_of_primitive
#print axioms DifferentialForm.exists_clm_localRep
#print axioms DifferentialForm.clm_localRep_spec
#print axioms DifferentialForm.darboux_chart_of_local
-- The real analytic Darboux theorem (`Symplectic/DarbouxAnalytic.lean`)
#print axioms Darboux.radialPrimitive_spec
#print axioms Darboux.realAnalyticOn_radialPrimitive
#print axioms Darboux.exists_primitive_realAnalytic
#print axioms Darboux.exists_darboux_local_realAnalytic'
#print axioms Darboux.exists_darboux_local_realAnalytic
#print axioms DifferentialForm.IsRealAnalytic.exists_clm_localRep
#print axioms DifferentialForm.exists_realAnalytic_darboux_chart
#print axioms SymplecticForm.IsStrong.exists_realAnalytic_darboux_chart
-- The canonical symplectic form on the cotangent bundle (`Symplectic/Cotangent.lean`)
#print axioms cotangentLiouville
#print axioms formLocalRep_liouvilleFun
#print axioms cotangentLiouville_localRep
#print axioms cotangentLiouville_d_apply
#print axioms cotangentSymplectic
#print axioms cotangentSymplectic_apply
#print axioms cotangentSymplectic_isExact
#print axioms cotangentSymplectic_isStrong_iff
-- Lema 9.1.8 fails without completeness of the model (`Examples/IncompleteFinsler.lean`)
#print axioms IncompleteFinsler.exists_not_continuous_ofFinsler
#print axioms IncompleteFinsler.exists_not_continuous_ofFinsler_c00
#print axioms IncompleteFinsler.not_completeSpace_c00
#print axioms IncompleteFinsler.GluingCurve.nonempty_of_not_completeSpace
#print axioms IncompleteFinsler.Glued.t2Space
#print axioms IncompleteFinsler.Glued.isBounded
#print axioms IncompleteFinsler.Glued.not_continuous_ofFinsler
#print axioms IncompleteFinsler.Glued.not_reach_exit
-- Maximal geodesics and the exponential map (`Geodesic/Maximal.lean`)
#print axioms Connection.isGeodesicThrough_maxGeodesic
#print axioms Connection.IsGeodesicThrough.maxGeodesic_eq
#print axioms Connection.maxInterval_smul
#print axioms Connection.maxGeodesic_smul
#print axioms Connection.smul_mem_expDomain_iff
#print axioms Connection.exp_smul
#print axioms Connection.expDomain_eq_univ_of_maxInterval_eq_univ
#print axioms Connection.exists_expDomainAt_eq_univ
-- The geodesic spray; `D(exp)` is open and `exp` is smooth (`Geodesic/GeodesicSpray.lean`)
#print axioms Connection.spray
#print axioms Connection.rep_spray
#print axioms Connection.spray_isSecondOrder
#print axioms Connection.IsGeodesicOn.isIntegralCurveOn_velocity
#print axioms Connection.isGeodesicOn_proj_of_isIntegralCurveOn
#print axioms Connection.maxInterval_eq_spray
#print axioms Connection.maxGeodesic_eq_proj_flow
#print axioms Connection.isOpen_expDomain
#print axioms Connection.smoothMBMOn_exp
#print axioms Connection.smoothMBMOn_expAt
#print axioms Connection.starConvex_expDomainAt
-- `exp_p` is a local diffeomorphism; uniformly normal neighbourhoods (`Geodesic/Normal.lean`)
#print axioms exists_openPartialHomeomorph_of_contDiffOn
#print axioms Connection.hasFDerivAt_expAt_zero
#print axioms Connection.exists_expAt_openPartialHomeomorph
#print axioms Connection.hasFDerivAt_expChart
#print axioms Connection.exists_expPair_openPartialHomeomorph
#print axioms Connection.exists_expPair_normal
#print axioms Connection.exists_uniformlyNormal
-- Proposición 9.2.1 of *Estructuras* (`Metric/FinslerExp.lean`)
#print axioms Connection.maxInterval_eq_univ_of_complete
#print axioms Connection.expDomain_eq_univ_of_complete
#print axioms Connection.exists_expDomainAt_eq_univ_of_complete
-- Projector fields on submanifolds of a Krein space (`Metric/KreinProjector.lean`)
#print axioms ProjectorField.isOrthoComplemented_of_isOrthogonal
#print axioms ProjectorField.isKreinSpace_of_isOrthogonal
#print axioms ProjectorField.continuous_E_of_isOrthogonal
-- Manifolds with rough boundary, Glöckner–Neeb §3.5 (`RoughBoundary/Basic.lean`)
#print axioms ContDiffLC.mem_interior_of_rightInvOn
#print axioms IsRoughChart.mem_interior_of_trans
#print axioms RoughAtlas.mem_interior_iff
#print axioms RoughAtlas.mem_boundary_iff
#print axioms RoughAtlas.maximal
#print axioms RoughAtlas.maximal_isMaximal
#print axioms RoughAtlas.maximal_atlas_eq
#print axioms RoughAtlas.boundary_maximal
#print axioms RoughAtlas.ContMDiff.comp
#print axioms RoughAtlas.contMDiff_maximal_iff
#print axioms RoughAtlas.ofChartedSpace
#print axioms RoughAtlas.boundary_ofChartedSpace
#print axioms RoughAtlas.prod
#print axioms RoughAtlas.boundary_prod
#print axioms RoughAtlas.ofSubset
#print axioms RoughAtlas.boundary_ofSubset
#print axioms RoughAtlas.halfSpace
#print axioms RoughAtlas.unitInterval
#print axioms RoughAtlas.boundary_unitInterval
-- Open subsets, full submanifolds and corners (`RoughBoundary/Submanifold.lean`)
#print axioms RoughAtlas.boundary_restrict
#print axioms RoughAtlas.boundary_fullSubmanifold
#print axioms RoughAtlas.boundary_quadrantAtlas
#print axioms RoughAtlas.isWithCorners_quadrantAtlas
-- Submanifolds modeled on closed subspaces (`RoughBoundary/Subspace.lean`)
#print axioms RoughAtlas.submanifold
-- Graphs (`RoughBoundary/Graph.lean`)
#print axioms RoughAtlas.exists_roughGraphChart
#print axioms RoughAtlas.boundary_graphSubmanifold
-- The tangent bundle of a manifold with rough boundary, G–N 3.5.22 (`RoughBoundary/TangentBundle.lean`)
#print axioms ContDiffLCUpTo.tangent
#print axioms RoughAtlas.tangentCoordChange_comp
#print axioms RoughAtlas.exists_clm_tangentCoordChange
#print axioms RoughAtlas.tangentBundleCore
#print axioms RoughAtlas.tangentChart_trans_eqOn
#print axioms RoughAtlas.tangentAtlas
#print axioms RoughAtlas.boundary_tangentAtlas
#print axioms RoughAtlas.contMDiff_proj
#print axioms RoughAtlas.dLC_localRep_change
#print axioms RoughAtlas.tangentChart_tangentMap
#print axioms RoughAtlas.continuous_tangentMap
#print axioms RoughAtlas.contMDiff_tangentMap
#print axioms RoughAtlas.tangentMap_id
#print axioms RoughAtlas.tangentMap_comp
#print axioms RoughAtlas.tangentCoordChange_ofChartedSpace
-- Newlander–Nirenberg on Banach manifolds (`Complex/NewlanderNirenberg.lean`)
#print axioms AlmostComplexStructure.exists_holomorphic_chart
#print axioms AlmostComplexStructure.IsHolomorphicChart.complexAnalyticOn_transition
-- The Frobenius theorem on Banach manifolds (`VectorField/Frobenius.lean`)
#print axioms localBracket_eq_lieBracket
#print axioms lieBracket_conj
#print axioms frob_of_localBracket
#print axioms fderiv_mem_graph_iff
#print axioms Distribution.IsInvolutive.frob
#print axioms Distribution.IsInvolutive.exists_flat_chart
#print axioms Distribution.isInvolutive_of_flat
#print axioms Distribution.isInvolutive_iff_flat
