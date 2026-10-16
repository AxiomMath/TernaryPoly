module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Frame
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Cone.Stokes
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Face.Pairing
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.ConjInvariance
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.ComplexStokes
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Cut
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Orth
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.ShapiroCut
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.OrbitPairing
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.OrbitStokes
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.QComparison
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Gamma6
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.ConjRestriction
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.PointLevel
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Face.Dictionary
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Face.Pairs
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Line.Orbits
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Plane.Orbits
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Flag.Orbits
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Gamma6.Faces
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Gamma6.Stokes
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Flag.Vanish
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Gamma6.Final
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.CoordNat
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Geo
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Glue
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Flag.Lifts
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.MixedTransfer
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Face.PairingLifts
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.CoefNat
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Face.PairingBil
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.FamAct
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.OrthCoef
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Face.Orth
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Face.Components
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Gamma6.Decomp
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Flag.Stab
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Flag.Ext
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.ShapiroProductS
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Face.CoordRes
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Const.Graph
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Const.Phi
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Const.Rel
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Const.Uniform
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Const.Nonzero
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Const.Final
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BLine5
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BPlane4
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BPG4
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BPG8
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BPG9

@[expose] public section


/-!
# Lemma `ar:lem:stokes` at level `Γ(N)`: reduction to the boundary frame

Formalized by Claude Sonnet 5.5.  The relation
`⟨r_P a, r_P b⟩_P + ∑ ⟨r_Q a, r_Q b⟩_Q = 0` is proved from the three steps of the paper's proof (geometric Stokes, mapping-cone decomposition,
orthogonality), recorded as the fields of `BoundaryFrame`.  `cone_stokes_gamma6` proves, for every rational coefficient system of `Γ(6)`, those three steps in the
model cone (geometric Stokes, lift decomposition, orthogonality of line-type and plane-type cocycles).

The face pairings are the cone pairings of the lifts of the face
classes (a choice-free function of the Shapiro coordinate, defined to be `0` on classes without lift); that they are bilinear forms equal to the algebraic face pairings, the lifts of arbitrary
mixed cuspidal classes and the passage to general `N` are not addressed here.

Orthogonality and decomposition of the face pairings along `S`-equivariant idempotents of the coefficients (label-dependent
conjugates `ρ(γ) e ρ(γ)⁻¹` applied pointwise to the lifts, adjointness of the cone pairing): `lineFacePairM_orth`, `lineFacePairM_decomp` and the plane analogues; the face pairing of lifts in coordinates
(base term on the flag component, line or plane term on the line or plane component of the Stokes cycle): `lineFacePairM_coords`, `planeFacePairM_coords`.
-/

namespace TernaryPeriodPolynomials.Argument.Statements.GammaNStokes

open TernaryPeriodPolynomials.Argument.GammaNStokes

alias cone_stokes_gamma6 := cone_stokes
alias cone_cross_orthogonal := cone_cross_zero
alias gammaN_stokes := BoundaryFrame.stokes
alias gammaN_stokes_of_comparison := BoundaryFrame.stokes_of_comparison
alias gammaN_face_obligations_of_frame := BoundaryFrame.toFaceObligations
alias gamma6_stokes_complex := cone_stokes_complex
alias gamma6_stokes_orbits := cone_stokes_orbits
alias gamma6_line_pairing_of_coordinates := LineDatum.pairC_eq_of_coord_eq
alias gamma6_plane_pairing_of_coordinates := PlaneDatum.pairC_eq_of_coord_eq
alias h2_inner_automorphism_trivial := h2Map_conj_self
alias gamma6_stokes_E_n := gamma6_stokes_En
alias gamma6_stokes_global_classes := gamma6_stokes_of_zeroFlags
alias gamma6_line_faces_equiv_orbits := lineFacesEquivOrbits
alias gamma6_plane_faces_equiv_orbits := planeFacesEquivOrbits
alias gamma6_equiv_principal_six := gammaSixEquiv
alias gamma6_stokes_cone_geo := cone_stokes_geo
alias gamma6_stokes_cycle_glue := stokesCycle_glue
alias gamma6_cone_pairing_geometric := conePairC_geo
alias gamma6_line_mixed_lifts := lineFace_exists_lifts
alias gamma6_plane_mixed_lifts := planeFace_exists_lifts
alias gamma6_line_face_pairing_bilinear := lineFacePairBil
alias gamma6_plane_face_pairing_bilinear := planeFacePairBil
alias gamma6_line_mixed_liftable := LineMixedModel_liftable
alias gamma6_line_face_pairing_orthogonal := lineFacePairM_orth
alias gamma6_plane_face_pairing_orthogonal := planeFacePairM_orth
alias gamma6_line_face_pairing_decomposition := lineFacePairM_decomp
alias gamma6_plane_face_pairing_decomposition := planeFacePairM_decomp
alias gamma6_line_face_pairing_components := lineFacePairM_coords
alias gamma6_stokes_decomposed_family := gamma6_stokes_decomposed
alias gamma6_flag_stabilizer_equiv := flagStabEquiv
alias gamma6_flag_stabilizer_extension := flagStabExt
alias gamma6_plane_face_pairing_components := planeFacePairM_coords
alias gamma6_plane_mixed_liftable := PlaneMixedModel_liftable
alias gamma6_face_coord_flag_line := faceCoord_flagLine
alias gamma6_face_coord_flag_plane := faceCoord_flagPlane
alias gamma6_orbit_graph_invariant_const := orbit_invariant_const
alias gamma6_corner_functional_line_relation := line_relation
alias gamma6_corner_functional_plane_relation := plane_relation
alias gamma6_corner_functional_nonzero := exists_flagPhi_ne_zero
alias gamma6_corner_coefficient_universal := lambda_universal
alias gamma6_face_constants := face_constants
alias gamma6_line_image_sum_zero := lineImageSumZero
alias gamma6_plane_image_sum_zero := planeImageSumZero
alias gamma6_line_transport_lambda := lineTransport_lam
alias gamma6_plane_transport_lambda := planeTransport_lam
alias gamma6_flag_orbit_cusp_injective := cuspMap_injective
alias gamma6_flag_orbit_cusp_surjective := cuspMap_surjective
alias gamma6_flag_orbit_cusp_injective_plane := cuspMapP_injective
alias gamma6_flag_orbit_cusp_surjective_plane := cuspMapP_surjective

alias gamma6_plane_flag_family := Pc
alias gamma6_plane_flag_family_plane := Pc_flagPlane
alias gamma6_plane_flag_stabilizer_radical := Pc_stab_nl
alias gamma6_plane_flag_stabilizer_levi := Pc_stab_ll
alias gamma6_plane_flag_orbit_injective := Pc_orbit_inj
alias gamma6_plane_flag_orbit_surjective := Pc_orbit_surj
alias gamma6_plane_test_calibration := plane_calibration
alias gamma6_plane_test_radical_A := planeE_inl_A
alias gamma6_plane_test_radical_v := planeE_inl_v
alias gamma6_plane_test_levi_A := planeE_split_A
alias gamma6_plane_test_levi_v := planeE_split_v

end TernaryPeriodPolynomials.Argument.Statements.GammaNStokes
