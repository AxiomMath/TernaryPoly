module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Perfect
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.InnerBoundaryCusps
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.FacePairingNondegenerate
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Dual.ConstantTerms
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Plane.Pairing
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.Cusps
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.CuspIso
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.InnerDecomposition
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.RightNondegenerate
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.BadLineParabolic
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.PerfectOdd
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.LiteralPairing
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.PlaneZeroDegree
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.StokesPairing
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.PLeftKernel
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Swap.Perfect
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Literal.Pairing
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Literal.Bijective
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Literal.FaceIdentification
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Literal.GoodLineIdentification
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Literal.BadPlaneIdentification
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Literal.GoodPlaneIdentification
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Graph
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.StandardOperator
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Stokes
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.StandardOperatorLinear
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.BoundaryCohomology
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.DualJ.DualSeries
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Coefficients
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Flags
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.LevelConj
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.LevelSix
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.BoundaryTopClass
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Cone.Corner
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.BoundaryH4
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.GeoStokes
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Model.CupP
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.NerveDiagonal
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.PairingCone
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.RationalPairing

@[expose] public section


/-!
# Face pairings, mixed cuspidal classes, and the dual constant terms (Appendix C.2, C.4)

Statements around the target `face_pairing_perfect` (the perfect line pairing
`ar:eq:facepair`, `R = Q`), proved in `Revision/Proofs/FacePairingFull`:

* `innerBoundary_iff_locallyInner_cusps`, `innerBoundary_line_iff_mixedCuspidal`:
  `InnerBoundary` is exactly the mixed cuspidal condition (zero restriction to the face radical and
  cuspidal binary restriction, end of Appendix C.4) at the bad reference line, and local
  innerness at the good reference line;
* `innerBoundary_line_iff_hs`, `innerBoundary_plane_iff_hs`: the same for all four reference cusps
  (good and bad line, good and identity plane) in Hochschild-Serre form, for every degree: zero
  restriction to the face radical and vanishing mixed class on the binary stabilizer of every
  complete flag over the reference flag (`HSInner`);
* `radicalKernelMixedMap_surjective`: Hochschild-Serre surjectivity (every class of `H¹(L, H¹(N, E))` is
  the mixed class of a radical-zero two-cocycle) for a split extension whose Levi has vanishing
  `H²`, proved without `H³` by lifting crossed cocycles through `Z¹(N, E) → H¹(N, E)`;
  `locallyInner_equiv_cuspidal_*`: at each of the four reference cusps the locally inner classes
  are isomorphic to the mixed cuspidal group `𝒞_F(E) ⊂ H¹(L_F, H¹(N_F, Sym^n))`;
* `innerClasses_line_equiv_cuspidal`, `innerClasses_plane_equiv_cuspidal`: the inner classes of a side
  are the direct sum of the mixed cuspidal groups of its good and bad reference cusps (Shapiro
  decomposition composed with the Hochschild-Serre isomorphisms);
* `facePairing_perfect_of_finrank_eq`: the right kernel of the line pairing is zero as soon as the
  two inner spaces are finite dimensional of the same dimension;
* `badLine_locallyInner_equiv_parabolic`, `finrank_badLine_locallyInner`: the locally inner classes at the
  standard bad line are exactly the parabolic classes of `H¹(Γ₁'(3), Sym^{n+1})` (Kostant isomorphism
  plus parabolic-at-`T`,`L` implies parabolic at every rational cusp), of dimension `⌊(n+3)/3⌋ - 1`;
* `goodPlane_locallyInner_equiv_parabolic`, `badPlane_locallyInner_equiv_parabolic`: the same for the good
  plane (level three, `Sym^{n+1} ⊗ det⁻¹`) and, for odd `n`, the identity plane (level one), through the
  edge maps and the cuspidal supply; `finrank_parabolic_le_goodLine`: the parabolic classes of
  `Sym^{n+1}` are realized by locally inner classes at the good line (Hochschild-Serre realization);
* `facePairing_right_nondegenerate`: **the right kernel of the line pairing is zero for every `n > 0`**,
  so `ar:eq:facepair` for `R = Q` is perfect in both arguments (`facePairing_perfect`);
  `innerClasses_plane_zero_eq_bot`: at `n = 0` there is no inner plane class (dual transport of the
  vanishing of the inner line classes), so `facePairing_perfect_all` holds for every `n`;
* `levelOne_pairing_perfect`, `levelThree_pairing_perfect_odd/even`: the literal per-face pairings
  `⟨ , ⟩_F` (parabolic cup pairings on the cuspidal groups of the four reference faces, whose
  identification with the locally inner classes is given by the equivalences above) are perfect in both
  arguments;
* `facePairing`, `facePairing_left_nondegenerate`: the line face pairing is a well-defined bilinear
  form on inner classes (independent of all representatives and primitives) with zero left kernel
  for every `n`;
* `facePairingP`: the plane face pairing `⟨ , ⟩_P` is a well-defined bilinear form on inner classes;
* `vertex_reversal_neg_H2`, `facePairing_swap_relation`, `facePairingP_perfect_all`: **the swap relation
  `⟨B, A⟩_Q = ± ⟨A, B⟩_P` between the two cochain face pairings** (vertex reversal is `-1` on `H²` and
  commutes, up to the explicit edge coboundary of `Swap/Comparison`, with the boundary cup product
  composed with the dual involution; the sign is the scalar of `levelTrace ∘ R = ± levelTrace` from the
  uniqueness of boundary traces) and hence **`ar:eq:facepair` for `R = P`: `⟨ , ⟩_P` is perfect in both
  arguments for every `n`**;
* `dual_constant_terms_pointwise`, `dual_constant_terms`: `ar:eq:dualconstantterms` for the dual
  coefficient system `E* = E ∘ φ`.

* `facePairing_even_literal`, `facePairing_odd_literal`, `facePairingP_even_literal`, `facePairingP_odd_literal`:
  **comparison of the cochain face pairings with the literal per-face parabolic pairings for arbitrary inner
  classes** (`Proofs/FacePairingFull/Literal/*`). For `n > 0` even, `⟨b, ξ⟩_Q = ((n+1)!/3)·⟨b_bl, ξ_gp⟩_{Γ₁'(3)}`;
  for `n` odd, `⟨b, ξ⟩_Q = (-(n+1)!/3)·⟨b_bl, ξ_gp⟩_{Γ₁'(3)} + (n+1)!·⟨b_gl, ξ_bp⟩_{GL₂(ℤ)}`, where
  `b_bl = -badLineEdge(cuspRes_false b)`, `ξ_gp = goodPlaneEdge(cuspRes_true ξ)`, `b_gl = phiL(cuspRes_true b)`,
  `ξ_bp = edgeH2(cuspRes_false ξ)` are parabolic classes (restriction to the cusp stabilizer, then the Kostant edge
  map); the constants are the nonzero scalars `c_n` of convention C4, block by block; the plane pairing is `a = ±1`
  times the same expressions (swap relation);

* `badLineParabolic_bijective_even`, `goodPlaneParabolic_bijective_even`, `lineDictionaryOdd_bijective`,
  `planeDictionaryOdd_bijective`: **the dictionary maps are linear isomorphisms of the inner classes onto the parabolic
  cohomology of the reference faces** (injective by the comparison theorems and the nondegeneracy of the cochain pairing,
  surjective by the exact dimension count); `badLineParabolic_eq_face`, `goodPlaneParabolic_eq_face`,
  `badPlaneParabolic_eq_face`: the dictionary equals the parabolic identifications of `Face/*` at the bad line (with a minus
  sign; there it is the Hochschild-Serre composite) and at the two planes (there `Face/*` defines the identification by the
  same edge maps, so this is definitional; the genuine Hochschild-Serre comparison at the planes is
  `badPlaneParabolic_eq_hs`, `goodPlaneParabolic_eq_hs` below);

* `goodLineParabolic_eq_hs`, `parabolicToGoodLine_goodLineParabolic`, `badPlaneParabolic_eq_hs`, `goodPlaneParabolic_eq_hs`:
  **the explicit edge dictionaries at the good line, the identity plane and the good plane are the Hochschild-Serre
  dictionaries, with sign `+1`** (`Literal/GoodLineIdentification`, `BadPlaneIdentification`, `GoodPlaneIdentification`):
  the edge map factors through the generic Hochschild-Serre isomorphism `locallyInnerEquivCuspidal` of `Face/Iso`
  (mixed class of a radical-zero representative) followed by the Kostant coordinate. At the good plane the stabilizer is
  presented by the library's own splitting conjugated by the rational frame `gF` (`GoodPlanePresentation`: the conjugation
  transport of the library and the inhomogeneous face cocycle differ by an explicit prism coboundary). Together with
  `badLineParabolic_eq_face` (sign `-1` at the bad line) all four edge-map dictionaries are compared with Hochschild-Serre
  composites; the comparison is with the library-native presentation of each stabilizer;
* `graph_containment_pair`, `graph_containment`: **`ar:prop:graph`** (`Graph.lean`): a global class with zero flag
  restrictions has line restriction `ξ_Q = T ξ_P` for the constant-term map `T` (`exists_constant_term_map`), by two
  Stokes relations, subtraction and the perfect line pairing; no invertibility or adjoint normalization of `T^∨`;
* `paper_stokes` (`PaperStokes.lean`): **`ar:lem:stokes` in the paper's form** `⟨r_P a, r_P b⟩_P + ⟨r_Q a, r_Q b⟩_Q = 0` for `a = c` (class of
  `E`) and `b = ȷ`-dual of `c'` (class of `E*`) with zero flag restrictions, with `⟨ , ⟩_P = facePairingP`, `⟨ , ⟩_Q = - facePairing`
  (the orientation sign forced by the mapping-cone convention) and the `E*`-face components paired through the transports
  `fromPlaneStar`/`fromLineStar`. This pins the relative orientation sign of the two face pairings inside the model; it is not a
  comparison with oriented faces of the Borel-Serre boundary (no face fundamental classes or de Rham integration over faces exist);
* `standardLine_eq_of_graph`, `standardLine_eq_T` (`StandardOperator.lean`): **the linearly selected constant-term map `T` is the
  standard (convergent) operator**: for every plane source cocycle `c` of every cohomological datum, `T [c] = [sourceStandard c]`
  (the class of the absolutely convergent standard line cocycle), because the explicit convergent global cocycle has coordinates
  `([c], [sourceStandard c])` and zero flag restrictions and `ar:prop:graph` forces its line coordinate;
* `standard_eq_T` (`StandardOperatorLinear.lean`, with the `StandardConv.realizesStandardConv_apply_eq_sourceStandard`): for every linear
  `standard : boundarySummand D .plane → boundarySummand D .line` with `RealizesStandardConv D standard` and every `T` with the graph property,
  `standard x = T x` on the whole summand;
* `modelBoundary_cohomology_iso`, `modelBoundary_cohomology_iso_E` (`Comparison/BoundaryCohomology.lean`): **the cohomology of the model boundary
  cone with coefficients `W` (any rational `Γ(6)`-module, in particular `Sym^n ⊗ det^e`) is the genuine `H^k(∂M; W)`, in every degree**
  (M's homotopy equivalence `coneEquiv` composed with the library's quasi-isomorphism `localBoundaryToStabilizerTotal`);
* `geoPairing`, `geoPairingEquiv`, `geoPairing_right_injective` (`Comparison/GeoPairing.lean`): the **geometric Poincaré-duality pairing**
  `H²(∂M; V*) × H²(∂M; V) → ℚ` of the closed oriented arithmetic boundary (Kronecker pairing with the cap product with the
  boundary fundamental class), left perfect against the full dual and right non-degenerate.  `geoPairingBoundary` is the one for
  `boundaryOrientation`.  The comparison with the cochain model's `facePairing` is not asserted.
* `geoPairingBoundary_restriction` (geometric Stokes: restrictions of `H²(M̄; V*)` and `H²(M̄; V)` pair to zero on `∂M`) and
  `geoPairingBoundary_annihilator_iff` (`Comparison/GeoStokes.lean`; Lagrangian property: a class of `H²(∂M; V*)` annihilates
  `res H²(M̄; V)` iff it lies in `res H²(M̄; V*)`; Lefschetz duality of `(M̄, ∂M)` plus universal coefficients).
* `modelCup_eq`, `modelCup_isCocycle`, `boundaryValue_eq_cone`, `traceValue_eq_evalOmega` (`Comparison/ModelCup.lean`,
  `ModelDiagonal.lean`, `PairingCone.lean`): the Alexander-Whitney cup product on homogeneous cochains and on the homotopy pullback of
  the line and plane complexes over the corner complex (Leibniz rule), and the identification of the model's boundary cup
  product `w ⌣ y^φ - γ` with the corner component of the cone cup product of the cone cocycles `(z, 0, w)` and `(y^φ, 0, s^φ)`;
  the face pairing value is `c ≠ 0` times `evalOmega Ω` of it (whole-boundary trace comparison).  `Bhom_complexify`
  (`RationalPairing.lean`) is the rational form of the coefficient pairing.
* `modelCupP_eq`, `boundaryValueP_eq_cone`, `traceValueP_eq_evalOmega` (`Comparison/ModelCupP.lean`): the plane-supported twin
  (`dualityDataP`) of the above for `⟨ , ⟩_P`.
* `nerveDelta`, `nerveDelta_d`, `nerveEps`, `nerveDelta_counit_left`, `nerveDelta_counit_right`, `nerveDelta_natural`
  (`Comparison/NerveDiagonal.lean`): the Alexander-Whitney diagonal of the resolutions `ℚ[V^{•+1} × Z]` as morphisms of
  representations with Leibniz rule, counit and strict naturality in `Z`.
* `jmath_eq_conj`, `mem_plane_jmath_iff`, `mem_line_jmath_iff`, `coefficient_intertwines`, `dualPairingJ_invariant`,
  `toLineStar_eq_jDual`, `jDual_edgeExact`, `dual_constant_terms_jmath`, `dual_series_coordinates_unique`:
  **the paper's `ȷ(g) = J (g⁻¹)ᵀ J` and the dual series through it** (`DualJ/*`): `ȷ = Ad(J a⁻¹) ∘ φ`, `ȷ` exchanges
  the two parabolics, `ρ(J a⁻¹)` carries `E ∘ φ` to `E ∘ ȷ`, the transport maps to `E*` are the `ȷ`-pullbacks of the
  conjugated cochains, `𝓔_Q^∨(η)` has `r_Q = η`, `r_P = T^∨η`, `r_B = 0`, and `T^∨` is determined by graph containment.

Not covered: the comparison of the Hochschild-Serre composite at the good plane in the presentation of `Face/GoodPlane`
(transported from the bad line along `φ`, at the flag `dualFlag standardBadLine`) with the one used here,
the Hecke compatibility of the face pairings,
the adelic intertwiner `ar:eq:intertwiner` as a named operator (it is the formula of `T`; its entry computation is not part
of this file), the geometric (de Rham / Stokes / orientation) normalization of the face dictionaries, and the comparison of
the cochain model with Borel-Serre / de Rham / Petersson objects (the whole-boundary trace comparison is in
`Statements.TraceComparison`). The construction "applied to `ȷ(Γ)`" is represented by the `Ad_w`-conjugate of the construction
for `Γ` (the paper's convention for rational conjugates); the existence of the construction for `ȷ(Γ)` as an
independent object is not separately proved.

Formalized by Claude Sonnet 5.5.
-/

namespace TernaryPeriodPolynomials.Argument.Statements.FacePairing

open GeneralEisenstein Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (goodLineSplitting identityPlaneSplitting)
open TernaryPeriodPolynomials.Argument.FacePairingFull
open TernaryPeriodPolynomials.Duality (differentialOneRaw)
open TernaryPeriodPolynomials.SphericalDetection.Helpers (arithmeticBinaryRep)
open TernaryPeriodPolynomials.Spectral.CuspOrbits (cuspFlag)
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.ArithmeticGenerators
  (upper lower)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
  (parabolicCrossedH1)

/-- **Perfect line pairing, zero left kernel form.** For every `n`, a class `b` of the inner line
classes pairing to zero with every inner plane class is zero. -/
theorem face_pairing_line_left_nondegenerate (n : ℕ) (b : innerClasses n .line)
    (h : ∀ ξ : innerClasses n .plane, facePairing n b ξ = 0) : b = 0 :=
  facePairing_left_nondegenerate n b h

/-- **Line `InnerBoundary` in Hochschild-Serre form** at the good line and the standard bad line. -/
theorem innerBoundary_line_iff_hs (degree : ℕ) (b : StratumH2 degree trivialCharacter .line) :
    InnerBoundary degree trivialCharacter .line b ↔
      Face.HSInner goodLineSplitting.conjAct degree trivialCharacter Face.goodLineFlag
          Face.goodLineSemidirectEquivFixed
          (fixedPointH2 rationalLevel (rationalCoefficientComponent degree trivialCharacter)
            Face.goodLineFlag b) ∧
      Face.HSInner integralBadLineSplitting.conjAct degree trivialCharacter standardBadLine
          standardBadLineSemidirectEquiv
          (fixedPointH2 rationalLevel (rationalCoefficientComponent degree trivialCharacter)
            standardBadLine b) :=
  Face.innerBoundary_line_iff_hs degree b

/-- **Plane `InnerBoundary` in Hochschild-Serre form** at the good plane and the identity plane. -/
theorem innerBoundary_plane_iff_hs (degree : ℕ) (b : StratumH2 degree trivialCharacter .plane) :
    InnerBoundary degree trivialCharacter .plane b ↔
      Face.HSInner integralBadLineSplitting.conjAct degree trivialCharacter Face.goodPlaneFlag
          Face.goodPlaneSemidirectEquiv
          (fixedPointH2 rationalLevel (rationalCoefficientComponent degree trivialCharacter)
            Face.goodPlaneFlag b) ∧
      Face.HSInner identityPlaneSplitting.conjAct degree trivialCharacter Face.badPlaneFlag
          Face.badPlaneSemidirectEquiv
          (fixedPointH2 rationalLevel (rationalCoefficientComponent degree trivialCharacter)
            Face.badPlaneFlag b) :=
  Face.innerBoundary_plane_iff_hs degree b

/-- **Hochschild-Serre surjectivity** for a split stabilizer with Levi of vanishing `H²`. -/
theorem radicalKernelMixedMap_surjective {Radical Levi Value : Type} [Group Radical] [Group Levi]
    [AddCommGroup Value] [Module ℂ Value] (action : Levi →* MulAut Radical)
    (representation : Representation ℂ (SemidirectProduct Radical Levi action) Value)
    (hL : Face.LeviH2Vanishes Levi) :
    Function.Surjective (radicalKernelMixedMap action representation) :=
  Face.radicalKernelMixedMap_surjective action representation hL

/-- **Standard bad line: locally inner classes `≅` mixed cuspidal group.** -/
theorem locallyInner_equiv_cuspidal_badLine (degree : ℕ) (character : RankOneCharacter) :
    Nonempty (locallyInnerClasses degree character .line standardBadLine ≃ₗ[ℂ]
      Face.FaceCuspidal integralBadLineSplitting.conjAct degree character standardBadLine
        standardBadLineSemidirectEquiv) :=
  ⟨Face.badLineLocallyInnerEquiv degree character⟩

/-- **Good line: locally inner classes `≅` mixed cuspidal group.** -/
theorem locallyInner_equiv_cuspidal_goodLine (degree : ℕ) (character : RankOneCharacter) :
    Nonempty (locallyInnerClasses degree character .line Face.goodLineFlag ≃ₗ[ℂ]
      Face.FaceCuspidal goodLineSplitting.conjAct degree character Face.goodLineFlag
        Face.goodLineSemidirectEquivFixed) :=
  ⟨Face.goodLineLocallyInnerEquiv degree character⟩

/-- **Identity plane: locally inner classes `≅` mixed cuspidal group.** -/
theorem locallyInner_equiv_cuspidal_badPlane (degree : ℕ) (character : RankOneCharacter) :
    Nonempty (locallyInnerClasses degree character .plane Face.badPlaneFlag ≃ₗ[ℂ]
      Face.FaceCuspidal identityPlaneSplitting.conjAct degree character Face.badPlaneFlag
        Face.badPlaneSemidirectEquiv) :=
  ⟨Face.badPlaneLocallyInnerEquiv degree character⟩

/-- **Good plane: locally inner classes `≅` mixed cuspidal group.** -/
theorem locallyInner_equiv_cuspidal_goodPlane (degree : ℕ) (character : RankOneCharacter) :
    Nonempty (locallyInnerClasses degree character .plane Face.goodPlaneFlag ≃ₗ[ℂ]
      Face.FaceCuspidal integralBadLineSplitting.conjAct degree character Face.goodPlaneFlag
        Face.goodPlaneSemidirectEquiv) :=
  ⟨Face.goodPlaneLocallyInnerEquiv degree character⟩

/-- **Line side:** inner classes `≅` good-line cuspidal group `×` bad-line cuspidal group. -/
theorem innerClasses_line_equiv_cuspidal (n : ℕ) :
    Nonempty (innerClasses n .line ≃ₗ[ℂ]
      Face.FaceCuspidal goodLineSplitting.conjAct n trivialCharacter Face.goodLineFlag
          Face.goodLineSemidirectEquivFixed ×
        Face.FaceCuspidal integralBadLineSplitting.conjAct n trivialCharacter standardBadLine
          standardBadLineSemidirectEquiv) :=
  ⟨Face.innerClassesLineEquiv n⟩

/-- **Plane side:** inner classes `≅` good-plane cuspidal group `×` identity-plane cuspidal group. -/
theorem innerClasses_plane_equiv_cuspidal (n : ℕ) :
    Nonempty (innerClasses n .plane ≃ₗ[ℂ]
      Face.FaceCuspidal integralBadLineSplitting.conjAct n trivialCharacter Face.goodPlaneFlag
          Face.goodPlaneSemidirectEquiv ×
        Face.FaceCuspidal identityPlaneSplitting.conjAct n trivialCharacter Face.badPlaneFlag
          Face.badPlaneSemidirectEquiv) :=
  ⟨Face.innerClassesPlaneEquiv n⟩

/-- **Zero right kernel from equal dimensions** (the left kernel is zero for every `n`). -/
theorem facePairing_perfect_of_finrank_eq (n : ℕ)
    [FiniteDimensional ℂ (innerClasses n .line)] [FiniteDimensional ℂ (innerClasses n .plane)]
    (hdim : Module.finrank ℂ (innerClasses n .line) = Module.finrank ℂ (innerClasses n .plane)) :
    ∀ ξ : innerClasses n .plane, (∀ b : innerClasses n .line, facePairing n b ξ = 0) → ξ = 0 :=
  TernaryPeriodPolynomials.Argument.FacePairingFull.facePairing_perfect_of_finrank_eq n hdim

/-- **Bad line: locally inner classes `≅` parabolic `H¹(Γ₁'(3), Sym^{n+1})`** (`n > 0`). -/
theorem badLine_locallyInner_equiv_parabolic (n : ℕ) (positive : 0 < n) :
    Nonempty (locallyInnerClasses n trivialCharacter .line standardBadLine ≃ₗ[ℂ]
      parabolicCrossedH1 (binaryArithmeticRepresentation n)) :=
  ⟨Face.badLineLocallyInnerEquivParabolic n positive⟩

/-- **Exact dimension at the standard bad line:** `dim + 1 = ⌊(n + 3)/3⌋`. -/
theorem finrank_badLine_locallyInner (n : ℕ) (positive : 0 < n) :
    Module.finrank ℂ (locallyInnerClasses n trivialCharacter .line standardBadLine) + 1 =
      (n + 3) / 3 :=
  Face.finrank_badLine_locallyInner n positive

/-- **Good plane: locally inner classes `≅` parabolic `H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)`** (`n > 0`). -/
theorem goodPlane_locallyInner_equiv_parabolic (n : ℕ) (hn : 0 < n) :
    Nonempty (locallyInnerClasses n trivialCharacter .plane (cuspFlag .plane true) ≃ₗ[ℂ]
      TernaryPeriodPolynomials.LevelThree.TwoGenerator.parabolicH1
        (TernaryPeriodPolynomials.LevelThree.ParabolicBounds.levelRep (n + 1) (-1))
        (upper 1) (lower 1)) :=
  ⟨goodPlaneLocallyInnerEquivParabolic n hn⟩

/-- **Identity plane, odd `n`: locally inner classes `≅` parabolic `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)`.** -/
theorem badPlane_locallyInner_equiv_parabolic (n : ℕ) (hn : 0 < n) (hodd : Odd n) :
    Nonempty (locallyInnerClasses n trivialCharacter .plane (cuspFlag .plane false) ≃ₗ[ℂ]
      TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne.parabolicH1
        (arithmeticBinaryRep (n + 1) (-1))) :=
  ⟨badPlaneLocallyInnerEquivParabolic n hn hodd⟩

/-- **Good line: the parabolic classes of `Sym^{n+1}` are realized by locally inner classes.** -/
theorem finrank_parabolic_le_goodLine (n : ℕ) (hn : 0 < n) :
    Module.finrank ℂ
        (TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne.parabolicH1
          (arithmeticBinaryRep (n + 1) 0)) ≤
      Module.finrank ℂ (locallyInnerClasses n trivialCharacter .line Face.goodLineFlag) :=
  have : FiniteDimensional ℂ (locallyInnerClasses n trivialCharacter .line Face.goodLineFlag) :=
    finiteDimensional_goodLine_locallyInner n hn
  LinearMap.finrank_le_finrank_of_injective (Face.parabolicToGoodLine_injective n hn)

/-- **The right kernel of the line face pairing is zero for every `n > 0`.** -/
theorem facePairing_right_nondegenerate (n : ℕ) (hn : 0 < n) (ξ : innerClasses n .plane)
    (h : ∀ b : innerClasses n .line, facePairing n b ξ = 0) : ξ = 0 := by
  rcases Nat.even_or_odd n with heven | hodd
  · exact facePairing_right_nondegenerate_even n hn heven ξ h
  · exact facePairing_right_nondegenerate_odd n hn hodd ξ h

/-- **`ar:eq:facepair` for `R = Q`, both arguments (`n > 0`).** -/
theorem facePairing_perfect (n : ℕ) (hn : 0 < n) :
    (∀ b : innerClasses n .line, (∀ ξ : innerClasses n .plane, facePairing n b ξ = 0) → b = 0) ∧
      ∀ ξ : innerClasses n .plane, (∀ b : innerClasses n .line, facePairing n b ξ = 0) → ξ = 0 :=
  ⟨fun b h => facePairing_left_nondegenerate n b h, fun ξ h => facePairing_right_nondegenerate n hn ξ h⟩

/-- **There is no inner plane class at `n = 0`** (dual transport of the vanishing of the inner line
classes; `E` and `E ∘ φ` agree on the level at degree zero). -/
theorem innerClasses_plane_zero_eq_bot : innerClasses 0 .plane = ⊥ :=
  TernaryPeriodPolynomials.Argument.FacePairingFull.innerClasses_plane_zero_eq_bot

/-- **`ar:eq:facepair` for `R = Q`, both arguments, every `n`.** -/
theorem facePairing_perfect_all (n : ℕ) :
    (∀ b : innerClasses n .line, (∀ ξ : innerClasses n .plane, facePairing n b ξ = 0) → b = 0) ∧
      ∀ ξ : innerClasses n .plane, (∀ b : innerClasses n .line, facePairing n b ξ = 0) → ξ = 0 := by
  refine ⟨fun b h => facePairing_left_nondegenerate n b h, fun ξ h => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact facePairing_right_nondegenerate_zero ξ h
  · exact facePairing_right_nondegenerate n hn ξ h

/-- **Vertex reversal of homogeneous two-cocycles is `-1` on `H²`.** The coboundary is
`u(a, b) = z(a, b, a) + z(b, b, b)`. -/
theorem vertex_reversal_neg_H2 {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (Γ : Subgroup G) (ρ : Representation ℂ G V) (a : H2 Γ ρ) :
    Swap.revH2 Γ ρ a = -a :=
  Swap.revH2_eq_neg Γ ρ a

/-- **Swap relation between the two cochain face pairings.** There is a sign `a = ±1` such that for
every `n`, every inner line class `B` and every inner plane class `A`,
`⟨B, A⟩_Q = a · ⟨A, B⟩_P`. -/
theorem facePairing_swap_relation :
    ∃ a : ℂ, (a = 1 ∨ a = -1) ∧ ∀ (n : ℕ) (A : innerClasses n .plane) (B : innerClasses n .line),
      facePairing n B A = a * Plane.facePairingP n A B :=
  Swap.exists_swap_relation

/-- **The left kernel of the plane face pairing `⟨ , ⟩_P` is zero, for every `n`.** -/
theorem facePairingP_left_nondegenerate (n : ℕ) (A : innerClasses n .plane)
    (h : ∀ B : innerClasses n .line, Plane.facePairingP n A B = 0) : A = 0 :=
  Swap.facePairingP_left_nondegenerate n A h

/-- **The right kernel of the plane face pairing `⟨ , ⟩_P` is zero, for every `n`.** -/
theorem facePairingP_right_nondegenerate (n : ℕ) (B : innerClasses n .line)
    (h : ∀ A : innerClasses n .plane, Plane.facePairingP n A B = 0) : B = 0 :=
  Swap.facePairingP_right_nondegenerate n B h

/-- **`ar:eq:facepair` for `R = P`, both arguments, every `n`.** -/
theorem facePairingP_perfect_all (n : ℕ) :
    (∀ A : innerClasses n .plane, (∀ B : innerClasses n .line, Plane.facePairingP n A B = 0) → A = 0) ∧
      ∀ B : innerClasses n .line, (∀ A : innerClasses n .plane, Plane.facePairingP n A B = 0) → B = 0 :=
  Swap.facePairingP_perfect_all n

/-- **Even `n > 0`: the cochain line pairing is the literal level-three parabolic pairing, for all inner
classes.** The dictionary classes are `-badLineEdge(cuspRes_false b)` and `goodPlaneEdge(cuspRes_true ξ)`. -/
theorem facePairing_even_literal (n : ℕ) (hn : 0 < n) (heven : Even n) (b : innerClasses n .line)
    (ξ : innerClasses n .plane) :
    facePairing n b ξ = (((n + 1).factorial : ℂ) / 3) *
      TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Even.badGoodPairingEven
        heven (Literal.badLineParabolic hn b) (Literal.goodPlaneParabolic hn ξ) :=
  Literal.facePairing_even_literal hn heven b ξ

/-- **Odd `n`: the cochain line pairing is the sum of the literal level-three and level-one parabolic
pairings, for all inner classes.** -/
theorem facePairing_odd_literal (n : ℕ) (hn : 0 < n) (hodd : Odd n) (b : innerClasses n .line)
    (ξ : innerClasses n .plane) :
    facePairing n b ξ = (-((n + 1).factorial : ℂ) / 3) *
        TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Odd.badGoodPairingOdd
          hodd (Literal.badLineParabolic hn b) (Literal.goodPlaneParabolic hn ξ) +
      ((n + 1).factorial : ℂ) *
        TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne.parabolicPairing
          (TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne.twistedPairing_goodLine_trivial
            hodd) (Literal.goodLineParabolic hn b) (Literal.badPlaneParabolic hn hodd ξ) :=
  Literal.facePairing_odd_literal hn hodd b ξ

/-- **The plane face pairing against the literal pairings, even `n`** (sign `a = ±1` from the swap relation). -/
theorem facePairingP_even_literal (n : ℕ) (hn : 0 < n) (heven : Even n) :
    ∃ a : ℂ, (a = 1 ∨ a = -1) ∧ ∀ (A : innerClasses n .plane) (B : innerClasses n .line),
      Plane.facePairingP n A B = a * ((((n + 1).factorial : ℂ) / 3) *
        TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Even.badGoodPairingEven
          heven (Literal.badLineParabolic hn B) (Literal.goodPlaneParabolic hn A)) :=
  Literal.facePairingP_even_literal hn heven

/-- **The plane face pairing against the literal pairings, odd `n`.** -/
theorem facePairingP_odd_literal (n : ℕ) (hn : 0 < n) (hodd : Odd n) :
    ∃ a : ℂ, (a = 1 ∨ a = -1) ∧ ∀ (A : innerClasses n .plane) (B : innerClasses n .line),
      Plane.facePairingP n A B = a * ((-((n + 1).factorial : ℂ) / 3) *
          TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Odd.badGoodPairingOdd
            hodd (Literal.badLineParabolic hn B) (Literal.goodPlaneParabolic hn A) +
        ((n + 1).factorial : ℂ) *
          TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne.parabolicPairing
            (TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne.twistedPairing_goodLine_trivial
              hodd) (Literal.goodLineParabolic hn B) (Literal.badPlaneParabolic hn hodd A)) :=
  Literal.facePairingP_odd_literal hn hodd

/-- **Even `n`: the bad-line dictionary is an isomorphism onto `parabolicCrossedH1 (Sym^{n+1})`.** -/
theorem badLineParabolic_bijective_even (n : ℕ) (hn : 0 < n) (heven : Even n) :
    Function.Bijective (Literal.badLineParabolic hn) :=
  Literal.badLineParabolic_bijective_even hn heven

/-- **Even `n`: the good-plane dictionary is an isomorphism onto `parabolicCrossedH1 (Sym^{n+1} ⊗ det⁻¹)`.** -/
theorem goodPlaneParabolic_bijective_even (n : ℕ) (hn : 0 < n) (heven : Even n) :
    Function.Bijective (Literal.goodPlaneParabolic hn) :=
  Literal.goodPlaneParabolic_bijective_even hn heven

/-- **Odd `n`: the line dictionary `(badLineParabolic, goodLineParabolic)` is an isomorphism onto
`P_bl × P_gl`.** -/
theorem lineDictionaryOdd_bijective (n : ℕ) (hn : 0 < n) (hodd : Odd n) :
    Function.Bijective (Literal.lineDictionaryOdd hn) :=
  Literal.lineDictionaryOdd_bijective hn hodd

/-- **Odd `n`: the plane dictionary `(goodPlaneParabolic, badPlaneParabolic)` is an isomorphism onto
`P_gp × P_bp`.** -/
theorem planeDictionaryOdd_bijective (n : ℕ) (hn : 0 < n) (hodd : Odd n) :
    Function.Bijective (Literal.planeDictionaryOdd hn hodd) :=
  Literal.planeDictionaryOdd_bijective hn hodd

open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
  (parabolicCrossedH1) in
/-- **Bad line: the edge-map dictionary is minus the Hochschild-Serre dictionary of `Face/*`.** -/
theorem badLineParabolic_eq_face (n : ℕ) (hn : 0 < n) (b : innerClasses n .line)
    (hx : fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
      standardBadLine b.val ∈ locallyInnerClasses n trivialCharacter .line standardBadLine) :
    ((Literal.badLineParabolic hn b : parabolicCrossedH1 (binaryArithmeticRepresentation n)) :
        CrossedH1 (binaryArithmeticRepresentation n)) =
      -((Face.badLineLocallyInnerEquivParabolic n hn ⟨_, hx⟩ :
        parabolicCrossedH1 (binaryArithmeticRepresentation n)) :
          CrossedH1 (binaryArithmeticRepresentation n)) :=
  Literal.badLineParabolic_eq_face hn b hx

/-- **Stokes (Lemma C.2) as an identity of face pairings.** For edge-exact global cocycles `c, c'`
of `E`, `⟨ r_P c , r_Q c' ⟩_P = ⟨ r_Q c , r_P c' ⟩_Q`; the model form of the paper's
`⟨ ξ , T^∨ η ⟩_P = - ⟨ T ξ , η ⟩_Q`. -/
theorem facePairingP_global_eq_facePairing_global (n : ℕ)
    (c c' : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (w w' : EdgeCochains n trivialCharacter 1)
    (hw : ∀ x e, c.val.val x = differentialOneRaw w.val x e)
    (hw' : ∀ x e, c'.val.val x = differentialOneRaw w'.val x e) :
    Plane.facePairingP n
        ⟨classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane)
          (restrictionCocycle n trivialCharacter .plane c),
          innerBoundary_restriction_of_exact c w hw .plane⟩
        ⟨classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line)
          (restrictionCocycle n trivialCharacter .line c'),
          innerBoundary_restriction_of_exact c' w' hw' .line⟩ =
      facePairing n
        ⟨classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line)
          (restrictionCocycle n trivialCharacter .line c),
          innerBoundary_restriction_of_exact c w hw .line⟩
        ⟨classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane)
          (restrictionCocycle n trivialCharacter .plane c'),
          innerBoundary_restriction_of_exact c' w' hw' .plane⟩ :=
  TernaryPeriodPolynomials.Argument.FacePairingFull.facePairingP_global_eq_facePairing_global
    c c' w w' hw hw'

/-- **Intermediate (n ≥ 4): the left kernel of `⟨,⟩_P` consists of plane restrictions of global
classes with zero line restriction.** -/
theorem facePairingP_left_kernel_eq_global (n : ℕ) (hn : 4 ≤ n) (ξ : innerClasses n .plane)
    (h : ∀ b : innerClasses n .line, Plane.facePairingP n ξ b = 0) :
    ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
      (globalCoordinates n trivialCharacter c).1 = ξ.val ∧
      (globalCoordinates n trivialCharacter c).2 = 0 :=
  TernaryPeriodPolynomials.Argument.FacePairingFull.facePairingP_left_kernel_eq_global hn ξ h

/-- **CONDITIONAL (n ≥ 4): `⟨,⟩_P` has zero left kernel if the constant-term map is injective**
(`hT`: inner restrictions and zero line restriction force zero plane restriction). `hT` is the
functional-equation content. -/
theorem facePairingP_left_nondegenerate_of_injective (n : ℕ) (hn : 4 ≤ n)
    (hT : ∀ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
      InnerBoundary n trivialCharacter .plane (globalCoordinates n trivialCharacter c).1 →
      (globalCoordinates n trivialCharacter c).2 = 0 →
        (globalCoordinates n trivialCharacter c).1 = 0)
    (ξ : innerClasses n .plane)
    (h : ∀ b : innerClasses n .line, Plane.facePairingP n ξ b = 0) : ξ = 0 :=
  TernaryPeriodPolynomials.Argument.FacePairingFull.facePairingP_left_nondegenerate_of_injective
    hn hT ξ h

/-- **Literal pairing, level one (good line × identity plane), odd `n`: perfect.** -/
theorem levelOne_pairing_perfect (n : ℕ) (hodd : Odd n) :
    let P := TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne.parabolicPairing
      (TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne.twistedPairing_arithmeticBinaryRep
        (n + 1) 0 (-1) hodd.add_one (by
          obtain ⟨k, hk⟩ := hodd
          exact ⟨-(k : ℤ) - 2, by push_cast; omega⟩))
    (∀ x, (∀ y, P x y = 0) → x = 0) ∧ (∀ y, (∀ x, P x y = 0) → y = 0) :=
  TernaryPeriodPolynomials.Argument.FacePairingFull.levelOne_pairing_perfect n hodd

/-- **Literal pairing, level three (bad line × good plane), odd `n`: perfect.** -/
theorem levelThree_pairing_perfect_odd (n : ℕ) (hn : 0 < n) (hodd : Odd n) :
    let P := TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree.parabolicPairing
      (TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree.twistedPairing_levelRep
        (n + 1) 0 (-1) (by
          obtain ⟨k, hk⟩ := hodd
          exact ⟨-(k : ℤ) - 2, by push_cast; omega⟩))
    (∀ x, (∀ y, P x y = 0) → x = 0) ∧ (∀ y, (∀ x, P x y = 0) → y = 0) :=
  TernaryPeriodPolynomials.Argument.FacePairingFull.levelThree_pairing_perfect_odd n hn hodd

/-- **Literal pairing, level three (bad line × good plane), even `n`: perfect.** -/
theorem levelThree_pairing_perfect_even (n : ℕ) (hn : 0 < n) (heven : Even n) :
    let P := TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Even.badGoodPairingEven heven
    (∀ x, (∀ y, P x y = 0) → x = 0) ∧ (∀ y, (∀ x, P x y = 0) → y = 0) :=
  TernaryPeriodPolynomials.Argument.FacePairingFull.levelThree_pairing_perfect_even n hn heven

/-- **L1 (coefficients), complex versus rational.** `ℂ ⊗_ℚ VQ n ≃ VC n`, where `VQ n` is the geometric
side's rational homogeneous polynomials (`TernaryPoly.PolynomialGLAction`), equivariant for every integral matrix. -/
theorem complexifyEquiv_equivariant (n : ℕ) (e : ℤ) (g : Matrix.GeneralLinearGroup (Fin 3) ℤ)
    (x : TensorProduct ℚ ℂ (Comparison.VQ n)) :
    Comparison.complexifyEquiv n
        (LinearMap.baseChange ℂ (TernaryPoly.PolynomialGLAction.integralAction n e g) x) =
      GeneralEisenstein.homogeneousAction n e
        (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) g) (Comparison.complexifyEquiv n x) :=
  Comparison.complexifyEquiv_equivariant n e g x

/-- **L1, the model coefficient system on the arithmetic level** is the complex action of the same
integral matrix. -/
theorem rationalCoefficientComponent_integral (n : ℕ) (γ : GeneralEisenstein.arithmeticLevel) :
    GeneralEisenstein.rationalCoefficientComponent n GeneralEisenstein.trivialCharacter
        (GeneralEisenstein.rationalInclusion γ) =
      GeneralEisenstein.homogeneousAction n (-1)
        (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) γ.1) :=
  Comparison.rationalCoefficientComponent_integral n γ

/-- **L1, the dual coefficient system `E* = E ∘ φ` is the complexified contragredient** of the rational
coefficient system, at every element of the arithmetic level. -/
theorem dualRep_comparison (n : ℕ) (γ : GeneralEisenstein.arithmeticLevel)
    (x : TensorProduct ℚ ℂ (Module.Dual ℚ (Comparison.VQ n))) :
    Comparison.dualComplexEquiv n
        (LinearMap.baseChange ℂ (Comparison.dualAct n (-1) γ.1) x) =
      (GeneralEisenstein.rationalCoefficientComponent n GeneralEisenstein.trivialCharacter)
        (TernaryPeriodPolynomials.Duality.dualInvolution
          (GeneralEisenstein.rationalInclusion γ)) (Comparison.dualComplexEquiv n x) :=
  Comparison.dualRep_comparison n γ x

/-- **L3a: complete flags of the model are the incident (line, plane) pairs of the geometric side.**
Together with `flagLine_smul`, `flagPlane_smul`, `edgePair_smul` (equivariance) and
`flagLine_mk : flagLine (g B) = lineLabel g` (the face labelling of the bordification). -/
theorem edgeEquiv_incident (e : Edges) :
    TernaryPoly.OrdinaryIncidence.incidence
      (Comparison.flagLine (endpoint .line e)) (Comparison.flagPlane (endpoint .plane e)) :=
  Comparison.edge_incidence e

/-- **L2/L3: the geometric level `K` is conjugate to the model level.** -/
theorem mem_K_iff_conj (g : Matrix.GeneralLinearGroup (Fin 3) ℤ) :
    g ∈ TernaryPoly.ModThreeGoodAction.K ↔
      Comparison.conjG * g * Comparison.conjG⁻¹ ∈ GeneralEisenstein.arithmeticLevel :=
  Comparison.mem_K_iff_conj g

/-- **L2 for the model:** `H²(rationalLevel, ρ)` is the `rationalLevel/Γ(6)`-invariants of `H²` of the
image `N6` of `Γ(6)`, for every complex representation `ρ` of `GL₃(ℚ)`; and `H²(N6, ρ)` is the
whole-group `H²` of `Γ(6)` (`n6H2Equiv`). -/
theorem levelSix_transfer {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ GeneralEisenstein.RationalGL3 V) :
    Nonempty (GeneralEisenstein.Homogeneous.H2 GeneralEisenstein.rationalLevel ρ ≃ₗ[ℂ]
      LevelTransfer.invariants ρ Comparison.N6_normalized) :=
  ⟨Comparison.levelSixTransfer ρ⟩

/-- **D1: `dim H₄(∂M; ℚ) ≤ 1`.** Every top-degree class of the arithmetic boundary
`∂M = Γ(6)\∂X̄` is a rational multiple of `boundaryFundamentalClass`. (General statement:
`Argument.TopHomology.chains_top_homology_eq_smul`, top homology of a connected compact
oriented manifold.) -/
theorem boundary_top_homology_eq_smul
    (c : (TernaryPoly.ContractibleSingularHomology.chains
      TernaryPoly.SingularBoundaryRestriction.BoundaryBase).homology 4) :
    ∃ q : ℚ, c = q • TernaryPoly.SymmetricSpaceBoundaryOrientation.boundaryFundamentalClass :=
  Comparison.boundary_top_homology_eq_smul c

open CategoryTheory in
/-- **D2 (injectivity):** a corner cochain of the signed boundary cone that is a total coboundary is a
corner coboundary plus pullbacks of line and plane cocycles. -/
theorem cone_corner_coboundary {G : Type} [Group G] {F L P : ChainComplex (Rep.{0} ℚ G) ℕ}
    (a : F ⟶ L) (b : F ⟶ P) (W : Rep.{0} ℚ G) (m : ℕ) (e : F.X (m+1) ⟶ W)
    (c' : (TernaryPoly.SymmetricSpaceBoundaryFull.signedCone a b).X (m+1) ⟶ W)
    (h : (TernaryPoly.SymmetricSpaceBoundaryFull.signedCone a b).d (m+2) (m+1) ≫ c' =
      Comparison.cornerCochain a b W (m+1) e) :
    ∃ (e' : F.X m ⟶ W) (l' : L.X (m+1) ⟶ W) (p' : P.X (m+1) ⟶ W),
      L.d (m+2) (m+1) ≫ l' = 0 ∧ P.d (m+2) (m+1) ≫ p' = 0 ∧
      e = -(F.d (m+1) m ≫ e') + a.f (m+1) ≫ l' - b.f (m+1) ≫ p' :=
  Comparison.corner_coboundary a b W m e c' h

open CategoryTheory in
/-- **D2′: the top cohomology of the stabilizer cone with trivial coefficients is `ℚ`.** Via the
quasi-isomorphism with the boundary local-system cochains, Poincaré duality of the closed `∂M` and the
connectedness of `∂M`. -/
theorem stabilizerTotal_H4_iso :
    Nonempty ((TernaryPoly.SymmetricSpaceBoundaryGeometricCone.stabilizerTotalCochains
      Comparison.trivialW).homology 4 ≅ ModuleCat.of ℚ ℚ) :=
  Comparison.stabilizerTotal_H4_iso

/-- **General: trivial local systems on a free quotient covering are ordinary chains.** -/
theorem trivialLocalChainIso_nonempty {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E]
    [ContinuousConstSMul G E] [IsCancelSMul G E] (p : E ⟶ B)
    (hp : IsQuotientCoveringMap p G) {V : Rep.{0} ℚ G}
    (hV : TernaryPeriodPolynomials.Argument.TopHomology.TrivialAction V) :
    Nonempty (TernaryPoly.SingularLocalHomology.localChains p hp V ≅
      TernaryPoly.SingularLocalConstant.ordinaryChains B (ModuleCat.of ℚ V)) :=
  ⟨TernaryPeriodPolynomials.Argument.TopHomology.trivialLocalChainIso p hp hV⟩

open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne
  (parabolicH1) in
/-- **Good line: the library's explicit edge dictionary is the Hochschild-Serre dictionary, with sign `+1`.**
For every inner line class `b`, `goodLineParabolic b = phiL (cuspRes true b)` is the image of the local class of `b`
at the good line under the Hochschild-Serre isomorphism `Face.goodLineLocallyInnerEquiv`, the Kostant coordinate
`Face.glPsi` and the comparison of crossed and Mathlib `H¹`. -/
theorem goodLineParabolic_eq_hs (n : ℕ) (hn : 0 < n) (b : innerClasses n .line) :
    ((Literal.goodLineParabolic hn b : parabolicH1 (arithmeticBinaryRep (n + 1) 0)) :
        groupCohomology.H1 (arithmeticBinaryRep (n + 1) 0)) =
      Parabolic.h1EquivCrossed (arithmeticBinaryRep (n + 1) 0)
        (Face.glPsi n hn ((Face.goodLineLocallyInnerEquiv n trivialCharacter
          ⟨fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
              Face.goodLineFlag b.val,
            innerBoundary_fixedPointH2_locallyInner b.property Face.goodLineFlag⟩ :
            Face.FaceCuspidal goodLineSplitting.conjAct n trivialCharacter Face.goodLineFlag
              Face.goodLineSemidirectEquivFixed) : CrossedH1 (Face.glAction n))) :=
  Literal.GoodLineId.goodLineParabolic_eq_hs hn b

/-- **The Hochschild-Serre inverse of the good line carries `goodLineParabolic b` back to the local class of `b`.** -/
theorem parabolicToGoodLine_goodLineParabolic (n : ℕ) (hn : 0 < n) (b : innerClasses n .line) :
    ((Face.parabolicToGoodLine n hn (Literal.goodLineParabolic hn b) :
        locallyInnerClasses n trivialCharacter .line Face.goodLineFlag) :
        H2 (fixedPointLevel rationalLevel Face.goodLineFlag)
          (rationalCoefficientComponent n trivialCharacter)) =
      fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) Face.goodLineFlag
        b.val :=
  Literal.GoodLineId.parabolicToGoodLine_goodLineParabolic hn b

/-- **Graph containment (`ar:prop:graph`), two-class form.** For `n ≥ 4`, two global classes with zero flag
restrictions and the same plane restriction have the same line restriction. -/
theorem graph_containment_pair (n : ℕ) (hn : 4 ≤ n)
    (c c₁ : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (hc : EdgeExactGlobal c) (hc₁ : EdgeExactGlobal c₁)
    (hP : (globalCoordinates n trivialCharacter c).1 = (globalCoordinates n trivialCharacter c₁).1) :
    (globalCoordinates n trivialCharacter c).2 = (globalCoordinates n trivialCharacter c₁).2 :=
  TernaryPeriodPolynomials.Argument.FacePairingFull.graph_containment_pair hn c c₁ hc hc₁ hP

/-- **Graph containment (`ar:prop:graph`).** For `n ≥ 4` there is a constant-term map `T` (the line restriction of a
class with zero flag restrictions and prescribed inner plane restriction) such that every global class with zero flag
restrictions has `ξ_Q = T ξ_P`. -/
theorem graph_containment (n : ℕ) (hn : 4 ≤ n) :
    ∃ T : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line,
      (∀ ξ, InnerBoundary n trivialCharacter .plane ξ →
        ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
          EdgeExactGlobal c ∧ globalCoordinates n trivialCharacter c = (ξ, T ξ)) ∧
      ∀ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
        EdgeExactGlobal c →
          (globalCoordinates n trivialCharacter c).2 = T (globalCoordinates n trivialCharacter c).1 :=
  TernaryPeriodPolynomials.Argument.FacePairingFull.graph_containment hn

/-- **`ȷ = Ad(w) ∘ φ`**: the paper's involution `ȷ(g) = J (g⁻¹)ᵀ J` is the model's level-preserving involution
`φ` up to conjugation by the fixed matrix `w = J a⁻¹`. -/
theorem jmath_eq_conj (g : GeneralEisenstein.RationalGL3) :
    DualJ.jmath g = DualJ.jmathConj * TernaryPeriodPolynomials.Duality.dualInvolution g *
      DualJ.jmathConj⁻¹ :=
  DualJ.jmath_eq_conj g

/-- **`ȷ` exchanges the plane and line parabolics.** -/
theorem mem_plane_jmath_iff (g : GeneralEisenstein.RationalGL3) :
    DualJ.jmath g ∈ parabolic .plane ↔ g ∈ parabolic .line :=
  DualJ.mem_plane_jmath_iff g

theorem mem_line_jmath_iff (g : GeneralEisenstein.RationalGL3) :
    DualJ.jmath g ∈ parabolic .line ↔ g ∈ parabolic .plane :=
  DualJ.mem_line_jmath_iff g

/-- **Coefficient identification.** `ρ(w) : (V, ρ ∘ φ) → (V, ρ ∘ ȷ)` is equivariant, for every representation. -/
theorem coefficient_intertwines {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ GeneralEisenstein.RationalGL3 W) (g : GeneralEisenstein.RationalGL3) (v : W) :
    ρ (DualJ.jmath g) (ρ DualJ.jmathConj v) = ρ DualJ.jmathConj (Dual.dualRep ρ g v) :=
  DualJ.coefficient_intertwines ρ g v

/-- **`E ∘ ȷ` is the dual of `E` after the coordinate change `ρ(w)`**: `B_J(v, u) = B(v, ρ(w)⁻¹ u)` is invariant. -/
theorem dualPairingJ_invariant (n : ℕ) (χ : RankOneCharacter) (g : GeneralEisenstein.RationalGL3)
    (v u : HomogeneousPoly n) :
    DualJ.dualPairingJ n χ (rationalCoefficientComponent n χ g v)
      (rationalCoefficientComponent n χ (DualJ.jmath g) u) = DualJ.dualPairingJ n χ v u :=
  DualJ.dualPairingJ_invariant n χ g v u

/-- **The transport to `E*` is the `ȷ`-pullback of the conjugate** (plane to line strata; likewise
`DualJ.toPlaneStar_eq_jDual`, `DualJ.toEdgeStar_eq_jDual`). -/
theorem toLineStar_eq_jDual {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ GeneralEisenstein.RationalGL3 V)
    (z : cocycles rationalLevel (flagRepresentation ρ .plane)) :
    (Dual.toLineStar ρ z).val = DualJ.jDualFlag ρ 2 DualJ.jFlagLine DualJ.jFlagLine_smul z.val :=
  DualJ.toLineStar_eq_jDual ρ z

/-- **`r_B = 0` for the dual series.** -/
theorem jDual_edgeExact {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ GeneralEisenstein.RationalGL3 V) (c : cocycles rationalLevel ρ)
    (u : cochains rationalLevel (functionRepresentation ρ Edges) 1)
    (hu : ∀ x e, c.val.val x = differentialOneRaw u.val x e) :
    ∀ x e, (DualJ.jDualCocycle ρ c).val.val x =
      differentialOneRaw (DualJ.jDualFlag ρ 1 DualJ.jEdge DualJ.jEdge_smul u).val x e :=
  DualJ.jDual_edgeExact ρ c u hu

/-- **The dual series through `ȷ` (`ar:eq:dualconstantterms`).** -/
theorem dual_constant_terms_jmath (n : ℕ) (hn : 4 ≤ n)
    (z : cocycles rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane))
    (hz : InnerBoundary n trivialCharacter .plane
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) z)) :
    ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
      EdgeExactGlobal c ∧
      (globalCoordinates n trivialCharacter c).1 =
        classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) z ∧
      InnerBoundary n trivialCharacter .line (globalCoordinates n trivialCharacter c).2 ∧
      (∃ u : cochains rationalLevel (functionRepresentation
          (Dual.dualRep (rationalCoefficientComponent n trivialCharacter)) Edges) 1,
        ∀ x e, (DualJ.jDualCocycle _ c).val.val x = differentialOneRaw u.val x e) ∧
      (Dual.globalCoordinatesRep (Dual.dualRep (rationalCoefficientComponent n trivialCharacter))
          (DualJ.jDualCocycle _ c)).2 =
        classOf rationalLevel
          (flagRepresentation (Dual.dualRep (rationalCoefficientComponent n trivialCharacter)) .line)
          (Dual.toLineStar _ z) ∧
      Dual.InnerBoundaryRep (Dual.dualRep (rationalCoefficientComponent n trivialCharacter)) .plane
        (Dual.globalCoordinatesRep (Dual.dualRep (rationalCoefficientComponent n trivialCharacter))
          (DualJ.jDualCocycle _ c)).1 ∧
      Dual.InnerBoundaryRep (Dual.dualRep (rationalCoefficientComponent n trivialCharacter)) .line
        (Dual.globalCoordinatesRep (Dual.dualRep (rationalCoefficientComponent n trivialCharacter))
          (DualJ.jDualCocycle _ c)).2 :=
  DualJ.dual_constant_terms_jmath hn z hz

/-- **`T^∨` is determined.** The coordinates `(r_P, r_Q)` of the `ȷ`-dual of a class with zero flag restrictions
depend only on its plane restriction. -/
theorem dual_series_coordinates_unique (n : ℕ) (hn : 4 ≤ n)
    (c c₁ : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (hc : EdgeExactGlobal c) (hc₁ : EdgeExactGlobal c₁)
    (hP : (globalCoordinates n trivialCharacter c).1 = (globalCoordinates n trivialCharacter c₁).1) :
    Dual.globalCoordinatesRep (Dual.dualRep (rationalCoefficientComponent n trivialCharacter))
        (DualJ.jDualCocycle _ c) =
      Dual.globalCoordinatesRep (Dual.dualRep (rationalCoefficientComponent n trivialCharacter))
        (DualJ.jDualCocycle _ c₁) :=
  DualJ.dual_series_coordinates_unique hn c c₁ hc hc₁ hP

open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne
  (parabolicH1) in
/-- **Identity plane: the library's explicit edge dictionary is the Hochschild-Serre dictionary, with sign `+1`**
(odd `n > 0`). `bpPsi` is the Kostant coordinate of the radical `H¹` transported to `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)`;
`badPlaneLocallyInnerEquiv` is the generic Hochschild-Serre isomorphism onto the mixed cuspidal group. -/
theorem badPlaneParabolic_eq_hs (n : ℕ) (hn : 0 < n) (hodd : Odd n) (ξ : innerClasses n .plane) :
    ((Literal.badPlaneParabolic hn hodd ξ : parabolicH1 (arithmeticBinaryRep (n + 1) (-1))) :
        groupCohomology.H1 (arithmeticBinaryRep (n + 1) (-1))) =
      Parabolic.h1EquivCrossed (arithmeticBinaryRep (n + 1) (-1))
        (Literal.BadPlaneId.bpPsi n ((Face.badPlaneLocallyInnerEquiv n trivialCharacter
          ⟨fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
              Face.badPlaneFlag ξ.val,
            innerBoundary_fixedPointH2_locallyInner ξ.property Face.badPlaneFlag⟩ :
            Face.FaceCuspidal identityPlaneSplitting.conjAct n trivialCharacter Face.badPlaneFlag
              Face.badPlaneSemidirectEquiv) : CrossedH1 (Literal.BadPlaneId.bpAction n))) :=
  Literal.BadPlaneId.badPlaneParabolic_eq_hs hn hodd ξ

open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep) in
/-- **Good plane: the library's explicit edge dictionary is the Hochschild-Serre dictionary, with sign `+1`** (`n > 0`):
the library's good-plane edge (conjugation to block coordinates, Sol's edge, Kostant coordinate, `Φ`) equals the image
of the local class under the Hochschild-Serre isomorphism `gpLocallyInnerEquiv` of the cusp stabilizer followed by the
Kostant coordinate and `Φ` (`gpPsi`). -/
theorem goodPlaneParabolic_eq_hs (n : ℕ) (hn : 0 < n) (ξ : innerClasses n .plane) :
    ((Literal.goodPlaneParabolic hn ξ : parabolicCrossedH1 (levelRep (n + 1) (-1))) :
        CrossedH1 (levelRep (n + 1) (-1))) =
      Literal.GoodPlaneId.gpPsi n ((Literal.GoodPlaneId.gpLocallyInnerEquiv n
        ⟨fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
            (cuspFlag .plane true) ξ.val,
          innerBoundary_fixedPointH2_locallyInner ξ.property (cuspFlag .plane true)⟩ :
          Face.FaceCuspidal TernaryPeriodPolynomials.LevelThree.GoodPlaneModel.goodPlaneSplitting.conjAct
            n trivialCharacter (cuspFlag .plane true) Literal.GoodPlaneId.gpIota) :
        CrossedH1 (Literal.GoodPlaneId.gpAction n)) :=
  Literal.GoodPlaneId.goodPlaneParabolic_eq_hs hn ξ

open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction in
/-- **The standard operator is the graph map.** For any linear `T` with the graph property of `ar:prop:graph`, `T` takes the
plane class of a source cocycle of a cohomological datum to the class of its standard line cocycle (the absolutely convergent
standard integral). -/
theorem standardLine_eq_of_graph {n : ℕ} (hn : 4 ≤ n)
    (T : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line)
    (hT : ∀ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
      EdgeExactGlobal c →
        (globalCoordinates n trivialCharacter c).2 = T (globalCoordinates n trivialCharacter c).1)
    (Dm : CohomologicalCuspData n)
    (plane : SourceSpace.sourceCocycles Dm.inducingData .plane) :
    SourceSpace.sourceClass Dm.inducingData .line
        (TernaryPeriodPolynomials.Argument.ConvergentEisenstein.EndpointSourceStandard.sourceStandard Dm.inducingData hn
          (TernaryPeriodPolynomials.Argument.ConvergentEisenstein.planeEisensteinConvergent hn Dm.inducingData) plane) =
      T (SourceSpace.sourceClass Dm.inducingData .plane plane) :=
  TernaryPeriodPolynomials.Argument.FacePairingFull.standardLine_eq_of_graph hn T hT Dm plane

/-- **`ar:lem:stokes` (paper form), in the model.** See `PaperStokes.lean`: with `⟨ , ⟩_P = facePairingP` and `⟨ , ⟩_Q = - facePairing`
(orientation sign of the cone convention), `⟨r_P a, r_P b⟩_P + ⟨r_Q a, r_Q b⟩_Q = 0` for global classes `a = c` of `E` and
`b = ȷ`-dual of `c'` of `E*` with zero flag restrictions. -/
theorem paper_stokes (n : ℕ)
    (c c' : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (w w' : EdgeCochains n trivialCharacter 1)
    (hw : ∀ x e, c.val.val x = differentialOneRaw w.val x e)
    (hw' : ∀ x e, c'.val.val x = differentialOneRaw w'.val x e) :
    Plane.facePairingP n
        ⟨classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane)
          (restrictionCocycle n trivialCharacter .plane c),
          innerBoundary_restriction_of_exact c w hw .plane⟩
        ⟨classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line)
          (Dual.fromPlaneStar (rationalCoefficientComponent n trivialCharacter)
            (Dual.restrictionCocycleRep (Dual.dualRep (rationalCoefficientComponent n trivialCharacter)) .plane
              (DualJ.jDualCocycle (rationalCoefficientComponent n trivialCharacter) c'))),
          by
            rw [fromPlaneStar_restriction_phi]
            exact innerBoundary_restriction_of_exact c' w' hw' .line⟩ +
      -facePairing n
        ⟨classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line)
          (restrictionCocycle n trivialCharacter .line c),
          innerBoundary_restriction_of_exact c w hw .line⟩
        ⟨classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane)
          (Dual.fromLineStar (rationalCoefficientComponent n trivialCharacter)
            (Dual.restrictionCocycleRep (Dual.dualRep (rationalCoefficientComponent n trivialCharacter)) .line
              (DualJ.jDualCocycle (rationalCoefficientComponent n trivialCharacter) c'))),
          by
            rw [fromLineStar_restriction_phi]
            exact innerBoundary_restriction_of_exact c' w' hw' .plane⟩ = 0 :=
  TernaryPeriodPolynomials.Argument.FacePairingFull.paper_stokes c c' w w' hw hw'

open TernaryPeriodPolynomials.Argument.ConvergentEisenstein in
/-- **`standard = T`.** The linear standard operator characterized by `RealizesStandardConv` (continuation of the standard family) is the
constant-term map `T` of `ar:prop:graph` on the whole plane boundary summand. -/
theorem standard_eq_T {n : ℕ} (hn : 4 ≤ n)
    (T : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line)
    (hT : ∀ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
      EdgeExactGlobal c →
        (globalCoordinates n trivialCharacter c).2 = T (globalCoordinates n trivialCharacter c).1)
    (Dm : CohomologicalCuspData n)
    (standard : boundarySummand Dm.inducingData .plane →ₗ[ℂ] boundarySummand Dm.inducingData .line)
    (hstd : RealizesStandardConv Dm.inducingData standard)
    (x : boundarySummand Dm.inducingData .plane) :
    (standard x).val = T x.val :=
  TernaryPeriodPolynomials.Argument.FacePairingFull.standard_eq_T hn T hT Dm standard hstd x

open TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.SymmetricSpaceBoundaryGeometricCone
  TernaryPoly.EquivariantSingularSmall CategoryTheory HomologicalComplex in
/-- **The model boundary complex computes `H^k(∂M; W)`** for every rational representation `W` of `Γ(6)` and every degree `k`
(model cone `coneR`: the cone of the signed incidence of the three model resolutions; `localBoundaryCochains W`: singular
local-system cochains of the arithmetic boundary). -/
noncomputable def modelBoundary_cohomology_iso (W : Rep.{0} ℚ principalSix) (k : ℕ) :
    (homCochains Comparison.coneR W).homology k ≅ (localBoundaryCochains W).homology k :=
  Comparison.modelBoundary_cohomology_iso W k

alias geoPairing := Comparison.geoPairing
alias geoPairingEquiv := Comparison.geoPairingEquiv
alias geoPairing_right_injective := Comparison.geoPairing_right_injective
alias geoPairingBoundary_restriction := Comparison.geoPairingBoundary_restriction
alias geoPairingBoundary_annihilator_iff := Comparison.geoPairingBoundary_annihilator_iff

alias modelCup_eq := Comparison.modelCup_eq
alias modelCup_isCocycle := Comparison.modelCup_isCocycle
alias boundaryValue_eq_cone := Comparison.boundaryValue_eq_cone
alias traceValue_eq_evalOmega := Comparison.traceValue_eq_evalOmega
alias modelCupP_eq := Comparison.modelCupP_eq
alias boundaryValueP_eq_cone := Comparison.boundaryValueP_eq_cone
alias traceValueP_eq_evalOmega := Comparison.traceValueP_eq_evalOmega
alias nerveDelta := Comparison.nerveDelta
alias nerveDelta_d := Comparison.nerveDelta_d
alias nerveDelta_counit_left := Comparison.nerveDelta_counit_left
alias nerveDelta_counit_right := Comparison.nerveDelta_counit_right
alias nerveDelta_natural := Comparison.nerveDelta_natural
alias Bhom_complexify := Comparison.Bhom_complexify

end TernaryPeriodPolynomials.Argument.Statements.FacePairing
