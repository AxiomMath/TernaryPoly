module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Literal.FaceIdentification
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Literal.FaceGeneric

@[expose] public section


/-!
# The good-line edge dictionary versus the Hochschild-Serre dictionary

At the good line `ℚe₃` the literal dictionary of `Literal.OddGood` is `b ↦ phiL (cuspRes true b)`, built from
the library's explicit edge `goodLineBinaryEdge` of relative two-cocycles of the arithmetic stabilizer `Λ₁ = 3ℤ² ⋊ GL₂(ℤ)`;
`Face/*` realizes the same parabolic classes through the Hochschild-Serre isomorphism
`goodLineLocallyInnerEquiv` (mixed class `ℓ ↦ [r ↦ c(ℓ, ℓ⁻¹·r) - c(r, ℓ)]`) and the Kostant coordinate `glPsi`.

* `goodLineParabolic_eq_hs`: for every inner line class `b` the two coincide **with sign `+1`**,
  `goodLineParabolic b = h1EquivCrossed (glPsi (goodLineLocallyInnerEquiv (local class of b)))`.
* `parabolicToGoodLine_goodLineParabolic`: hence the Hochschild-Serre inverse `Face.parabolicToGoodLine`
  carries `goodLineParabolic b` back to the local class of `b` at the good line.

Together with `Literal.FaceIdentification` (bad line: `-1`) the edge-map dictionary is compared with the
Hochschild-Serre composites of `Face/*` at both line faces, with signs `(bad line, good line) = (-1, +1)`; the two planes are
`Literal.BadPlaneIdentification` and `Literal.GoodPlaneIdentification` (sign `+1`).

Proof. A radical-zero inhomogeneous representative `c₀` of the face class (`radicalRestrictionH2_ker_representative`)
is pushed along the isomorphism `goodLineSemidirectEquiv : N ⋊ GL₂(ℤ) ≃ Λ₁` to a relative two-cocycle of `Λ₁`
(`pushCycle`); it represents the image of the local class under `toH2L` (the homogeneous-to-group comparison, because the
two differ by an inhomogeneous coboundary, `toH2L_eq_of_face`), and the library's `goodLineBinaryEdgeCycle` of the pushed
cocycle is the Kostant coordinate of the mixed cocycle of `c₀` pointwise (`mixed_eq_binaryEdgeCycle`): both are
`r ↦ c(s ℓ, ι (ℓ⁻¹·r)) - c(ι r, s ℓ)`.

Scope. This is the comparison of the two *algebraic* dictionaries. It does not assert any geometric (de Rham, Stokes,
orientation) normalization of the face dictionaries.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section


open GeneralEisenstein GeneralEisenstein.Homogeneous Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.LocalUniqueness (phiL ML)
open TernaryPeriodPolynomials.Spectral.GoodLineHecke (edgeK KL toH2L)
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCoordinate (ρn)
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne (parabolicH1)
open TernaryPeriodPolynomials.Argument.FacePairingFull
open TernaryPeriodPolynomials.Argument.FacePairingFull.Face
open TernaryPeriodPolynomials.Argument.FacePairingFull.Parabolic
open TernaryPeriodPolynomials.Argument.FacePairingFull.Literal

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Literal.GoodLineId

variable (n : ℕ)

/-- The face representation of the good line. -/
abbrev glRep :=
  faceRep goodLineSplitting.conjAct n trivialCharacter goodLineFlag goodLineSemidirectEquivFixed

theorem glRep_symm (g : ↥(flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))) :
    glRep n (goodLineSemidirectEquiv.symm g) = rationalCoefficientComponent n trivialCharacter g.val := by
  change rationalCoefficientComponent n trivialCharacter
    (goodLineSemidirectEquiv (goodLineSemidirectEquiv.symm g)).val = _
  rw [MulEquiv.apply_symm_apply]

/-- Push an inhomogeneous two-cocycle of the split extension to a two-cocycle of the arithmetic
stabilizer `Λ₁` of the good line. -/
def pushCycle (c : inhomogeneousTwoCycles (glRep n)) :
    groupCohomology.cocycles₂ (goodLineCoefficientRep n) := by
  refine ⟨fun p => (c.val (goodLineSemidirectEquiv.symm p.1)
    (goodLineSemidirectEquiv.symm p.2) : (goodLineCoefficientRep n)), ?_⟩
  refine (groupCohomology.mem_cocycles₂_iff (A := goodLineCoefficientRep n) _).mpr ?_
  intro g h j
  have h1 := c.property (goodLineSemidirectEquiv.symm g) (goodLineSemidirectEquiv.symm h)
    (goodLineSemidirectEquiv.symm j)
  rw [glRep_symm] at h1
  have h2 : c.val (goodLineSemidirectEquiv.symm g * goodLineSemidirectEquiv.symm h)
        (goodLineSemidirectEquiv.symm j) + c.val (goodLineSemidirectEquiv.symm g)
        (goodLineSemidirectEquiv.symm h) =
      rationalCoefficientComponent n trivialCharacter g.val
        (c.val (goodLineSemidirectEquiv.symm h) (goodLineSemidirectEquiv.symm j)) +
      c.val (goodLineSemidirectEquiv.symm g)
        (goodLineSemidirectEquiv.symm h * goodLineSemidirectEquiv.symm j) := by
    have h3 := sub_eq_zero.mp h1
    rw [← h3]
    abel
  simp only [map_mul]
  exact h2

theorem pushCycle_apply (c : inhomogeneousTwoCycles (glRep n)) (g h : _) :
    pushCycle n c (g, h) = c.val (goodLineSemidirectEquiv.symm g)
      (goodLineSemidirectEquiv.symm h) := rfl

theorem iota_inl (r : RadicalLattice) :
    goodLineSemidirectEquiv (SemidirectProduct.inl r) = goodLineRadicalInclusion r := by
  change goodLineRadicalInclusion r * goodLineSplitting 1 = _
  rw [map_one, mul_one]

theorem iota_inr (l : GeneralLinearGroup (Fin 2) ℤ) :
    goodLineSemidirectEquiv (SemidirectProduct.inr l) = goodLineLeviSection l := by
  change goodLineRadicalInclusion 1 * goodLineSplitting l = _
  rw [map_one, one_mul]
  rfl

theorem iota_symm_inl (r : RadicalLattice) :
    goodLineSemidirectEquiv.symm (goodLineRadicalInclusion r) = SemidirectProduct.inl r := by
  rw [MulEquiv.symm_apply_eq]
  exact (iota_inl r).symm

theorem iota_symm_inr (l : GeneralLinearGroup (Fin 2) ℤ) :
    goodLineSemidirectEquiv.symm (goodLineLeviSection l) = SemidirectProduct.inr l := by
  rw [MulEquiv.symm_apply_eq]
  exact (iota_inr l).symm

theorem pushCycle_relative (c : radicalZeroTwoCycles goodLineSplitting.conjAct (glRep n)) :
    pushCycle n c.val ∈ relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRep n) := by
  intro r r'
  rw [pushCycle_apply, ← iota_inl, ← iota_inl, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
  exact c.property r r'

theorem pushCycle_sub (a b : inhomogeneousTwoCycles (glRep n)) :
    pushCycle n (a - b) = pushCycle n a - pushCycle n b := rfl

theorem pushCycle_boundary (u : _ → HomogeneousPoly n) :
    groupCohomology.H2π (goodLineCoefficientRep n)
      (pushCycle n (inhomogeneousBoundaryMap (glRep n) u)) = 0 := by
  rw [groupCohomology.H2π_eq_zero_iff]
  refine ⟨fun g => (u (goodLineSemidirectEquiv.symm g) : goodLineCoefficientRep n), ?_⟩
  funext p
  have hd := groupCohomology.d₁₂_hom_apply (goodLineCoefficientRep n)
    (fun g => u (goodLineSemidirectEquiv.symm g)) p
  rw [hd]
  change _ = (glRep n (goodLineSemidirectEquiv.symm p.1) (u (goodLineSemidirectEquiv.symm p.2)) -
    u (goodLineSemidirectEquiv.symm p.1 * goodLineSemidirectEquiv.symm p.2) +
    u (goodLineSemidirectEquiv.symm p.1))
  rw [glRep_symm, map_mul]
  rfl

theorem pushCycle_faceCycle
    (C : cocycles (fixedPointLevel rationalLevel goodLineFlag)
      (rationalCoefficientComponent n trivialCharacter)) :
    pushCycle n (faceCycle goodLineSplitting.conjAct n trivialCharacter goodLineFlag
      goodLineSemidirectEquivFixed C) =
      ambientCocycleToGroup (fixedPointLevel rationalLevel goodLineFlag)
        (rationalCoefficientComponent n trivialCharacter) C := by
  apply Subtype.ext
  funext p
  change (faceCycle goodLineSplitting.conjAct n trivialCharacter goodLineFlag
      goodLineSemidirectEquivFixed C).val (goodLineSemidirectEquiv.symm p.1)
      (goodLineSemidirectEquiv.symm p.2) = _
  rw [faceCycle_apply]
  change C.val.val ![1, (goodLineSemidirectEquiv (goodLineSemidirectEquiv.symm p.1)).val,
    (goodLineSemidirectEquiv (goodLineSemidirectEquiv.symm p.1)).val *
      (goodLineSemidirectEquiv (goodLineSemidirectEquiv.symm p.2)).val] = _
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  rfl

variable {n}

theorem mixed_eq_binaryEdgeCycle (hn : 0 < n)
    (c : radicalZeroTwoCycles goodLineSplitting.conjAct (glRep n))
    (l : GeneralLinearGroup (Fin 2) ℤ) :
    glTheta n hn ((mixedH1CocycleMap goodLineSplitting.conjAct (glRep n) c).val l) =
      goodLineBinaryEdgeCycle n hn ⟨pushCycle n c.val, pushCycle_relative n c⟩ l := by
  rw [goodLineBinaryEdgeCycle_apply]
  have e1 : glTheta n hn ((mixedH1CocycleMap goodLineSplitting.conjAct (glRep n) c).val l) =
      lowerRadicalH1Coordinate n hn (groupCohomology.H1π (lowerRadicalLatticeRep n)
        (cocycleOfCrossed (lowerRadicalLatticeRep n)
          (crossedRepresentationEqEquiv _ _ (faceRep_goodLine_radical n)
            (mixedCrossedMap goodLineSplitting.conjAct (glRep n) l c)))) := rfl
  rw [e1, lowerRadicalH1Coordinate_apply]
  congr 1
  apply groupCohomology.cocycles₁_ext
  intro r
  change mixedCrossedCochain goodLineSplitting.conjAct (glRep n) c l r =
    goodLineRadicalEdgeCycle n ⟨pushCycle n c.val, pushCycle_relative n c⟩ l r
  rw [goodLineSplitEdgeCycle_apply]
  dsimp only [mixedCrossedCochain]
  rw [pushCycle_apply, pushCycle_apply, iota_symm_inr, iota_symm_inl, iota_symm_inl,
    goodLineSplitting_inverse_action]
  rfl

/-- The `H¹` class of the library's good-line edge cocycle of a pushed radical-zero cycle is the
edge map of the corresponding class. -/
theorem edgeK_eq_of_pushCycle (hn : 0 < n) (z : H2 (fixedPointLevel rationalLevel goodLineFlag) (ρn n))
    (hz : z ∈ KL n)
    (c : radicalZeroTwoCycles goodLineSplitting.conjAct (glRep n))
    (h : groupCohomology.H2π (goodLineCoefficientRep n) (pushCycle n c.val) = toH2L n z) :
    edgeK n hn ⟨z, hz⟩ = groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0)
      (goodLineBinaryEdgeCycle n hn ⟨pushCycle n c.val, pushCycle_relative n c⟩) := by
  rw [goodLineBinaryEdgeCycle_H1]
  change goodLineBinaryEdge n hn ⟨toH2L n z, hz⟩ = _
  congr 1
  exact Subtype.ext h.symm

theorem toH2L_eq_of_face (z : H2 (fixedPointLevel rationalLevel goodLineFlag) (ρn n))
    (c : radicalZeroTwoCycles goodLineSplitting.conjAct (glRep n))
    (h : (inhomogeneousBoundaries (glRep n)).mkQ c.val =
      faceH2Equiv goodLineSplitting.conjAct n trivialCharacter goodLineFlag
        goodLineSemidirectEquivFixed z) :
    groupCohomology.H2π (goodLineCoefficientRep n) (pushCycle n c.val) = toH2L n z := by
  induction z using Submodule.Quotient.induction_on with
  | _ C =>
  have h' := h.trans (faceH2Equiv_classOf goodLineSplitting.conjAct n trivialCharacter goodLineFlag
    goodLineSemidirectEquivFixed C)
  obtain ⟨u, hu⟩ := (Submodule.Quotient.eq (inhomogeneousBoundaries (glRep n))).mp h'
  have e2 : c.val = faceCycle goodLineSplitting.conjAct n trivialCharacter goodLineFlag
      goodLineSemidirectEquivFixed C + (c.val - faceCycle goodLineSplitting.conjAct n trivialCharacter
        goodLineFlag goodLineSemidirectEquivFixed C) := by abel
  have e3 : pushCycle n c.val = pushCycle n (faceCycle goodLineSplitting.conjAct n trivialCharacter
      goodLineFlag goodLineSemidirectEquivFixed C) + pushCycle n (c.val - faceCycle
        goodLineSplitting.conjAct n trivialCharacter goodLineFlag goodLineSemidirectEquivFixed C) := by
    conv_lhs => rw [e2]
    rfl
  rw [e3, map_add, ← hu, pushCycle_boundary, add_zero, pushCycle_faceCycle]
  exact (TernaryPeriodPolynomials.Spectral.GoodLineHecke.toH2L_classOf n C).symm



theorem hs_class_eq_mixed (x : H2 (fixedPointLevel rationalLevel goodLineFlag)
      (rationalCoefficientComponent n trivialCharacter))
    (hxli : x ∈ locallyInnerClasses n trivialCharacter .line goodLineFlag)
    (c₀ : radicalZeroTwoCycles goodLineSplitting.conjAct (glRep n))
    (hc₀ : (inhomogeneousBoundaries (glRep n)).mkQ c₀.val =
      faceH2Equiv goodLineSplitting.conjAct n trivialCharacter goodLineFlag
        goodLineSemidirectEquivFixed x) :
    ((goodLineLocallyInnerEquiv n trivialCharacter ⟨x, hxli⟩ :
        FaceCuspidal goodLineSplitting.conjAct n trivialCharacter goodLineFlag
          goodLineSemidirectEquivFixed) : CrossedH1 (glAction n)) =
      (crossedBoundaries (glAction n)).mkQ
        (mixedH1CocycleMap goodLineSplitting.conjAct (glRep n) c₀) :=
  FaceGeneric.locallyInnerEquivCuspidal_coe_eq_mixed goodLineSplitting.conjAct n trivialCharacter
    goodLineFlag goodLineSemidirectEquivFixed
    (leviH2Vanishes_of_binary goodLineLeviEmbedding goodLineLeviEmbedding_injective)
    (fun radical e he => goodLine_radical_fixes radical e he) goodLineLeviEmbedding
    goodLineLeviEmbedding_injective x hxli c₀ hc₀

theorem repExists (x : H2 (fixedPointLevel rationalLevel goodLineFlag)
      (rationalCoefficientComponent n trivialCharacter))
    (hxli : x ∈ locallyInnerClasses n trivialCharacter .line goodLineFlag) :
    ∃ c₀ : radicalZeroTwoCycles goodLineSplitting.conjAct (glRep n),
      (inhomogeneousBoundaries (glRep n)).mkQ c₀.val =
        faceH2Equiv goodLineSplitting.conjAct n trivialCharacter goodLineFlag
          goodLineSemidirectEquivFixed x :=
  FaceGeneric.exists_radicalZero_representative goodLineSplitting.conjAct n trivialCharacter
    goodLineFlag goodLineSemidirectEquivFixed
    (fun radical e he => goodLine_radical_fixes radical e he) goodLineLeviEmbedding
    goodLineLeviEmbedding_injective x hxli

/-- The Kostant coordinate of the mixed class of a radical-zero cycle is the class of the library's edge cocycle of the
pushed relative cocycle. -/
theorem hs_coordinate_eq_edgeCycle (hn : 0 < n)
    (c₀ : radicalZeroTwoCycles goodLineSplitting.conjAct (glRep n)) :
    h1EquivCrossed (arithmeticBinaryRep (n + 1) 0)
        (glPsi n hn ((crossedBoundaries (glAction n)).mkQ
          (mixedH1CocycleMap goodLineSplitting.conjAct (glRep n) c₀))) =
      groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0)
        (goodLineBinaryEdgeCycle n hn ⟨pushCycle n c₀.val, pushCycle_relative n c₀⟩) := by
  obtain ⟨y, hy1, hy2⟩ := glPsi_mk n hn (mixedH1CocycleMap goodLineSplitting.conjAct (glRep n) c₀)
  rw [hy2, h1EquivCrossed_mk]
  congr 1
  apply groupCohomology.cocycles₁_ext
  intro l
  change y.val l = _
  rw [hy1 l]
  exact mixed_eq_binaryEdgeCycle hn c₀ l

/-- **Good line: the library's explicit edge dictionary is the Hochschild-Serre dictionary.**
For an inner line class `b`, the parabolic class `goodLineParabolic b = phiL (cuspRes true b)` of
`H¹(GL₂(ℤ), Sym^{n+1})` is (with sign `+1`) the image, under the Hochschild-Serre isomorphism
`Face.goodLineLocallyInnerEquiv` followed by the Kostant coordinate `glPsi`, of the local class of `b`
at the good line. -/
theorem goodLineParabolic_eq_hs (hn : 0 < n) (b : innerClasses n .line) :
    ((goodLineParabolic hn b : parabolicH1 (arithmeticBinaryRep (n + 1) 0)) :
        groupCohomology.H1 (arithmeticBinaryRep (n + 1) 0)) =
      h1EquivCrossed (arithmeticBinaryRep (n + 1) 0)
        (glPsi n hn ((goodLineLocallyInnerEquiv n trivialCharacter
          ⟨fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
              goodLineFlag b.val,
            innerBoundary_fixedPointH2_locallyInner b.property goodLineFlag⟩ :
            FaceCuspidal goodLineSplitting.conjAct n trivialCharacter goodLineFlag
              goodLineSemidirectEquivFixed) : CrossedH1 (glAction n))) := by
  have hxli : fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
      goodLineFlag b.val ∈ locallyInnerClasses n trivialCharacter .line goodLineFlag :=
    innerBoundary_fixedPointH2_locallyInner b.property goodLineFlag
  have hrep := repExists _ hxli
  rcases hrep with ⟨c₀, hc₀⟩
  have e1 := hs_class_eq_mixed _ hxli c₀ hc₀
  have e2 := hs_coordinate_eq_edgeCycle hn c₀
  have hKL := TernaryPeriodPolynomials.Argument.FacePairing.fixedPointH2_mem_KL_of_innerBoundary
    b.property
  have hphi : ((goodLineParabolic hn b : parabolicH1 (arithmeticBinaryRep (n + 1) 0)) :
      groupCohomology.H1 (arithmeticBinaryRep (n + 1) 0)) =
      edgeK n hn ⟨fixedPointH2 rationalLevel (ρn n) goodLineFlag b.val, hKL⟩ :=
    congrArg (edgeK n hn) (Subtype.ext
      (TernaryPeriodPolynomials.Argument.FacePairing.psiL_cuspRes_eq n b.val))
  have e3 := edgeK_eq_of_pushCycle hn _ hKL c₀ (toH2L_eq_of_face _ c₀ hc₀)
  exact hphi.trans (e3.trans (e2.symm.trans (congrArg (fun m => h1EquivCrossed
    (arithmeticBinaryRep (n + 1) 0) (glPsi n hn m)) e1.symm)))

theorem hs_image_parabolicToGoodLine (hn : 0 < n)
    (c : parabolicH1 (arithmeticBinaryRep (n + 1) 0)) :
    ((goodLineLocallyInnerEquiv n trivialCharacter (parabolicToGoodLine n hn c) :
        FaceCuspidal goodLineSplitting.conjAct n trivialCharacter goodLineFlag
          goodLineSemidirectEquivFixed) : CrossedH1 (glAction n)) =
      (glPsi n hn).symm ((h1EquivCrossed (arithmeticBinaryRep (n + 1) 0)).symm
        (c : groupCohomology.H1 (arithmeticBinaryRep (n + 1) 0))) :=
  congrArg Subtype.val (LinearEquiv.apply_symm_apply (goodLineLocallyInnerEquiv n trivialCharacter) _)

/-- The Hochschild-Serre inverse of the good line carries `goodLineParabolic b` back to the local class of `b`. -/
theorem parabolicToGoodLine_goodLineParabolic (hn : 0 < n) (b : innerClasses n .line) :
    ((parabolicToGoodLine n hn (goodLineParabolic hn b) :
        locallyInnerClasses n trivialCharacter .line goodLineFlag) :
        H2 (fixedPointLevel rationalLevel goodLineFlag) (rationalCoefficientComponent n trivialCharacter)) =
      fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) goodLineFlag b.val := by
  have hxli : fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
      goodLineFlag b.val ∈ locallyInnerClasses n trivialCharacter .line goodLineFlag :=
    innerBoundary_fixedPointH2_locallyInner b.property goodLineFlag
  have e1 := hs_image_parabolicToGoodLine hn (goodLineParabolic hn b)
  have e2 : ((goodLineLocallyInnerEquiv n trivialCharacter ⟨_, hxli⟩ :
        FaceCuspidal goodLineSplitting.conjAct n trivialCharacter goodLineFlag
          goodLineSemidirectEquivFixed) : CrossedH1 (glAction n)) =
      (glPsi n hn).symm ((h1EquivCrossed (arithmeticBinaryRep (n + 1) 0)).symm
        ((goodLineParabolic hn b : parabolicH1 (arithmeticBinaryRep (n + 1) 0)) :
          groupCohomology.H1 (arithmeticBinaryRep (n + 1) 0))) :=
    ((glPsi n hn).symm_apply_eq.mpr ((h1EquivCrossed (arithmeticBinaryRep (n + 1) 0)).symm_apply_eq.mpr
      (goodLineParabolic_eq_hs hn b))).symm
  have key : goodLineLocallyInnerEquiv n trivialCharacter (parabolicToGoodLine n hn (goodLineParabolic hn b)) =
      goodLineLocallyInnerEquiv n trivialCharacter ⟨_, hxli⟩ := Subtype.ext (e1.trans e2.symm)
  exact congrArg Subtype.val ((goodLineLocallyInnerEquiv n trivialCharacter).injective key)

end TernaryPeriodPolynomials.Argument.FacePairingFull.Literal.GoodLineId
