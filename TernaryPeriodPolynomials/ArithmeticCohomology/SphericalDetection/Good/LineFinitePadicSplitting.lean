module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.AwayThreePadicSplitting

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem finitePadicPlaneCoordinates_add_place_block (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ (localPair : ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] × ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val])
      (first second : FiniteAdeles), finiteEvaluation place first = 0 → finiteEvaluation place second = 0 →
      (finitePadicPlaneCoordinates
        (finiteAtPlaceScalar place ((finiteCompletionPadicEquiv place).symm localPair.1) + first)
        (finiteAtPlaceScalar place ((finiteCompletionPadicEquiv place).symm localPair.2) + second)).block =
        (finitePadicPlaneCoordinates first second).block *
          finiteAtPadicGL 2 place (padicPlanePivotCoordinates localPair.1 localPair.2).block := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro localPair first second first_zero second_zero
  have equality := finitePadicPlaneCoordinates_split_block place localPair (⟨first, first_zero⟩, ⟨second, second_zero⟩)
  have coordinate_equality := congrArg₂ (fun first second : FiniteAdeles => (finitePadicPlaneCoordinates first second).block)
    (finitePadicSplit_symm place (localPair.1, ⟨first, first_zero⟩))
    (finitePadicSplit_symm place (localPair.2, ⟨second, second_zero⟩))
  exact coordinate_equality.symm.trans equality

theorem standardGoodLineFinitePadicCoordinates_split_block (place : FinitePlace) (distinct : place ≠ placeThree) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ (localPair : ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] × ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val])
      (awayPair : FiniteAwayThreePlace place × FiniteAwayThreePlace place),
      (standardGoodLineFinitePadicCoordinates (finiteAwayThreePadicRadicalJoin place distinct (localPair, awayPair))).block =
        (standardGoodLineFinitePadicCoordinates (awayPair.1.val, awayPair.2.val)).block *
          finiteAtPadicGL 2 place (padicPlanePivotCoordinates localPair.1 localPair.2).block := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro localPair awayPair
  rw [finiteAwayThreePadicRadicalJoin_apply]
  change (finitePadicPlaneCoordinates
    ((finiteAwayThreePadicSplit place distinct).symm (localPair.1, awayPair.1)).val
    ((finiteAwayThreePadicSplit place distinct).symm (localPair.2, awayPair.2)).val).block = _
  rw [finiteAwayThreePadicSplit_symm_val, finiteAwayThreePadicSplit_symm_val]
  exact finitePadicPlaneCoordinates_add_place_block place localPair awayPair.1.val.val awayPair.2.val.val
    awayPair.1.property awayPair.2.property

def goodLineFinitePadicIntegrand (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (exponent : ℂ) (finite : FiniteAwayThree × FiniteAwayThree) : ℂ :=
  finitePadicCuspIntegrand cusp vector exponent (finite.1.val, finite.2.val)

theorem goodLineFinitePadicIntegrand_eq (degree : ℕ) (cusp : CuspidalRepresentation) (parameter : ℂ)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (finite : FiniteAwayThree × FiniteAwayThree) :
    standardGoodLineFiniteCuspWeight degree parameter finite *
      cusp.realize vector (atFinite (standardGoodLineFiniteCoordinates finite).block) =
      goodLineFinitePadicIntegrand cusp vector ((degree : ℂ) / 2 + 3 + parameter) finite := by
  rw [standardGoodLineFiniteCuspWeight_det]
  have independent := finiteSphericalPlaneValue_independent cusp vector spherical
    ((degree : ℂ) / 2 + 3 + parameter) (standardGoodLineFiniteArgument finite)
    (finitePlaneLevelInductionCoordinates _ (standardGoodLineFiniteCoordinates finite))
    (standardGoodLineFinitePadicCoordinates finite)
  unfold goodLineFinitePadicIntegrand finitePadicCuspIntegrand
  dsimp only
  rw [binary_det_atFinite]
  exact independent

theorem goodLineFinitePadicIntegrand_split (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (exponent : ℂ) (place : FinitePlace) (distinct : place ≠ placeThree) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ (localPair : ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] × ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val])
      (awayPair : FiniteAwayThreePlace place × FiniteAwayThreePlace place),
      goodLineFinitePadicIntegrand cusp vector exponent (finiteAwayThreePadicRadicalJoin place distinct (localPair, awayPair)) =
        cuspLocalPadicIntegrand cusp vector (standardGoodLineFinitePadicCoordinates (awayPair.1.val, awayPair.2.val)).block
          place exponent localPair := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro localPair awayPair
  change normPower (GeneralLinearGroup.det (atFinite
    (standardGoodLineFinitePadicCoordinates (finiteAwayThreePadicRadicalJoin place distinct (localPair, awayPair))).block))
      exponent * cusp.realize vector (atFinite
        (standardGoodLineFinitePadicCoordinates (finiteAwayThreePadicRadicalJoin place distinct (localPair, awayPair))).block) = _
  rw [standardGoodLineFinitePadicCoordinates_split_block]
  rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
