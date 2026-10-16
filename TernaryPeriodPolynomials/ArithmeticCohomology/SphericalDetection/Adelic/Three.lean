module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Adelic.CongruenceFactorization

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem padicThree_coeRingHom (integer : ℤ_[3]) :
    PadicInt.Coe.ringHom integer = (integer : ℚ_[3]) := rfl

def padicThreeEmbedding : ℤ_[3] →+* ℚ_[3] := PadicInt.Coe.ringHom

theorem padicThreeEmbedding_apply (integer : ℤ_[3]) :
    padicThreeEmbedding integer = (integer : ℚ_[3]) := rfl

theorem padicThreeEmbedding_matrix (matrix : GeneralLinearGroup (Fin 3) ℤ_[3]) :
    GeneralLinearGroup.map PadicInt.Coe.ringHom matrix =
      GeneralLinearGroup.map padicThreeEmbedding matrix := rfl

def finiteThree : FiniteAdeles →+* ℚ_[3] :=
  threeCompletionEquiv.toAlgEquiv.toRingEquiv.toRingHom.comp (finiteEvaluation placeThree)

def adelicThreeGroup : AdelicGL →* LocalThreeGL :=
  (GeneralLinearGroup.map finiteThree).comp finiteGroup

theorem finiteThree_integral (integer : IntegralAdeles) :
    finiteThree (integralEmbedding integer) = (integralThree integer : ℚ_[3]) :=
  (threeIntegral_coe (integer placeThree)).symm

theorem finiteThree_rational (rational : ℚ) :
    finiteThree (algebraMap ℚ FiniteAdeles rational) = (rational : ℚ_[3]) := by
  rw [finiteThree, RingHom.comp_apply, finiteEvaluation_rational]
  exact threeCompletion_rational rational

theorem adelicThreeGroup_rational (matrix : RationalGL3) :
    adelicThreeGroup (rationalGroup matrix) = GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) matrix := by
  change GeneralLinearGroup.map finiteThree (finiteGroup (rationalGroup matrix)) = _
  rw [finiteGroup_rational]
  apply Units.ext
  funext row column
  simp only [rationalFinite, GeneralLinearGroup.map_apply]
  exact finiteThree_rational (matrix.val row column)

theorem adelicThreeGroup_atInfinity (matrix : RealGL3) :
    adelicThreeGroup (atInfinity matrix) = 1 := by
  change GeneralLinearGroup.map finiteThree (finiteGroup (atInfinity matrix)) = 1
  rw [finiteGroup_atInfinity, map_one]

theorem adelicThreeGroup_atFinite (matrix : FiniteGL) :
    adelicThreeGroup (atFinite matrix) = GeneralLinearGroup.map finiteThree matrix := by
  change GeneralLinearGroup.map finiteThree (finiteGroup (atFinite matrix)) = _
  rw [finiteGroup_atFinite]

theorem integralThree_reduceMatrix (integer : GeneralLinearGroup (Fin 3) IntegralAdeles) :
    GeneralLinearGroup.map PadicInt.toZMod (GeneralLinearGroup.map integralThree integer) =
      GeneralLinearGroup.map integralReduction integer := by
  rw [← MonoidHom.comp_apply, ← GeneralLinearGroup.map_comp]
  rfl

theorem generalLinearGroup_map_square {first second third fourth : Type*}
    [CommRing first] [CommRing second] [CommRing third] [CommRing fourth]
    (left : first →+* second) (top : second →+* fourth)
    (bottom : first →+* third) (right : third →+* fourth)
    (square : ∀ value, top (left value) = right (bottom value))
    (matrix : GeneralLinearGroup (Fin 3) first) :
    GeneralLinearGroup.map top (GeneralLinearGroup.map left matrix) =
      GeneralLinearGroup.map right (GeneralLinearGroup.map bottom matrix) := by
  apply Units.ext
  funext row column
  simp only [GeneralLinearGroup.map_apply]
  exact square (matrix.val row column)

theorem finiteThree_integralMatrix (integer : GeneralLinearGroup (Fin 3) IntegralAdeles) :
    GeneralLinearGroup.map padicThreeEmbedding (GeneralLinearGroup.map integralThree integer) =
      GeneralLinearGroup.map finiteThree (GeneralLinearGroup.map integralEmbedding integer) := by
  exact generalLinearGroup_map_square integralThree padicThreeEmbedding integralEmbedding finiteThree
    (fun value => (padicThreeEmbedding_apply (integralThree value)).trans (finiteThree_integral value).symm)
    integer

theorem finiteLevel_atThree (matrix : finiteLevel) :
    InLocalThreeLevel (adelicThreeGroup (atFinite matrix.val)) := by
  obtain ⟨integer, row_fixed, equality⟩ := matrix.property
  refine ⟨GeneralLinearGroup.map integralThree integer, ?_, ?_⟩
  · rw [integralThree_reduceMatrix]
    exact row_fixed
  · rw [padicThreeEmbedding_matrix, adelicThreeGroup_atFinite, ← equality, finiteThree_integralMatrix]

theorem arithmeticLevel_atThree (matrix : arithmeticLevel) :
    InLocalThreeLevel (GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) (rationalInclusion matrix)) := by
  refine ⟨GeneralLinearGroup.map (Int.castRingHom ℤ_[3]) matrix.val, ?_, ?_⟩
  · have reduction : GeneralLinearGroup.map PadicInt.toZMod
        (GeneralLinearGroup.map (Int.castRingHom ℤ_[3]) matrix.val) = reductionThree matrix.val := by
      apply Units.ext
      funext row column
      simp [GeneralLinearGroup.map_apply, reductionThree]
    rw [reduction]
    exact matrix.property
  · apply Units.ext
    funext row column
    simp [GeneralLinearGroup.map_apply, rationalInclusion]

theorem InLocalThreeLevel_mul {first second : LocalThreeGL}
    (first_level : InLocalThreeLevel first) (second_level : InLocalThreeLevel second) :
    InLocalThreeLevel (first * second) := by
  obtain ⟨first_integer, first_row, first_eq⟩ := first_level
  obtain ⟨second_integer, second_row, second_eq⟩ := second_level
  refine ⟨first_integer * second_integer, ?_, ?_⟩
  · rw [map_mul, GeneralLinearGroup.coe_mul, ← Matrix.vecMul_vecMul, first_row, second_row]
  · rw [map_mul, first_eq, second_eq]

theorem rational_badPlane_local_support (representative : RationalGL3)
    (bad : ¬ GoodFlag .plane (QuotientGroup.mk representative)) :
    ∃ parabolic : planeParabolic ℚ_[3], ∃ compact : LocalThreeGL,
      InLocalThreeLevel compact ∧
      GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) representative⁻¹ = parabolic.val * compact := by
  obtain ⟨integer, same_flag⟩ := badPlane_exists_arithmetic_frame (QuotientGroup.mk representative) bad
  have parabolic : representative⁻¹ * rationalInclusion integer ∈ planeParabolic ℚ :=
    QuotientGroup.eq.mp same_flag.symm
  let local_parabolic := GeneralLinearGroup.map (algebraMap ℚ ℚ_[3])
    (representative⁻¹ * rationalInclusion integer)
  have local_member : local_parabolic ∈ planeParabolic ℚ_[3] := by
    constructor
    · change algebraMap ℚ ℚ_[3] ((representative⁻¹ * rationalInclusion integer).val 2 0) = 0
      rw [parabolic.1, map_zero]
    · change algebraMap ℚ ℚ_[3] ((representative⁻¹ * rationalInclusion integer).val 2 1) = 0
      rw [parabolic.2, map_zero]
  refine ⟨⟨local_parabolic, local_member⟩,
    GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) (rationalInclusion integer⁻¹),
    arithmeticLevel_atThree integer⁻¹, ?_⟩
  change GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) representative⁻¹ =
    GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) (representative⁻¹ * rationalInclusion integer) * _
  rw [map_inv rationalInclusion, ← map_mul, mul_inv_cancel_right]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
