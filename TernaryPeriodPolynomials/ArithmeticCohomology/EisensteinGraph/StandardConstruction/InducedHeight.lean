module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Cusp.LiftCovariance

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.InducedHeight

theorem det_map {size : ℕ} {R S : Type} [CommRing R] [CommRing S]
    (hom : R →+* S) (element : GeneralLinearGroup (Fin size) R) :
    GeneralLinearGroup.det (GeneralLinearGroup.map hom element) =
      Units.map hom.toMonoidHom (GeneralLinearGroup.det element) := by
  apply Units.ext
  exact (hom.map_det element.val).symm

theorem unit_split (unit : Adelesˣ) (integral : IntegralAdelesˣ)
    (finite : Units.map (RingHom.snd ℝ FiniteAdeles) unit =
      Units.map integralEmbedding.toMonoidHom integral) :
    unit = realAdeleUnit (Units.map (RingHom.fst ℝ FiniteAdeles) unit) *
      integralAdeleUnit integral := by
  apply Units.ext
  apply Prod.ext
  · change unit.val.1 = unit.val.1 * 1
    exact (mul_one _).symm
  · change unit.val.2 = 1 * integralEmbedding integral.val
    rw [one_mul]
    exact congrArg Units.val finite

theorem orthogonal_det_square (element : RealGL3)
    (orthogonal : element.val.transpose * element.val = 1) :
    GeneralLinearGroup.det element * GeneralLinearGroup.det element = 1 := by
  apply Units.ext
  change element.val.det * element.val.det = 1
  have equation := congrArg Matrix.det orthogonal
  simpa only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] using equation

theorem compact_det_norm (element : AdelicGL) (membership : inMaximalCompact element) :
    adeleNorm (GeneralLinearGroup.det element) = 1 := by
  obtain ⟨integral, finite⟩ := membership.2
  have finiteDet : Units.map (RingHom.snd ℝ FiniteAdeles) (GeneralLinearGroup.det element) =
      Units.map integralEmbedding.toMonoidHom (GeneralLinearGroup.det integral) := by
    calc
      _ = GeneralLinearGroup.det (finiteGroup element) := (det_map _ _).symm
      _ = GeneralLinearGroup.det (GeneralLinearGroup.map integralEmbedding integral) :=
        congrArg GeneralLinearGroup.det finite.symm
      _ = _ := det_map integralEmbedding integral
  have realDet : Units.map (RingHom.fst ℝ FiniteAdeles) (GeneralLinearGroup.det element) =
      GeneralLinearGroup.det (realGroup element) :=
    (det_map (RingHom.fst ℝ FiniteAdeles) element).symm
  rw [unit_split (GeneralLinearGroup.det element) (GeneralLinearGroup.det integral) finiteDet,
    realDet, map_mul, Norms.integralUnit_norm, mul_one]
  apply Norms.square_one_norm
  change realUnitHom (GeneralLinearGroup.det (realGroup element)) *
      realUnitHom (GeneralLinearGroup.det (realGroup element)) = 1
  rw [← map_mul, orthogonal_det_square _ membership.1, map_one]

theorem planeUnipotent_det (first second : Adeles) :
    GeneralLinearGroup.det (planeUnipotent first second) = 1 := by
  apply Units.ext
  simp [planeUnipotent, GeneralLinearGroup.det, Matrix.det_fin_three]

theorem planeLevi_det (binary : BinaryAdelicGL) (unit : Adelesˣ) :
    GeneralLinearGroup.det (planeLevi binary unit) = GeneralLinearGroup.det binary * unit := by
  apply Units.ext
  change (planeBlock binary.val unit.val).det = binary.val.det * unit.val
  simp [planeBlock, Matrix.det_fin_three, Matrix.det_fin_two]
  ring

theorem decomposition_det_norm (first second : Adeles) (binary : BinaryAdelicGL)
    (unit : Adelesˣ) (compact : AdelicGL) (membership : inMaximalCompact compact) :
    adeleNorm (GeneralLinearGroup.det
      (planeUnipotent first second * planeLevi binary unit * compact)) =
        adeleNorm (GeneralLinearGroup.det binary) * adeleNorm unit := by
  simp only [map_mul, planeUnipotent_det, planeLevi_det, one_mul,
    compact_det_norm compact membership, mul_one]

theorem exponent_identity (degree : ℕ) (parameter : ℂ) :
    (-2 * inductionExponent .plane parameter).re -
      (binaryInductionExponent degree .plane parameter).re =
        -((degree : ℝ) + 6) / 2 - parameter.re := by
  simp [inductionExponent, binaryInductionExponent, Complex.mul_re]
  ring

theorem positive_weight_identity (first second : ℝ) (firstPositive : 0 < first)
    (secondPositive : 0 < second) (rankExponent binaryExponent : ℝ) :
    second ^ rankExponent * first ^ binaryExponent =
      (first * second) ^ binaryExponent * second ^ (rankExponent - binaryExponent) := by
  rw [Real.mul_rpow firstPositive.le secondPositive.le, mul_assoc,
    ← Real.rpow_add secondPositive,
    show binaryExponent + (rankExponent - binaryExponent) = rankExponent by ring, mul_comm]

theorem plane_weight_identity (degree : ℕ) (parameter : ℂ) (first second : Adeles)
    (binary : BinaryAdelicGL) (unit : Adelesˣ) (compact : AdelicGL)
    (membership : inMaximalCompact compact) :
    (adeleNorm unit : ℝ) ^ (-2 * inductionExponent .plane parameter).re *
      (adeleNorm (GeneralLinearGroup.det binary) : ℝ) ^
        (binaryInductionExponent degree .plane parameter).re =
    (adeleNorm (GeneralLinearGroup.det
      (planeUnipotent first second * planeLevi binary unit * compact)) : ℝ) ^
        (binaryInductionExponent degree .plane parameter).re *
      (adeleNorm unit : ℝ) ^ (-((degree : ℝ) + 6) / 2 - parameter.re) := by
  rw [decomposition_det_norm first second binary unit compact membership, NNReal.coe_mul]
  have binaryPositive : (0 : ℝ) < (adeleNorm (GeneralLinearGroup.det binary) : ℝ) :=
    adeleNorm_pos (GeneralLinearGroup.det binary)
  have unitPositive : (0 : ℝ) < (adeleNorm unit : ℝ) := adeleNorm_pos unit
  rw [positive_weight_identity _ _ binaryPositive unitPositive, exponent_identity]

theorem flat_height_bound {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension) :
    ∃ bound : ℝ, ∀ parameter first second binary unit compact, inMaximalCompact compact →
      ‖(CuspLift.vector data .plane parameter (extension parameter) (flat.1 parameter)
        (planeUnipotent first second * planeLevi binary unit * compact)).val‖ ≤
        ((adeleNorm (GeneralLinearGroup.det
          (planeUnipotent first second * planeLevi binary unit * compact)) : ℝ) ^
            (binaryInductionExponent degree .plane parameter).re *
          (adeleNorm unit : ℝ) ^ (-((degree : ℝ) + 6) / 2 - parameter.re)) * bound := by
  obtain ⟨bound, bounded⟩ := CuspLiftCovariance.flat_plane_bound data extension flat
  refine ⟨bound, ?_⟩
  intro parameter first second binary unit compact membership
  rw [← plane_weight_identity degree parameter first second binary unit compact membership]
  exact bounded parameter first second binary unit compact membership

theorem flat_norm_eq_of_re_eq {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (firstParameter secondParameter : ℂ) (sameReal : firstParameter.re = secondParameter.re)
    (argument : AdelicGL) :
    ‖extension firstParameter argument‖ = ‖extension secondParameter argument‖ := by
  obtain ⟨first, second, binary, unit, compact, membership, decomposition⟩ :=
    AdelicDecomposition.adelic_planeDecomposition argument
  rw [decomposition,
    CuspLiftCovariance.flat_scalar_formula data extension flat firstParameter
      first second binary unit compact membership,
    CuspLiftCovariance.flat_scalar_formula data extension flat secondParameter
      first second binary unit compact membership]
  simp only [norm_mul, NormPower.normPower_norm, binaryInductionExponent, inductionExponent]
  congr 2 <;> simp [Complex.mul_re, sameReal]

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.InducedHeight
