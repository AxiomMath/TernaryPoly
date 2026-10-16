module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Recovery.ParabolicRelations

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteSectionProjection TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegralFrameOrbit
open scoped Classical Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RecoveryGlobalCusp

theorem levi_unipotent (binary : BinaryAdelicGL) (first second : Adeles) :
    planeLevi binary 1 * planeUnipotent first second =
      planeUnipotent (binary.val 0 0 * first + binary.val 0 1 * second)
        (binary.val 1 0 * first + binary.val 1 1 * second) * planeLevi binary 1 := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [planeLevi, planeBlock, planeUnipotent, Matrix.mul_apply, Fin.sum_univ_three]

theorem levi_product (first second : BinaryAdelicGL) (scalar : Adelesˣ) :
    planeLevi first 1 * planeLevi second scalar = planeLevi (first * second) scalar := by
  have equality := (planeLeviHom Adeles).map_mul (first, 1) (second, scalar)
  change planeLevi (first * second) (1 * scalar) = _ at equality
  rw [one_mul] at equality
  exact equality.symm

theorem point_factorization (point : AdelicGL) :
    ∃ first second : Adeles, ∃ binary : BinaryAdelicGL, ∃ scalar : Adelesˣ,
      ∃ integer : IntegralFiniteGL, ∃ realPoint : RealGL3,
        point = planeUnipotent first second * (planeLevi binary scalar * (inclusion integer * atInfinity realPoint)) := by
  obtain ⟨parabolic, compact, equality, compactMem⟩ := FiniteDecomposition.adelic_plane_compact_factorization point
  obtain ⟨integer, integerEquality⟩ := compactMem.2
  have compactEquality : compact = inclusion integer * atInfinity (realGroup compact) := by
    calc
      compact = atInfinity (realGroup compact) * atFinite (finiteGroup compact) := TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adelicGL_eq_mul compact
      _ = inclusion integer * atInfinity (realGroup compact) := by
        rw [← integerEquality, ← atFinite_atInfinity_commute]
        rfl
  refine ⟨parabolic.val.val 0 2 * (planeCornerUnit parabolic).inv,
    parabolic.val.val 1 2 * (planeCornerUnit parabolic).inv,
    planeBinaryBlock parabolic, planeCornerUnit parabolic, integer, realGroup compact, ?_⟩
  exact equality.trans ((congrArg₂ (fun x y : AdelicGL => x * y)
    (planeParabolic_factorization parabolic) compactEquality).trans (mul_assoc _ _ _))

theorem section_parabolic {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re)
    (first second : Adeles) (binary : BinaryAdelicGL) (scalar : Adelesˣ)
    (point : IntegralFiniteGL) (realPoint : RealGL3) (evaluation : BinaryAdelicGL) :
    FiniteSectionProjection.sectionFunction induced
      (planeLevi evaluation 1 * (planeUnipotent first second * (planeLevi binary scalar * (inclusion point * atInfinity realPoint)))) =
      outerCharacter data parameter scalar *
        (normPower (GeneralLinearGroup.det (evaluation * binary)) (binaryInductionExponent degree .plane parameter) *
          data.cusp.realize (TupleCuspLift.vector induced halfPlane point realPoint) (evaluation * binary)) := by
  rw [← mul_assoc, levi_unipotent, mul_assoc, RecoveryParabolicRelations.section_unipotent,
    ← mul_assoc, levi_product, Helpers.planeLevi_split, mul_assoc, RecoveryParabolicRelations.section_scalar,
    TupleCuspLift.section_realize induced halfPlane point realPoint (evaluation * binary)]
  simp only [TupleCuspLift.vector, map_smul, Pi.smul_apply, smul_eq_mul]

def translated (data : CuspidalRepresentation) (binary : BinaryAdelicGL) : data.smooth →ₗ[ℂ] data.smooth where
  toFun vector := ⟨data.π binary vector.val, data.smooth_stable binary vector.val vector.property⟩
  map_add' first second := Subtype.ext (map_add _ first.val second.val)
  map_smul' scalar vector := Subtype.ext (map_smul _ scalar vector.val)

def vector {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re)
    (binary : BinaryAdelicGL) (scalar : Adelesˣ) (point : IntegralFiniteGL) (realPoint : RealGL3) : data.cusp.smooth :=
  (outerCharacter data parameter scalar * normPower (GeneralLinearGroup.det binary) (binaryInductionExponent degree .plane parameter)) •
    translated data.cusp binary (TupleCuspLift.vector induced halfPlane point realPoint)

theorem realize_vector {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re)
    (first second : Adeles) (binary : BinaryAdelicGL) (scalar : Adelesˣ)
    (point : IntegralFiniteGL) (realPoint : RealGL3) (evaluation : BinaryAdelicGL) :
    data.cusp.realize (vector induced halfPlane binary scalar point realPoint) evaluation =
      normPower (GeneralLinearGroup.det evaluation) (-binaryInductionExponent degree .plane parameter) *
        FiniteSectionProjection.sectionFunction induced
          (planeLevi evaluation 1 * (planeUnipotent first second * (planeLevi binary scalar * (inclusion point * atInfinity realPoint)))) := by
  rw [section_parabolic induced halfPlane first second binary scalar point realPoint evaluation]
  simp only [vector, map_smul, Pi.smul_apply, smul_eq_mul, translated, LinearMap.coe_mk, AddHom.coe_mk, data.cusp.equivariant,
    map_mul, Helpers.normPower_mul, Helpers.normPower_neg]
  field_simp [Helpers.normPower_ne_zero]

theorem vector_smooth {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re)
    (binary : BinaryAdelicGL) (scalar : Adelesˣ) (point : IntegralFiniteGL) (realPoint : RealGL3) :
    Smooth (fun matrices : Fin 1 → RealGL3 => (vector induced halfPlane binary scalar point (realPoint * matrices 0)).val) := by
  change Smooth (fun matrices : Fin 1 → RealGL3 =>
    (outerCharacter data parameter scalar * normPower (GeneralLinearGroup.det binary) (binaryInductionExponent degree .plane parameter)) •
      FiniteHilbertConvolution.action data.cusp binary (TupleCuspLift.vector induced halfPlane point (realPoint * matrices 0)).val)
  exact (((FiniteHilbertConvolution.action data.cusp binary).restrictScalars ℝ).contDiff.comp_contDiffOn
    (TupleCuspRegularity.vector_smooth induced halfPlane point realPoint)).const_smul _

theorem smooth_lift {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) :
    HasSmoothCuspLift data .plane parameter (fun _ : Fin 0 → RealGL3 => FiniteSectionProjection.sectionFunction induced) := by
  intro basePoint
  obtain ⟨first, second, binary, scalar, point, realPoint, rfl⟩ := point_factorization basePoint
  refine ⟨fun matrices => vector induced halfPlane binary scalar point (realPoint * matrices 0),
    vector_smooth induced halfPlane binary scalar point realPoint, ?_⟩
  intro matrices evaluation
  rw [realize_vector induced halfPlane first second binary scalar point (realPoint * matrices 0) evaluation]
  simp only [binaryLevi, Fin.last_zero, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.atInfinity_mul, mul_assoc]

theorem cuspFunctions_mem {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (basePoint : AdelicGL) :
    (fun evaluation : BinaryAdelicGL => normPower (GeneralLinearGroup.det evaluation) (-binaryInductionExponent degree .plane parameter) *
      FiniteSectionProjection.sectionFunction induced (planeLevi evaluation 1 * basePoint)) ∈ cuspFunctions data.cusp := by
  obtain ⟨first, second, binary, scalar, point, realPoint, rfl⟩ := point_factorization basePoint
  refine ⟨vector induced halfPlane binary scalar point realPoint, ?_⟩
  funext evaluation
  exact realize_vector induced halfPlane first second binary scalar point realPoint evaluation

theorem section_smooth {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (basePoint : AdelicGL) :
    Smooth (fun matrices : Fin 1 → RealGL3 => FiniteSectionProjection.sectionFunction induced (basePoint * atInfinity (matrices 0))) := by
  obtain ⟨first, second, binary, scalar, point, realPoint, rfl⟩ := point_factorization basePoint
  have expression (matrices : Fin 1 → RealGL3) :
      FiniteSectionProjection.sectionFunction induced
        ((planeUnipotent first second * (planeLevi binary scalar * (inclusion point * atInfinity realPoint))) * atInfinity (matrices 0)) =
        (outerCharacter data parameter scalar * normPower (GeneralLinearGroup.det binary) (binaryInductionExponent degree .plane parameter)) *
          data.cusp.realize (TupleCuspLift.vector induced halfPlane point (realPoint * matrices 0)) binary := by
    have equality := section_parabolic induced halfPlane first second binary scalar point (realPoint * matrices 0) 1
    have leviOne : planeLevi (1 : BinaryAdelicGL) 1 = 1 := (planeLeviHom Adeles).map_one
    simpa only [leviOne, one_mul, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.atInfinity_mul, mul_assoc] using equality
  simp only [expression]
  exact contDiffOn_const.mul (TupleScalarRegularity.vector_realize_smooth induced halfPlane point realPoint binary)

theorem section_induced {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) :
    IsInduced data .plane parameter (FiniteSectionProjection.sectionFunction induced) := by
  refine ⟨section_smooth induced halfPlane, fun matrix point => FiniteSectionProjection.section_level induced point matrix,
    smooth_lift induced halfPlane, fun first second point => RecoveryParabolicRelations.section_unipotent induced point first second,
    fun scalar point => RecoveryParabolicRelations.section_scalar induced point scalar, cuspFunctions_mem induced halfPlane⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RecoveryGlobalCusp
