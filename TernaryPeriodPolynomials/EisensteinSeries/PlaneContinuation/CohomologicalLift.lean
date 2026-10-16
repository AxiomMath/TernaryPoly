module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Cusp.PolynomialLift

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspPolynomialLift TernaryPeriodPolynomials.PlaneEisensteinContinuation.DirectionalRealization

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CohomologicalLift

theorem binaryCoefficient_one (degree : ℕ) : binaryCoefficient degree 1 = 1 := by
  unfold binaryCoefficient
  rw [map_one, map_one]

theorem binaryCoefficient_mul (degree : ℕ) (first second : BinaryRealGL) :
    binaryCoefficient degree (first * second) = binaryCoefficient degree first * binaryCoefficient degree second := by
  unfold binaryCoefficient
  rw [map_mul, map_mul]

theorem cohomologicalAction_one (degree : ℕ)
    (function : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1)) (point : BinaryAdelicGL) :
    binaryCohomologicalAction degree 1 function point = function point := by
  simp only [binaryCohomologicalAction, TernaryPeriodPolynomials.PlaneEisensteinContinuation.AveragingSmooth.atInfinity_one, map_one,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers.normPower_one, binaryCoefficient_one, mul_one, Module.End.one_apply, one_smul]

theorem cohomologicalAction_mul (degree : ℕ) (first second : BinaryRealGL)
    (function : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1)) (point : BinaryAdelicGL) :
    binaryCohomologicalAction degree (first * second) function point =
      binaryCohomologicalAction degree first (binaryCohomologicalAction degree second function) point := by
  simp only [binaryCohomologicalAction, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.atInfinity_mul, map_mul,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers.normPower_mul, binaryCoefficient_mul, Module.End.mul_apply,
    map_smul, smul_smul, mul_assoc]

noncomputable def coefficientAction (data : CuspidalRepresentation) (degree : ℕ) (matrix : BinaryRealGL) :
    Vectors data degree →ₗ[ℂ] Vectors data degree where
  toFun vectors index := normPower (Matrix.GeneralLinearGroup.det (atInfinity matrix)) (((degree : ℂ) + 3) / 2) •
    ∑ other : Index (degree + 1), (binaryCoefficient degree matrix (basisMonomial other)).val.coeff index.val •
      smoothTranslate data matrix (vectors other)
  map_add' first second := by
    funext index
    simp only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
  map_smul' scalar vectors := by
    funext index
    simp only [Pi.smul_apply, map_smul, Finset.smul_sum, smul_smul, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro other _
    congr 1
    ring

theorem coefficientAction_realize (data : CuspidalRepresentation) (degree : ℕ) (matrix : BinaryRealGL)
    (vectors : Vectors data degree) (point : BinaryAdelicGL) :
    realization data degree (coefficientAction data degree matrix vectors) point =
      binaryCohomologicalAction degree matrix (realization data degree vectors) point := by
  apply polynomial_ext (degree + 1)
  intro index
  rw [realization_coefficient]
  change data.realize (normPower (Matrix.GeneralLinearGroup.det (atInfinity matrix)) (((degree : ℂ) + 3) / 2) •
    ∑ other : Index (degree + 1), (binaryCoefficient degree matrix (basisMonomial other)).val.coeff index.val •
      smoothTranslate data matrix (vectors other)) point = _
  simp only [map_smul, map_sum, Pi.smul_apply, Finset.sum_apply, smoothTranslate_realize]
  change _ = (normPower (Matrix.GeneralLinearGroup.det (atInfinity matrix))
    (((degree : ℂ) + 3) / 2) • binaryCoefficient degree matrix
      (∑ other : Index (degree + 1), data.realize (vectors other) (point * atInfinity matrix) • basisMonomial other)).val.coeff index.val
  simp only [map_sum, map_smul, Submodule.coe_smul, Submodule.coe_sum, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_smul, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro other _
  exact mul_comm _ _

theorem coefficientAction_one (data : CuspidalRepresentation) (degree : ℕ) :
    coefficientAction data degree 1 = 1 := by
  apply LinearMap.ext
  intro vectors
  apply realization_injective data degree
  funext point
  rw [coefficientAction_realize, cohomologicalAction_one]
  rfl

theorem coefficientAction_mul (data : CuspidalRepresentation) (degree : ℕ) (first second : BinaryRealGL) :
    coefficientAction data degree (first * second) = coefficientAction data degree first * coefficientAction data degree second := by
  apply LinearMap.ext
  intro vectors
  apply realization_injective data degree
  funext point
  simp only [Module.End.mul_apply, coefficientAction_realize, cohomologicalAction_mul]
  congr 1
  funext otherPoint
  exact (coefficientAction_realize data degree second vectors otherPoint).symm

noncomputable def coefficientRepresentation (data : CuspidalRepresentation) (degree : ℕ) :
    Representation ℂ BinaryRealGL (Vectors data degree) where
  toFun := coefficientAction data degree
  map_one' := coefficientAction_one data degree
  map_mul' := coefficientAction_mul data degree

theorem lifted_cocycle_equation (data : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1))
    (values : ∀ matrix, BinaryValues data degree (cocycle matrix))
    (equation : ∀ first second point, cocycle (first * second) point =
      cocycle first point + binaryCohomologicalAction degree first (cocycle second) point)
    (first second : BinaryRealGL) :
    lift data degree (cocycle (first * second)) (values (first * second)) =
      lift data degree (cocycle first) (values first) +
        coefficientAction data degree first (lift data degree (cocycle second) (values second)) := by
  apply realization_injective data degree
  funext point
  rw [map_add, Pi.add_apply, realization_lift, realization_lift, coefficientAction_realize, realization_lift]
  exact equation first second point

theorem lifted_not_coboundary (data : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1))
    (values : ∀ matrix, BinaryValues data degree (cocycle matrix))
    (nontrivialClass : ¬ ∃ function : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1),
      BinaryValues data degree function ∧ ∀ matrix point,
        cocycle matrix point = binaryCohomologicalAction degree matrix function point - function point) :
    ¬ ∃ vectors : Vectors data degree, ∀ matrix,
      lift data degree (cocycle matrix) (values matrix) = coefficientAction data degree matrix vectors - vectors := by
  rintro ⟨vectors, coboundary⟩
  apply nontrivialClass
  refine ⟨realization data degree vectors, realization_values data degree vectors, ?_⟩
  intro matrix point
  have equality := congrArg (fun lifted => realization data degree lifted point) (coboundary matrix)
  rw [realization_lift, map_sub, Pi.sub_apply, coefficientAction_realize] at equality
  exact equality

theorem lifted_joint_smooth (data : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1))
    (values : ∀ matrix, BinaryValues data degree (cocycle matrix))
    (smoothness : ∀ monomial, ∃ family : (Fin 2 → BinaryRealGL) → data.smooth,
      Smooth (fun x => (family x).val) ∧ ∀ x point,
        data.realize (family x) point = (cocycle (x 0) (point * atInfinity (x 1))).val.coeff monomial)
    (index : Index (degree + 1)) :
    Smooth (fun x : Fin 2 → BinaryRealGL =>
      (smoothTranslate data (x 1) (lift data degree (cocycle (x 0)) (values (x 0)) index)).val) := by
  obtain ⟨family, familySmooth, familyRealize⟩ := smoothness index.val
  have equality (x : Fin 2 → BinaryRealGL) :
      smoothTranslate data (x 1) (lift data degree (cocycle (x 0)) (values (x 0)) index) = family x := by
    apply data.injective
    funext point
    rw [smoothTranslate_realize, lift_coefficient, familyRealize]
  simpa only [equality] using familySmooth

theorem lifted_fixed (data : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1))
    (values : ∀ matrix, BinaryValues data degree (cocycle matrix))
    (level : Subgroup BinaryFiniteGL)
    (fixed : ∀ element : level, ∀ matrix point, cocycle matrix (point * atFinite element.val) = cocycle matrix point)
    (element : level) (matrix : BinaryRealGL) (index : Index (degree + 1)) :
    data.π (atFinite element.val) (lift data degree (cocycle matrix) (values matrix) index).val =
      (lift data degree (cocycle matrix) (values matrix) index).val := by
  have equality : TernaryPeriodPolynomials.PlaneEisensteinContinuation.CasimirIrreducibility.smoothAction data (atFinite element.val)
      (lift data degree (cocycle matrix) (values matrix) index) =
      lift data degree (cocycle matrix) (values matrix) index := by
    apply data.injective
    funext point
    change data.realize ⟨data.π (atFinite element.val) (lift data degree (cocycle matrix) (values matrix) index).val,
      data.smooth_stable _ _ (lift data degree (cocycle matrix) (values matrix) index).property⟩ point = _
    rw [data.equivariant, lift_coefficient, lift_coefficient, fixed]
  exact congrArg Subtype.val equality

/-- The statement's nonzero cohomology class has an actual smooth-vector-valued coefficient lift. -/
theorem exists_lifted_cocycle {degree : ℕ} (data : InducingData degree) :
    ∃ cocycle : BinaryRealGL → Vectors data.cusp degree,
      (∀ index : Index (degree + 1), Smooth (fun x : Fin 2 → BinaryRealGL =>
        (smoothTranslate data.cusp (x 1) (cocycle (x 0) index)).val)) ∧
      (∃ level : Subgroup BinaryFiniteGL, IsOpen (level : Set BinaryFiniteGL) ∧
        IsCompact (level : Set BinaryFiniteGL) ∧ ∀ element : level, ∀ matrix index,
          data.cusp.π (atFinite element.val) (cocycle matrix index).val = (cocycle matrix index).val) ∧
      (∀ first second, cocycle (first * second) =
        cocycle first + coefficientAction data.cusp degree first (cocycle second)) ∧
      ¬ ∃ vectors : Vectors data.cusp degree, ∀ matrix,
        cocycle matrix = coefficientAction data.cusp degree matrix vectors - vectors := by
  obtain ⟨cocycle, values, smoothness, ⟨level, openness, compactness, fixed⟩, equation, nontrivialClass⟩ := data.cohomological
  refine ⟨fun matrix => lift data.cusp degree (cocycle matrix) (values matrix),
    lifted_joint_smooth data.cusp degree cocycle values smoothness,
    ⟨level, openness, compactness, lifted_fixed data.cusp degree cocycle values level fixed⟩,
    lifted_cocycle_equation data.cusp degree cocycle values equation,
    lifted_not_coboundary data.cusp degree cocycle values nontrivialClass⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CohomologicalLift
