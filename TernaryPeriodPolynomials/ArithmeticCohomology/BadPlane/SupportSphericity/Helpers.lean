module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix

noncomputable section

namespace TernaryPeriodPolynomials.BadPlaneSupportSphericity.Helpers

theorem normPower_mul (first second : Adelesˣ) (exponent : ℂ) :
    normPower (first * second) exponent =
      normPower first exponent * normPower second exponent := by
  unfold normPower
  rw [map_mul, NNReal.coe_mul, Real.log_mul (by exact_mod_cast ne_of_gt (adeleNorm_pos first))
    (by exact_mod_cast ne_of_gt (adeleNorm_pos second)), Complex.ofReal_add, mul_add,
    Complex.exp_add]

theorem normPower_ne_zero (unit : Adelesˣ) (exponent : ℂ) :
    normPower unit exponent ≠ 0 := Complex.exp_ne_zero _

theorem planeInductionExponent (degree : ℕ) :
    binaryInductionExponent degree .plane cohomologicalPoint =
      (((degree : ℝ) + 3) / 2 : ℝ) := by
  unfold binaryInductionExponent inductionExponent cohomologicalPoint
  push_cast
  ring

theorem normPower_plane_real (degree : ℕ) (unit : Adelesˣ) :
    normPower unit (-binaryInductionExponent degree .plane cohomologicalPoint) =
      (Real.exp (-((degree : ℝ) + 3) / 2 * Real.log (adeleNorm unit : ℝ)) : ℂ) := by
  rw [planeInductionExponent]
  unfold normPower
  rw [← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_exp]
  congr 2
  ring

theorem map_planeLevi {source target : Type*} [CommRing source] [CommRing target]
    (hom : source →+* target) (binary : GeneralLinearGroup (Fin 2) source)
    (scalar : sourceˣ) :
    GeneralLinearGroup.map hom (planeLevi binary scalar) =
      planeLevi (GeneralLinearGroup.map hom binary) (Units.map hom scalar) := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [planeLevi, planeBlock, GeneralLinearGroup.map_apply]

theorem atFinite_planeLevi (binary : GeneralLinearGroup (Fin 2) FiniteAdeles) :
    atFinite (planeLevi binary 1) = planeLevi (atFinite binary) 1 := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    apply Prod.ext <;> rfl

theorem atInfinity_one {dimension : ℕ} :
    atInfinity (1 : GeneralLinearGroup (Fin dimension) ℝ) = 1 := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  change ((1 : Matrix (Fin dimension) (Fin dimension) ℝ) row column,
    (1 : Matrix (Fin dimension) (Fin dimension) FiniteAdeles) row column) =
      (1 : Matrix (Fin dimension) (Fin dimension) Adeles) row column
  by_cases equal : row = column <;>
    simp only [Matrix.one_apply, equal, ite_true, ite_false] <;> rfl

theorem integral_planeLevi_mem_level (binary : GeneralLinearGroup (Fin 2) IntegralAdeles) :
    GeneralLinearGroup.map integralEmbedding (planeLevi binary 1) ∈ finiteLevel := by
  apply Subgroup.mem_map.mpr
  refine ⟨planeLevi binary 1, ?_, rfl⟩
  change lastRow ᵥ* (GeneralLinearGroup.map integralReduction (planeLevi binary 1)).val = lastRow
  rw [map_planeLevi]
  ext column
  fin_cases column <;>
    simp [lastRow, planeLevi, planeBlock, Matrix.vecMul]

theorem realize_fixed_of_positive_eigenvalue (cusp : CuspidalRepresentation)
    (vector : cusp.smooth) (element : BinaryAdelicGL) (scalar : ℝ)
    (positive : 0 < scalar)
    (eigenfunction : ∀ argument,
      cusp.realize vector (argument * element) = (scalar : ℂ) * cusp.realize vector argument) :
    cusp.π element vector.val = vector.val := by
  have eigenvector : cusp.π element vector.val = (scalar : ℂ) • vector.val := by
    have equal : (⟨cusp.π element vector.val,
        cusp.smooth_stable element vector.val vector.property⟩ : cusp.smooth) =
        (scalar : ℂ) • vector := by
      apply cusp.injective
      funext argument
      rw [cusp.equivariant, eigenfunction, map_smul]
      rfl
    exact congrArg Subtype.val equal
  by_cases zero : vector.val = 0
  · rw [zero, map_zero]
  have norm_equal := cusp.unitary element vector.val
  rw [eigenvector, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos positive] at norm_equal
  have scalar_one : scalar = 1 := by
    exact (mul_right_cancel₀ (norm_ne_zero_iff.mpr zero) (by simpa using norm_equal))
  simpa [scalar_one] using eigenvector

theorem spherical_of_nonzero_at_identity {degree : ℕ} (data : InducingData degree)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane cohomologicalPoint function)
    (nonzero : function 1 ≠ 0) : SphericalCusp data.cusp := by
  obtain ⟨vectors, _, lift⟩ := induced.2.2.1 (1 : AdelicGL)
  let vector : data.cusp.smooth := vectors (fun _ => 1)
  have realization (argument : BinaryAdelicGL) :
      data.cusp.realize vector argument =
        normPower (GeneralLinearGroup.det argument)
          (-binaryInductionExponent degree .plane cohomologicalPoint) *
        function (planeLevi argument 1) := by
    simpa [vector, binaryLevi, atInfinity_one] using
      lift (fun _ => 1) argument
  refine ⟨vector, ?_, ?_⟩
  · intro zero
    have at_one := realization 1
    have vector_zero : data.cusp.realize vector = 0 := by rw [zero, map_zero]
    rw [vector_zero] at at_one
    apply nonzero
    have levi_one : planeLevi (1 : BinaryAdelicGL) 1 = 1 := (planeLeviHom Adeles).map_one
    simpa [normPower, levi_one] using at_one.symm
  · intro integral
    let element : BinaryAdelicGL :=
      atFinite (GeneralLinearGroup.map integralEmbedding integral)
    apply realize_fixed_of_positive_eigenvalue data.cusp vector element
      (Real.exp (-((degree : ℝ) + 3) / 2 * Real.log (adeleNorm (GeneralLinearGroup.det element) : ℝ)))
      (Real.exp_pos _)
    intro argument
    rw [realization, realization, map_mul, normPower_mul, ← normPower_plane_real]
    have levi_mul : planeLevi (argument * element) 1 =
        planeLevi argument 1 * planeLevi element 1 := by
      simpa [planeLeviHom] using (planeLeviHom Adeles).map_mul (argument, 1) (element, 1)
    rw [levi_mul]
    have level := integral_planeLevi_mem_level integral
    have invariant := induced.2.1
      ⟨GeneralLinearGroup.map integralEmbedding (planeLevi integral 1), level⟩
      (planeLevi argument 1)
    change function (planeLevi argument 1 *
      atFinite (GeneralLinearGroup.map integralEmbedding (planeLevi integral 1))) = _ at invariant
    rw [map_planeLevi, map_one, atFinite_planeLevi] at invariant
    rw [invariant]
    ring

theorem representative_nonzero_value {degree : ℕ} (data : InducingData degree)
    (boundaryClass : boundarySummand data .plane) (nonzero : boundaryClass ≠ 0)
    (representative : BadPlaneRepresentative data boundaryClass) :
    ∃ (source : SourceCochain degree), IsSourceCocycle data .plane source ∧
      BadPlaneSource source ∧ ∃ (vertices : Fin 3 → RationalGL3) (flag : RationalGL3),
        source (fun index => GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices index))
          (rationalGroup flag⁻¹) ≠ 0 := by
  obtain ⟨source, cycle, cocycle, evaluates, equal, supported⟩ := representative
  refine ⟨source, cocycle, supported, ?_⟩
  by_contra no_value
  push Not at no_value
  have cycle_zero : cycle = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    funext vertices flag
    obtain ⟨representative, rfl⟩ := QuotientGroup.mk_surjective flag
    rw [evaluates]
    exact no_value vertices representative
  apply nonzero
  apply Subtype.ext
  simpa [cycle_zero] using equal.symm

end TernaryPeriodPolynomials.BadPlaneSupportSphericity.Helpers
