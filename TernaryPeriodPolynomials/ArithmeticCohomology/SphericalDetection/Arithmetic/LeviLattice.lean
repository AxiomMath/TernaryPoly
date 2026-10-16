module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Lattice.CocycleNaturality
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Radical.LatticePairs

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem map_planeLevi_one {R S : Type*} [CommRing R] [CommRing S]
    (hom : R →+* S) (matrix : GeneralLinearGroup (Fin 2) R) :
    GeneralLinearGroup.map hom (planeLevi matrix 1) =
      planeLevi (GeneralLinearGroup.map hom matrix) 1 := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [GeneralLinearGroup.map_apply, planeLevi, planeBlock]

theorem planeLevi_one_inverse {R : Type*} [CommRing R] (matrix : GeneralLinearGroup (Fin 2) R) :
    planeLevi matrix⁻¹ 1 = (planeLevi matrix 1)⁻¹ := by
  apply Units.ext
  rfl

def upperLeviLatticeInput (matrix : GeneralLinearGroup (Fin 2) ℤ) : RadicalLattice →* RadicalLattice where
  toFun element := Multiplicative.ofAdd
    (matrix⁻¹.val 0 0 * element.toAdd.1 + matrix⁻¹.val 0 1 * element.toAdd.2,
      matrix⁻¹.val 1 0 * element.toAdd.1 + matrix⁻¹.val 1 1 * element.toAdd.2)
  map_one' := by simp
  map_mul' first second := by
    apply Multiplicative.toAdd.injective
    dsimp
    ext <;> ring

def lowerLeviLatticeInput (matrix : GeneralLinearGroup (Fin 2) ℤ) : RadicalLattice →* RadicalLattice where
  toFun element := Multiplicative.ofAdd
    (element.toAdd.1 * matrix.val 0 0 + element.toAdd.2 * matrix.val 1 0,
      element.toAdd.1 * matrix.val 0 1 + element.toAdd.2 * matrix.val 1 1)
  map_one' := by simp
  map_mul' first second := by
    apply Multiplicative.toAdd.injective
    dsimp
    ext <;> ring

def arithmeticLevi (matrix : GeneralLinearGroup (Fin 2) ℤ) : RationalGL3 :=
  GeneralLinearGroup.map (Int.castRingHom ℚ) (planeLevi matrix 1)

theorem upperLeviLatticeInput_conjugation (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (element : RadicalLattice) :
    upperRadicalLattice element * arithmeticLevi matrix =
      arithmeticLevi matrix * upperRadicalLattice (upperLeviLatticeInput matrix element) := by
  have inverse_eq := planeLevi_planeUnipotent_commute matrix⁻¹ element.toAdd.1 element.toAdd.2
  rw [planeLevi_one_inverse] at inverse_eq
  have equality := congrArg (fun value => planeLevi matrix 1 * value * planeLevi matrix 1) inverse_eq
  simp only [mul_assoc, inv_mul_cancel, mul_one, mul_inv_cancel_left] at equality
  have mapped := congrArg (GeneralLinearGroup.map (Int.castRingHom ℚ)) equality
  simpa [upperRadicalLattice, arithmeticLevi, upperLeviLatticeInput, map_planeUnipotent] using mapped

theorem lowerLeviLatticeInput_conjugation (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (element : RadicalLattice) :
    lowerRadicalLattice element * arithmeticLevi matrix =
      arithmeticLevi matrix * lowerRadicalLattice (lowerLeviLatticeInput matrix element) := by
  have equality := lowerPlaneUnipotent_planeLevi_commute matrix (3 * element.toAdd.1) (3 * element.toAdd.2)
  have mapped := congrArg (GeneralLinearGroup.map (Int.castRingHom ℚ)) equality
  simpa [lowerRadicalLattice, arithmeticLevi, lowerLeviLatticeInput,
    map_lowerPlaneUnipotent, mul_add, mul_assoc] using mapped

def arithmeticLeviCoefficient (degree : ℕ) (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    Module.End ℂ (HomogeneousPoly degree) :=
  rationalCoefficientComponent degree trivialCharacter (arithmeticLevi matrix)

theorem arithmeticLeviCoefficient_injective (degree : ℕ) (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    Function.Injective (arithmeticLeviCoefficient degree matrix) := by
  let representation := Rep.of (rationalCoefficientComponent degree trivialCharacter)
  exact (representationLinearEquiv representation (arithmeticLevi matrix)).injective

theorem rationalCoefficient_integer (degree : ℕ) (matrix : GeneralLinearGroup (Fin 3) ℤ)
    (polynomial : HomogeneousPoly degree) :
    rationalCoefficientComponent degree trivialCharacter
        (GeneralLinearGroup.map (Int.castRingHom ℚ) matrix) polynomial =
      homogeneousAction degree (-1) (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix) polynomial := by
  change realCoefficientComponent degree trivialCharacter
    (GeneralLinearGroup.map (algebraMap ℚ ℝ) (GeneralLinearGroup.map (Int.castRingHom ℚ) matrix)) polynomial = _
  rw [realCoefficientComponent_trivial]
  have maps : GeneralLinearGroup.map (algebraMap ℝ ℂ)
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) (GeneralLinearGroup.map (Int.castRingHom ℚ) matrix)) =
      GeneralLinearGroup.map (Int.castRingHom ℂ) matrix := by
    apply Units.ext
    funext row column
    simp [GeneralLinearGroup.map_apply]
  rw [maps]

theorem arithmeticLeviCoefficient_homogeneous (degree : ℕ) (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    arithmeticLeviCoefficient degree matrix =
      homogeneousAction degree (-1) (planeLevi (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix) 1) := by
  apply LinearMap.ext
  intro polynomial
  change rationalCoefficientComponent degree trivialCharacter
    (GeneralLinearGroup.map (Int.castRingHom ℚ) (planeLevi matrix 1)) polynomial = _
  rw [rationalCoefficient_integer, map_planeLevi_one]

theorem upperLeviLatticeInput_intertwines (degree : ℕ) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (element : RadicalLattice) :
    ((upperRadicalLatticeRep degree).ρ element).comp (arithmeticLeviCoefficient degree matrix) =
      (arithmeticLeviCoefficient degree matrix).comp
        ((upperRadicalLatticeRep degree).ρ (upperLeviLatticeInput matrix element)) := by
  change rationalCoefficientComponent degree trivialCharacter (upperRadicalLattice element) *
    rationalCoefficientComponent degree trivialCharacter (arithmeticLevi matrix) =
    rationalCoefficientComponent degree trivialCharacter (arithmeticLevi matrix) *
    rationalCoefficientComponent degree trivialCharacter (upperRadicalLattice (upperLeviLatticeInput matrix element))
  rw [← map_mul, ← map_mul, upperLeviLatticeInput_conjugation]

theorem lowerLeviLatticeInput_intertwines (degree : ℕ) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (element : RadicalLattice) :
    ((lowerRadicalLatticeRep degree).ρ element).comp (arithmeticLeviCoefficient degree matrix) =
      (arithmeticLeviCoefficient degree matrix).comp
        ((lowerRadicalLatticeRep degree).ρ (lowerLeviLatticeInput matrix element)) := by
  change rationalCoefficientComponent degree trivialCharacter (lowerRadicalLattice element) *
    rationalCoefficientComponent degree trivialCharacter (arithmeticLevi matrix) =
    rationalCoefficientComponent degree trivialCharacter (arithmeticLevi matrix) *
    rationalCoefficientComponent degree trivialCharacter (lowerRadicalLattice (lowerLeviLatticeInput matrix element))
  rw [← map_mul, ← map_mul, lowerLeviLatticeInput_conjugation]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
