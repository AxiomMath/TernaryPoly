module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.ShearExponential
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.GoodLineBlocks
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Lattice.CocycleDetection

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

abbrev RadicalLattice := Multiplicative (ℤ × ℤ)

def radicalLatticeFirst : RadicalLattice := Multiplicative.ofAdd (1, 0)
def radicalLatticeSecond : RadicalLattice := Multiplicative.ofAdd (0, 1)

theorem radicalLattice_generated (element : RadicalLattice) :
    ∃ first second : ℤ, element = radicalLatticeFirst ^ first * radicalLatticeSecond ^ second := by
  refine ⟨element.toAdd.1, element.toAdd.2, ?_⟩
  apply Multiplicative.toAdd.injective
  simp [radicalLatticeFirst, radicalLatticeSecond]

theorem planeUnipotent_add {R : Type*} [CommRing R] (first second third fourth : R) :
    planeUnipotent first second * planeUnipotent third fourth =
      planeUnipotent (first + third) (second + fourth) := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [planeUnipotent, Matrix.mul_apply, Fin.sum_univ_three, add_comm]

theorem lowerPlaneUnipotent_add {R : Type*} [CommRing R] (first second third fourth : R) :
    lowerPlaneUnipotent first second * lowerPlaneUnipotent third fourth =
      lowerPlaneUnipotent (first + third) (second + fourth) := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [lowerPlaneUnipotent, Matrix.mul_apply, Fin.sum_univ_three]

def upperRadicalLattice : RadicalLattice →* RationalGL3 where
  toFun element := planeUnipotent (element.toAdd.1 : ℚ) (element.toAdd.2 : ℚ)
  map_one' := by
    apply Units.ext
    funext row column
    fin_cases row <;> fin_cases column <;> simp [planeUnipotent]
  map_mul' first second := by
    rw [planeUnipotent_add]
    simp

def lowerRadicalLattice : RadicalLattice →* RationalGL3 where
  toFun element := lowerPlaneUnipotent (3 * (element.toAdd.1 : ℚ)) (3 * (element.toAdd.2 : ℚ))
  map_one' := by
    apply Units.ext
    funext row column
    fin_cases row <;> fin_cases column <;> simp [lowerPlaneUnipotent]
  map_mul' first second := by
    rw [lowerPlaneUnipotent_add]
    simp [mul_add]

theorem upperRadicalLattice_injective : Function.Injective upperRadicalLattice := by
  intro first second equality
  apply Multiplicative.toAdd.injective
  apply Prod.ext
  · have entry := congrArg (fun matrix : RationalGL3 => matrix.val 0 2) equality
    change (first.toAdd.1 : ℚ) = (second.toAdd.1 : ℚ) at entry
    exact_mod_cast entry
  · have entry := congrArg (fun matrix : RationalGL3 => matrix.val 1 2) equality
    change (first.toAdd.2 : ℚ) = (second.toAdd.2 : ℚ) at entry
    exact_mod_cast entry

theorem lowerRadicalLattice_injective : Function.Injective lowerRadicalLattice := by
  intro first second equality
  apply Multiplicative.toAdd.injective
  apply Prod.ext
  · have entry := congrArg (fun matrix : RationalGL3 => matrix.val 2 0) equality
    change 3 * (first.toAdd.1 : ℚ) = 3 * (second.toAdd.1 : ℚ) at entry
    exact_mod_cast (mul_left_cancel₀ (by norm_num : (3 : ℚ) ≠ 0) entry)
  · have entry := congrArg (fun matrix : RationalGL3 => matrix.val 2 1) equality
    change 3 * (first.toAdd.2 : ℚ) = 3 * (second.toAdd.2 : ℚ) at entry
    exact_mod_cast (mul_left_cancel₀ (by norm_num : (3 : ℚ) ≠ 0) entry)

theorem upperRadicalLattice_stabilizer (element : RadicalLattice) :
    upperRadicalLattice element ∈ flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)) := by
  apply (identityPlane_stabilizer_blocks_iff _).mpr
  refine ⟨element.toAdd.1, element.toAdd.2, 1, ?_⟩
  have levi_one : planeLevi (1 : GeneralLinearGroup (Fin 2) ℤ) 1 = 1 := by
    apply Units.ext
    exact planeBlock_one
  rw [levi_one, mul_one, map_planeUnipotent]
  rfl

theorem lowerRadicalLattice_stabilizer (element : RadicalLattice) :
    lowerRadicalLattice element ∈ flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) := by
  apply (goodLine_stabilizer_blocks_iff _).mpr
  refine ⟨element.toAdd.1, element.toAdd.2, 1, ?_⟩
  have levi_one : planeLevi (1 : GeneralLinearGroup (Fin 2) ℤ) 1 = 1 := by
    apply Units.ext
    exact planeBlock_one
  rw [levi_one, one_mul, map_lowerPlaneUnipotent]
  simp [lowerRadicalLattice]

def upperRadicalLatticeRep (degree : ℕ) : Rep ℂ RadicalLattice :=
  Rep.of ((rationalCoefficientComponent degree trivialCharacter).comp upperRadicalLattice)

def lowerRadicalLatticeRep (degree : ℕ) : Rep ℂ RadicalLattice :=
  Rep.of ((rationalCoefficientComponent degree trivialCharacter).comp lowerRadicalLattice)

theorem upperRadicalLatticeRep_rho (degree : ℕ) (element : RadicalLattice) :
    (upperRadicalLatticeRep degree).ρ element =
      rationalCoefficientComponent degree trivialCharacter (upperRadicalLattice element) := rfl

theorem lowerRadicalLatticeRep_rho (degree : ℕ) (element : RadicalLattice) :
    (lowerRadicalLatticeRep degree).ρ element =
      rationalCoefficientComponent degree trivialCharacter (lowerRadicalLattice element) := rfl

theorem rationalCoefficient_planeUnipotent (degree : ℕ) (first second : ℚ)
    (polynomial : HomogeneousPoly degree) :
    rationalCoefficientComponent degree trivialCharacter (planeUnipotent first second) polynomial =
      homogeneousAction degree (-1) (planeUnipotent (first : ℂ) (second : ℂ)) polynomial := by
  change realCoefficientComponent degree trivialCharacter
    (GeneralLinearGroup.map (algebraMap ℚ ℝ) (planeUnipotent first second)) polynomial = _
  rw [map_planeUnipotent, realCoefficientComponent_trivial, map_planeUnipotent]
  simp

theorem rationalCoefficient_lowerPlaneUnipotent (degree : ℕ) (first second : ℚ)
    (polynomial : HomogeneousPoly degree) :
    rationalCoefficientComponent degree trivialCharacter (lowerPlaneUnipotent first second) polynomial =
      homogeneousAction degree (-1) (lowerPlaneUnipotent (first : ℂ) (second : ℂ)) polynomial := by
  change realCoefficientComponent degree trivialCharacter
    (GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerPlaneUnipotent first second)) polynomial = _
  rw [map_lowerPlaneUnipotent, realCoefficientComponent_trivial, map_lowerPlaneUnipotent]
  simp

attribute [local instance] complexEndRationalAlgebra

theorem upperRadicalLatticeRep_first (degree : ℕ) :
    (upperRadicalLatticeRep degree).ρ radicalLatticeFirst = IsNilpotent.exp (upperRadicalGenerator degree 0) := by
  rw [upperRadicalLatticeRep_rho, upperRadicalGenerator_exponential]
  change rationalCoefficientComponent degree trivialCharacter (planeUnipotent 1 0) =
    homogeneousAction degree (-1) (planeUnipotent 1 0)
  apply LinearMap.ext
  intro polynomial
  simpa only [Rat.cast_one, Rat.cast_zero] using rationalCoefficient_planeUnipotent degree 1 0 polynomial

theorem upperRadicalLatticeRep_second (degree : ℕ) :
    (upperRadicalLatticeRep degree).ρ radicalLatticeSecond = IsNilpotent.exp (upperRadicalGenerator degree 1) := by
  rw [upperRadicalLatticeRep_rho, upperRadicalGenerator_exponential]
  change rationalCoefficientComponent degree trivialCharacter (planeUnipotent 0 1) =
    homogeneousAction degree (-1) (planeUnipotent 0 1)
  apply LinearMap.ext
  intro polynomial
  simpa only [Rat.cast_one, Rat.cast_zero] using rationalCoefficient_planeUnipotent degree 0 1 polynomial

theorem lowerRadicalLatticeRep_first (degree : ℕ) :
    (lowerRadicalLatticeRep degree).ρ radicalLatticeFirst = IsNilpotent.exp (lowerRadicalGenerator degree 0) := by
  rw [lowerRadicalLatticeRep_rho, lowerRadicalGenerator_exponential]
  change rationalCoefficientComponent degree trivialCharacter (lowerPlaneUnipotent (3 * 1) (3 * 0)) =
    homogeneousAction degree (-1) (lowerPlaneUnipotent 3 0)
  norm_num only
  apply LinearMap.ext
  intro polynomial
  have equality := rationalCoefficient_lowerPlaneUnipotent degree 3 0 polynomial
  norm_num only at equality
  exact equality

theorem lowerRadicalLatticeRep_second (degree : ℕ) :
    (lowerRadicalLatticeRep degree).ρ radicalLatticeSecond = IsNilpotent.exp (lowerRadicalGenerator degree 1) := by
  rw [lowerRadicalLatticeRep_rho, lowerRadicalGenerator_exponential]
  change rationalCoefficientComponent degree trivialCharacter (lowerPlaneUnipotent (3 * 0) (3 * 1)) =
    homogeneousAction degree (-1) (lowerPlaneUnipotent 0 3)
  norm_num only
  apply LinearMap.ext
  intro polynomial
  have equality := rationalCoefficient_lowerPlaneUnipotent degree 0 3 polynomial
  norm_num only at equality
  exact equality

end TernaryPeriodPolynomials.SphericalDetection.Helpers
