module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Radical.LatticeCohomology
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Split.CocycleEdge

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

attribute [local instance] complexEndRationalAlgebra

theorem radicalLattice_invariants_iff (representation : Rep ℂ RadicalLattice) (vector : representation) :
    vector ∈ representation.ρ.invariants ↔
      (representation.ρ radicalLatticeFirst - 1) vector = 0 ∧
      (representation.ρ radicalLatticeSecond - 1) vector = 0 := by
  rw [Representation.mem_invariants]
  constructor
  · intro invariant
    constructor
    · change representation.ρ radicalLatticeFirst vector - vector = 0
      rw [invariant, sub_self]
    · change representation.ρ radicalLatticeSecond vector - vector = 0
      rw [invariant, sub_self]
  · rintro ⟨first_zero, second_zero⟩ element
    have zero := oneCocycle_eq_zero_of_two_generators representation (oneBoundaryCycle representation vector)
      radicalLatticeFirst radicalLatticeSecond radicalLattice_generated first_zero second_zero
    have value := congrArg (fun cycle : groupCohomology.cocycles₁ representation => cycle element) zero
    exact sub_eq_zero.mp value

theorem upperRadicalInvariant_generators (degree : ℕ) (polynomial : HomogeneousPoly degree) :
    polynomial ∈ (upperRadicalLatticeRep degree).ρ.invariants ↔
      upperRadicalGenerator degree 0 polynomial = 0 ∧ upperRadicalGenerator degree 1 polynomial = 0 := by
  refine (radicalLattice_invariants_iff (upperRadicalLatticeRep degree) polynomial).trans ?_
  rw [upperRadicalLatticeRep_first, upperRadicalLatticeRep_second]
  exact and_congr
    (by rw [exp_inst_irrel _ Algebra.toModule]; exact nilpotent_difference_kernel _ degree (upperRadicalGenerator_power_zero degree 0) polynomial)
    (by rw [exp_inst_irrel _ Algebra.toModule]; exact nilpotent_difference_kernel _ degree (upperRadicalGenerator_power_zero degree 1) polynomial)

theorem lowerRadicalInvariant_generators (degree : ℕ) (polynomial : HomogeneousPoly degree) :
    polynomial ∈ (lowerRadicalLatticeRep degree).ρ.invariants ↔
      lowerRadicalGenerator degree 0 polynomial = 0 ∧ lowerRadicalGenerator degree 1 polynomial = 0 := by
  refine (radicalLattice_invariants_iff (lowerRadicalLatticeRep degree) polynomial).trans ?_
  rw [lowerRadicalLatticeRep_first, lowerRadicalLatticeRep_second]
  exact and_congr
    (by rw [exp_inst_irrel _ Algebra.toModule]; exact nilpotent_difference_kernel _ degree (lowerRadicalGenerator_power_zero degree 0) polynomial)
    (by rw [exp_inst_irrel _ Algebra.toModule]; exact nilpotent_difference_kernel _ degree (lowerRadicalGenerator_power_zero degree 1) polynomial)

theorem upperRadicalGenerator_zero_iff (degree : ℕ) (polynomial : HomogeneousPoly degree) (coordinate : Fin 2) :
    upperRadicalGenerator degree coordinate polynomial = 0 ↔ pderiv coordinate.castSucc polynomial.val = 0 := by
  constructor
  · intro zero
    have value := congrArg Subtype.val zero
    change (-1 : ℂ) • (X 2 * pderiv coordinate.castSucc polynomial.val) = 0 at value
    exact (mul_eq_zero.mp ((smul_eq_zero.mp value).resolve_left (by norm_num))).resolve_left (X_ne_zero 2)
  · intro zero
    apply Subtype.ext
    change (-1 : ℂ) • (X 2 * pderiv coordinate.castSucc polynomial.val) = 0
    rw [zero, mul_zero, smul_zero]

theorem lowerRadicalGenerator_zero_iff (degree : ℕ) (polynomial : HomogeneousPoly degree) (coordinate : Fin 2) :
    lowerRadicalGenerator degree coordinate polynomial = 0 ↔ pderiv 2 polynomial.val = 0 := by
  constructor
  · intro zero
    have value := congrArg Subtype.val zero
    change (-3 : ℂ) • (X coordinate.castSucc * pderiv 2 polynomial.val) = 0 at value
    exact (mul_eq_zero.mp ((smul_eq_zero.mp value).resolve_left (by norm_num))).resolve_left (X_ne_zero coordinate.castSucc)
  · intro zero
    apply Subtype.ext
    change (-3 : ℂ) • (X coordinate.castSucc * pderiv 2 polynomial.val) = 0
    rw [zero, mul_zero, smul_zero]

theorem upperRadicalInvariant_derivatives (degree : ℕ) (polynomial : HomogeneousPoly degree) :
    polynomial ∈ (upperRadicalLatticeRep degree).ρ.invariants ↔
      pderiv 0 polynomial.val = 0 ∧ pderiv 1 polynomial.val = 0 := by
  rw [upperRadicalInvariant_generators, upperRadicalGenerator_zero_iff, upperRadicalGenerator_zero_iff]
  rfl

theorem lowerRadicalInvariant_derivative (degree : ℕ) (polynomial : HomogeneousPoly degree) :
    polynomial ∈ (lowerRadicalLatticeRep degree).ρ.invariants ↔ pderiv 2 polynomial.val = 0 := by
  rw [lowerRadicalInvariant_generators, lowerRadicalGenerator_zero_iff, lowerRadicalGenerator_zero_iff, and_self]

theorem homogeneous_binary_derivatives_zero {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (first_zero : pderiv 0 polynomial.val = 0) (second_zero : pderiv 1 polynomial.val = 0) :
    polynomial.val = C (polynomial.val.coeff (Finsupp.single 2 degree)) * X 2 ^ degree := by
  have support_single (exponent : Fin 3 →₀ ℕ) (nonzero : polynomial.val.coeff exponent ≠ 0) :
      exponent = Finsupp.single 2 degree := by
    have member := mem_support_iff.mpr nonzero
    have first := mem_support_notMem_vars_zero member (pderiv_zero_notMem_vars 0 polynomial.val first_zero)
    have second := mem_support_notMem_vars_zero member (pderiv_zero_notMem_vars 1 polynomial.val second_zero)
    have equality : exponent = Finsupp.single 2 (exponent 2) := by
      ext coordinate
      fin_cases coordinate <;> simp [first, second]
    have total : exponent.degree = degree := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using polynomial.property nonzero
    rw [equality, Finsupp.degree_single] at total
    exact equality.trans (congrArg (Finsupp.single 2) total)
  rw [C_mul_X_pow_eq_monomial]
  apply MvPolynomial.ext
  intro exponent
  by_cases equal : Finsupp.single 2 degree = exponent
  · subst exponent
    simp
  · have zero : polynomial.val.coeff exponent = 0 := by
      by_contra nonzero
      exact equal (support_single exponent nonzero).symm
    simp only [coeff_monomial, ite_eq_right equal, zero]

theorem upperRadicalInvariant_scalar (degree : ℕ) (polynomial : HomogeneousPoly degree) :
    polynomial ∈ (upperRadicalLatticeRep degree).ρ.invariants ↔
      ∃ scalar : ℂ, polynomial.val = C scalar * X 2 ^ degree := by
  rw [upperRadicalInvariant_derivatives]
  constructor
  · rintro ⟨first, second⟩
    exact ⟨_, homogeneous_binary_derivatives_zero polynomial first second⟩
  · rintro ⟨scalar, equality⟩
    rw [equality]
    constructor <;> simp

theorem lowerRadicalInvariant_binary (degree : ℕ) (polynomial : HomogeneousPoly degree) :
    polynomial ∈ (lowerRadicalLatticeRep degree).ρ.invariants ↔
      ∃ binary : Binary.HomogeneousPoly degree, binaryHomogeneousLift degree binary = polynomial := by
  rw [lowerRadicalInvariant_derivative]
  constructor
  · exact homogeneous_pderiv_third_zero_exists_binary polynomial
  · rintro ⟨binary, rfl⟩
    exact binaryPolynomialLift_pderiv_third binary.val

end TernaryPeriodPolynomials.SphericalDetection.Helpers
