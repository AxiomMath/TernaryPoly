module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.Radical.Polynomial
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous Adelic Matrix MvPolynomial

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

def radicalInfinitesimal (degree : ℕ) (positive : 0 < degree) (index : Fin 2) :
    Module.End ℂ (HomogeneousPoly degree) where
  toFun polynomial := ⟨X index.succ * pderiv 0 polynomial.val, by
    have derivativeHomogeneous := MvPolynomial.IsHomogeneous.pderiv
      (φ := polynomial.val) (i := (0 : Fin 3)) polynomial.property
    have homogeneous := (isHomogeneous_X ℂ index.succ).mul derivativeHomogeneous
    have equality : 1 + (degree - 1) = degree := by omega
    exact Eq.mp (congrArg (fun order =>
      (X index.succ * pderiv 0 polynomial.val : Poly).IsHomogeneous order) equality)
      homogeneous⟩
  map_add' first second := by
    apply Subtype.ext
    simp [map_add, mul_add]
  map_smul' scalar polynomial := by
    apply Subtype.ext
    change X index.succ * pderiv 0 (scalar • polynomial.val) =
      scalar • (X index.succ * pderiv 0 polynomial.val)
    rw [Derivation.map_smul, mul_smul_comm]

def radicalKoszulDifferentialZero (degree : ℕ) (positive : 0 < degree) :
    HomogeneousPoly degree →ₗ[ℂ] HomogeneousPoly degree × HomogeneousPoly degree :=
  (radicalInfinitesimal degree positive 0).prod (radicalInfinitesimal degree positive 1)

def radicalKoszulDifferentialOne (degree : ℕ) (positive : 0 < degree) :
    (HomogeneousPoly degree × HomogeneousPoly degree) →ₗ[ℂ] HomogeneousPoly degree :=
  ((radicalInfinitesimal degree positive 0).comp (LinearMap.snd ℂ _ _)) -
    ((radicalInfinitesimal degree positive 1).comp (LinearMap.fst ℂ _ _))

def radicalKoszulProjection (degree : ℕ) :
    (HomogeneousPoly degree × HomogeneousPoly degree) →ₗ[ℂ] HomogeneousPoly (degree + 1) where
  toFun pair := ⟨X 1 * pair.2.val - X 2 * pair.1.val, by
    have equality : 1 + degree = degree + 1 := by omega
    exact equality ▸ ((isHomogeneous_X ℂ (1 : Fin 3)).mul pair.2.property).sub
      ((isHomogeneous_X ℂ (2 : Fin 3)).mul pair.1.property)⟩
  map_add' first second := by
    apply Subtype.ext
    change X 1 * (first.2.val + second.2.val) - X 2 * (first.1.val + second.1.val) =
      (X 1 * first.2.val - X 2 * first.1.val) +
        (X 1 * second.2.val - X 2 * second.1.val)
    ring
  map_smul' scalar pair := by
    apply Subtype.ext
    change X 1 * (scalar • pair.2.val) - X 2 * (scalar • pair.1.val) =
      scalar • (X 1 * pair.2.val - X 2 * pair.1.val)
    rw [mul_smul_comm, mul_smul_comm, smul_sub]

theorem radicalKoszulProjection_derivative (degree : ℕ) (positive : 0 < degree)
    (pair : HomogeneousPoly degree × HomogeneousPoly degree) :
    pderiv 0 (radicalKoszulProjection degree pair).val =
      (radicalKoszulDifferentialOne degree positive pair).val := by
  change pderiv 0 (X 1 * pair.2.val - X 2 * pair.1.val) =
    X 1 * pderiv 0 pair.2.val - X 2 * pderiv 0 pair.1.val
  simp [map_sub, pderiv_X]

theorem radicalKoszulProjection_differentialZero (degree : ℕ) (positive : 0 < degree)
    (polynomial : HomogeneousPoly degree) :
    radicalKoszulProjection degree (radicalKoszulDifferentialZero degree positive polynomial) =
      0 := by
  apply Subtype.ext
  change X 1 * (X 2 * pderiv 0 polynomial.val) -
    X 2 * (X 1 * pderiv 0 polynomial.val) = 0
  ring

theorem radicalKoszulDifferentialOne_differentialZero (degree : ℕ)
    (positive : 0 < degree) (polynomial : HomogeneousPoly degree) :
    radicalKoszulDifferentialOne degree positive
      (radicalKoszulDifferentialZero degree positive polynomial) = 0 := by
  apply Subtype.ext
  rw [← radicalKoszulProjection_derivative, radicalKoszulProjection_differentialZero]
  exact map_zero _

theorem radicalKoszulProjection_kernel (degree : ℕ) (positive : 0 < degree) :
    (radicalKoszulProjection degree).ker =
      (radicalKoszulDifferentialZero degree positive).range := by
  apply le_antisymm
  · intro pair kernel
    have relation : X 1 * pair.2.val - X 2 * pair.1.val = 0 :=
      congrArg Subtype.val kernel
    obtain ⟨quotient, firstEquality, secondEquality⟩ :=
      polynomial_pair_syzygy pair.1.val pair.2.val relation
    have homogeneous : quotient.IsHomogeneous (degree - 1) := by
      apply homogeneous_of_X_mul degree 1
      exact firstEquality ▸ pair.1.property
    obtain ⟨primitive, derivative⟩ := homogeneous_antiderivative (degree - 1)
      ⟨quotient, homogeneous⟩
    have degreeEquality : degree - 1 + 1 = degree := by omega
    have primitiveHomogeneous : primitive.val.IsHomogeneous degree := by
      exact Eq.mp (congrArg (fun order =>
        (primitive.val : Poly).IsHomogeneous order) degreeEquality) primitive.property
    refine ⟨⟨primitive.val, primitiveHomogeneous⟩, ?_⟩
    apply Prod.ext <;> apply Subtype.ext
    · change X 1 * pderiv 0 primitive.val = pair.1.val
      rw [derivative, firstEquality]
    · change X 2 * pderiv 0 primitive.val = pair.2.val
      rw [derivative, secondEquality]
  · rintro pair ⟨polynomial, rfl⟩
    exact radicalKoszulProjection_differentialZero degree positive polynomial

def radicalKoszulCycles (degree : ℕ) (positive : 0 < degree) :
    Submodule ℂ (HomogeneousPoly degree × HomogeneousPoly degree) :=
  (radicalKoszulDifferentialOne degree positive).ker

instance radicalKoszulCyclesAddCommGroup (degree : ℕ) (positive : 0 < degree) :
    AddCommGroup (radicalKoszulCycles degree positive) :=
  @Submodule.addCommGroup ℂ (HomogeneousPoly degree × HomogeneousPoly degree)
    inferInstance inferInstance inferInstance (radicalKoszulCycles degree positive)

def radicalKoszulCycleProjection (degree : ℕ) (positive : 0 < degree) :
    radicalKoszulCycles degree positive →ₗ[ℂ] radicalDerivativeKernel (degree + 1) :=
  ((radicalKoszulProjection degree).comp (radicalKoszulCycles degree positive).subtype).codRestrict
    (radicalDerivativeKernel (degree + 1)) (by
      intro cycle
      change pderiv 0 (radicalKoszulProjection degree cycle.val).val = 0
      rw [radicalKoszulProjection_derivative]
      exact congrArg Subtype.val cycle.property)

def radicalKoszulBoundaryMap (degree : ℕ) (positive : 0 < degree) :
    HomogeneousPoly degree →ₗ[ℂ] radicalKoszulCycles degree positive :=
  (radicalKoszulDifferentialZero degree positive).codRestrict
    (radicalKoszulCycles degree positive)
    (radicalKoszulDifferentialOne_differentialZero degree positive)

def radicalKoszulBoundaries (degree : ℕ) (positive : 0 < degree) :
    Submodule ℂ (radicalKoszulCycles degree positive) :=
  (radicalKoszulBoundaryMap degree positive).range

abbrev RadicalKoszulH1 (degree : ℕ) (positive : 0 < degree) :=
  @HasQuotient.Quotient (radicalKoszulCycles degree positive)
    (Submodule ℂ (radicalKoszulCycles degree positive))
    (@Submodule.hasQuotient ℂ (radicalKoszulCycles degree positive)
      inferInstance inferInstance inferInstance)
    (radicalKoszulBoundaries degree positive)

theorem radicalKoszulCycleProjection_kernel (degree : ℕ) (positive : 0 < degree) :
    (radicalKoszulCycleProjection degree positive).ker =
      radicalKoszulBoundaries degree positive := by
  apply le_antisymm
  · intro cycle kernel
    have projection : radicalKoszulProjection degree cycle.val = 0 := by
      apply Subtype.ext
      exact congrArg (fun value : radicalDerivativeKernel (degree + 1) => value.val.val) kernel
    have membership : cycle.val ∈ (radicalKoszulProjection degree).ker := projection
    rw [radicalKoszulProjection_kernel degree positive] at membership
    obtain ⟨primitive, equality⟩ := membership
    exact ⟨primitive, Subtype.ext equality⟩
  · rintro cycle ⟨primitive, rfl⟩
    apply Subtype.ext
    exact radicalKoszulProjection_differentialZero degree positive primitive

theorem radicalKoszulCycleProjection_surjective (degree : ℕ) (positive : 0 < degree) :
    Function.Surjective (radicalKoszulCycleProjection degree positive) := by
  intro polynomial
  have homogeneous : polynomial.val.val.IsHomogeneous (degree + 1) := polynomial.val.property
  have derivative : pderiv 0 polynomial.val.val = 0 := polynomial.property
  have firstHomogeneous : (pderiv (1 : Fin 3) polynomial.val.val).IsHomogeneous degree := by
    simpa only [Nat.add_sub_cancel] using MvPolynomial.IsHomogeneous.pderiv
      (i := (1 : Fin 3)) homogeneous
  have secondHomogeneous : (pderiv (2 : Fin 3) polynomial.val.val).IsHomogeneous degree := by
    simpa only [Nat.add_sub_cancel] using MvPolynomial.IsHomogeneous.pderiv
      (i := (2 : Fin 3)) homogeneous
  let normalization : ℂ := ((degree + 1 : ℕ) : ℂ)⁻¹
  let pair : HomogeneousPoly degree × HomogeneousPoly degree :=
    (-normalization • ⟨pderiv 2 polynomial.val.val, secondHomogeneous⟩,
      normalization • ⟨pderiv 1 polynomial.val.val, firstHomogeneous⟩)
  have euler := MvPolynomial.IsHomogeneous.sum_X_mul_pderiv homogeneous
  simp only [Fin.sum_univ_three, derivative, mul_zero, zero_add] at euler
  have scalarEuler : X 1 * pderiv 1 polynomial.val.val + X 2 * pderiv 2 polynomial.val.val =
      ((degree + 1 : ℕ) : ℂ) • polynomial.val.val := by
    simpa only [Nat.cast_smul_eq_nsmul] using euler
  have nonzero : ((degree + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero degree
  have projection : radicalKoszulProjection degree pair = polynomial.val := by
    apply Subtype.ext
    change X 1 * (normalization • pderiv 1 polynomial.val.val) -
      X 2 * (-normalization • pderiv 2 polynomial.val.val) = polynomial.val.val
    rw [mul_smul_comm, mul_smul_comm, neg_smul, sub_neg_eq_add,
      ← smul_add, scalarEuler, smul_smul]
    dsimp [normalization]
    rw [inv_mul_cancel₀ nonzero, one_smul]
  have cycle : pair ∈ radicalKoszulCycles degree positive := by
    apply Subtype.ext
    rw [← radicalKoszulProjection_derivative, projection]
    exact derivative
  refine ⟨⟨pair, cycle⟩, ?_⟩
  apply Subtype.ext
  exact projection

def radicalKoszulQuotientKernelEquiv (degree : ℕ) (positive : 0 < degree) :
    RadicalKoszulH1 degree positive ≃ₗ[ℂ]
      (radicalKoszulCycles degree positive ⧸
        (radicalKoszulCycleProjection degree positive).ker) :=
  (radicalKoszulBoundaries degree positive).quotEquivOfEq
    (radicalKoszulCycleProjection degree positive).ker
    (radicalKoszulCycleProjection_kernel degree positive).symm

def radicalKoszulKernelQuotientEquiv (degree : ℕ) (positive : 0 < degree) :
    (radicalKoszulCycles degree positive ⧸
      (radicalKoszulCycleProjection degree positive).ker) ≃ₗ[ℂ]
        radicalDerivativeKernel (degree + 1) :=
  @LinearMap.quotKerEquivOfSurjective ℂ (radicalKoszulCycles degree positive)
    (radicalDerivativeKernel (degree + 1)) inferInstance inferInstance inferInstance
    inferInstance inferInstance (radicalKoszulCycleProjection degree positive)
    (radicalKoszulCycleProjection_surjective degree positive)

def radicalKoszulBinaryEquiv (degree : ℕ) (positive : 0 < degree) :
    RadicalKoszulH1 degree positive ≃ₗ[ℂ] Binary.HomogeneousPoly (degree + 1) :=
  (radicalKoszulQuotientKernelEquiv degree positive).trans
    ((radicalKoszulKernelQuotientEquiv degree positive).trans
      (binaryDerivativeKernelEquiv (degree + 1)).symm)

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
