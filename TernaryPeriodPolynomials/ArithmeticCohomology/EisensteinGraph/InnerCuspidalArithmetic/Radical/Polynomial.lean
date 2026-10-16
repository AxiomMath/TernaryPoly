module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.Binary.Embedding
public import Mathlib.Algebra.MvPolynomial.Division

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous Adelic Matrix MvPolynomial

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

instance homogeneousPolyAddCommGroup (degree : ℕ) : AddCommGroup (HomogeneousPoly degree) :=
  @Submodule.addCommGroup ℂ Poly inferInstance inferInstance inferInstance (HomogeneousPoly degree)

theorem pderiv_zero_coeff_of_positive (polynomial : Poly)
    (derivative : pderiv 0 polynomial = 0) (exponent : Fin 3 →₀ ℕ)
    (positive : 0 < exponent 0) : polynomial.coeff exponent = 0 := by
  have coefficient := congrArg (·.coeff (exponent - Finsupp.single 0 1)) derivative
  rw [coeff_pderiv, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply,
    Finsupp.sub_add_single_one_cancel (Nat.ne_of_gt positive)] at coefficient
  let predecessor : Fin 3 →₀ ℕ := exponent - Finsupp.single 0 1
  have scalar : (predecessor 0 : ℂ) + 1 ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero (predecessor 0)
  exact (mul_eq_zero.mp coefficient).resolve_right scalar

theorem pderiv_zero_notMem_vars (polynomial : Poly)
    (derivative : pderiv 0 polynomial = 0) : (0 : Fin 3) ∉ polynomial.vars := by
  intro membership
  obtain ⟨exponent, support, nonzero⟩ :=
    (MvPolynomial.mem_vars_iff_mem_support 0).mp membership
  have positive : 0 < exponent 0 := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp nonzero)
  exact (MvPolynomial.mem_support_iff.mp support)
    (pderiv_zero_coeff_of_positive polynomial derivative exponent positive)

theorem pderiv_zero_iff_binary (polynomial : Poly) :
    pderiv 0 polynomial = 0 ↔
      ∃ binary : Binary.Poly, binaryPolynomialEmbedding binary = polynomial := by
  constructor
  · intro derivative
    apply exists_rename_eq_of_vars_subset_range polynomial Fin.succ (Fin.succ_injective 2)
    intro index membership
    have nonzero := pderiv_zero_notMem_vars polynomial derivative
    fin_cases index
    · exact (nonzero membership).elim
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · rintro ⟨binary, rfl⟩
    apply pderiv_eq_zero_of_notMem_vars
    intro membership
    obtain ⟨index, _, equality⟩ := mem_vars_rename Fin.succ binary membership
    exact Fin.succ_ne_zero index equality

def radicalDerivativeKernel (degree : ℕ) : Submodule ℂ (HomogeneousPoly degree) :=
  (pderiv (0 : Fin 3)).toLinearMap.ker.comap
    (homogeneousSubmodule (Fin 3) ℂ degree).subtype

theorem binaryHomogeneousEmbedding_range_eq_derivativeKernel (degree : ℕ) :
    LinearMap.range (binaryHomogeneousEmbedding degree) = radicalDerivativeKernel degree := by
  ext polynomial
  constructor
  · rintro ⟨binary, rfl⟩
    exact (pderiv_zero_iff_binary _).mpr ⟨binary.val, rfl⟩
  · intro derivative
    obtain ⟨binary, equality⟩ := (pderiv_zero_iff_binary polynomial.val).mp derivative
    have homogeneous : binary.IsHomogeneous degree := by
      apply (MvPolynomial.IsHomogeneous.rename_isHomogeneous_iff
        (φ := binary) (Fin.succ_injective 2)).mp
      exact equality.symm ▸ polynomial.property
    exact ⟨⟨binary, homogeneous⟩, Subtype.ext equality⟩

def binaryDerivativeKernelEquiv (degree : ℕ) :
    Binary.HomogeneousPoly degree ≃ₗ[ℂ] radicalDerivativeKernel degree :=
  (LinearEquiv.ofInjective (binaryHomogeneousEmbedding degree)
    (binaryHomogeneousEmbedding_injective degree)).trans
      (LinearEquiv.ofEq _ _ (binaryHomogeneousEmbedding_range_eq_derivativeKernel degree))

theorem homogeneous_antiderivative (degree : ℕ) (polynomial : HomogeneousPoly degree) :
    ∃ primitive : HomogeneousPoly (degree + 1), pderiv 0 primitive.val = polynomial.val := by
  have result : ∀ (value : Poly), value.IsHomogeneous degree →
      ∃ primitive : Poly, primitive.IsHomogeneous (degree + 1) ∧
        pderiv 0 primitive = value := by
    intro value homogeneous
    induction homogeneous using MvPolynomial.IsWeightedHomogeneous.induction_on with
    | zero => exact ⟨0, isHomogeneous_zero _ _ _, map_zero _⟩
    | add first second firstHomogeneous secondHomogeneous firstPrimitive secondPrimitive =>
      obtain ⟨primitiveOne, homogeneousOne, derivativeOne⟩ := firstPrimitive
      obtain ⟨primitiveTwo, homogeneousTwo, derivativeTwo⟩ := secondPrimitive
      exact ⟨primitiveOne + primitiveTwo, homogeneousOne.add homogeneousTwo,
        by rw [map_add, derivativeOne, derivativeTwo]⟩
    | monomial exponent scalar homogeneous =>
      refine ⟨monomial (exponent + Finsupp.single 0 1)
        (scalar / ((exponent 0 : ℂ) + 1)), ?_, ?_⟩
      · apply isHomogeneous_monomial
        have exponentDegree : Finsupp.degree exponent = degree := by
          simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using homogeneous
        simp [map_add, exponentDegree]
      · rw [pderiv_monomial]
        have exponentIdentity : exponent + Finsupp.single 0 1 - Finsupp.single 0 1 =
            exponent := by
          ext index
          simp
        rw [exponentIdentity]
        congr 1
        simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.cast_add, Nat.cast_one]
        have nonzero : (exponent 0 : ℂ) + 1 ≠ 0 := by
          exact_mod_cast Nat.succ_ne_zero (exponent 0)
        exact div_mul_cancel₀ scalar nonzero
  obtain ⟨primitive, homogeneous, derivative⟩ := result polynomial.val polynomial.property
  exact ⟨⟨primitive, homogeneous⟩, derivative⟩

theorem homogeneous_of_X_mul (degree : ℕ) (index : Fin 3) (polynomial : Poly)
    (homogeneous : (X index * polynomial).IsHomogeneous degree) :
    polynomial.IsHomogeneous (degree - 1) := by
  intro exponent nonzero
  have coefficient : (X index * polynomial).coeff (Finsupp.single index 1 + exponent) ≠ 0 := by
    simpa only [coeff_X_mul] using nonzero
  have total := homogeneous coefficient
  have exponentDegree : 1 + Finsupp.degree exponent = degree := by
    simpa only [← Finsupp.degree_eq_weight_one, Pi.one_def,
      map_add, Finsupp.degree_single] using total
  have equality : Finsupp.degree exponent = degree - 1 := by omega
  simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using equality

theorem polynomial_pair_syzygy (first second : Poly)
    (relation : X 1 * second - X 2 * first = 0) :
    ∃ quotient : Poly, first = X 1 * quotient ∧ second = X 2 * quotient := by
  have equality : X 1 * second = X 2 * first := sub_eq_zero.mp relation
  have divides : (X (1 : Fin 3) : Poly) ∣ X 2 * first := by
    rw [← equality]
    exact dvd_mul_right _ _
  have firstDivides : (X (1 : Fin 3) : Poly) ∣ first := by
    rcases ((MvPolynomial.X_prime (R := ℂ) (i := (1 : Fin 3))).dvd_or_dvd divides) with
      other | desired
    · have impossible := MvPolynomial.X_dvd_X.mp other
      exact (by decide : (1 : Fin 3) ≠ 2) impossible |>.elim
    · exact desired
  obtain ⟨quotient, firstEquality⟩ := firstDivides
  refine ⟨quotient, firstEquality, ?_⟩
  apply mul_left_cancel₀ (MvPolynomial.X_ne_zero (1 : Fin 3))
  rw [equality, firstEquality]
  ring

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
