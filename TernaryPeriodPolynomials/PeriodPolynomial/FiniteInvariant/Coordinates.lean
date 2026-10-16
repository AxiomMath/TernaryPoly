module

public import TernaryPeriodPolynomials.PeriodPolynomial.FiniteInvariant.Operators

@[expose] public section


open MvPolynomial Matrix
noncomputable section
namespace TernaryPoly.BinaryFiniteInvariant
open BinaryHomogeneous

instance homogeneous_finite (d : ℕ) : FiniteDimensional ℚ (H d) :=
  FiniteDimensional.of_injective (coefficientEquiv ℚ d).toLinearMap (coefficientEquiv ℚ d).injective

/-- The literal monomial with bounded first-coordinate exponent. -/
def monomialVector (d : ℕ) (i : Fin (d+1)) : H d := polynomial ℚ d (Pi.single i 1)

theorem monomialVector_coe (d : ℕ) (i : Fin (d+1)) :
    (monomialVector d i).val = monomial (exponent d i) 1 := by
  classical
  simp [monomialVector,polynomial,Pi.single_apply,apply_ite]

theorem monomialVector_powers (d : ℕ) (i : Fin (d+1)) :
    (monomialVector d i).val = (X 0)^i.val * (X 1)^(d-i.val) := by
  rw [monomialVector_coe,exponent,monomial_add_single,←X_pow_eq_monomial]

@[simp] theorem coordinates_monomialVector (d : ℕ) (i : Fin (d+1)) :
    coordinates ℚ d (monomialVector d i) = Pi.single i 1 := coordinates_polynomial ℚ d _

/-- Trace in the actual bounded coefficient basis. -/
theorem trace_coordinates (d : ℕ) (f : Module.End ℚ (H d)) :
    LinearMap.trace ℚ (H d) f = ∑ i : Fin (d+1), coordinates ℚ d (f (monomialVector d i)) i := by
  rw [←LinearMap.trace_conj' f (coefficientEquiv ℚ d),
    LinearMap.trace_eq_matrix_trace ℚ (Pi.basisFun ℚ (Fin (d+1)))]
  simp [Matrix.trace,LinearEquiv.conj_apply,monomialVector,
    coefficientEquiv]

/-- Swap reverses the literal bounded monomial basis. -/
theorem swap_monomialVector (d : ℕ) (i : Fin (d+1)) : swap d (monomialVector d i) = monomialVector d i.rev := by
  apply Subtype.ext
  rw [swap_coe,monomialVector_powers,monomialVector_powers,map_mul,map_pow,map_pow]
  simp only [bind₁_X_right,Matrix.cons_val_zero,Matrix.cons_val_one]
  have hir : i.rev.val = d-i.val := by rw [Fin.val_rev]; omega
  rw [hir]
  have hi : d-(d-i.val)=i.val := Nat.sub_sub_self (Nat.le_of_lt_succ i.isLt)
  rw [hi,mul_comm]

/-- First-coordinate sign is diagonal in the literal bounded monomial basis. -/
theorem negateFirst_monomialVector (d : ℕ) (i : Fin (d+1)) :
    negateFirst d (monomialVector d i) = (-1 : ℚ)^i.val • monomialVector d i := by
  apply Subtype.ext
  rw [negateFirst_coe,Submodule.coe_smul,monomialVector_powers]
  simp only [map_mul,map_pow,bind₁_X_right,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [neg_pow]
  simp only [Algebra.smul_def,MvPolynomial.algebraMap_eq,map_pow,map_neg,map_one]
  ring

end TernaryPoly.BinaryFiniteInvariant
