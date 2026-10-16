module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Hecke.ArithmeticDenominators

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryHeckeArithmetic
open Matrix PolynomialGLAction ModThreeGoodAction OrdinaryHeckeTransfer

/-- Extending scalars commutes with an integer scalar multiple of a matrix. -/
theorem matrixCast_zsmul (z : ℤ) (M : Matrix (Fin 3) (Fin 3) ℤ) :
    matrixCast (z • M)=(z : ℚ) • matrixCast M := by
  ext i j
  change ((z*(M i j) : ℤ) : ℚ)=(z : ℚ)*(M i j : ℚ)
  exact Int.cast_mul z (M i j)

/-- The product of two denominator bounds clears every conjugated congruence element. -/
theorem conjugate_integralEntries (g : GL3) (a b : ℕ)
    (A B : Matrix (Fin 3) (Fin 3) ℤ)
    (ha : matrixCast A=(a : ℚ) • g.val)
    (hb : matrixCast B=(b : ℚ) • (g⁻¹).val)
    (k : IntegralGL) (hk : congruenceMap (a*b) k=1) :
    IntegralEntries (g⁻¹*integral k*g).val := by
  obtain ⟨Z,hZ⟩ := congruence_matrix (a*b) k hk
  apply (integralEntries_iff_matrix _).mpr
  refine ⟨1+B*Z*A,?_⟩
  change matrixCast (1+B*Z*A)=(g⁻¹).val*matrixCast k.val*g.val
  rw [hZ,map_add,map_one,map_mul,map_mul,hb,ha,map_add,map_one,matrixCast_zsmul]
  simp only [Nat.cast_mul,Int.cast_mul,Int.cast_natCast,Matrix.add_mul,Matrix.mul_add,Matrix.mul_one,
    Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  rw [show (g⁻¹).val*g.val=1 from g.inv_val,mul_comm (a : ℚ) (b : ℚ)]

/-- Both a congruence element and its inverse become integral after conjugation. -/
theorem conjugate_mem_Gamma (g : GL3) (a b : ℕ)
    (A B : Matrix (Fin 3) (Fin 3) ℤ)
    (ha : matrixCast A=(a : ℚ) • g.val)
    (hb : matrixCast B=(b : ℚ) • (g⁻¹).val)
    (k : IntegralGL) (hk : congruenceMap (a*b) k=1) :
    g⁻¹*integral k*g ∈ Gamma := by
  apply (mem_Gamma_iff _).mpr
  refine ⟨conjugate_integralEntries g a b A B ha hb k hk,?_⟩
  have hi : congruenceMap (a*b) k⁻¹=1 := by rw [map_inv,hk,inv_one]
  have he := conjugate_integralEntries g a b A B ha hb k⁻¹ hi
  simpa only [_root_.mul_inv_rev,inv_inv,map_inv,mul_assoc] using he

/-- Congruence quotient on the actual rational image of integral GL3. -/
def gammaCongruenceMap (m : ℕ) : Gamma →* GeneralLinearGroup (Fin 3) (ZMod m) :=
  (congruenceMap m).comp integralEquiv.symm.toMonoidHom

/-- The actual intersection contains a congruence kernel with an explicit denominator modulus. -/
theorem congruenceKernel_le_intersection (g : GL3) (a b : ℕ)
    (A B : Matrix (Fin 3) (Fin 3) ℤ)
    (ha : matrixCast A=(a : ℚ) • g.val)
    (hb : matrixCast B=(b : ℚ) • (g⁻¹).val) :
    (gammaCongruenceMap (a*b)).ker ≤ intersection Gamma g := by
  intro k hk
  apply (mem_intersection Gamma g k).mpr
  have hi : integral (integralEquiv.symm k)=k.val :=
    congrArg Subtype.val (integralEquiv.apply_symm_apply k)
  have he := conjugate_mem_Gamma g a b A B ha hb (integralEquiv.symm k) hk
  rwa [hi] at he

/-- Rational GL3 commensurates the actual full integral subgroup. -/
theorem intersection_finiteIndex (g : GL3) : (intersection Gamma g).FiniteIndex := by
  obtain ⟨a,ha,A,hA⟩ := matrix_denominator g.val
  obtain ⟨b,hb,B,hB⟩ := matrix_denominator (g⁻¹).val
  let : NeZero (a*b) := ⟨mul_ne_zero ha hb⟩
  have : (gammaCongruenceMap (a*b)).ker.FiniteIndex := inferInstance
  exact Subgroup.finiteIndex_of_le (congruenceKernel_le_intersection g a b A B hA hB)

end TernaryPoly.OrdinaryHeckeArithmetic
