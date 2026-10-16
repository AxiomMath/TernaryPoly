module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Hecke.ArithmeticDeterminant
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Hecke.CosetsNormalization

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryHeckeCosets
open Matrix PolynomialGLAction ModThreeGoodAction OrdinaryHeckeArithmetic OrdinaryHeckeTransfer

/-- The literal rational prime matrix, with first diagonal entry p. -/
def primeDiagonal (p : ℕ) [Fact p.Prime] : GL3 :=
  ⟨!![(p : ℚ),0,0;0,1,0;0,0,1],!![(p : ℚ)⁻¹,0,0;0,1,0;0,0,1],by
    have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_three,hp],by
    have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_three,hp]⟩

/-- Literal conjugation divides precisely the two off-diagonal entries of the first row by p. -/
theorem primeDiagonal_conjugate (p : ℕ) [Fact p.Prime] (k : IntegralGL) :
    ((primeDiagonal p)⁻¹*integral k*primeDiagonal p).val=
      !![(k.val 0 0 : ℚ),(k.val 0 1 : ℚ)/p,(k.val 0 2 : ℚ)/p;
        p*(k.val 1 0 : ℚ),(k.val 1 1 : ℚ),(k.val 1 2 : ℚ);
        p*(k.val 2 0 : ℚ),(k.val 2 1 : ℚ),(k.val 2 2 : ℚ)] := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [primeDiagonal,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_three,div_eq_mul_inv,hp,mul_comm,OrdinaryFullAction.integral] <;> rfl

/-- The actual prime intersection is exactly the first-row congruence stabilizer. -/
theorem mem_primeIntersection_iff (p : ℕ) [Fact p.Prime] (k : IntegralGL) :
    integralEquiv k ∈ intersection Gamma (primeDiagonal p) ↔
      (p : ℤ) ∣ k.val 0 1 ∧ (p : ℤ) ∣ k.val 0 2 := by
  rw [mem_intersection]
  change (primeDiagonal p)⁻¹*integral k*primeDiagonal p ∈ Gamma ↔ _
  rw [conjugate_mem_iff_integralEntries,primeDiagonal_conjugate]
  constructor
  · intro h
    exact ⟨(integer_div_iff p (Fact.out : p.Prime).ne_zero _).mp (h 0 1),
      (integer_div_iff p (Fact.out : p.Prime).ne_zero _).mp (h 0 2)⟩
  · rintro ⟨h1,h2⟩
    have h1' := (integer_div_iff p (Fact.out : p.Prime).ne_zero _).mpr h1
    have h2' := (integer_div_iff p (Fact.out : p.Prime).ne_zero _).mpr h2
    intro i j
    fin_cases i <;> fin_cases j
    · exact ⟨k.val 0 0,rfl⟩
    · exact h1'
    · exact h2'
    · exact ⟨(p : ℤ)*k.val 1 0,by push_cast; rfl⟩
    · exact ⟨k.val 1 1,rfl⟩
    · exact ⟨k.val 1 2,rfl⟩
    · exact ⟨(p : ℤ)*k.val 2 0,by push_cast; rfl⟩
    · exact ⟨k.val 2 1,rfl⟩
    · exact ⟨k.val 2 2,rfl⟩

/-- The same exact intersection criterion in the finite congruence quotient. -/
theorem mem_primeIntersection_iff_mod (p : ℕ) [Fact p.Prime] (k : IntegralGL) :
    integralEquiv k ∈ intersection Gamma (primeDiagonal p) ↔
      (k.val 0 1 : ZMod p)=0 ∧ (k.val 0 2 : ZMod p)=0 := by
  rw [mem_primeIntersection_iff, ZMod.intCast_zmod_eq_zero_iff_dvd,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

end TernaryPoly.OrdinaryHeckeCosets
