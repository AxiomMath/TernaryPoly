module

public import TernaryPeriodPolynomials.PeriodPolynomial.RationalHecke.Arithmetic.Determinant
public import TernaryPeriodPolynomials.PeriodPolynomial.RationalHecke.Prime.Normalization

@[expose] public section


noncomputable section
namespace TernaryPoly.BinaryRationalHeckePrime
open BinaryModularSymbol (GL2)
open Matrix RankTwoAugmentedFrames BinaryRationalHeckeArithmetic OrdinaryHeckeTransfer

/-- The literal rational prime matrix. -/
def primeDiagonal (p : ℕ) [Fact p.Prime] : GL2 :=
  ⟨!![(p : ℚ),0;0,1],!![(p : ℚ)⁻¹,0;0,1],by
    have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two,hp],by
    have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two,hp]⟩

theorem primeDiagonal_conjugate (p : ℕ) [Fact p.Prime] (k : IntegralGL) :
    ((primeDiagonal p)⁻¹*integral k*primeDiagonal p).val=
      !![(k.val 0 0 : ℚ),(k.val 0 1 : ℚ)/p;p*(k.val 1 0 : ℚ),(k.val 1 1 : ℚ)] := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [primeDiagonal,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,
      div_eq_mul_inv,hp,mul_comm,BinaryModularSymbol.integral]

theorem mem_primeIntersection_iff (p : ℕ) [Fact p.Prime] (k : IntegralGL) :
    integralEquiv k ∈ intersection Gamma (primeDiagonal p) ↔ (p : ℤ) ∣ k.val 0 1 := by
  rw [mem_intersection]
  change (primeDiagonal p)⁻¹*integral k*primeDiagonal p ∈ Gamma ↔ _
  rw [conjugate_mem_iff_integralEntries,primeDiagonal_conjugate]
  constructor
  · intro h
    exact (integer_div_iff p (Fact.out : p.Prime).ne_zero _).mp (h 0 1)
  · intro h1
    have h1' := (integer_div_iff p (Fact.out : p.Prime).ne_zero _).mpr h1
    intro i j
    fin_cases i <;> fin_cases j
    · exact ⟨k.val 0 0,rfl⟩
    · exact h1'
    · exact ⟨(p : ℤ)*k.val 1 0,by push_cast; rfl⟩
    · exact ⟨k.val 1 1,rfl⟩

theorem mem_primeIntersection_iff_mod (p : ℕ) [Fact p.Prime] (k : IntegralGL) :
    integralEquiv k ∈ intersection Gamma (primeDiagonal p) ↔ (k.val 0 1 : ZMod p)=0 := by
  rw [mem_primeIntersection_iff,ZMod.intCast_zmod_eq_zero_iff_dvd]

end TernaryPoly.BinaryRationalHeckePrime
