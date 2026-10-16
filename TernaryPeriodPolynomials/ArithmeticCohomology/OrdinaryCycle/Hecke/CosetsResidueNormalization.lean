module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Hecke.CosetsRepresentatives

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinaryHeckeCosets
open Matrix PolynomialGLAction OrdinaryHeckeArithmetic

/-- First diagonal entry of the representative: one in the two affine families, p at the final chart. -/
def primeLambda (p : ℕ) : PrimeIndex p → ℚ
  | .inl _ => 1
  | .inr (.inl _) => 1
  | .inr (.inr _) => p

theorem primeLambda_ne_zero (p : ℕ) [Fact p.Prime] (i : PrimeIndex p) : primeLambda p i ≠ 0 := by
  rcases i with a|a|u
  · exact one_ne_zero
  · exact one_ne_zero
  · exact Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero

theorem primeRepresentative_firstDiagonal (p : ℕ) [Fact p.Prime] (i : PrimeIndex p) :
    (primeRepresentative p i).val 0 0=primeLambda p i := by
  rw [primeRepresentative_matrix]
  rcases i with a|a|u <;> rfl

/-- All literal representatives have positive determinant p. -/
theorem primeRepresentative_det (p : ℕ) [Fact p.Prime] (i : PrimeIndex p) :
    (primeRepresentative p i).val.det=(p : ℚ) := by
  rw [primeRepresentative_matrix]
  rcases i with ⟨b,c⟩|a|u <;> simp [Matrix.det_fin_three]

/-- An invertible matrix with first row (t,0,0) has inverse first row (t^-1,0,0). -/
theorem inverse_firstRow (g : GL3) (t : ℚ) (ht : t ≠ 0)
    (h0 : g.val 0 0=t) (h1 : g.val 0 1=0) (h2 : g.val 0 2=0) (j : Fin 3) :
    (g⁻¹).val 0 j=if j=0 then t⁻¹ else 0 := by
  have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℚ => M 0 j) g.val_inv
  change ∑ k : Fin 3, g.val 0 k*(g⁻¹).val k j=(1 : Matrix (Fin 3) (Fin 3) ℚ) 0 j at he
  simp only [Fin.sum_univ_three,h0,h1,h2,zero_mul,add_zero] at he
  apply (mul_left_cancel₀ ht)
  rw [he]
  fin_cases j <;> simp [ht,Matrix.one_apply]

/-- Exact inverse-substitution normalization of the first-coordinate pole denominator. -/
theorem primeRepresentative_denominator (p : ℕ) [Fact p.Prime] (i : PrimeIndex p) :
    substitute ((primeRepresentative p i)⁻¹).val (X 0)=
      C ((primeLambda p i)⁻¹)*X 0 := by
  have hi := inverse_firstRow (primeRepresentative p i) (primeLambda p i)
    (primeLambda_ne_zero p i) (primeRepresentative_firstDiagonal p i)
    (primeRepresentative_firstRow p i).1 (primeRepresentative_firstRow p i).2
  rw [substitute_X]
  simp [linearForm,Fin.sum_univ_three,hi]

end TernaryPoly.OrdinaryHeckeCosets
