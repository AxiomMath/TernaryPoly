module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Hecke.CosetsLifts

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryHeckeCosets
open Matrix PolynomialGLAction ModThreeGoodAction OrdinaryHeckeArithmetic OrdinaryHeckeTransfer

/-- The integral column permutation which converts the transfer representative into lower triangular form. -/
def chartPermutation {p : ℕ} (i : PrimeIndex p) : IntegralGL := by
  rcases i with ⟨b,c⟩|a|u
  · exact ⟨!![0,0,1;1,0,0;0,1,0],!![0,1,0;0,0,1;1,0,0],by decide +kernel,by decide +kernel⟩
  · exact ⟨!![0,1,0;1,0,0;0,0,1],!![0,1,0;1,0,0;0,0,1],by decide +kernel,by decide +kernel⟩
  · exact 1

/-- Actual rational representatives, defined by exact integral left/right factors of the prime matrix. -/
def primeRepresentative (p : ℕ) [Fact p.Prime] (i : PrimeIndex p) : GL3 :=
  (integral (chartLift i))⁻¹*primeDiagonal p*integral (chartPermutation i)

/-- Their literal matrices are exactly the three lower triangular families. -/
theorem primeRepresentative_matrix (p : ℕ) [Fact p.Prime] (i : PrimeIndex p) :
    (primeRepresentative p i).val=match i with
      | .inl (b,c) => !![1,0,0;0,1,0;(b.val : ℚ),(c.val : ℚ),(p : ℚ)]
      | .inr (.inl a) => !![1,0,0;(a.val : ℚ),(p : ℚ),0;0,0,1]
      | .inr (.inr _) => !![(p : ℚ),0,0;0,1,0;0,0,1] := by
  change matrixCast (chartInverse i)*(primeDiagonal p).val*matrixCast (chartPermutation i).val=_
  rcases i with ⟨b,c⟩|a|u <;> ext j k <;> fin_cases j <;> fin_cases k <;>
    simp [chartInverse,chartPermutation,primeDiagonal,Matrix.mul_apply,Fin.sum_univ_three]


/-- Exact normalization for the inverse-right-coset convention in the generic Hecke sum. -/
theorem inverse_coset_normalization (p : ℕ) [Fact p.Prime] (i : PrimeIndex p) :
    (integralEquiv (chartLift i)).val⁻¹*primeDiagonal p=
      primeRepresentative p i*(integral (chartPermutation i))⁻¹ := by
  change (integral (chartLift i))⁻¹*primeDiagonal p=
    ((integral (chartLift i))⁻¹*primeDiagonal p*integral (chartPermutation i))*(integral (chartPermutation i))⁻¹
  group

/-- Every literal representative preserves the coordinate plane a=0. -/
theorem primeRepresentative_firstRow (p : ℕ) [Fact p.Prime] (i : PrimeIndex p) :
    (primeRepresentative p i).val 0 1=0 ∧ (primeRepresentative p i).val 0 2=0 := by
  rw [primeRepresentative_matrix]
  rcases i with ⟨b,c⟩|a|u <;> exact ⟨rfl,rfl⟩

/-- Each family belongs to the actual Gamma–prime–Gamma double coset, with explicit factors. -/
theorem primeRepresentative_doubleCoset (p : ℕ) [Fact p.Prime] (i : PrimeIndex p) :
    ∃ a b : Gamma, primeRepresentative p i=a.val*primeDiagonal p*b.val :=
  ⟨(integralEquiv (chartLift i))⁻¹,integralEquiv (chartPermutation i),rfl⟩

end TernaryPoly.OrdinaryHeckeCosets
