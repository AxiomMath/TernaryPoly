module

public import TernaryPeriodPolynomials.PeriodPolynomial.RationalHecke.Prime.Lifts

@[expose] public section

noncomputable section
namespace TernaryPoly.BinaryRationalHeckePrime
open BinaryModularSymbol (GL2)
open Matrix RankTwoAugmentedFrames BinaryRationalHeckeArithmetic OrdinaryHeckeTransfer

def chartPermutation {p : ℕ} (i : PrimeIndex p) : IntegralGL := by
  rcases i with a|u
  · exact ⟨!![0,1;1,0],!![0,1;1,0],by decide +kernel,by decide +kernel⟩
  · exact 1

/-- Actual lower triangular representatives of the binary prime Hecke correspondence. -/
def primeRepresentative (p : ℕ) [Fact p.Prime] (i : PrimeIndex p) : GL2 :=
  (integral (chartLift i))⁻¹*primeDiagonal p*integral (chartPermutation i)

theorem primeRepresentative_matrix (p : ℕ) [Fact p.Prime] (i : PrimeIndex p) :
    (primeRepresentative p i).val=match i with
      | .inl a => !![1,0;(a.val : ℚ),(p : ℚ)]
      | .inr _ => !![(p : ℚ),0;0,1] := by
  change matrixCast (chartInverse i)*(primeDiagonal p).val*matrixCast (chartPermutation i).val=_
  rcases i with a|u <;> ext j k <;> fin_cases j <;> fin_cases k <;>
    simp [chartInverse,chartPermutation,primeDiagonal,Matrix.mul_apply,Fin.sum_univ_two]

theorem inverse_coset_normalization (p : ℕ) [Fact p.Prime] (i : PrimeIndex p) :
    (integralEquiv (chartLift i)).val⁻¹*primeDiagonal p=
      primeRepresentative p i*(integral (chartPermutation i))⁻¹ := by
  change (integral (chartLift i))⁻¹*primeDiagonal p=
    ((integral (chartLift i))⁻¹*primeDiagonal p*integral (chartPermutation i))*(integral (chartPermutation i))⁻¹
  group

theorem primeRepresentative_doubleCoset (p : ℕ) [Fact p.Prime] (i : PrimeIndex p) :
    ∃ a b : Gamma, primeRepresentative p i=a.val*primeDiagonal p*b.val :=
  ⟨(integralEquiv (chartLift i))⁻¹,integralEquiv (chartPermutation i),rfl⟩

end TernaryPoly.BinaryRationalHeckePrime
