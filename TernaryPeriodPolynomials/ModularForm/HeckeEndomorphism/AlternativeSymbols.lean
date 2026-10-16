module

public import TernaryPeriodPolynomials.PeriodPolynomial.RationalHecke.Prime.Formula

@[expose] public section


noncomputable section
open Matrix
namespace TernaryPoly.BinaryCuspHeckeEndomorphism
open BinaryModularSymbol BinaryRationalHeckePrime

variable {E : Type*} [AddCommGroup E] [Module ℚ E]

theorem homAction_integral_fixed (ρ : Representation ℚ GL2 E) (F : Hom ρ)
    (g : RankTwoAugmentedFrames.IntegralGL) : homAction ρ (integral g) F.val = F.val :=
  (homAction_fixed_iff ρ (integral g) F.val).mpr (F.property g)

/-- Simultaneous integral conjugation of every representative preserves the actual Hom transfer sum. -/
theorem rationalHecke_prime_conjugate (p : ℕ) [Fact p.Prime] (ρ : Representation ℚ GL2 E)
    (F : Hom ρ) (g : RankTwoAugmentedFrames.IntegralGL) :
    (BinaryRationalHecke.rationalHecke (primeDiagonal p) ρ F).val =
      ∑ i : PrimeIndex p, homAction ρ (integral g * primeRepresentative p i * integral g⁻¹) F.val := by
  simp only [map_mul,Module.End.mul_apply,homAction_integral_fixed]
  rw [←map_sum,←BinaryRationalHeckePrime.rationalHecke_prime,homAction_integral_fixed]

/-- The integral rotation identifying lower representatives with adjugates of the standard upper ones. -/
def rotation : RankTwoAugmentedFrames.IntegralGL :=
  ⟨!![0,-1;1,0],!![0,1;-1,0],by decide +kernel,by decide +kernel⟩

/-- The actual adjugate representatives, defined by integral conjugation of transfer representatives. -/
def adjugateRepresentative (p : ℕ) [Fact p.Prime] (i : PrimeIndex p) : GL2 :=
  integral rotation * primeRepresentative p i * integral rotation⁻¹

@[simp] theorem adjugateRepresentative_matrix (p : ℕ) [Fact p.Prime] (i : PrimeIndex p) :
    (adjugateRepresentative p i).val = match i with
      | .inl b => !![(p : ℚ),-(b.val : ℚ);0,1]
      | .inr _ => !![1,0;0,(p : ℚ)] := by
  change (integral rotation).val * (primeRepresentative p i).val * (integral rotation⁻¹).val = _
  rw [primeRepresentative_matrix]
  cases i <;> ext j k <;> fin_cases j <;> fin_cases k <;>
    simp [integral,rotation,Matrix.mul_apply,Fin.sum_univ_two]

/-- The exact actual binary Hom Hecke formula using adjugates of the cusp upper representatives. -/
theorem rationalHecke_prime_adjugate (p : ℕ) [Fact p.Prime] (ρ : Representation ℚ GL2 E) (F : Hom ρ) :
    (BinaryRationalHecke.rationalHecke (primeDiagonal p) ρ F).val =
      ∑ i : PrimeIndex p, homAction ρ (adjugateRepresentative p i) F.val :=
  rationalHecke_prime_conjugate p ρ F rotation

end TernaryPoly.BinaryCuspHeckeEndomorphism
