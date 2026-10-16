module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Hecke.CosetsResidueNormalization
public import TernaryPeriodPolynomials.PeriodPolynomial.RationalHecke.Prime.Formula
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.Parabolic

@[expose] public section


open scoped BigOperators
noncomputable section
namespace TernaryPoly.OrdinaryBinaryHecke
open OrdinaryResidueParabolic

/-- The actual binary Levi block in each of the three lower-triangular ternary families. -/
def primeLevi (p : ℕ) [Fact p.Prime] : OrdinaryHeckeCosets.PrimeIndex p → BinaryModularSymbol.GL2
  | .inl (_,c) => BinaryRationalHeckePrime.primeRepresentative p (.inl c)
  | .inr (.inl _) => BinaryRationalHeckePrime.primeRepresentative p (.inr ())
  | .inr (.inr _) => 1

def primeNormalUnit (p : ℕ) [Fact p.Prime] : OrdinaryHeckeCosets.PrimeIndex p → ℚˣ
  | .inl _ => 1
  | .inr (.inl _) => 1
  | .inr (.inr _) => Units.mk0 (p : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

def primeShear (p : ℕ) : OrdinaryHeckeCosets.PrimeIndex p → Fin 2 → ℚ
  | .inl (b,_) => ![0,(b.val : ℚ)]
  | .inr (.inl a) => ![(a.val : ℚ),0]
  | .inr (.inr _) => 0

/-- The exact matrices, including all normal scalars and lower-left entries, agree with the block decomposition. -/
theorem prime_block (p : ℕ) [Fact p.Prime] (i : OrdinaryHeckeCosets.PrimeIndex p) :
    (OrdinaryHeckeCosets.primeRepresentative p i).val =
      blockMatrix (primeNormalUnit p i) (primeShear p i) (primeLevi p i) := by
  rw [OrdinaryHeckeCosets.primeRepresentative_matrix]
  rcases i with ⟨b,c⟩ | a | u
  · simp only [primeLevi,primeNormalUnit,primeShear,blockMatrix,
      BinaryRationalHeckePrime.primeRepresentative_matrix]
    rfl
  · simp only [primeLevi,primeNormalUnit,primeShear,blockMatrix,
      BinaryRationalHeckePrime.primeRepresentative_matrix]
    rfl
  · simp [primeLevi,primeNormalUnit,primeShear,blockMatrix]
    rfl

/-- The p² and p families repeat each binary representative exactly p times; the last term has identity Levi. -/
theorem sum_primeLevi {E : Type*} [AddCommGroup E] [Module ℚ E]
    (p : ℕ) [Fact p.Prime] (f : BinaryModularSymbol.GL2 → E) :
    (∑ i : OrdinaryHeckeCosets.PrimeIndex p, f (primeLevi p i)) =
      (p : ℚ) • (∑ j : BinaryRationalHeckePrime.PrimeIndex p,
        f (BinaryRationalHeckePrime.primeRepresentative p j)) + f 1 := by
  simp [OrdinaryHeckeCosets.PrimeIndex,BinaryRationalHeckePrime.PrimeIndex,primeLevi,
    Fintype.sum_sum_type,Fintype.sum_prod_type,Nat.cast_smul_eq_nsmul,smul_add,add_assoc]

end TernaryPoly.OrdinaryBinaryHecke
