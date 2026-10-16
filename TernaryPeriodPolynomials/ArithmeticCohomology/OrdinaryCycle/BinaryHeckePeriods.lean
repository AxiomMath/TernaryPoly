module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BinaryHeckeComparison
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.SymbolEquiv
public import TernaryPeriodPolynomials.PeriodPolynomial.RationalHecke.Period

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBinaryHecke
open OrdinaryResidueSymbol

/-- The genuine ternary and binary period operators have the exact same left-convention p-times-plus-identity relation. -/
theorem period_prime (n p : ℕ) [Fact p.Prime] (q : OrdinaryResiduePeriod.periodSpace (n+1)) :
    OrdinaryResiduePeriod.periodHecke n (OrdinaryHeckeCosets.primeDiagonal p) q =
      (p : ℚ) • BinaryRationalHecke.periodHecke (n+1) (BinaryRationalHeckePrime.primeDiagonal p) q + q := by
  obtain ⟨F,rfl⟩ := (OrdinaryResiduePeriod.periodEquiv n).surjective q
  rw [OrdinaryResiduePeriod.periodHecke_equiv]
  have hcoord (G : OrdinaryFullCoefficient.ResidueHom n (-1)) :
      BinaryModularSymbol.periodEquiv (n+1) (toBinaryHom n G) = OrdinaryResiduePeriod.periodEquiv n G :=
    BinaryModularSymbol.periodEvaluation_restriction n G
  have he := congrArg (BinaryModularSymbol.periodEquiv (n+1)) (toBinaryHom_prime n p F)
  rw [map_add,map_smul,hcoord,←BinaryRationalHecke.periodHecke_evaluation,hcoord] at he
  exact he

/-- The literal liftable-period subspace is stable under the actual binary prime correspondence. -/
theorem liftable_period_prime_stable (n p : ℕ) [Fact p.Prime]
    (q : OrdinaryResiduePeriod.periodSpace (n+1)) (hq : q ∈ OrdinaryResiduePeriod.liftable n) :
    BinaryRationalHecke.periodHecke (n+1) (BinaryRationalHeckePrime.primeDiagonal p) q ∈
      OrdinaryResiduePeriod.liftable n := by
  have hT := OrdinaryResiduePeriod.liftable_stable n (OrdinaryHeckeCosets.primeDiagonal p) q hq
  rw [period_prime] at hT
  have hz : q + (-1 : ℚ) • q = 0 := by
    calc
      _ = ((1 : ℚ) + (-1)) • q := by rw [add_smul,one_smul]
      _ = 0 := by norm_num
  have hs := (OrdinaryResiduePeriod.liftable n).add_mem hT
    ((OrdinaryResiduePeriod.liftable n).smul_mem (-1 : ℚ) hq)
  rw [add_assoc,hz,add_zero] at hs
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hi := (OrdinaryResiduePeriod.liftable n).smul_mem (p : ℚ)⁻¹ hs
  simpa only [smul_smul,inv_mul_cancel₀ hp,one_smul] using hi

/-- Every actual binary prime translate of a liftable period satisfies the existing extreme-coordinate obstruction. -/
theorem binary_prime_liftable_extreme (n p : ℕ) [Fact p.Prime]
    (q : OrdinaryResiduePeriod.periodSpace (n+1)) (hq : q ∈ OrdinaryResiduePeriod.liftable n)
    (m : Fin 1 →₀ ℕ) :
    (BinaryRationalHecke.periodHecke (n+1) (BinaryRationalHeckePrime.primeDiagonal p) q).val.val.coeff (Finsupp.cons 1 m) = 0 :=
  OrdinaryResiduePeriod.liftable_extreme n _ (liftable_period_prime_stable n p q hq) m

end TernaryPoly.OrdinaryBinaryHecke
