module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BinaryHeckeTerm
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BinaryHeckeRepresentatives
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Hecke.CosetsTransfer

@[expose] public section


open scoped BigOperators
noncomputable section
namespace TernaryPoly.OrdinaryBinaryHecke
open OrdinaryPlaneEdge OrdinaryResidueParabolic OrdinaryResidueSymbol SinglePole

/-- The existing genuine ternary Hom operator has exactly the lower-triangular sum. -/
theorem ternary_rationalHecke_prime {E : Type*} [AddCommGroup E] [Module ℚ E]
    (p : ℕ) [Fact p.Prime] (ρ : Representation ℚ OrdinaryFullAction.GL3 E)
    (F : OrdinaryFullCoefficient.Hom ρ) :
    (OrdinaryHomHecke.rationalHecke (OrdinaryHeckeCosets.primeDiagonal p) ρ F).val =
      ∑ i : OrdinaryHeckeCosets.PrimeIndex p,
        OrdinaryHomHecke.linearAction ρ (OrdinaryHeckeCosets.primeRepresentative p i) F.val :=
  OrdinaryHeckeCosets.hecke_prime_apply p (OrdinaryHomHecke.linearRep ρ) (OrdinaryHomHecke.homEquiv ρ F)

/-- In the actual left coefficient-and-cycle convention the ternary prime operator restricts to p times binary Hecke plus identity. -/
theorem toBinaryHom_prime (n p : ℕ) [Fact p.Prime] (F : OrdinaryFullCoefficient.ResidueHom n (-1)) :
    toBinaryHom n (OrdinaryHomHecke.rationalHecke (OrdinaryHeckeCosets.primeDiagonal p)
      (residueAction n (-1)) F) =
    (p : ℚ) • BinaryRationalHecke.rationalHecke (BinaryRationalHeckePrime.primeDiagonal p)
      (BinaryModularSymbolCoefficients.homogeneousAction (n+1) (-1)) (toBinaryHom n F) + toBinaryHom n F := by
  apply Subtype.ext
  apply LinearMap.ext
  intro c
  change zeroCoordinate n ((OrdinaryHomHecke.rationalHecke (OrdinaryHeckeCosets.primeDiagonal p)
    (residueAction n (-1)) F).val (binaryCone c)) = _
  rw [ternary_rationalHecke_prime,LinearMap.sum_apply,map_sum]
  have ht (i : OrdinaryHeckeCosets.PrimeIndex p) :=
    parabolic_term n F (OrdinaryHeckeCosets.primeRepresentative p i) (primeNormalUnit p i)
      (primeShear p i) (primeLevi p i) (prime_block p i) c
  simp_rw [ht]
  rw [sum_primeLevi p (fun C => BinaryModularSymbol.homAction
    (BinaryModularSymbolCoefficients.homogeneousAction (n+1) (-1)) C (toBinaryHom n F).val c)]
  have hb := congrArg (fun f : BinaryModularSymbol.St →ₗ[ℚ] SinglePoleCoordinate.BinaryV (n+1) => f c)
    (BinaryRationalHeckePrime.rationalHecke_prime p
      (BinaryModularSymbolCoefficients.homogeneousAction (n+1) (-1)) (toBinaryHom n F))
  simp only [LinearMap.sum_apply] at hb
  rw [←hb]
  simp only [map_one,Module.End.one_apply]
  rfl

/-- The actual binary Hom image of liftable ternary residue functionals. -/
def liftableSymbols (n : ℕ) : Submodule ℚ (BinaryModularSymbol.PeriodHom (n+1)) :=
  (OrdinaryFullCoefficient.liftableResidueHoms n (-1)).map (toBinaryHom n)

/-- Genuine liftable symbols are stable under the actual binary prime Hecke operator. -/
theorem liftableSymbols_prime_stable (n p : ℕ) [Fact p.Prime]
    (f : BinaryModularSymbol.PeriodHom (n+1)) (hf : f ∈ liftableSymbols n) :
    BinaryRationalHecke.rationalHecke (BinaryRationalHeckePrime.primeDiagonal p)
      (BinaryModularSymbolCoefficients.homogeneousAction (n+1) (-1)) f ∈ liftableSymbols n := by
  obtain ⟨F,hF,rfl⟩ := hf
  have hT : toBinaryHom n (OrdinaryHomHecke.rationalHecke (OrdinaryHeckeCosets.primeDiagonal p)
      (residueAction n (-1)) F) ∈ liftableSymbols n :=
    ⟨_,OrdinaryHomHecke.liftableResidueHoms_rational_stable _ n (-1) F hF,rfl⟩
  rw [toBinaryHom_prime] at hT
  have hF' : toBinaryHom n F ∈ liftableSymbols n := ⟨F,hF,rfl⟩
  have hz : toBinaryHom n F + (-1 : ℚ) • toBinaryHom n F = 0 := by
    calc
      _ = ((1 : ℚ) + (-1)) • toBinaryHom n F := by rw [add_smul,one_smul]
      _ = 0 := by norm_num
  have hs := (liftableSymbols n).add_mem hT ((liftableSymbols n).smul_mem (-1 : ℚ) hF')
  rw [add_assoc,hz,add_zero] at hs
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hi := (liftableSymbols n).smul_mem (p : ℚ)⁻¹ hs
  simpa only [smul_smul,inv_mul_cancel₀ hp,one_smul] using hi

end TernaryPoly.OrdinaryBinaryHecke
