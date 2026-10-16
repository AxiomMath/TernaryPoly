module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.GeneralPolynomial
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.Fraction
public import TernaryPeriodPolynomials.SymmetricSolution.Odd.RationalSeed

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinaryResidueGeneral
open OrdinaryResiduePolynomial

/-- The literal three substituted rational representatives, before any norm hypothesis. -/
def representativeNorm (q : BP) : Frac :=
  representative q (X 0) (X 1) (X 2)+
    representative q (-X 1) (X 0-X 1) (X 2)+
    representative q (X 1-X 0) (-X 0) (X 2)

private theorem embed_X_ne (i : Fin 3) : embed (X i)≠0 := by
  simpa only [map_zero] using (IsFractionRing.injective TP Frac).ne (X_ne_zero i)

private theorem embed_difference_ne : embed (X 0)-embed (X 1)≠0 := by
  rw [←map_sub]
  have h : (X 0-X 1 : TP)≠0 := sub_ne_zero.mpr (X_injective.ne (by decide : (0 : Fin 3)≠1))
  simpa only [map_zero] using (IsFractionRing.injective TP Frac).ne h

/-- The full rational norm has exactly the binary norm residue on c=0. -/
theorem representativeNorm_formula (q : BP) (h : SymmetricOdd q) :
    representativeNorm q=embed (polynomialDefect q h)+
      embed (binaryLiftEval (periodDefect q) (X 0) (X 1))/embed (X 2) := by
  have hd : embed denominator≠0 := by
    simpa only [denominator,map_mul,map_sub] using
      mul_ne_zero (mul_ne_zero (embed_X_ne 0) (embed_X_ne 1)) embed_difference_ne
  have hk : embed (polynomialDefect q h)=embed (numerator q)/embed denominator := by
    apply (eq_div_iff hd).mpr
    rw [←map_mul]
    apply congrArg embed
    rw [numerator_eq q h]
    ring
  rw [hk,periodDefect_eval]
  simp only [representativeNorm,representative,show (X 1-X 0 : TP)= -(X 0-X 1) by ring,
    eval_neg_first h,eval_neg_second h,neg_neg]
  rw [eval_swap h (X 0-X 1) (X 1),eval_swap h (X 0) (X 0-X 1)]
  simp only [numerator,denominator,map_sub,map_add,map_mul,map_pow,map_neg]
  field_simp [embed_X_ne,embed_difference_ne]
  ring

/-- A binary numerator divided by the third coordinate can be polynomial only if it vanishes. -/
theorem third_pole_polynomial_iff (q : BP) :
    (∃ p : TP,embed p=embed (binaryLiftEval q (X 0) (X 1))/embed (X 2)) ↔ q=0 := by
  rw [SymmetricOddRationalSeed.fraction_polynomial_iff_dvd _ _ (X_ne_zero 2)]
  constructor
  · rintro ⟨p,hp⟩
    let E : TP →ₐ[ℚ] BP := bind₁ ![X 0,X 1,0]
    have he : E (binaryLiftEval q (X 0) (X 1))=q := by
      have hv : (fun i : Fin 2 => E ((![X 0,X 1] : Fin 2 → TP) i))=X := by
        funext i
        fin_cases i <;> simp [E]
      dsimp only [E]
      simp only [binaryLiftEval,bind₁_bind₁]
      change bind₁ (fun i : Fin 2 => E ((![X 0,X 1] : Fin 2 → TP) i)) q=q
      rw [hv,bind₁_X_left,AlgHom.id_apply]
    have hh := congrArg E hp
    rw [he,map_mul] at hh
    simpa [E] using hh
  · rintro rfl
    simp [binaryLiftEval]

/-- Polynomiality of the actual norm forces the full binary period equation, without a degree bound. -/
theorem representativeNorm_polynomial_iff (q : BP) (h : SymmetricOdd q) :
    (∃ p : TP,embed p=representativeNorm q) ↔ SymmetricBinaryPeriodRelations q := by
  rw [representativeNorm_formula q h]
  constructor
  · rintro ⟨p,hp⟩
    apply (period_iff h).mp
    apply (third_pole_polynomial_iff (periodDefect q)).mp
    refine ⟨p-polynomialDefect q h,?_⟩
    rw [map_sub,hp,add_sub_cancel_left]
  · intro hp
    refine ⟨polynomialDefect q h,?_⟩
    rw [(period_iff h).mpr hp]
    simp [binaryLiftEval]

end TernaryPoly.OrdinaryResidueGeneral
