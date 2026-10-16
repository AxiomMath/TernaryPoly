module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.Polynomial
public import Mathlib.Tactic.FieldSimp

@[expose] public section

open MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinaryResiduePolynomial

abbrev Frac := FractionRing TP
abbrev embed : TP →+* Frac := algebraMap TP Frac

/-- The exact three-coordinate single-pole rational representative. -/
def representative (q : BP) (a b c : TP) : Frac :=
  embed (binaryLiftEval q b c)/embed a + embed (binaryLiftEval q a c)/embed b +
    embed (binaryLiftEval q a b)/embed c

private theorem embed_X_ne (i : Fin 3) : embed (X i)≠0 := by
  simpa only [map_zero] using (IsFractionRing.injective TP Frac).ne (X_ne_zero i)

private theorem embed_difference_ne : embed (X 0)-embed (X 1)≠0 := by
  rw [←map_sub]
  have h : (X 0-X 1 : TP)≠0 := sub_ne_zero.mpr (X_injective.ne (by decide : (0 : Fin 3)≠1))
  simpa only [map_zero] using (IsFractionRing.injective TP Frac).ne h

/-- The ternary norm of the actual symmetric single-pole representative is a polynomial,
with precisely the normalized defect from the residue calculation. -/
theorem representative_norm (q : BP) (hq : SymmetricBinaryPeriodRelations q) :
    representative q (X 0) (X 1) (X 2) +
      representative q (-X 1) (X 0-X 1) (X 2) +
      representative q (X 1-X 0) (-X 0) (X 2) = embed (defect q hq) := by
  have hp := symmetricBinaryEval_period hq (X 0) (X 1)
  rw [symmetricBinaryEval_swap hq (X 1) (X 0-X 1),
    symmetricBinaryEval_swap hq (X 0-X 1) (X 0)] at hp
  have he : binaryLiftEval q (X 0-X 1) (X 0)=
      binaryLiftEval q (X 1) (X 0-X 1)-binaryLiftEval q (X 0) (X 1) := by
    linear_combination hp
  have hd : embed denominator≠0 := by
    simpa only [denominator,map_mul,map_sub] using
      mul_ne_zero (mul_ne_zero (embed_X_ne 0) (embed_X_ne 1)) embed_difference_ne
  apply mul_left_cancel₀ hd
  rw [←map_mul,←numerator_eq]
  simp only [representative,show (X 1-X 0 : TP)= -(X 0-X 1) by ring,
    symmetricBinaryEval_neg_first hq,symmetricBinaryEval_neg_second hq,neg_neg,he,
    denominator,numerator,map_sub,map_mul,map_pow,map_neg]
  field_simp [embed_X_ne,embed_difference_ne]
  ring

end TernaryPoly.OrdinaryResiduePolynomial
