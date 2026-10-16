module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.NormAction
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.Extreme

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinaryResidueGeneral
open OrdinaryResiduePolynomial

/-- For an actual period residue, every polynomial correction to a norm-zero lift
has precisely the old normalized polynomial norm defect. -/
theorem polynomial_correction_norm (e : ℤ) (q : BP) (hq : SymmetricBinaryPeriodRelations q)
    (p : TP) (hn : fractionNorm e (representative q (X 0) (X 1) (X 2)+embed p)=0) :
    N p= -defect q hq := by
  rw [fractionNorm_add,fractionNorm_representative,fractionNorm_embed] at hn
  have he : representativeNorm q=embed (defect q hq) := representative_norm q hq
  rw [he,←map_add] at hn
  have hz : defect q hq+N p=0 := (IsFractionRing.injective TP Frac) (hn.trans (map_zero embed).symm)
  linear_combination hz

/-- Genuine fraction-field norm-zero lifts detect the binary period relation and every
extreme coefficient. No homogeneous degree or a priori period relation is required. -/
theorem norm_zero_lift_extreme (e : ℤ) (q : BP) (h : SymmetricOdd q) (p : TP)
    (hodd : bind₁ ![-X 0,X 1,X 2] p= -p)
    (hn : fractionNorm e (representative q (X 0) (X 1) (X 2)+embed p)=0) :
    SymmetricBinaryPeriodRelations q ∧ ∀ m : Fin 1 →₀ ℕ,q.coeff (Finsupp.cons 1 m)=0 := by
  have hq := period_of_norm_zero_lift e q h p hn
  exact ⟨hq,fun m => OrdinaryResidueExtreme.extreme_coefficient_zero q hq p hodd
    (polynomial_correction_norm e q hq p hn) m⟩

end TernaryPoly.OrdinaryResidueGeneral
