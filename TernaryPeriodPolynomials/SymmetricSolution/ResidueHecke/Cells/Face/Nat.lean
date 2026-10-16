module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Face.Interface
public import TernaryPeriodPolynomials.ArithmeticCohomology.CoefficientNaturality.Assemble

@[expose] public section


/-!
# Lemma B.1: the reduction to `FaceEvalAvg`, unconditional in the coefficient naturality

Formalized by Claude Sonnet 5.5.

`FaceInterface` proves the equivalence `PHCompat n ↔ FaceEvalAvg n` from the coefficient naturality of the neat duality
`groupOrdinaryIso` as an explicit hypothesis `hnat`.  Here the hypothesis is discharged by
`CoefficientNaturality.groupOrdinaryIso_natural`, so the reduction of `PHCompat` to the single neat-level statement
`FaceEvalAvg` holds with no hypothesis at all: `termF_eq_zero` (the support clause), `phCompat_iff_faceEvalAvg'`,
`phCompatUniform_of_faceEvalAvgUniform'`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open TernaryPoly TernaryPoly.ModThreeGoodAction IntegralGL3Congruence CategoryTheory
open TernaryPeriodPolynomials.Argument.CoefficientNaturality

/-- The coefficient naturality hypothesis of `FaceSupport` / `FaceInterface`, proved. -/
theorem neatDuality_natural {W W' : Rep.{0} ℚ principalSix} (f : W ⟶ W') (x : groupHomology W 3) :
    (OrdinaryTopBoundaryComparison.groupOrdinaryIso W').hom.hom
        ((groupHomology.map (MonoidHom.id principalSix) f 3).hom x) =
      (OrdinaryTopBoundaryComparison.groupOrdinaryIso W).hom.hom x ≫ f :=
  groupOrdinaryIso_natural f x

/-- **The support clause of `FaceEval`**: for `g ∉ P_H · Γ(6)` the `a = 0` residue of `ρ(g) Θ_N(ι_* y)(g⁻¹ σ₀)` vanishes. -/
theorem termF_eq_zero (n : ℕ) (y : groupHomology (Rep.res PN.subtype (FibRep n)) 3) {g : IntegralGL}
    (hg : ¬ InPHN g) : termF n y g = 0 :=
  termF_eq_zero_of_natural neatDuality_natural n y hg

/-- **`PHCompat n` is equivalent to the neat-level face evaluation `FaceEvalAvg n`.** -/
theorem phCompat_iff_faceEvalAvg' (n : ℕ) : PHCompat n ↔ FaceEvalAvg n :=
  phCompat_iff_faceEvalAvg neatDuality_natural n

theorem phCompatUniform_of_faceEvalAvgUniform' (h : FaceEvalAvgUniform) : PHCompatUniform :=
  phCompatUniform_of_faceEvalAvgUniform neatDuality_natural h

end TernaryPeriodPolynomials.Argument.AppendixBResidue
