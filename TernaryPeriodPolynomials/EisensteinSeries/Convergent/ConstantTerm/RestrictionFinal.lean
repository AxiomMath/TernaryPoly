module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.ConstantTerm.FlagExact
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.ConstantTerm.RestrictionAssembly
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.FlagFrames

@[expose] public section


/-!
# The restriction formula for degrees `n ≥ 4` (convergent)

The restriction formula for the global Eisenstein cocycle built from the absolutely convergent Eisenstein series.

Re-port of `TernaryPeriodPolynomials.Argument.EisensteinGraph.ConstantTerm.RestrictionFinal` (from the Sol reference implementation, ported by AxiomCode) with `PlaneEisensteinHolomorphic` replaced by the continuation-free
`PlaneEisensteinConvergent`; declarations that do not depend on the continuation hypothesis are
not copied (the original ones are used).  Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.ConstantTerm

open TernaryPeriodPolynomials
open TernaryPeriodPolynomials.EisensteinGraph
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm


open GeneralEisenstein GeneralEisenstein.Homogeneous
/-- **The restriction formula** `GraphReduction.RestrictionFormula` for `4 ≤ n`. -/
theorem restrictionFormula {n : ℕ} (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinConvergent D) : GraphReduction.RestrictionFormula large D hol :=
  restrictionFormula_of_exact large D hol fun c side =>
    defectCochain_exact_of_integral_flags large D hol c side
      (fun x => exists_integral_representative side x)
      (fun g => defect_flag_exact large D hol c side g)



end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.ConstantTerm
