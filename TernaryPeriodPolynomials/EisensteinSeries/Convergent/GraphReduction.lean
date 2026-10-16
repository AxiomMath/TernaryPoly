module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.EndpointEisensteinCocycle
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.EndpointSourceStandard

@[expose] public section


/-!
# The restriction formula (convergent)

Statement of the restriction formula for the convergent construction (cf.
`GraphReduction.RestrictionFormula`).  Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.GraphReduction

open TernaryPeriodPolynomials.EisensteinGraph
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

/-- The unprojected constant-term formula for the convergent construction: the maximal-stratum
coordinates of the global Eisenstein cocycle of a plane source cocycle `c` are the classes of
`c` and of its standard line cocycle. -/
def RestrictionFormula {n : ℕ} (large : 4 ≤ n) (D : InducingData n)
    (holomorphic : PlaneEisensteinConvergent D) : Prop :=
  ∀ plane : SourceSpace.sourceCocycles D .plane,
    globalCoordinates n D.chi (EndpointEisensteinCocycle.globalCocycle D holomorphic large plane) =
      (SourceSpace.sourceClass D .plane plane,
        SourceSpace.sourceClass D .line
          (EndpointSourceStandard.sourceStandard D large holomorphic plane))

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.GraphReduction
