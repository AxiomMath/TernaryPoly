module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Edge.AssemblyLocal
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCRealLift
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCRealScalar
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCLiftVector
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCLiftJoint

@[expose] public section


/-!
# Unconditional totality of the standard relation at `n = 3`

Original work by Claude Sonnet 5.5.

All inputs of `related_total_three_local` are proved: `LocalLiftVector` (`HCLiftVector`),
`LocalLiftRealization` (`HCRealLift`) and `LocalLiftScalarSmooth` (`HCRealScalar`, from the analytic
joint orbit `LocalLiftOrbit` proved in `HCLiftJoint`).
-/

open GeneralEisenstein
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

/-- **Totality of the standard relation at `n = 3`**: the `existsIntegral` input of
`GraphReduction.standard_graph_of_eisenstein` for `n = 3`. -/
theorem related_total_three_unconditional {n : ℕ} (hn : n = 3) (data : InducingData n)
    (holomorphic : PlaneEisensteinHolomorphic data) :
    ∀ plane : SourceSpace.sourceCocycles data .plane,
      ∃ line, StandardRelation.Related data plane line :=
  related_total_three_local hn data holomorphic (localLiftVector data holomorphic)
    (localLiftRealization data holomorphic)
    (localLiftScalarSmooth data holomorphic (localLiftOrbit data holomorphic))

end TernaryPeriodPolynomials.EdgeConvergence
