module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Edge.Assembly
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCLocalSmooth
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCLocalScalar
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCTwist

@[expose] public section


/-!
# Assembly at `n = 3` with the local smoothness, holomorphy and twisted continuity discharged

Original work by Claude Sonnet 5.5.

Three of the six analytic inputs of `EdgeAssembly.related_total_three` are proved in the `HC*` files:
`LocalVectorsSmooth` (`HCLocalSmooth`), `LocalScalarAnalytic` (`HCLocalScalar`) and
`TwistedLocalContinuity` (`HCTwist`). This file feeds them into the assembly. The hypotheses are the Cauchy-lift inputs: the vector `LocalLiftVector`, its realization
`LocalLiftRealization` and the scalar smoothness `LocalLiftScalarSmooth` (see `EdgeAssemblyReduced`
for their reduction).
-/

open GeneralEisenstein
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.EdgeConvergence.EdgeInputs

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

/-- **Totality of the standard relation at `n = 3`** from the three Cauchy-lift inputs: the
`existsIntegral` input of `GraphReduction.standard_graph_of_eisenstein` for `n = 3`. -/
theorem related_total_three_local {n : ℕ} (hn : n = 3) (data : InducingData n)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (llv : LocalLiftVector data holomorphic) (llr : LocalLiftRealization data holomorphic)
    (lss : LocalLiftScalarSmooth data holomorphic) :
    ∀ plane : SourceSpace.sourceCocycles data .plane,
      ∃ line, StandardRelation.Related data plane line :=
  related_total_three hn data holomorphic (localVectorsSmooth data holomorphic)
    (localScalarAnalytic data holomorphic) llv llr lss
    (twistedLocalContinuity_unconditional data holomorphic SectionMultipliersXiSmooth.heightLaw)

end TernaryPeriodPolynomials.EdgeConvergence
