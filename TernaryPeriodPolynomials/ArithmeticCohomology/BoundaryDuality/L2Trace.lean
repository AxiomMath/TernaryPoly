module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.HeisComparison
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.ChainPairing

@[expose] public section


/-!
# The boundary trace and boundary duality on the associate pair

The cusp cycles `C_{L₀}(T)`, `−C_{L₀}(L)`, `C_{L₁}(T₀)` at the three orbits of complete flags,
with the vertex relations at the two lines and the two planes and the three orientation comparisons
`(s₀, s₁, s₂) = (1, −1, −1)`, form the chain data `traceDataL2` of a boundary trace. Boundary
duality on the associate pair follows from a chain witness for it: for every nonzero line summand
class a plane summand class and representatives with nonzero chain value
`Σ_e ⟨(w ⌣ y^φ)(·)(ē), C_e⟩ − Σ_v ⟨(z ⌣ y^φ)(·)(v̄), D_v⟩`
(`associatePairDuality_of_chainWitnessL2`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein

namespace TernaryPeriodPolynomials.BoundaryDuality.L2Trace

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.ChainPairing
open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly
open TernaryPeriodPolynomials.BoundaryDuality.HeisComparison

/-- The chain data of the boundary trace of the level. -/
def traceDataL2 : TraceData (Fin 3) (Fin 2) (Fin 2) :=
  traceData_of_comparisons 1 (-1) (-1) (by norm_num) comparison_e₀ comparison_e₁ comparison_e₂

/-- The boundary trace of the level satisfies the trace conditions. -/
theorem isBoundaryTrace_traceDataL2 :
    TraceReduction.IsBoundaryTrace traceDataL2.trace.toAddMonoidHom :=
  traceDataL2.isBoundaryTrace_trace

/-- **Boundary duality on the associate pair from a chain witness for the boundary trace of the
level.** -/
theorem associatePairDuality_of_chainWitnessL2 {n : ℕ} (D : InducingData n)
    (witness : ChainWitness traceDataL2 D (dualityData n D.chi)) : AssociatePairDuality D :=
  associatePairDuality_of_chainWitness traceDataL2 D witness

end TernaryPeriodPolynomials.BoundaryDuality.L2Trace
