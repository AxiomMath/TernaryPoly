module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.FlagExact
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.RestrictionAssembly

@[expose] public section


/-!
# The restriction formula for the global Eisenstein cocycle (degrees `n ≥ 4`)

The maximal-stratum coordinates of the global Eisenstein cocycle of a plane source cocycle `c` are
the classes of `c` and of its standard continuation `J c`. By the Shapiro assembly and the
existence of integral flag representatives, this reduces to exactness of the defect cochain at
every integral flag (`defect_flag_exact`), which is the torus-averaging argument of
`EngineGrid.lean` fed with the covariance, periodicity and constant-term inputs.

Written by AxiomCode.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm

open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

/-- **The restriction formula** `GraphReduction.RestrictionFormula` for `4 ≤ n`. -/
theorem restrictionFormula {n : ℕ} (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinHolomorphic D) : GraphReduction.RestrictionFormula large D hol :=
  restrictionFormula_of_exact large D hol fun c side =>
    defectCochain_exact_of_integral_flags large D hol c side
      (fun x => exists_integral_representative side x)
      (fun g => defect_flag_exact large D hol c side g)


/-- **Global Eisenstein classes for `4 ≤ n`.** For every projection onto the associate pair that is
the identity there, the global Eisenstein classes of Sol's construction project to `([c], [J c])`
for every related pair. This is the `HasEisensteinClasses` input of
`GraphReduction.standard_graph_of_large_degree`. -/
theorem hasEisensteinClasses_of_large {n : ℕ} (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinHolomorphic D)
    (projection : Module.End ℂ (BoundaryCoordinates n D.chi))
    (identity : ∀ x ∈ associatePair D, projection x = x) :
    GraphReduction.HasEisensteinClasses D projection :=
  GraphReduction.hasEisensteinClasses_of_constantTermFormula large D hol projection
    (GraphReduction.constantTermFormula_of_restrictionFormula large D hol projection identity
      (restrictionFormula large D hol))

end TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm
