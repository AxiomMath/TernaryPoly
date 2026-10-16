module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.GraphPieces.RationalNorm
public import TernaryPeriodPolynomials.ArithmeticCohomology.GraphPieces.EndpointReduction
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Commutativity.AlgebraProjector
public import TernaryPeriodPolynomials.ArithmeticCohomology.SpectralSeparation.Boundary
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.LineTranslateInvariance
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.SmallDegreeGraph
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.GraphReduction
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.RestrictionFinal
public import TernaryPeriodPolynomials.EisensteinSeries.Edge.Final
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Edge.Totality
public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.Interface
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.AssociatePairDualityFinal
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0OddFinal
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0EvenFinal
public import TernaryPeriodPolynomials.Building.FreeResolution.Main
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.EigencharacterSeparation

@[expose] public section


/-! Proof of the general Eisenstein graph child.

`graphConclusion_iff` and `sourceComparison` are from AxiomDeep (Claude Opus 5.5), ported
unchanged to `TernaryPeriodPolynomials.GraphPieces`.  They construct the
canonical restriction, coordinate and Hecke maps and discharge the source
comparison conjunct; `EndpointReduction.boundarySummand_le_ker` reduces endpoint
vanishing to stabilizer exactness at each complete flag.  Eigencharacter separation of
`associatePair D` for the away-three algebra (constituent separation) is
`Separation.eigenSeparated`; the proved `spectral_of_eigenSeparated`
(AxiomDeep, `Proofs/SpectralSeparation`) turns it into a spectral projector in the algebra, which by
`isIsotypicalProjection_of_mem_awayThree` and `isotypicalProjection_unique_of_mem` is the unique
isotypical projector.  For that projector the standard intertwiner whose graph is the projected
global image is built below.  Boundary duality on the associate pair
(`Duality.AssociatePairDuality`) is reduced to four local nondegeneracy cases (good line and
bad line, each for the trivial and the odd conductor-three character or degree parity), all proved
in `Proofs/AxiomCodeBoundaryDuality` (AxiomCode, Claude Opus 5.5 Claude Sonnet 5.5).

Endpoint vanishing is proved: `EndpointReduction.boundarySummand_le_ker` reduces it to
stabilizer exactness `FlagExact` at every complete flag, which is proved for plane and line
source cocycles by `plane_flagExact` and `line_flagExact` (AxiomDeep, `Proofs/FlagExactness`).

Degrees `n < 3` are closed unconditionally by
`EisensteinGraph.SmallDegreeGraph.graphConclusion_of_small_degree` (both cuspidal summands vanish, the Sol reference implementation `SmallDegreeLineBoundary`, AxiomCode).

For `3 ≤ n` the standard-graph obligation is reduced by
`EisensteinGraph.GraphReduction.standard_graph_of_eisenstein` (AxiomCode): descent of
the standard integral, `RealizesStandard` and the graph equality follow from
* totality of the standard relation (every plane source cocycle has a regular standard
  continuation), proved for `4 ≤ n` by the Sol reference implementation `StandardConstruction` (ported into
  `Proofs/AxiomCodeGraph`), and in degree `3`, the edge `Re s = -n/2` of absolute convergence, by
  `EdgeConvergence.related_total_three_unconditional` (AxiomCode, Claude Sonnet 5.5);
* `HasEisensteinClasses`: global classes projecting to `([c], [J c])`; for `4 ≤ n` this is proved
  by `EisensteinGraph.ConstantTerm.hasEisensteinClasses_of_large` (AxiomCode, Claude
  Sonnet 5.5, via the constant-term restriction formula); at `n = 3` it follows from the edge
  Eisenstein operator (`EdgeEisenstein.hasEisensteinClasses_three_unconditional`, Claude Opus 5.5 Claude Sonnet 5.5);
* `HalfDimension`: no global class projects to `(0, b)` with `b ≠ 0`; it follows
  (`Duality.halfDimension`) from cup-product exactness, proved from the free resolution
  of the principal level-three subgroup (`FreeResolution.cupProductExactness`, Opus 5.5), and boundary duality on the associate pair.
-/

open GeneralEisenstein

namespace TernaryPeriodPolynomials

theorem general_eisenstein_graph (n : ℕ) (D : InducingData n)
    (hhol : PlaneEisensteinHolomorphic D) : GraphConclusion D := by
  -- Degrees `n < 3`: both cuspidal summands vanish, proved unconditionally
  --  (AxiomCode, from the Sol reference implementation `SmallDegreeGraph`).
  rcases Nat.lt_or_ge n 3 with small | atLeastThree
  · exact TernaryPeriodPolynomials.EisensteinGraph.SmallDegreeGraph.graphConclusion_of_small_degree
      small D
  open TernaryPeriodPolynomials.GraphPieces in
  open TernaryPeriodPolynomials.EisensteinGraph in
  -- Local nondegeneracy of the boundary pairing at the bad-line cusp in even degree (AxiomCode, Claude Sonnet 5.5).  The good-line cases are proved
  -- in `LocalPairingCaseL1TrivialFinal`, `LocalPairingCaseL1OddUnconditional` (Claude Sonnet 5.5) on the level-one Hecke adjointness of the cup pairing,
  -- `AdjCore.parabolicPairingHeckeAdjoint` (Claude Opus 5.5).
  have badEven :
      TernaryPeriodPolynomials.BoundaryDuality.ParityCases.BadLineEvenInput n :=
    TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Even.badLineEvenInput_unconditional
      atLeastThree
  -- The bad line in odd degree (AxiomCode, Claude Sonnet 5.5:
  -- level-three Hecke adjointness `AdjL3.badGoodHeckeAdjoint`).
  have badOdd : TernaryPeriodPolynomials.BoundaryDuality.ParityCases.BadLineOddInput n :=
    TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Odd.badLineOddInput_unconditional
      atLeastThree
  -- Boundary duality on the associate pair, from the four local cases (Claude Opus 5.5 Claude Sonnet 5.5).
  have duality : TernaryPeriodPolynomials.Duality.AssociatePairDuality D :=
    TernaryPeriodPolynomials.BoundaryDuality.AssociatePairDualityFinal.associatePairDuality_of_badLine
      atLeastThree D badEven badOdd
  -- Eigencharacter separation (Harder–Raghuram constituent separation), proved for every actual
  -- boundary Hecke structure (`Separation.eigenSeparated`, the same input
  -- as the three spectral targets).
  have separated : TernaryPeriodPolynomials.SpectralSeparation.EigenSeparated
      (awayThreeHeckeAlgebra D
        (TernaryPeriodPolynomials.GraphPieces.Reduction.canonicalStratumHecke n D.chi))
      (associatePair D) :=
    TernaryPeriodPolynomials.Separation.eigenSeparated (by omega) D _
      (TernaryPeriodPolynomials.GraphPieces.Reduction.canonicalStratumHecke_realizes n D.chi)
  -- Stabilizer exactness (proved unconditionally, AxiomDeep `Proofs/FlagExactness`).
  have flagExact : ∀ side source, IsSourceCocycle D side source →
      ∀ flag, TernaryPeriodPolynomials.GraphPieces.EndpointReduction.FlagExact D source flag := by
    intro side source isSource flag
    cases side
    · exact TernaryPeriodPolynomials.FlagExactness.plane_flagExact D source isSource flag
    · exact TernaryPeriodPolynomials.FlagExactness.line_flagExact D source isSource flag
  have actual : ActualBoundaryHecke n D.chi
      (TernaryPeriodPolynomials.GraphPieces.Reduction.canonicalStratumHecke n D.chi) :=
    TernaryPeriodPolynomials.GraphPieces.Reduction.canonicalStratumHecke_realizes n D.chi
  -- Separation gives a spectral projector in the away-three algebra.
  have key := TernaryPeriodPolynomials.SpectralSeparation.spectral_of_eigenSeparated D _
    actual separated
  have mem := key.choose_spec.1
  have range := key.choose_spec.2.1
  have identity := key.choose_spec.2.2
  have standardGraph : ∃ standard : boundarySummand D .plane →ₗ[ℂ] boundarySummand D .line,
      RealizesStandard D standard ∧
      (LinearMap.range (TernaryPeriodPolynomials.GraphPieces.Reduction.projectedRestriction
        D key.choose) : Set (BoundaryCoordinates n D.chi)) =
        TernaryPeriodPolynomials.GraphPieces.Reduction.spectralGraph D standard := by
    -- Totality of the standard relation: Sol's continuation for `4 ≤ n`, the Cauchy-endpoint lift at
    -- the edge `n = 3` (AxiomCode).
    have existsIntegral : ∀ plane :
        TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SourceSpace.sourceCocycles
          D .plane,
        ∃ line,
          TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.StandardRelation.Related
            D plane line := by
      by_cases large : 4 ≤ n
      · exact
          TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.EndpointSourceStandard.related_total
            D large hhol
      · exact TernaryPeriodPolynomials.EdgeConvergence.related_total_three_unconditional
          (by omega) D hhol
    -- Global Eisenstein classes: the constant-term restriction formula for `4 ≤ n`,
    -- the edge Eisenstein operator at `n = 3`.
    have eisenstein :
        TernaryPeriodPolynomials.EisensteinGraph.GraphReduction.HasEisensteinClasses D
          key.choose := by
      by_cases large : 4 ≤ n
      · exact TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm.hasEisensteinClasses_of_large
          large D hhol key.choose identity
      · have hn3 : n = 3 := by omega
        exact
          TernaryPeriodPolynomials.EdgeEisenstein.hasEisensteinClasses_three_unconditional
            hn3 D hhol key.choose identity
    -- Half-dimension: cup-product exactness from the free resolution (`H⁴ = 0`) and
    -- boundary duality on the associate pair.
    have half : TernaryPeriodPolynomials.EisensteinGraph.GraphReduction.HalfDimension D key.choose :=
      TernaryPeriodPolynomials.Duality.halfDimension D key.choose mem range.le
        existsIntegral eisenstein
        (TernaryPeriodPolynomials.FreeResolution.cupProductExactness D)
        duality
    exact TernaryPeriodPolynomials.EisensteinGraph.GraphReduction.standard_graph_of_eisenstein
      D key.choose range existsIntegral eisenstein.choose eisenstein.choose_spec half
  -- A spectral projector in the away-three algebra is the unique isotypical projection.
  have projects := TernaryPeriodPolynomials.HeckeCommutativity.isIsotypicalProjection_of_mem_awayThree
    D _ actual mem range identity
  have unique : ∀ alternative, IsIsotypicalProjection D
      (TernaryPeriodPolynomials.GraphPieces.Reduction.canonicalStratumHecke n D.chi)
      alternative → alternative = key.choose := fun alternative h =>
    TernaryPeriodPolynomials.HeckeStability.isotypicalProjection_unique_of_mem projects mem h
  apply (TernaryPeriodPolynomials.GraphPieces.Reduction.graphConclusion_iff D).mpr
  exact ⟨TernaryPeriodPolynomials.GraphPieces.RationalNorm.sourceComparison D,
    ⟨TernaryPeriodPolynomials.GraphPieces.EndpointReduction.boundarySummand_le_ker D .plane
        (flagExact .plane),
      TernaryPeriodPolynomials.GraphPieces.EndpointReduction.boundarySummand_le_ker D .line
        (flagExact .line)⟩,
    key.choose, standardGraph.choose, projects, unique, standardGraph.choose_spec.1,
    standardGraph.choose_spec.2⟩

end TernaryPeriodPolynomials
