module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.SmallDegreeLineBoundary
public import TernaryPeriodPolynomials.ArithmeticCohomology.GraphPieces.RationalNorm

@[expose] public section


/-! # The general Eisenstein graph in degrees `n < 3`

For `n < 3` both cuspidal summands vanish (`SmallDegreeLineBoundary`, ported from the Sol reference implementation), so the zero projection and the zero intertwiner
satisfy every clause of `GraphConclusion`. The assembly below uses the repository's
`GraphPieces.Reduction.graphConclusion_iff` (AxiomDeep) in place of Sol's
`CanonicalGraphAssembly`; it follows Sol's `SmallDegreeGraph.general_eisenstein_graph_of_small_degree`.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.EisensteinGraph.SmallDegreeGraph

open TernaryPeriodPolynomials.GraphPieces

theorem plane_summand_eq_bot {n : ℕ} (small : n < 3) (D : InducingData n) :
    boundarySummand D .plane = ⊥ :=
  SmallDegreePlaneBoundary.plane_boundarySummand_eq_bot_of_small_degree small D

theorem line_summand_eq_bot {n : ℕ} (small : n < 3) (D : InducingData n) :
    boundarySummand D .line = ⊥ :=
  SmallDegreeLineBoundary.line_boundarySummand_eq_bot_of_small_degree small D

theorem isotypical_eq_zero {n : ℕ} (small : n < 3) (D : InducingData n)
    {hecke : (side : Side) → HeckeCorrespondence → Module.End ℂ (StratumH2 n D.chi side)}
    {p : Module.End ℂ (BoundaryCoordinates n D.chi)} (hp : IsIsotypicalProjection D hecke p) :
    p = 0 := by
  apply LinearMap.ext
  intro x
  have hx := LinearMap.mem_range_self p x
  rw [hp.1, SmallDegreeLineBoundary.associatePair_eq_bot_of_small_degree small D] at hx
  simpa using hx

theorem isotypical_zero {n : ℕ} (small : n < 3) (D : InducingData n)
    (hecke : (side : Side) → HeckeCorrespondence → Module.End ℂ (StratumH2 n D.chi side)) :
    IsIsotypicalProjection D hecke 0 := by
  have hbot := SmallDegreeLineBoundary.associatePair_eq_bot_of_small_degree small D
  refine ⟨by rw [hbot, LinearMap.range_zero], fun x hx => ?_, fun t => by simp⟩
  rw [hbot, Submodule.mem_bot] at hx
  simp [hx]

/-- `GraphConclusion` in every degree `n < 3`, unconditionally. -/
theorem graphConclusion_of_small_degree {n : ℕ} (small : n < 3) (D : InducingData n) :
    GraphConclusion D := by
  apply (Reduction.graphConclusion_iff D).mpr
  refine ⟨RationalNorm.sourceComparison D, ⟨?_, ?_⟩, 0, 0, isotypical_zero small D _,
    fun p hp => isotypical_eq_zero small D hp,
    SmallDegreePlaneBoundary.realizesStandard_zero_of_small_degree small D, ?_⟩
  · rw [plane_summand_eq_bot small D]; exact bot_le
  · rw [line_summand_eq_bot small D]; exact bot_le
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨0, by simp [Reduction.projectedRestriction]; rfl⟩
    · rintro ⟨ξ, rfl⟩
      have hξ : ξ = 0 :=
        SmallDegreePlaneBoundary.plane_boundaryClass_zero_of_small_degree small D ξ
      subst hξ
      exact ⟨0, by simp; rfl⟩

end TernaryPeriodPolynomials.EisensteinGraph.SmallDegreeGraph
