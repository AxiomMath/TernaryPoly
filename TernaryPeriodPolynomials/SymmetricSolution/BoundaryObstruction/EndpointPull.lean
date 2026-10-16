module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.GraphPieces.BoundaryExactness
public import TernaryPeriodPolynomials.BoundaryComparison.PlaneLineComparison
public import TernaryPeriodPolynomials.BoundaryComparison.FiniteEntries

@[expose] public section



/-! In this formalization "mixed cuspidal" (`InnerBoundary`) at a side is literally the vanishing of
the edge pullback `endpointPullH2` in the cohomology of `Edges`
(`TernaryPeriodPolynomials.GraphPieces.BoundaryExactness`), so no Hochschild–Serre computation is needed here. For a
global cocycle `c`, the two restrictions `restrictionCocycle .plane c` and
`restrictionCocycle .line c` have literally the same edge-pullback cocycle (both reduce to
`fun x _ => c.val.val x`, independent of the flag coordinate), so their `endpointPullH2` classes
agree; combined with `hline` this makes the plane coordinate `InnerBoundary` too. Proposition C.5's
`T` then forces `ξ_Q = T ξ_P`, and Appendix C.6 forces
`ξ_P = 0` from `GoodBoundaryVanishing`, hence `ξ_Q = T 0 = 0`. -/

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.GraphPieces.BoundaryExactness

namespace TernaryPeriodPolynomials.Argument.Classification

/-- `InnerBoundary` implies the edge-pullback `H2` class vanishes. -/
theorem endpointPullH2_eq_zero_of_innerBoundary (n : ℕ) (χ : RankOneCharacter) (side : Side)
    (a : StratumH2 n χ side) (ha : InnerBoundary n χ side a) :
    endpointPullH2 n χ side a = 0 := by
  obtain ⟨z, hz, u, hu⟩ := ha
  rw [← hz, endpointPullH2_realizes]
  have hz2 : endpointPullCocycle n χ side z =
      boundaryMap rationalLevel
        (functionRepresentation (rationalCoefficientComponent n χ) Edges) u := by
    apply Subtype.ext
    apply Subtype.ext
    funext x e
    exact hu x e
  rw [hz2]
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩

/-- Conversely, a vanishing edge-pullback `H2` class comes from an `InnerBoundary` witness. -/
theorem innerBoundary_of_endpointPullH2_eq_zero (n : ℕ) (χ : RankOneCharacter) (side : Side)
    (a : StratumH2 n χ side) (ha : endpointPullH2 n χ side a = 0) :
    InnerBoundary n χ side a := by
  obtain ⟨z, hz⟩ : ∃ z : MaximalCycles n χ side,
      classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) side) z = a :=
    (LinearMap.range (boundaryMap rationalLevel
      (flagRepresentation (rationalCoefficientComponent n χ) side))).mkQ_surjective a
  refine ⟨z, hz, ?_⟩
  have ha' : classOf rationalLevel
      (functionRepresentation (rationalCoefficientComponent n χ) Edges)
      (endpointPullCocycle n χ side z) = 0 := by
    have heq := endpointPullH2_realizes n χ side z
    rw [hz] at heq
    exact heq.symm.trans ha
  obtain ⟨u, hu⟩ := (Submodule.Quotient.mk_eq_zero _).mp ha'
  refine ⟨u, fun x e => ?_⟩
  show (endpointPullCocycle n χ side z).val.val x e =
    (boundaryMap rationalLevel
      (functionRepresentation (rationalCoefficientComponent n χ) Edges) u).val.val x e
  rw [hu]

/-- The two restrictions of a global cocycle have the same edge-pullback cocycle: both are
literally `fun x _ => c.val.val x`, independent of the flag coordinate. -/
theorem endpointPullCocycle_restriction_eq (n : ℕ) (χ : RankOneCharacter)
    (c : cocycles rationalLevel (rationalCoefficientComponent n χ)) :
    endpointPullCocycle n χ .plane (restrictionCocycle n χ .plane c) =
      endpointPullCocycle n χ .line (restrictionCocycle n χ .line c) := by
  apply Subtype.ext
  apply Subtype.ext
  funext x e
  rfl

/-- Hence the two edge-pullback `H2` classes of the restrictions of a global cocycle agree. -/
theorem endpointPullH2_plane_eq_line_of_global (n : ℕ) (χ : RankOneCharacter)
    (c : cocycles rationalLevel (rationalCoefficientComponent n χ)) :
    endpointPullH2 n χ .plane (globalCoordinates n χ c).1 =
      endpointPullH2 n χ .line (globalCoordinates n χ c).2 := by
  show endpointPullH2 n χ .plane
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane)
        (restrictionCocycle n χ .plane c)) =
    endpointPullH2 n χ .line
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line)
        (restrictionCocycle n χ .line c))
  rw [endpointPullH2_realizes, endpointPullH2_realizes, endpointPullCocycle_restriction_eq]

/-- If the line coordinate of a global cocycle is `InnerBoundary`, so is the plane coordinate. -/
theorem plane_innerBoundary_of_line_innerBoundary (n : ℕ) (χ : RankOneCharacter)
    (c : cocycles rationalLevel (rationalCoefficientComponent n χ))
    (hline : InnerBoundary n χ .line (globalCoordinates n χ c).2) :
    InnerBoundary n χ .plane (globalCoordinates n χ c).1 := by
  apply innerBoundary_of_endpointPullH2_eq_zero
  rw [endpointPullH2_plane_eq_line_of_global]
  exact endpointPullH2_eq_zero_of_innerBoundary n χ .line _ hline

/-- The proof of `line_restriction_eq_zero_of_good_vertices`: assemble the above with Proposition C.5 and Appendix C.6. -/
theorem line_restriction_eq_zero_of_good_vertices_of_route (n : ℕ) (hn : 4 ≤ n)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (hline : InnerBoundary n trivialCharacter .line (globalCoordinates n trivialCharacter c).2)
    (hgood : GoodBoundaryVanishing n trivialCharacter (globalCoordinates n trivialCharacter c)) :
    (globalCoordinates n trivialCharacter c).2 = 0 := by
  obtain ⟨T, hT1, hT2⟩ := TernaryPeriodPolynomials.line_constant_term_comparison n hn
  have hξP : InnerBoundary n trivialCharacter .plane (globalCoordinates n trivialCharacter c).1 :=
    plane_innerBoundary_of_line_innerBoundary n trivialCharacter c hline
  have hTeq : (globalCoordinates n trivialCharacter c).2 =
      T (globalCoordinates n trivialCharacter c).1 :=
    hT2 c hξP hline
  have hT : ∀ ξ, InnerBoundary n trivialCharacter .plane ξ →
      ∃ c' : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
        globalCoordinates n trivialCharacter c' = (ξ, T ξ) :=
    fun ξ hξ => (hT1 ξ hξ).2
  have hgood2' :
      VanishesOnGood n trivialCharacter .line (T (globalCoordinates n trivialCharacter c).1) := by
    rw [← hTeq]; exact hgood.2
  have hzero : (globalCoordinates n trivialCharacter c).1 = 0 :=
    TernaryPeriodPolynomials.bad_plane_data_injective n hn T hT
      (globalCoordinates n trivialCharacter c).1 hξP hgood.1 hgood2'
  rw [hTeq, hzero, map_zero]

end TernaryPeriodPolynomials.Argument.Classification
