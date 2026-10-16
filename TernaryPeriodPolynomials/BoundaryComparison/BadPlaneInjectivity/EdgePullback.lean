module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.GraphPieces.BoundaryExactness

@[expose] public section


/-!
# Edge-pullback transfer of `InnerBoundary` between the two sides of a global cocycle

`InnerBoundary` at a side is the vanishing of the edge-pullback `endpointPullH2` class
(`TernaryPeriodPolynomials.GraphPieces.BoundaryExactness`). For a *global* cocycle `c`, the two restrictions
`restrictionCocycle .plane c` / `restrictionCocycle .line c` have literally the same edge-pullback
cocycle (`fun x _ => c.val.val x`), so their `endpointPullH2` classes agree
(`endpointPullH2_plane_eq_line_of_global`). Hence `InnerBoundary` transfers automatically *both
ways* between the plane and line coordinates of the same global cocycle. The first four lemmas
below reproduce (self-contained, only from `Definitions` + `BoundaryExactness`, no dependence on
`Targets/PropC5` or `Targets/AppendixC6`) the ones already used by
`Revision/Proofs/NewRoute/Prop42Boundary.lean` for the line⇒plane direction; the last lemma is the
converse plane⇒line direction needed for `bad_plane_data_injective`.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.GraphPieces.BoundaryExactness


namespace TernaryPeriodPolynomials.Argument.BadPlaneInjectivity

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

theorem endpointPullCocycle_restriction_eq (n : ℕ) (χ : RankOneCharacter)
    (c : cocycles rationalLevel (rationalCoefficientComponent n χ)) :
    endpointPullCocycle n χ .plane (restrictionCocycle n χ .plane c) =
      endpointPullCocycle n χ .line (restrictionCocycle n χ .line c) := by
  apply Subtype.ext
  apply Subtype.ext
  funext x e
  rfl

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

/-- **Converse transfer direction.** If the *plane* coordinate of a global cocycle is
`InnerBoundary`, so is the *line* coordinate. (The reverse of
`TernaryPeriodPolynomials.Argument.Classification.plane_innerBoundary_of_line_innerBoundary`; together the two directions show
`InnerBoundary` is forced to hold on one side iff it holds on the other, for coordinates of the
same global cocycle.) -/
theorem line_innerBoundary_of_plane_innerBoundary (n : ℕ) (χ : RankOneCharacter)
    (c : cocycles rationalLevel (rationalCoefficientComponent n χ))
    (hplane : InnerBoundary n χ .plane (globalCoordinates n χ c).1) :
    InnerBoundary n χ .line (globalCoordinates n χ c).2 := by
  apply innerBoundary_of_endpointPullH2_eq_zero
  rw [← endpointPullH2_plane_eq_line_of_global]
  exact endpointPullH2_eq_zero_of_innerBoundary n χ .plane _ hplane

end TernaryPeriodPolynomials.Argument.BadPlaneInjectivity
