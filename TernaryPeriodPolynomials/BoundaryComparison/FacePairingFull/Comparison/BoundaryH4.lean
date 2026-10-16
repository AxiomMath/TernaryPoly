module

public import TernaryPeriodPolynomials.Topology.TopHomology.TrivialLocalSystem
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.BoundaryTopClass
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.GeometricConeComplete
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.ManifoldCap
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.Orientation

@[expose] public section


/-!
# D2′: the top total cohomology of the arithmetic boundary is one-dimensional

For the trivial rational coefficient system `ℚ` of `Γ(6)`, the top cohomology
`H⁴(stabilizerTotalCochains ℚ)` of the stabilizer cone (the cone of the flag stabilizer cochains over
the line and plane stabilizer cochains; `TernaryPoly.SymmetricSpaceBoundaryGeometricCone`) is isomorphic
to `ℚ` (`stabilizerTotal_H4_iso`): the stabilizer cone is quasi-isomorphic to the local-system cochains
of the boundary (`localBoundaryToStabilizerTotal`), Poincaré duality of the closed 4-manifold `∂M`
(`boundaryOrdinaryCapIso`) identifies `H⁴` with `H₀` of the local chains, which for the trivial system
on the path-connected base is `ℚ` (`TopHomology.trivialLocalH0Iso`; `∂M` is path connected by
`boundary_preconnected_space` and its charts).

Together with `ConeCorner` (corner cocycles modulo corner coboundaries and pullbacks inject into the total
cohomology), this bounds the space of boundary traces by one dimension.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits HomologicalComplex
open TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.SingularBoundaryRestriction
  TernaryPoly.SymmetricSpaceBoundaryGeometricCone TernaryPoly.SymmetricSpaceBoundaryManifold
  TernaryPoly.SymmetricSpaceBoundaryOrientation

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

open TernaryPeriodPolynomials.Argument.TopHomology
  TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

/-- The trivial rational coefficient system of `Γ(6)`. -/
abbrev trivialW : Rep.{0} ℚ principalSix := Rep.trivial ℚ principalSix ℚ

theorem trivialW_action : TrivialAction trivialW := fun g v => by
  simp [trivialW]

instance boundaryBase_nonempty : Nonempty BoundaryBase := by
  obtain ⟨x, hx⟩ := SymmetricSpaceBoundaryFaces.lineFace_nonempty
    SymmetricSpaceBoundaryFaces.standardLine
  have hxb : x ∈ upstairsBoundary := by
    have h : x ∈ (Set.range SymmetricSpaceRationalGluing.embedding)ᶜ := by
      rw [SymmetricSpaceBoundaryFaces.boundary_eq_face_union]
      exact Or.inl (Set.mem_iUnion.mpr ⟨_, hx⟩)
    exact h
  exact ⟨⟨_, (boundary_iff x).mp hxb⟩⟩

instance boundaryBase_pathConnected : PathConnectedSpace BoundaryBase := by
  have : ConnectedSpace BoundaryBase :=
    { toPreconnectedSpace := boundary_preconnected_space
      toNonempty := inferInstance }
  have : LocallyPathConnectedSpace BoundaryBase :=
    ChartedSpace.locallyPathConnectedSpace (Fin 4 → ℝ) BoundaryBase
  exact pathConnectedSpace_iff_connectedSpace.mpr ‹_›


theorem boundary_trivial_H0 :
    Nonempty ((SingularLocalCompactCap.coveringLocalChains boundaryProjection trivialW).homology 0 ≅
      ModuleCat.of ℚ ℚ) := by
  have : IsCancelSMul principalSix BoundaryCover := boundaryQuotientCovering.isCancelSMul
  exact ⟨trivialLocalH0Iso boundaryProjection boundaryQuotientCovering trivialW_action⟩


/-- **D2′: the top total cohomology of the arithmetic boundary with trivial coefficients is
one-dimensional.** (Poincaré duality of `∂M` identifies it with `H₀`, which is `ℚ` for the connected
`∂M`.) -/
theorem stabilizerTotal_H4_iso :
    Nonempty ((stabilizerTotalCochains trivialW).homology 4 ≅ ModuleCat.of ℚ ℚ) := by
  obtain ⟨e⟩ := boundary_trivial_H0
  have : IsIso (homologyMap (localBoundaryToStabilizerTotal trivialW) 4) := inferInstance
  exact ⟨(asIso (homologyMap (localBoundaryToStabilizerTotal trivialW) 4)).symm ≪≫
    boundaryOrdinaryCapIso trivialW boundaryOrientation 4 0 rfl ≪≫ e⟩

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
