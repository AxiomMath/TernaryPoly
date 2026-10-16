module

public import TernaryPeriodPolynomials.Topology.Covering.BoundaryDeformationEquivariant
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.Neighborhood
public import TernaryPeriodPolynomials.Topology.Singular.BoundaryRestrictionGeometry

@[expose] public section


noncomputable section
namespace TernaryPoly.CoveringBoundaryDeformation.Actual
open SymmetricSpaceRationalGluing SymmetricSpaceBordifiedPrincipalSix
  SymmetricSpaceBordifiedQuotient IntegralGL3Congruence SingularBoundaryRestriction
open scoped unitInterval

abbrev Cover (S : Set BordifiedOrbit) := (projection principalSix) ⁻¹' S

instance coverAction (S : Set BordifiedOrbit) : MulAction principalSix (Cover S) :=
  preimageAction (projection_smul principalSix) S

instance coverContinuous (S : Set BordifiedOrbit) : ContinuousConstSMul principalSix (Cover S) :=
  preimageContinuous (projection_smul principalSix) S

/-- The exact preimage of every open base neighborhood is open in the actual full cover. -/
theorem cover_open {S : Set BordifiedOrbit} (hS : IsOpen S) : IsOpen (Cover S) :=
  hS.preimage (projection_continuous principalSix)

variable {W : Set BordifiedOrbit} (c : SymmetricSpaceBoundaryNeighborhood.Collapse W)

/-- Lift the actual finite assembled deformation through the genuine principal-six covering. -/
def deformation : BoundaryNeighborhood.Deformation (Cover (boundary principalSix)) (Cover W) :=
  liftedDeformation SymmetricSpaceCompactBordification.actual_projection_covering c.deformation

theorem deformation_projection (t : I) (x : Glued) :
    projection principalSix ((deformation c).homotopy (t, x)) =
      c.deformation.homotopy (t, projection principalSix x) :=
  lift_projection SymmetricSpaceCompactBordification.actual_projection_covering c.deformation t x

theorem deformation_equivariant (g : principalSix) (t : I) (x : Glued) :
    (deformation c).homotopy (t, g • x) = g • (deformation c).homotopy (t, x) :=
  lift_equivariant SymmetricSpaceCompactBordification.actual_projection_covering
    (projection_smul principalSix) c.deformation g t x

/-- Every actual geometric boundary point is fixed throughout the lifted homotopy. -/
theorem deformation_fixed (t : I) (x : BoundaryCover) :
    (deformation c).homotopy (t, x.val) = x.val :=
  (deformation c).fixes t x.val ((boundary_iff x.val).mp x.property)

/-- The lifted endpoint lies in the literal geometric boundary, not just an abstract model. -/
theorem endpoint_mem (x : Cover c.neighborhood) :
    (deformation c).homotopy (1, x.val) ∈ upstairsBoundary :=
  (boundary_iff _).mpr (lift_endpoint
    SymmetricSpaceCompactBordification.actual_projection_covering c.deformation
    c.neighborhood c.collapses x.val x.property)

/-- The actual continuous endpoint map to the whole geometric boundary cover. -/
def endpoint : C(Cover c.neighborhood, BoundaryCover) :=
  ⟨fun x => ⟨(deformation c).homotopy (1, x.val), endpoint_mem c x⟩,
    ((deformation c).homotopy.continuous.comp
      (continuous_const.prodMk continuous_subtype_val)).subtype_mk _⟩

theorem endpoint_equivariant (g : principalSix) (x : Cover c.neighborhood) :
    endpoint c (g • x) = g • endpoint c x :=
  Subtype.ext (deformation_equivariant c g 1 x.val)

/-- The actual endpoint fixes each boundary point in the smaller neighborhood cover. -/
theorem endpoint_boundary (x : BoundaryCover) :
    endpoint c ⟨x.val, c.contains_boundary ((boundary_iff x.val).mp x.property)⟩ = x :=
  Subtype.ext (deformation_fixed c 1 x)

/-- Literal inclusion of the smaller neighborhood cover in the prescribed larger cover. -/
def inclusion : C(Cover c.neighborhood, Cover W) :=
  ⟨fun x => ⟨x.val, c.subset x.property⟩, continuous_subtype_val.subtype_mk _⟩

theorem inclusion_equivariant (g : principalSix) (x : Cover c.neighborhood) :
    inclusion c (g • x) = g • inclusion c x := rfl

/-- Literal inclusion of the boundary cover in the cover of W. -/
def boundaryToW (hAW : boundary principalSix ⊆ W) : C(BoundaryCover, Cover W) :=
  ⟨fun x => ⟨x.val, hAW ((boundary_iff x.val).mp x.property)⟩,
    continuous_subtype_val.subtype_mk _⟩

theorem boundaryToW_equivariant (hAW : boundary principalSix ⊆ W)
    (g : principalSix) (x : BoundaryCover) : boundaryToW hAW (g • x) = g • boundaryToW hAW x := rfl

/-- A genuine homotopy inside the W-cover from inclusion to the map through the boundary cover. -/
def homotopy (hAW : boundary principalSix ⊆ W) :
    ContinuousMap.Homotopy (inclusion c) ((boundaryToW hAW).comp (endpoint c)) where
  toFun z := ⟨(deformation c).homotopy (z.1, z.2.val),
    (deformation c).preserves z.1 z.2.val (c.subset z.2.property)⟩
  continuous_toFun := ((deformation c).homotopy.continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left x := Subtype.ext ((deformation c).zero x.val)
  map_one_left _ := rfl

/-- The lifted neighborhood homotopy is principal-six equivariant at every time. -/
theorem homotopy_equivariant (hAW : boundary principalSix ⊆ W)
    (g : principalSix) (t : I) (x : Cover c.neighborhood) :
    homotopy c hAW (t, g • x) = g • homotopy c hAW (t, x) :=
  Subtype.ext (deformation_equivariant c g t x.val)

/-- Projection recovers the actual assembled base deformation with the same time parameter. -/
theorem homotopy_projection (hAW : boundary principalSix ⊆ W)
    (t : I) (x : Cover c.neighborhood) :
    projection principalSix (homotopy c hAW (t, x)).val =
      c.deformation.homotopy (t, projection principalSix x.val) :=
  deformation_projection c t x.val

/-- The lifted neighborhood homotopy fixes every actual boundary point throughout. -/
theorem homotopy_boundary (hAW : boundary principalSix ⊆ W) (t : I) (x : BoundaryCover) :
    homotopy c hAW (t, ⟨x.val, c.contains_boundary ((boundary_iff x.val).mp x.property)⟩) =
      boundaryToW hAW x := Subtype.ext (deformation_fixed c t x)

end TernaryPoly.CoveringBoundaryDeformation.Actual
