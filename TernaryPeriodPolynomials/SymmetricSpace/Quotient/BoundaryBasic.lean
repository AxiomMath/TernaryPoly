module

public import TernaryPeriodPolynomials.SymmetricSpace.CompactBordification
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.Charts

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceQuotientBoundary
open Topology SymmetricSpaceRationalGluing SymmetricSpaceBordifiedQuotient
  SymmetricSpaceBordifiedPrincipalSix IntegralGL3Congruence

/-- The actual finite-transporter theorem supplies the literal principal-six quotient covering. -/
theorem actualCovering : IsCoveringMap (projection principalSix) :=
  SymmetricSpaceCompactBordification.actual_projection_covering

/-- A genuine local section of the actual orbit covering. -/
def localLift (x : Glued) : OpenPartialHomeomorph BordifiedOrbit Glued :=
  actualCovering.isLocalHomeomorph.localInverseAt x

@[simp] theorem localLift_symm (x : Glued) :
    (localLift x).symm=projection principalSix :=
  actualCovering.isLocalHomeomorph.localInverseAt_symm x

@[simp] theorem localLift_self (x : Glued) :
    localLift x (projection principalSix x)=x :=
  actualCovering.isLocalHomeomorph.localInverseAt_apply_self

theorem self_mem_localLift_source (x : Glued) :
    projection principalSix x∈(localLift x).source :=
  actualCovering.isLocalHomeomorph.apply_self_mem_localInverseAt_source

theorem self_mem_localLift_target (x : Glued) : x∈(localLift x).target :=
  actualCovering.isLocalHomeomorph.self_mem_localInverseAt_target

theorem projection_localLift (x : Glued) {q : BordifiedOrbit} (hq : q∈(localLift x).source) :
    projection principalSix (localLift x q)=q := by
  rw [←localLift_symm x]
  exact (localLift x).left_inv hq

/-- The already-constructed arithmetic manifold has the literal interior-orbit image. -/
theorem arithmeticEmbedding_range :
    Set.range arithmeticEmbedding=Set.range (interiorEmbedding principalSix) := by
  ext q
  constructor
  · rintro ⟨z,rfl⟩
    exact ⟨arithmeticInteriorHomeomorph z,rfl⟩
  · rintro ⟨z,rfl⟩
    refine ⟨arithmeticInteriorHomeomorph.symm z,?_⟩
    simp [arithmeticEmbedding]

theorem projection_preimage_arithmetic :
    projection principalSix ⁻¹' Set.range arithmeticEmbedding=Set.range embedding := by
  rw [arithmeticEmbedding_range,projection_preimage_interior]

theorem projection_arithmetic_iff (x : Glued) :
    projection principalSix x∈Set.range arithmeticEmbedding ↔ x∈Set.range embedding :=
  Set.ext_iff.mp projection_preimage_arithmetic x

end TernaryPoly.SymmetricSpaceQuotientBoundary
