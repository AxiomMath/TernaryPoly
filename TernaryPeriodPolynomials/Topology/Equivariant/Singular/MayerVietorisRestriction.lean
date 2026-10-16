module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.MayerVietorisSeparated

@[expose] public section


noncomputable section
namespace TernaryPoly.EquivariantSingularMayerVietoris
open CategoryTheory HomologicalComplex EquivariantSingularSmall EquivariantSingularResolution
open SphereOddDegree

variable (G : Type) [Group G] (E : TopCat.{0}) [MulAction G E] [ContinuousConstSMul G E]
  (𝒰 : OpenCoverData E) (h𝒰 : InvariantCover G E 𝒰)
  (S : Set E) (hS : InvariantSet G E S) (hmem : S ∈ 𝒰.sets)

/-- Inclusion of subordinate chains through small chains is the actual ambient inclusion. -/
theorem subordinateToSmall_inclusion :
    subordinateToSmall G E 𝒰 h𝒰 S hS hmem ≫ smallInclusion G E 𝒰 h𝒰 =
      subordinateInclusion G E S hS := by
  apply HomologicalComplex.hom_ext
  intro n
  ext c
  rfl

/-- Restriction through small cochains agrees literally with direct subordinate restriction. -/
theorem subordinateToSmall_restriction (W : Rep.{0} ℚ G) :
    smallRestriction G E 𝒰 h𝒰 W ≫ homPullback (subordinateToSmall G E 𝒰 h𝒰 S hS hmem) W =
      homPullback (subordinateInclusion G E S hS) W := by
  change homPullback _ W ≫ homPullback _ W = _
  rw [← homPullback_comp, subordinateToSmall_inclusion]

end TernaryPoly.EquivariantSingularMayerVietoris
