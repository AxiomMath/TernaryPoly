module

public import TernaryPeriodPolynomials.Analysis.Compact.Interior.RelativeBoundaryInterior
public import TernaryPeriodPolynomials.Analysis.Compact.Interior.RelativeBoundaryPairAlgebra
public import TernaryPeriodPolynomials.GroupCohomology.HomCokernelKernelIso

@[expose] public section


noncomputable section
namespace TernaryPoly.CompactInteriorRelativeBoundary
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalSupport SingularLocalCoefficient SingularCoverNaturality EquivariantSingularSmall
open SingularBoundaryRestriction EquivariantSingularPairHomotopy
open SymmetricSpaceRationalGluing SymmetricSpaceBordifiedQuotient SymmetricSpaceBordifiedPrincipalSix
  IntegralGL3Congruence

/-- Actual equivariant relative Hom cochains of the whole bordification relative to a covering preimage. -/
abbrev ambientRelativeCochains (W : Set BordifiedOrbit) (V : Rep.{0} ℚ principalSix) :=
  relativeHomCochains principalSix (TopCat.of Glued) (wholeProjection ⁻¹' W) V

/-- The literal ambient-cochain inclusion of an actual relative Hom complex is precomposition
with the genuine relative chain quotient. -/
def ambientRelativeInclusion (W : Set BordifiedOrbit) (V : Rep.{0} ℚ principalSix) :
    ambientRelativeCochains W V ⟶ absoluteCochains V :=
  homPullback (cokernel.π (EquivariantSingularPairHomotopy.inclusion principalSix (TopCat.of Glued)
    (wholeProjection ⁻¹' W))) V

/-- The actual Hom-kernel and geometric local-cochain kernel agree for every support. -/
def supportKernelIso (K : Set BordifiedOrbit) (V : Rep.{0} ℚ principalSix) :
    kernel (homPullback (EquivariantSingularPairHomotopy.inclusion principalSix (TopCat.of Glued)
      (wholeProjection ⁻¹' Kᶜ)) V) ≅ supportCochains wholeProjection V K := by
  refine kernel.mapIso _ _ (SingularLocalCoefficient.cochainIso wholeProjection wholeQuotientCovering V)
    (SingularLocalCoefficient.cochainIso (restrictedProjection wholeProjection Kᶜ)
      (restrictedQuotientCovering wholeProjection Kᶜ) V) ?_
  exact (cochainIso_pullback (restrictedProjection wholeProjection Kᶜ) wholeProjection
    (TopCat.ofHom ⟨(Subtype.val : (wholeProjection ⁻¹' Kᶜ) → Glued),continuous_subtype_val⟩)
    (TopCat.ofHom ⟨(Subtype.val : (Kᶜ : Set BordifiedOrbit) → BordifiedOrbit),continuous_subtype_val⟩)
    (by ext x; rfl) (restrictedQuotientCovering wholeProjection Kᶜ) wholeQuotientCovering (fun _ _ => rfl) V)

/-- Actual equivariant Hom-relative cochains identify with literal geometric support cochains. -/
def supportRelativeIso (K : Set BordifiedOrbit) (V : Rep.{0} ℚ principalSix) :
    ambientRelativeCochains Kᶜ V ≅ supportCochains wholeProjection V K :=
  HomCokernelKernel.cochainIso
    (EquivariantSingularPairHomotopy.inclusion principalSix (TopCat.of Glued) (wholeProjection ⁻¹' Kᶜ)) V ≪≫
      supportKernelIso K V

/-- The support-relative identification preserves the literal ambient cochain under the
equivariant-to-geometric cochain isomorphism. -/
theorem supportRelativeIso_inclusion (K : Set BordifiedOrbit) (V : Rep.{0} ℚ principalSix) :
    (supportRelativeIso K V).hom ≫ supportInclusion wholeProjection V K =
      ambientRelativeInclusion Kᶜ V ≫
        (SingularLocalCoefficient.cochainIso wholeProjection wholeQuotientCovering V).hom := by
  unfold supportRelativeIso supportKernelIso
  erw [Iso.trans_hom,Category.assoc,kernel.lift_ι,← Category.assoc,
    HomCokernelKernel.cochainIso_hom_inclusion]
  rfl

end TernaryPoly.CompactInteriorRelativeBoundary
