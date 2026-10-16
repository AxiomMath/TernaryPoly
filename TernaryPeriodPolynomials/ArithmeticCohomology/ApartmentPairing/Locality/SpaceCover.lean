module

public import TernaryPeriodPolynomials.Analysis.Compact.Interior.RelativeBoundaryInterior
public import TernaryPeriodPolynomials.SymmetricSpace.Relative.CapComparison

@[expose] public section


/-!
# Lemma 3.3, G3: the symmetric space as a quotient covering of the interior of the orbit bordification

`pS : Space ⟶ ↥(boundary principalSix)ᶜ` is the covering of the interior arithmetic quotient by the
symmetric space with deck group `Γ(6)` (the interior covering `interiorCover` followed by the identification
`interiorBase` of the interior orbit space with the complement of the boundary).  It is a quotient covering
map (`pS_isQuotientCovering`, instance `pSFact`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

open CategoryTheory TernaryPoly TernaryPoly.SymmetricSpaceBordifiedQuotient
  TernaryPoly.SymmetricSpaceBordifiedPrincipalSix TernaryPoly.IntegralGL3Congruence
  TernaryPoly.SymmetricSpaceBordifiedCohomology TernaryPoly.SymmetricSpacePositive

/-- The interior orbit space as the complement of the boundary of the orbit bordification. -/
def interiorBase : InteriorOrbit principalSix ≃ₜ ↥(boundary principalSix)ᶜ :=
  (interiorEmbedding_isOpenEmbedding principalSix).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (by rw [boundary, compl_compl]))

/-- The covering of the interior arithmetic quotient by the symmetric space, with base the complement
of the boundary. -/
def pS : TopCat.of Space ⟶ TopCat.of ↥(boundary principalSix)ᶜ :=
  interiorCover ≫ TopCat.ofHom ⟨interiorBase, interiorBase.continuous⟩

theorem pS_isQuotientCovering : IsQuotientCoveringMap pS principalSix :=
  interiorCover_isQuotientCovering.homeomorph_comp interiorBase

instance pSFact : Fact (IsQuotientCoveringMap pS principalSix) := ⟨pS_isQuotientCovering⟩

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
