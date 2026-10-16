module

public import TernaryPeriodPolynomials.SymmetricSpace.Glued.ArithmeticProper
public import TernaryPeriodPolynomials.SymmetricSpace.Bordified.Covering

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceCompactBordification
open Topology SymmetricSpaceRationalGluing SymmetricSpaceArithmeticProper
  SymmetricSpaceBordifiedQuotient SymmetricSpaceBordifiedPrincipalSix IntegralGL3Congruence

/-- Actual integral compact transporter finiteness restricts to every subgroup. -/
theorem subgroup_compact_transporters (H : Subgroup IntegralGL)
    (C D : Set Glued) (hC : IsCompact C) (hD : IsCompact D) :
    {g : H | ((g • ·) '' C ∩ D).Nonempty}.Finite := by
  apply Set.Finite.of_finite_image (f := H.subtype)
  · apply (SymmetricSpaceGluedArithmetic.compact_transporter_finite C D hC hD).subset
    rintro _ ⟨g,hg,rfl⟩
    exact hg
  · exact Subtype.val_injective.injOn

/-- Every actual arithmetic subgroup orbit quotient is Hausdorff, including at the boundary. -/
theorem quotient_hausdorff (H : Subgroup IntegralGL) : T2Space (QuotientSpace H) :=
  hausdorff_of_finite_transporters H (subgroup_compact_transporters H)

/-- Every finite-index arithmetic subgroup has a compact actual bordified orbit quotient. -/
theorem quotient_compact (H : Subgroup IntegralGL) [H.FiniteIndex] :
    CompactSpace (QuotientSpace H) := by
  let := quotient_hausdorff H
  exact SymmetricSpaceBordifiedQuotient.compact_of_hausdorff H

/-- The exact principal-six action is free on the full bordification. -/
theorem principalSix_free (g : principalSix) (x : Glued) (hx : g • x=x) : g=1 :=
  principalSix_fixed_eq_one SymmetricSpaceGluedArithmetic.compact_transporter_finite g x hx

/-- The actual projection, with its existing quotient topology, is a genuine covering. -/
theorem actual_projection_covering : IsCoveringMap (projection principalSix) :=
  projection_covering SymmetricSpaceGluedArithmetic.compact_transporter_finite

/-- The exact principal-six arithmetic quotient admits the constructed compact Hausdorff
bordification with compact boundary and its original interior as an open dense subspace. -/
theorem actual_compact_bordification :
    T2Space BordifiedOrbit ∧ CompactSpace BordifiedOrbit ∧
    IsCoveringMap (projection principalSix) ∧ IsCompact (boundary principalSix) ∧
    IsOpenEmbedding arithmeticEmbedding ∧ DenseRange arithmeticEmbedding :=
  SymmetricSpaceBordifiedPrincipalSix.actual_compact_bordification
    SymmetricSpaceGluedArithmetic.compact_transporter_finite

end TernaryPoly.SymmetricSpaceCompactBordification
