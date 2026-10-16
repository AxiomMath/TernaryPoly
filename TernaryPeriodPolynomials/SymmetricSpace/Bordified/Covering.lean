module

public import TernaryPeriodPolynomials.SymmetricSpace.Bordified.PrincipalSix
public import TernaryPeriodPolynomials.ArithmeticGroup.GL3Congruence.Consumer

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBordifiedPrincipalSix
open Topology SymmetricSpaceRationalGluing SymmetricSpaceArithmeticProper
  SymmetricSpaceBordifiedQuotient IntegralGL3Congruence

variable (hfinite : ∀ C D : Set Glued, IsCompact C → IsCompact D →
  {g : IntegralGL | ((g • ·) '' C ∩ D).Nonempty}.Finite)

include hfinite

/-- Actual finite integral transporters pass to the exact principal-six subgroup. -/
theorem principalSix_compact_transporters (C D : Set Glued) (hC : IsCompact C) (hD : IsCompact D) :
    {g : principalSix | ((g • ·) '' C ∩ D).Nonempty}.Finite := by
  apply Set.Finite.of_finite_image (f := principalSix.subtype)
  · apply (hfinite C D hC hD).subset
    rintro _ ⟨g,hg,rfl⟩
    exact hg
  · exact Subtype.val_injective.injOn

/-- Finite stabilizers and the proved level-six torsion theorem give freeness on the boundary too. -/
theorem principalSix_fixed_eq_one (g : principalSix) (x : Glued) (hg : g • x = x) : g = 1 := by
  let : ProperlyDiscontinuousSMul principalSix Glued :=
    ⟨fun hC hD => principalSix_compact_transporters hfinite _ _ hC hD⟩
  let : Finite (MulAction.stabilizer principalSix x) :=
    (ProperlyDiscontinuousSMul.finite_stabilizer x).to_subtype
  apply principalSix_subgroup_finiteOrder_eq_one
  exact (MulAction.stabilizer principalSix x).subtype.isOfFinOrder
    (isOfFinOrder_of_finite (⟨g,hg⟩ : MulAction.stabilizer principalSix x))

/-- The exact arithmetic quotient projection becomes a genuine covering of the bordification. -/
theorem projection_covering : IsCoveringMap (projection principalSix) :=
  SymmetricSpaceCovering.covering_of_finite_transporters
    (principalSix_compact_transporters hfinite) (principalSix_fixed_eq_one hfinite)

theorem bordified_hausdorff : T2Space BordifiedOrbit :=
  hausdorff_of_finite_transporters principalSix (principalSix_compact_transporters hfinite)


theorem bordified_compact : CompactSpace BordifiedOrbit := by
  let := bordified_hausdorff hfinite
  exact compact_of_hausdorff

theorem boundary_compact : IsCompact (boundary principalSix) := by
  let := bordified_compact hfinite
  exact (boundary_closed principalSix).isCompact

/-- The precise remaining geometric assembly gate: finite integral compact transporters supply
an actual compact Hausdorff principal-six bordification and its actual quotient covering. -/
theorem actual_compact_bordification :
    T2Space BordifiedOrbit ∧ CompactSpace BordifiedOrbit ∧
    IsCoveringMap (projection principalSix) ∧ IsCompact (boundary principalSix) ∧
    IsOpenEmbedding arithmeticEmbedding ∧ DenseRange arithmeticEmbedding :=
  ⟨bordified_hausdorff hfinite,bordified_compact hfinite,projection_covering hfinite,
    boundary_compact hfinite,arithmeticEmbedding_isOpenEmbedding,arithmeticEmbedding_dense⟩

end TernaryPoly.SymmetricSpaceBordifiedPrincipalSix
