module

public import TernaryPeriodPolynomials.SymmetricSpace.CoveringGeneral
public import TernaryPeriodPolynomials.SymmetricSpace.CoveringTopology
public import TernaryPeriodPolynomials.SymmetricSpace.Arithmetic.SymmetricSpaceArithmeticProperConsumer

@[expose] public section

noncomputable section
open Topology Set
namespace TernaryPoly.SymmetricSpaceCovering
open SymmetricSpacePositive SymmetricSpaceArithmeticProper IntegralGL3Congruence

/-- The actual principal-six subgroup inside the sum-covector fixer. -/
abbrev DeckGroup := principalSixInK

/-- The exact inclusion into integral matrices, through the fixed subgroup K. -/
def deckInclusion : DeckGroup →* IntegralGL :=
  ModThreeGoodAction.K.subtype.comp principalSixInK.subtype

theorem deckInclusion_injective : Function.Injective deckInclusion :=
  Subtype.val_injective.comp Subtype.val_injective

@[simp] theorem deck_smul (g : DeckGroup) (S : Space) :
    g • S=act (realIntegral (deckInclusion g)) S := rfl

instance deckContinuous : ContinuousConstSMul DeckGroup Space where
  continuous_const_smul g := continuous_act (realIntegral (deckInclusion g))

/-- Compact transporter finiteness is proved for this actual subgroup action. -/
theorem deck_compact_transporters (C D : Set Space) (hC : IsCompact C) (hD : IsCompact D) :
    {g : DeckGroup | ((g • ·) '' C ∩ D).Nonempty}.Finite := by
  apply Set.Finite.of_finite_image (f := deckInclusion)
  · apply (compact_transporter_finite C D hC hD).subset
    rintro _ ⟨g,hg,rfl⟩
    obtain ⟨_,⟨S,hS,rfl⟩,hT⟩ := hg
    exact ⟨S,hS,hT⟩
  · exact deckInclusion_injective.injOn

instance deckProperlyDiscontinuous : ProperlyDiscontinuousSMul DeckGroup Space :=
  ⟨fun hC hD => deck_compact_transporters _ _ hC hD⟩

/-- Freeness comes from finite actual stabilizers and the principal-six torsion theorem. -/
theorem deck_fixed_eq_one (g : DeckGroup) (S : Space) (h : g • S=S) : g=1 := by
  apply Subtype.ext
  exact principalSixInK_fixed_eq_one g.val g.property S h

instance deckFree : IsCancelSMul DeckGroup Space :=
  isCancelSMul_iff_eq_one_of_smul_eq.mpr deck_fixed_eq_one

/-- The orbit quotient uses the literal principal-six action on actual positive forms. -/
abbrev OrbitSpace := Quotient (MulAction.orbitRel DeckGroup Space)

def quotientProjection : Space → OrbitSpace := Quotient.mk _

/-- The actual orbit projection is a quotient covering map. -/
theorem quotientProjection_quotientCovering : IsQuotientCoveringMap quotientProjection DeckGroup :=
  quotientCovering_of_finite_transporters deck_compact_transporters deck_fixed_eq_one

/-- The actual orbit projection is a covering map, with no assumed arithmetic hypotheses. -/
theorem quotientProjection_covering : IsCoveringMap quotientProjection :=
  quotientProjection_quotientCovering.isCoveringMap

theorem orbitSpace_hausdorff : T2Space OrbitSpace := inferInstance

theorem quotientProjection_surjective : Function.Surjective quotientProjection :=
  quotientProjection_quotientCovering.surjective

/-- Every actual positive form has an open neighborhood disjoint from its nonidentity translates. -/
theorem actual_disjoint_neighborhood (S : Space) :
    ∃ U : Set Space, IsOpen U ∧ S∈U ∧ ∀ g : DeckGroup, g≠1 → Disjoint ((g • ·) '' U) U :=
  exists_open_disjoint_translates deck_compact_transporters deck_fixed_eq_one S

end TernaryPoly.SymmetricSpaceCovering
