module

public import TernaryPeriodPolynomials.SymmetricSpace.CompactBordification
public import Mathlib.Topology.Homotopy.Contractible

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBordifiedContractible
open SymmetricSpacePositive SymmetricSpaceRationalGluing SymmetricSpaceBordifiedQuotient
  SymmetricSpaceBordifiedPrincipalSix IntegralGL3Congruence

/-- The designated interior of the actual compact principal-six orbit bordification. -/
def arithmeticInterior : Set BordifiedOrbit := Set.range arithmeticEmbedding

/-- The two existing presentations of the actual arithmetic interior have exactly the same range. -/
theorem arithmeticInterior_eq :
    arithmeticInterior = Set.range (interiorEmbedding principalSix) := by
  change Set.range (interiorEmbedding principalSix ∘ arithmeticInteriorHomeomorph) = _
  rw [Set.range_comp, arithmeticInteriorHomeomorph.surjective.range_eq, Set.image_univ]

/-- The actual downstairs arithmetic interior is open in the existing quotient topology. -/
theorem arithmeticInterior_open : IsOpen arithmeticInterior :=
  arithmeticEmbedding_isOpenEmbedding.isOpen_range

/-- The preimage under the genuine principal-six covering is exactly the actual embedded Space. -/
theorem projection_preimage_arithmeticInterior :
    projection principalSix ⁻¹' arithmeticInterior = Set.range embedding := by
  rw [arithmeticInterior_eq, projection_preimage_interior]

/-- The covering's actual interior preimage is homeomorphic to the concrete contractible Space. -/
def preimageInteriorHomeomorph :
    (projection principalSix ⁻¹' arithmeticInterior) ≃ₜ Space :=
  (Homeomorph.setCongr projection_preimage_arithmeticInterior).trans
    embedding_isOpenEmbedding.isEmbedding.toHomeomorph.symm

/-- This homeomorphism identifies the actual inclusion with the given symmetric-space embedding. -/
theorem preimageInteriorHomeomorph_embedding
    (x : projection principalSix ⁻¹' arithmeticInterior) :
    embedding (preimageInteriorHomeomorph x) = x.val := by
  have h := embedding_isOpenEmbedding.isEmbedding.toHomeomorph.apply_symm_apply
    (Homeomorph.setCongr projection_preimage_arithmeticInterior x)
  exact congrArg Subtype.val h

/-- The actual preimage interior is genuinely contractible, independently of any inward homotopy. -/
instance preimageInterior_contractible :
    ContractibleSpace (projection principalSix ⁻¹' arithmeticInterior) :=
  preimageInteriorHomeomorph.contractibleSpace

end TernaryPoly.SymmetricSpaceBordifiedContractible
