module

public import TernaryPeriodPolynomials.Topology.Rational.Relative.SupportQuotient

@[expose] public section

noncomputable section
namespace TernaryPoly.RationalRelativeSupport
open CategoryTheory Limits
variable {C : Type*} [Category C] [Abelian C]
variable {A B M N : C} (a : A ⟶ M) (b : B ⟶ N)

/-- Literal quotient projections respect the direct sum of two subobject inclusions. -/
theorem biprod_quotient_condition :
    biprod.map a b ≫ biprod.map (cokernel.π a) (cokernel.π b) = 0 := by
  apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp

/-- The cokernel of a direct sum is the direct sum of the actual cokernels. -/
def cokernelBiprodIso : cokernel (biprod.map a b) ≅ cokernel a ⊞ cokernel b where
  hom := cokernel.desc _ (biprod.map (cokernel.π a) (cokernel.π b)) (biprod_quotient_condition a b)
  inv := biprod.desc
    (cokernel.desc a (biprod.inl ≫ cokernel.π (biprod.map a b)) (by
      rw [← biprod.inl_map_assoc, cokernel.condition, comp_zero]))
    (cokernel.desc b (biprod.inr ≫ cokernel.π (biprod.map a b)) (by
      rw [← biprod.inr_map_assoc, cokernel.condition, comp_zero]))
  hom_inv_id := by
    apply (cancel_epi (cokernel.π (biprod.map a b))).mp
    rw [cokernel.π_desc_assoc, Category.comp_id]
    apply biprod.hom_ext'
    · simp only [biprod.inl_map_assoc, biprod.inl_desc]
      exact cokernel.π_desc _ _ _
    · simp only [biprod.inr_map_assoc, biprod.inr_desc]
      exact cokernel.π_desc _ _ _
  inv_hom_id := by
    apply biprod.hom_ext'
    · apply (cancel_epi (cokernel.π a)).mp
      simp only [biprod.inl_desc_assoc, cokernel.π_desc_assoc, Category.comp_id]
      rw [Category.assoc, cokernel.π_desc, biprod.inl_map]
    · apply (cancel_epi (cokernel.π b)).mp
      simp only [biprod.inr_desc_assoc, cokernel.π_desc_assoc, Category.comp_id]
      rw [Category.assoc, cokernel.π_desc, biprod.inr_map]

/-- The direct-sum quotient comparison preserves the actual pair of projections. -/
theorem cokernelBiprodIso_projection :
    cokernel.π (biprod.map a b) ≫ (cokernelBiprodIso a b).hom =
      biprod.map (cokernel.π a) (cokernel.π b) := cokernel.π_desc _ _ _

end TernaryPoly.RationalRelativeSupport
