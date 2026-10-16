module

public import TernaryPeriodPolynomials.SymmetricSpace.Quotient.BoundaryBoundary

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceQuotientBoundary
open Topology SymmetricSpaceRationalGluing SymmetricSpaceBordifiedQuotient
  SymmetricSpaceBordifiedPrincipalSix IntegralGL3Congruence
open SymmetricSpaceBoundaryCharts

/-- Literal quotient charts in the product half-space model used for collar constructions. -/
def productChart (x : Glued) : OpenPartialHomeomorph BordifiedOrbit ProductModel :=
  (quotientChart x).transHomeomorph productHalfSpaceHomeomorph.symm

@[simp] theorem productChart_source (x : Glued) :
    (productChart x).source=(quotientChart x).source := rfl

@[simp] theorem productChart_symm_apply (x : Glued) (p : ProductModel) :
    (productChart x).symm p=(quotientChart x).symm (productHalfSpaceHomeomorph p) := rfl

theorem productChart_symm_boundary (x : Glued) (p : ProductModel) :
    (productChart x).symm p∈boundary principalSix ↔ p.2.val=0 := by
  rw [productChart_symm_apply,quotientChart_symm_boundary,productHalfSpace_height]

theorem productChart_symm_interior (x : Glued) (p : ProductModel) :
    (productChart x).symm p∈Set.range arithmeticEmbedding ↔ 0<p.2.val := by
  rw [productChart_symm_apply,quotientChart_symm_interior,productHalfSpace_height]

/-- Exact positive-height criterion for local inward-deformation consumers. -/
theorem productChart_interior (x : Glued) {q : BordifiedOrbit}
    (hq : q∈(productChart x).source) :
    q∈Set.range arithmeticEmbedding ↔ 0<(productChart x q).2.val := by
  have h := productChart_symm_interior x (productChart x q)
  rw [(productChart x).left_inv hq] at h
  exact h

theorem productChart_boundary (x : Glued) {q : BordifiedOrbit}
    (hq : q∈(productChart x).source) :
    q∈boundary principalSix ↔ (productChart x q).2.val=0 := by
  have h := productChart_symm_boundary x (productChart x q)
  rw [(productChart x).left_inv hq] at h
  exact h

theorem self_mem_productChart (x : Glued) :
    projection principalSix x∈(productChart x).source := self_mem_quotientChart x

theorem productCharts_cover (q : BordifiedOrbit) :
    ∃ x : Glued,q∈(productChart x).source := by
  refine ⟨q.out,?_⟩
  have h := self_mem_productChart q.out
  simpa only [projection,Quotient.out_eq] using h

end TernaryPoly.SymmetricSpaceQuotientBoundary
