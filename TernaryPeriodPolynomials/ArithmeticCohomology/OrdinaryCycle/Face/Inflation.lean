module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Parabolic.Groups
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.LowDegree.OneTransport

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryFaceInflation
open CategoryTheory groupCohomology OrdinaryParabolicGroups OrdinaryBoundaryCommonRoot
open LowDegreeHochschildSerre BoundaryCochainNormalization RadicalFirstCohomologyLattice

/-- Literal plane normal form for the actual 26-covector representation. The sole cohomological premise is the genuine Levi-fixed radical H1 vanishing assertion. -/
theorem plane_normalized (n : ℕ) (e : ℤ)
    (hvan : ∀ v : groupCohomology (radicalRep planeAction (Rep.of (planeCoefficients n e))) 1,
      (∀ q,(cohomologyRep planeAction (Rep.of (planeCoefficients n e)) 1).ρ q v=v) → v=0)
    (c : cocycles₁ (Rep.of (planeParabolicCoefficients n e))) :
    ∃ u : Coefficients n,
      (∀ r : planeRadical,normalize (Rep.of (planeParabolicCoefficients n e)) c u
        (planeEquiv (SemidirectProduct.inl r))=0) ∧
      ∀ g,normalize (Rep.of (planeParabolicCoefficients n e)) c u g ∈
        Representation.invariants ((coefficientAction n e).comp planeRadical.subtype) := by
  obtain ⟨u,hu,hv⟩ := exists_normalized_along_equiv planeAction planeEquiv
    (Rep.of (planeParabolicCoefficients n e)) hvan c
  refine ⟨u,hu,?_⟩
  intro g r
  have h := hv g r
  change planeCoefficients n e (SemidirectProduct.inl r) _ = _ at h
  rwa [planeCoefficients_inl] at h

/-- Literal line normal form, preserving the independent unit factor and full lower GL2. -/
theorem line_normalized (n : ℕ) (e : ℤ)
    (hvan : ∀ v : groupCohomology (radicalRep lineAction (Rep.of (lineCoefficients n e))) 1,
      (∀ q,(cohomologyRep lineAction (Rep.of (lineCoefficients n e)) 1).ρ q v=v) → v=0)
    (c : cocycles₁ (Rep.of (lineParabolicCoefficients n e))) :
    ∃ u : Coefficients n,
      (∀ r : lineRadical,normalize (Rep.of (lineParabolicCoefficients n e)) c u
        (lineEquiv (SemidirectProduct.inl r))=0) ∧
      ∀ g,normalize (Rep.of (lineParabolicCoefficients n e)) c u g ∈
        Representation.invariants ((coefficientAction n e).comp lineRadical.subtype) := by
  obtain ⟨u,hu,hv⟩ := exists_normalized_along_equiv lineAction lineEquiv
    (Rep.of (lineParabolicCoefficients n e)) hvan c
  refine ⟨u,hu,?_⟩
  intro g r
  have h := hv g r
  change lineCoefficients n e (SemidirectProduct.inl r) _ = _ at h
  rwa [lineCoefficients_inl] at h

end TernaryPoly.OrdinaryFaceInflation
