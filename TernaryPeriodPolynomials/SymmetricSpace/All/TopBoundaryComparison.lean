module

public import TernaryPeriodPolynomials.Analysis.Compact.Interior.RelativeBoundary

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceAllTopBoundary
open CategoryTheory Limits HomologicalComplex IntegralGL3Congruence
open SingularBoundaryRestriction SingularLocalCoefficient SingularLocalSupport
open CompactInteriorRelativeBoundary SymmetricSpaceBordifiedCohomology

/-- The literal compact/relative comparison and proved interior cohomology isomorphism
identify vanishing of the geometric relative-to-absolute map with compact support forgetting. -/
theorem geometric_relative_zero_iff_compactForget_zero (V : Rep.{0} ℚ principalSix) (k : ℕ) :
    RelativeCochainSequence.relativeMap (geometricBoundaryRestriction V) k = 0 ↔
      compactForget interiorCover V k = 0 := by
  rw [← compactGeometricRelativeIso_toOrdinary V k]
  constructor
  · intro h
    change homologyMap (kernel.ι (geometricBoundaryRestriction V)) k = 0 at h
    rw [h]
    erw [zero_comp,comp_zero]
  · intro h
    apply (cancel_epi (compactGeometricRelativeIso V k).hom).mp
    rw [comp_zero]
    apply (cancel_mono (homologyMap (interiorRestriction V) k)).mp
    erw [zero_comp,Category.assoc]
    exact h

/-- The original equivariant relative model retains the same compactForget-zero
condition through its actual cochain and interior restriction isomorphisms. -/
theorem relative_zero_iff_compactForget_zero (V : Rep.{0} ℚ principalSix) (k : ℕ) :
    relativeToAbsolute V k = 0 ↔ compactForget interiorCover V k = 0 := by
  rw [← compactRelativeIso_toOrdinary V k]
  constructor
  · intro h
    rw [h]
    simp only [zero_comp,comp_zero]
  · intro h
    apply (cancel_epi (compactRelativeIso V k).hom).mp
    rw [comp_zero]
    apply (cancel_mono (homologyMap (cochainIso wholeProjection wholeQuotientCovering V).hom k)).mp
    rw [zero_comp]
    apply (cancel_mono (homologyMap (interiorRestriction V) k)).mp
    erw [zero_comp,Category.assoc,Category.assoc]
    exact h

end TernaryPoly.SymmetricSpaceAllTopBoundary
