module

public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.LowDegree.Inflation

@[expose] public section


open CategoryTheory CategoryTheory.Limits groupCohomology
noncomputable section
namespace TernaryPoly.LowDegreeHochschildSerre

variable {N Q : Type} [Group N] [Group Q] (φ : Q →* MulAut N)
variable (A : Rep ℚ (G φ))

/-- Genuine degree-two Hochschild–Serre vanishing for a semidirect product.

All three hypotheses use the literal quotient actions: coefficient action on A^N and
inverse-conjugation pullback with coefficient action on Hᵏ(N,A). The proof uses explicit
actual cocycles and coboundaries, with no spectral-sequence or comparison assumption. -/
theorem isZero_H2
    (hbase : IsZero (groupCohomology (invariantsRep φ A) 2))
    (hcross : IsZero (groupCohomology (cohomologyRep φ A 1) 1))
    (hradical : ∀ x : groupCohomology (radicalRep φ A) 2,
      (∀ q, (cohomologyRep φ A 2).ρ q x = x) → x = 0) :
    IsZero (groupCohomology A 2) := by
  apply ModuleCat.isZero_of_iff_subsingleton.mpr
  have hz (x : groupCohomology A 2) : x = 0 := by
    induction x using H2_induction_on with
    | h c =>
      obtain ⟨c₁,he₁,hc₁⟩ := normalize_first φ A c (restriction_primitive φ A hradical c)
      obtain ⟨c₂,he₂,hc₂,hcross₂⟩ := normalize_cross_classes φ A hcross c₁ hc₁
      obtain ⟨c₃,he₃,hc₃⟩ := normalize_cross_principal φ A c₂ hc₂ hcross₂
      rw [← he₁, ← he₂, ← he₃]
      exact mixed_class_zero φ A hbase c₃ hc₃
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

end TernaryPoly.LowDegreeHochschildSerre
