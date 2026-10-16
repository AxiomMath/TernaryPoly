module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.GluingCompactMaps

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothDeRhamGluing
open Set SmoothLocalDeRham SmoothCoveringDeRham SymmetricSpaceCharts SymmetricSpaceCovering
open scoped ContDiff Topology

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {ρ : Representation ℝ DeckGroup F} {U V : Set OrbitSpace} {n : ℕ}

/-- Exactness at the middle compact Mayer-Vietoris term. The cancellation identity forces
both forms to have the same actual projected support, contained in the intersection. -/
theorem compact_kernel_exact (hU : IsOpen U) (hV : IsOpen V)
    (p : CompactSupportForm ρ U n × CompactSupportForm ρ V n) :
    unionExtension ρ hU hV n p = 0 ↔
      ∃ w : CompactSupportForm ρ (U ∩ V) n, intersectionExtension ρ hU hV n w = p := by
  constructor
  · intro hp
    have hab : ∀ x, (p.1.val.val : RawForm Coordinates F n) x = -(p.2.val.val : RawForm Coordinates F n) x := by
      intro x
      have he := congrArg (fun w : CompactSupportForm ρ (U ∪ V) n => (w.val.val : RawForm Coordinates F n) x) hp
      change (p.1.val.val : RawForm Coordinates F n) x + (p.2.val.val : RawForm Coordinates F n) x = 0 at he
      exact eq_neg_of_add_eq_zero_left he
    have hsupport : quotientSupport p.1.val = quotientSupport p.2.val := by
      unfold quotientSupport
      congr 1
      apply congrArg (fun s => coordinateProjection '' s)
      ext x
      change (p.1.val.val : RawForm Coordinates F n) x ≠ 0 ↔ (p.2.val.val : RawForm Coordinates F n) x ≠ 0
      rw [hab x, neg_ne_zero]
    have hi : quotientSupport p.1.val ⊆ U ∩ V := by
      intro q hq
      exact ⟨p.1.property.2 hq, p.2.property.2 (hsupport ▸ hq)⟩
    let z := compactRestrictOfSupport (inter_subset_left : U ∩ V ⊆ U) p.1 hi
    refine ⟨z, ?_⟩
    apply Prod.ext
    · exact extend_compactRestrictOfSupport (hU.inter hV) inter_subset_left p.1 hi
    · apply Subtype.ext
      apply Subtype.ext
      apply Form.ext
      intro x hx
      change -(p.1.val.val : RawForm Coordinates F n) x = (p.2.val.val : RawForm Coordinates F n) x
      rw [hab x, neg_neg]
  · rintro ⟨w, rfl⟩
    exact unionExtension_intersectionExtension ρ hU hV n w

end TernaryPoly.SmoothDeRhamGluing
