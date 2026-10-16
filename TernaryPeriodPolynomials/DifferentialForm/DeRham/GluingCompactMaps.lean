module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.GluingGluing
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.GluingExhaustion

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothDeRhamGluing
open Set Filter Function SmoothLocalDeRham SmoothCoveringDeRham
  SymmetricSpaceCharts SymmetricSpaceCovering
open scoped ContDiff Topology

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) {U V : Set OrbitSpace} (hU : IsOpen U) (hV : IsOpen V) (n : ℕ)

/-- The compact Mayer-Vietoris first map extends to both sides with signs plus and minus. -/
def intersectionExtension : CompactSupportForm ρ (U ∩ V) n →ₗ[ℝ]
    CompactSupportForm ρ U n × CompactSupportForm ρ V n :=
  (compactZeroExtend (hU.inter hV) inter_subset_left n).prod
    (-compactZeroExtend (hU.inter hV) inter_subset_right n)

/-- The compact Mayer-Vietoris second map adds the actual zero extensions to the union. -/
def unionExtension : (CompactSupportForm ρ U n × CompactSupportForm ρ V n) →ₗ[ℝ]
    CompactSupportForm ρ (U ∪ V) n :=
  (compactZeroExtend hU (subset_union_left : U ⊆ U ∪ V) n).comp
    (LinearMap.fst ℝ (CompactSupportForm ρ U n) (CompactSupportForm ρ V n)) +
  (compactZeroExtend hV (subset_union_right : V ⊆ U ∪ V) n).comp
    (LinearMap.snd ℝ (CompactSupportForm ρ U n) (CompactSupportForm ρ V n))

theorem unionExtension_intersectionExtension (w : CompactSupportForm ρ (U ∩ V) n) :
    unionExtension ρ hU hV n (intersectionExtension ρ hU hV n w) = 0 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Form.ext
  intro x hx
  change (w.val.val : RawForm Coordinates F n) x + -(w.val.val : RawForm Coordinates F n) x = 0
  exact add_neg_cancel _

theorem intersectionExtension_injective : Function.Injective (intersectionExtension ρ hU hV n) := by
  intro w z h
  apply compactZeroExtend_injective (hU.inter hV) (inter_subset_left : U ∩ V ⊆ U) n
  exact congrArg Prod.fst h

/-- Surjectivity of compact Mayer-Vietoris, proved using a genuine smooth partition on the
actual compact projected support and support-controlled restriction/zero extension. -/
theorem unionExtension_surjective : Function.Surjective (unionExtension ρ hU hV n) := by
  intro w
  obtain ⟨f, hf⟩ := exists_quotient_partition (K := quotientSupport w.val) isClosed_closure hU hV w.property.2
  let a := compactScalarMultiply (ρ := ρ) (f 0) (f 0).contMDiff.contMDiffOn n w
  let b := compactScalarMultiply (ρ := ρ) (f 1) (f 1).contMDiff.contMDiffOn n w
  have ha : quotientSupport a.val ⊆ U :=
    (quotientSupport_scalarMultiply_subset_tsupport (f 0) (f 0).contMDiff.contMDiffOn w.val).trans (hf 0)
  have hb : quotientSupport b.val ⊆ V :=
    (quotientSupport_scalarMultiply_subset_tsupport (f 1) (f 1).contMDiff.contMDiffOn w.val).trans (hf 1)
  refine ⟨(compactRestrictOfSupport subset_union_left a ha,
    compactRestrictOfSupport subset_union_right b hb), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Form.ext
  intro x hx
  change liftScalar (f 0) x • (w.val.val : RawForm Coordinates F n) x +
    liftScalar (f 1) x • (w.val.val : RawForm Coordinates F n) x = (w.val.val : RawForm Coordinates F n) x
  by_cases hw : (w.val.val : RawForm Coordinates F n) x = 0
  · simp only [hw, smul_zero, add_zero]
  · have hsum := f.sum_eq_one (subset_closure ⟨x, hw, rfl⟩)
    rw [finsum_eq_sum_of_fintype, Fin.sum_univ_two] at hsum
    rw [← add_smul]
    change ((f 0) (coordinateProjection x) + (f 1) (coordinateProjection x)) • _ = _
    rw [hsum, one_smul]

end TernaryPoly.SmoothDeRhamGluing
