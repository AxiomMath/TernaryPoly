module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.GluingSupport

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothDeRhamGluing
open Set Filter ContinuousAlternatingMap SmoothLocalDeRham SmoothCoveringDeRham
  SymmetricSpaceCharts SymmetricSpaceCovering
open scoped ContDiff Topology Manifold

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {ρ : Representation ℝ DeckGroup F} {U V : Set OrbitSpace} {n : ℕ}

/-- Zero extension is the same canonical raw representative, provided smoothness on the larger
actual covering preimage has been proved. Equivariance outside the original domain is automatic. -/
def zeroExtendOfSmooth (hUV : U ⊆ V) (w : EquivariantForm ρ U n)
    (hs : ContDiffOn ℝ ∞ (w.val : RawForm Coordinates F n) (liftedDomain V)) :
    EquivariantForm ρ V n :=
  ⟨⟨(w.val : RawForm Coordinates F n), hs, fun _ hx => Form.outside w.val
    (fun h => hx (liftedDomain_mono hUV h))⟩, by
    intro g x hx
    by_cases hxU : x ∈ liftedDomain U
    · exact w.property g x hxU
    · have hgU : deckMap g x ∉ liftedDomain U := by
        intro h
        apply hxU
        refine ⟨hx.1, ?_⟩
        have hq : coordinateProjection (deckMap g x) ∈ U := h.2
        rwa [coordinateProjection_deck g hx.1] at hq
      change ((w.val : RawForm Coordinates F n) (deckMap g x)).compContinuousLinearMap _ =
        coefficientFormMap _ _ ((w.val : RawForm Coordinates F n) x)
      rw [Form.outside w.val hgU, Form.outside w.val hxU]
      ext v
      simp [coefficientFormMap]⟩

@[simp] theorem zeroExtendOfSmooth_apply (hUV : U ⊆ V) (w : EquivariantForm ρ U n)
    (hs : ContDiffOn ℝ ∞ (w.val : RawForm Coordinates F n) (liftedDomain V)) (x : Coordinates) :
    ((zeroExtendOfSmooth hUV w hs).val : RawForm Coordinates F n) x =
      (w.val : RawForm Coordinates F n) x := rfl

@[simp] theorem quotientSupport_zeroExtendOfSmooth (hUV : U ⊆ V) (w : EquivariantForm ρ U n)
    (hs : ContDiffOn ℝ ∞ (w.val : RawForm Coordinates F n) (liftedDomain V)) :
    quotientSupport (zeroExtendOfSmooth hUV w hs) = quotientSupport w := rfl

/-- Genuine compact-support zero extension along inclusion of quotient open sets. -/
def compactZeroExtend (hU : IsOpen U) (hUV : U ⊆ V) (n : ℕ) :
    CompactSupportForm ρ U n →ₗ[ℝ] CompactSupportForm ρ V n where
  toFun w := ⟨zeroExtendOfSmooth hUV w.val
    ((raw_smooth_of_support_subset hU w.val w.property.2).mono inter_subset_left),
    w.property.1, w.property.2.trans hUV⟩
  map_add' w z := by
    apply Subtype.ext
    apply Subtype.ext
    apply Form.ext
    intro x hx
    rfl
  map_smul' c w := by
    apply Subtype.ext
    apply Subtype.ext
    apply Form.ext
    intro x hx
    rfl

@[simp] theorem compactZeroExtend_apply (hU : IsOpen U) (hUV : U ⊆ V)
    (w : CompactSupportForm ρ U n) (x : Coordinates) :
    ((compactZeroExtend hU hUV n w).val.val : RawForm Coordinates F n) x =
      (w.val.val : RawForm Coordinates F n) x := rfl

@[simp] theorem quotientSupport_compactZeroExtend (hU : IsOpen U) (hUV : U ⊆ V)
    (w : CompactSupportForm ρ U n) :
    quotientSupport (compactZeroExtend hU hUV n w).val = quotientSupport w.val := rfl

theorem compactZeroExtend_injective (hU : IsOpen U) (hUV : U ⊆ V) (n : ℕ) :
    Function.Injective (compactZeroExtend (ρ := ρ) hU hUV n) := by
  intro w z h
  apply Subtype.ext
  apply Subtype.ext
  apply Form.ext
  intro x hx
  exact congrArg (fun a : CompactSupportForm ρ V n => (a.val.val : RawForm Coordinates F n) x) h

end TernaryPoly.SmoothDeRhamGluing
