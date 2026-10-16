module

public import TernaryPeriodPolynomials.Building.Ambient.TriangleRetraction
public import TernaryPeriodPolynomials.Building.Ambient.RelativeFilling

@[expose] public section


noncomputable section
namespace TernaryPoly.AmbientLowLinkFilling
open ModThreeGoodAction GoodIntegralNormalization AugmentedFrameComplex
open PrimitiveLineHeight AmbientEdgeRetraction AmbientTriangleRetraction OrientedListChains

/-- Every finite edge cycle in the strict lower unrestricted link has a strict lower triangle filler. -/
theorem one_cycle_filling (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector)
    (w : RationalLine) (hW : Primitive W)
    (hspan : Submodule.span ℚ {rationalVector W} = w.val) (hN : 0 < F W)
    {a : Chain RationalLine} (ha : a ∈ chains (lowLink F W w) 2) (hz : boundary a = 0) :
    ∃ b : Chain RationalLine, b ∈ chains (lowLink F W w) 3 ∧ boundary b = a := by
  have ha' : a ∈ chains (link w) 2 := chains_mono (lowLink_le_link F W w) 2 ha
  obtain ⟨c,hc,he⟩ := AmbientRelativeFilling.one_cycle_filling w ha' hz
  exact boundary_lift_of_low F W w hW hspan hN c a hc ha he

/-- The primitive nonnegative direction gives the strict descending-link H1 theorem at any positive-height vertex. -/
theorem descending_one_cycle_filling (F : IntegralVector →ₗ[ℤ] ℤ) (w : RationalLine)
    (hw : 0 < height F w) {a : Chain RationalLine}
    (ha : a ∈ chains (lowLink F (nonnegativeRepresentative F w) w) 2)
    (hz : boundary a = 0) :
    ∃ b : Chain RationalLine,
      b ∈ chains (lowLink F (nonnegativeRepresentative F w) w) 3 ∧ boundary b = a := by
  have hp : 0 < F (nonnegativeRepresentative F w) := by
    rw [nonnegativeRepresentative_value]
    exact_mod_cast hw
  exact one_cycle_filling F (nonnegativeRepresentative F w) w
    (nonnegativeRepresentative_primitive F w) (nonnegativeRepresentative_span F w) hp ha hz

end TernaryPoly.AmbientLowLinkFilling
