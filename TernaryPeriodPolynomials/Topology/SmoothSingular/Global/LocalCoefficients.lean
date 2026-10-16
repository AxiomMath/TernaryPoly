module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.ClosedForms

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Opposite TopologicalSpace Set
open SmoothLocalDeRham SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts SymmetricSpacePositive
open scoped Topology ContDiff
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F)

/-- A constant in one genuine covering frame, extended by the actual deck representation. -/
def framedConstant (S : Space) {V : Set Coordinates} (hV : IsOpen V) (hc : IsPreconnected V)
    (c : F) : coefficientSections ρ (chartOpen S V) :=
  closedFormCoefficient ρ (chartOpen_isOpen S hV)
    (chartExtendOn ρ S hV 0 (constant V c)) (constant_extension_closed ρ S hV hc c)

/-- The coefficient frame is the literal sheet action ρ(sheetElement), with no inverse convention. -/
theorem framedConstant_apply (S : Space) {V : Set Coordinates} (hV : IsOpen V)
    (hc : IsPreconnected V) (c : F) (x : CoverOpen (chartOpen S V)) :
    (framedConstant ρ S hV hc c).val x = ρ (sheetElement S x.val) c := by
  change zeroEquiv.symm
    (((chartExtendOn ρ S hV 0 (constant V c)).val : RawForm Coordinates F 0) x.val) = _
  rw [chartExtendOn_apply ρ S hV _ x.property]
  unfold extendRaw pullRaw
  rw [constant, ofFunction_apply _ _ (baseCoordinate_mem_chartOpen S x.property)]
  rfl

/-- Smooth augmentation preserves the actual chosen constant frame. -/
theorem coefficientForm_framedConstant (S : Space) {V : Set Coordinates} (hV : IsOpen V)
    (hc : IsPreconnected V) (c : F) :
    coefficientForm ρ (chartOpen_isOpen S hV) (framedConstant ρ S hV hc c) =
      chartExtendOn ρ S hV 0 (constant V c) :=
  coefficientForm_closedFormCoefficient ρ _ _ _

/-- Every actual coefficient section is locally a constant in an actual covering frame. -/
theorem coefficient_locally_framed {U : Set OrbitSpace} (hU : IsOpen U)
    {q : OrbitSpace} (hq : q ∈ U) (f : coefficientSections ρ U) :
    ∃ S : Space, ∃ r : ℝ, 0 < r ∧
      ∃ hball : Metric.ball (quotientChart S q) r ⊆ chartDomain S U,
        q ∈ chartOpen S (Metric.ball (quotientChart S q) r) ∧ ∃ c : F,
          coefficientRestriction ρ (chartOpen_subset_of_chartDomain S hball) f =
            framedConstant ρ S Metric.isOpen_ball
              (convex_ball (quotientChart S q) r).isPreconnected c := by
  obtain ⟨S, r, hr, hball, hqV, c, he⟩ := closed_zero_local_constant ρ hU hq
    (coefficientForm ρ hU f) (coefficientForm_closed ρ hU f)
  refine ⟨S, r, hr, hball, hqV, c, ?_⟩
  apply coefficientForm_injective ρ (chartOpen_isOpen S Metric.isOpen_ball)
  rw [← coefficientForm_restrict ρ hU (chartOpen_isOpen S Metric.isOpen_ball), he,
    coefficientForm_framedConstant]

end TernaryPoly.SmoothSingularGlobal
