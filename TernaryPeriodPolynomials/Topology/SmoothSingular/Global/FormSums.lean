module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.Resolution
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.GluingWeightedExtension

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set Filter Function CategoryTheory
open SmoothLocalDeRham SmoothCoveringDeRham SymmetricSpaceCharts SymmetricSpaceCovering
open scoped Topology ContDiff
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {ρ : Representation ℝ DeckGroup F} {U : Set OrbitSpace} {n : ℕ} {ι : Type*}

/-- The genuine projected nonzero locus of a covering form. -/
def projectedFormSupport (w : EquivariantForm ρ U n) : Set OrbitSpace :=
  coordinateProjection '' Function.support (w.val : RawForm Coordinates F n)

/-- A locally finite family of projected supports has finitely many nonzero values at each
actual covering point, including points outside the lifted domain. -/
theorem formValues_finite (w : ι → EquivariantForm ρ U n)
    (hw : LocallyFinite (fun i => projectedFormSupport (w i))) (x : Coordinates) :
    (Function.support (fun i => ((w i).val : RawForm Coordinates F n) x)).Finite :=
  (hw.point_finite (coordinateProjection x)).subset (fun _i hi => ⟨x, hi, rfl⟩)

/-- A locally finite family of actual smooth forms has a smooth pointwise finite sum. -/
theorem formFinsum_smooth (hU : IsOpen U) (w : ι → EquivariantForm ρ U n)
    (hw : LocallyFinite (fun i => projectedFormSupport (w i))) :
    ContDiffOn ℝ ∞ (fun x => ∑ᶠ i, ((w i).val : RawForm Coordinates F n) x) (liftedDomain U) := by
  classical
  intro x hx
  obtain ⟨t, ht, hfin⟩ := hw (coordinateProjection x)
  let s := hfin.toFinset
  have he : (fun y => ∑ᶠ i, ((w i).val : RawForm Coordinates F n) y) =ᶠ[𝓝 x] fun y => ∑ i ∈ s, ((w i).val : RawForm Coordinates F n) y := by
    have hp := coordinateProjection_continuousOn.continuousAt
      (isOpen_positiveCoordinates.mem_nhds hx.1)
    filter_upwards [hp.preimage_mem_nhds ht] with y hy
    apply finsum_eq_sum_of_support_subset
    intro i hi
    exact hfin.mem_toFinset.mpr ⟨coordinateProjection y, ⟨y, hi, rfl⟩, hy⟩
  have hs : ContDiffAt ℝ ∞ (fun y => ∑ i ∈ s, ((w i).val : RawForm Coordinates F n) y) x :=
    ContDiffAt.sum (fun i _ => (Form.smooth (w i).val x hx).contDiffAt
      ((liftedDomain_isOpen hU).mem_nhds hx))
  exact (hs.congr_of_eventuallyEq he).contDiffWithinAt

/-- The pointwise finite sum of actual equivariant covering forms remains equivariant. -/
theorem formFinsum_equivariant (w : ι → EquivariantForm ρ U n)
    (hw : LocallyFinite (fun i => projectedFormSupport (w i))) :
    IsEquivariant ρ U (fun x => ∑ᶠ i, ((w i).val : RawForm Coordinates F n) x) := by
  intro g x hx
  change ContinuousAlternatingMap.compContinuousLinearMapCLM (fderiv ℝ (deckMap g) x)
    (∑ᶠ i, ((w i).val : RawForm Coordinates F n) (deckMap g x)) =
    SmoothCoveringDeRham.coefficientFormMap (coefficientMap ρ g) n (∑ᶠ i, ((w i).val : RawForm Coordinates F n) x)
  rw [map_finsum _ (formValues_finite w hw (deckMap g x)), map_finsum _ (formValues_finite w hw x)]
  exact finsum_congr (fun i => (w i).property g x hx)

/-- The genuine locally finite sum of smooth equivariant forms, using their literal covering
representatives and actual projected support locality. -/
def locallyFiniteFormSum (hU : IsOpen U) (w : ι → EquivariantForm ρ U n)
    (hw : LocallyFinite (fun i => projectedFormSupport (w i))) : EquivariantForm ρ U n :=
  ⟨⟨fun x => ∑ᶠ i, ((w i).val : RawForm Coordinates F n) x, formFinsum_smooth hU w hw, by
    intro x hx
    simp only [Form.outside _ hx, finsum_zero]⟩, formFinsum_equivariant w hw⟩

/-- Evaluation of the actual locally finite sum is its literal finite-support sum. -/
theorem locallyFiniteFormSum_apply (hU : IsOpen U) (w : ι → EquivariantForm ρ U n)
    (hw : LocallyFinite (fun i => projectedFormSupport (w i))) (x : Coordinates) :
    ((locallyFiniteFormSum hU w hw).val : RawForm Coordinates F n) x = ∑ᶠ i, ((w i).val : RawForm Coordinates F n) x := rfl

end TernaryPoly.SmoothSingularGlobal
