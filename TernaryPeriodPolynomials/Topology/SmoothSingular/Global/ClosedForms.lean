module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FormAugmentation

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Opposite TopologicalSpace Set
open SmoothLocalDeRham SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts
open scoped Topology ContDiff
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) {U : Set OrbitSpace}

/-- Closed actual zero-forms have zero Fréchet derivative in their decoded coefficient function. -/
theorem closedForm_fderiv (hU : IsOpen U) (w : EquivariantForm ρ U 0)
    (hw : differential ρ hU 0 w = 0) {x : Coordinates} (hx : x ∈ liftedDomain U) :
    fderiv ℝ (toFunction w.val) x = 0 := by
  have hd := congrArg (fun a : EquivariantForm ρ U 1 => (a.val : RawForm Coordinates F 1) x) hw
  change (d (liftedDomain_isOpen hU) 0 w.val : RawForm Coordinates F 1) x = 0 at hd
  rw [← ofFunction_toFunction w.val, d_ofFunction _ _ _ hx] at hd
  exact oneEquiv.injective (hd.trans oneEquiv.map_zero.symm)

/-- The coefficient function of a closed actual zero-form is locally constant on the cover. -/
theorem closedForm_locallyConstant (hU : IsOpen U) (w : EquivariantForm ρ U 0)
    (hw : differential ρ hU 0 w = 0) :
    IsLocallyConstant (fun x : CoverOpen U => toFunction w.val x.val) := by
  intro A
  have ho := (liftedDomain_isOpen hU).isOpen_inter_preimage_of_fderiv_eq_zero
    ((smooth_toFunction w.val).differentiableOn (by simp))
    (fun x hx => closedForm_fderiv ρ hU w hw hx) A
  convert ho.preimage continuous_subtype_val using 1
  ext x
  exact (and_iff_right x.property).symm

/-- Decode the actual deck equivariance of a zero-form without inserting a dual or inverse action. -/
theorem toFunction_equivariant (w : EquivariantForm ρ U 0) (g : DeckGroup) (x : CoverOpen U) :
    toFunction w.val (g • x).val = ρ g (toFunction w.val x.val) := by
  have he := congrArg (fun a : Coordinates [⋀^Fin 0]→L[ℝ] F => a 0) (w.property g x.val x.property)
  change ((w.val : RawForm Coordinates F 0) (deckMap g x.val)) 0 =
    ρ g (((w.val : RawForm Coordinates F 0) x.val) 0)
  change ((w.val : RawForm Coordinates F 0) (deckMap g x.val))
    ((fderiv ℝ (deckMap g) x.val) ∘ (0 : Fin 0 → Coordinates)) =
      ρ g (((w.val : RawForm Coordinates F 0) x.val) 0) at he
  rw [show (fderiv ℝ (deckMap g) x.val) ∘ (0 : Fin 0 → Coordinates) = 0 from
    Subsingleton.elim _ _] at he
  exact he

/-- Every closed actual zero-form determines its genuine locally constant coefficient section. -/
def closedFormCoefficient (hU : IsOpen U) (w : EquivariantForm ρ U 0)
    (hw : differential ρ hU 0 w = 0) : coefficientSections ρ U :=
  ⟨⟨fun x => toFunction w.val x.val, closedForm_locallyConstant ρ hU w hw⟩,
    toFunction_equivariant ρ w⟩

/-- Re-augmenting the decoded coefficient section recovers the literal closed zero-form. -/
theorem coefficientForm_closedFormCoefficient (hU : IsOpen U) (w : EquivariantForm ρ U 0)
    (hw : differential ρ hU 0 w = 0) :
    coefficientForm ρ hU (closedFormCoefficient ρ hU w hw) = w := by
  apply Subtype.ext
  apply Form.ext
  intro x hx
  rw [coefficientForm_apply ρ hU _ hx]
  exact zeroEquiv.apply_symm_apply _

/-- On every quotient open the actual coefficient augmentation has image exactly the closed forms. -/
theorem coefficientFormMap_range (hU : IsOpen U) :
    LinearMap.range (coefficientFormMap ρ hU) = LinearMap.ker (differential ρ hU 0) := by
  ext w
  constructor
  · rintro ⟨f, rfl⟩
    exact coefficientForm_closed ρ hU f
  · intro hw
    exact ⟨closedFormCoefficient ρ hU w hw, coefficientForm_closedFormCoefficient ρ hU w hw⟩

end TernaryPoly.SmoothSingularGlobal
