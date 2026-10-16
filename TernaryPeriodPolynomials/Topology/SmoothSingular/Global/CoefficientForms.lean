module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CoefficientGluing

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Opposite TopologicalSpace Set Filter
open SmoothLocalDeRham SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts
open scoped Topology ContDiff Classical
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (ρ : Representation ℝ DeckGroup F) {U : Set OrbitSpace}

/-- Extend an actual coefficient section by zero outside its lifted domain. -/
def coefficientExtension (f : coefficientSections ρ U) : Coordinates → F :=
  fun x => if hx : x ∈ liftedDomain U then f.val ⟨x, hx⟩ else 0

/-- On the lifted domain this is the actual coefficient value. -/
theorem coefficientExtension_apply (f : coefficientSections ρ U) {x : Coordinates}
    (hx : x ∈ liftedDomain U) : coefficientExtension ρ f x = f.val ⟨x, hx⟩ := by
  exact dite_eq_left hx

/-- Near an interior point, the extension is literally constant. -/
theorem coefficientExtension_eventually (hU : IsOpen U) (f : coefficientSections ρ U)
    (x : CoverOpen U) : coefficientExtension ρ f =ᶠ[𝓝 x.val] fun _ => f.val x := by
  have ho := (liftedDomain_isOpen hU).isOpenMap_subtype_val _
    (f.val.isLocallyConstant.isOpen_fiber (f.val x))
  have hx : x.val ∈ Subtype.val '' {y : CoverOpen U | f.val y = f.val x} := ⟨x, rfl, rfl⟩
  filter_upwards [ho.mem_nhds hx] with y hy
  obtain ⟨z, hz, rfl⟩ := hy
  exact (coefficientExtension_apply ρ f z.property).trans hz

/-- Actual locally constant coefficient sections are smooth on their lifted domains. -/
theorem coefficientExtension_smooth (hU : IsOpen U) (f : coefficientSections ρ U) :
    ContDiffOn ℝ ∞ (coefficientExtension ρ f) (liftedDomain U) := by
  intro x hx
  exact (contDiffAt_const.congr_of_eventuallyEq
    (coefficientExtension_eventually ρ hU f ⟨x, hx⟩)).contDiffWithinAt

variable [FiniteDimensional ℝ F]

/-- The genuine coefficient section as an actual equivariant smooth zero-form. -/
def coefficientForm (hU : IsOpen U) (f : coefficientSections ρ U) : EquivariantForm ρ U 0 :=
  ⟨ofFunction (coefficientExtension ρ f) (coefficientExtension_smooth ρ hU f), by
    intro g x hx
    change ((ofFunction (coefficientExtension ρ f) (coefficientExtension_smooth ρ hU f) : RawForm Coordinates F 0) (deckMap g x)).compContinuousLinearMap
      (fderiv ℝ (deckMap g) x) = coefficientFormMap (coefficientMap ρ g) 0
        ((ofFunction (coefficientExtension ρ f) (coefficientExtension_smooth ρ hU f) : RawForm Coordinates F 0) x)
    rw [ofFunction_apply _ _ (deckMap_liftedDomain g U hx), ofFunction_apply _ _ hx,
      coefficientExtension_apply ρ f (deckMap_liftedDomain g U hx), coefficientExtension_apply ρ f hx]
    ext v
    exact f.property g ⟨x, hx⟩⟩

/-- The actual zero-form augmentation evaluates to the original coefficient value. -/
theorem coefficientForm_apply (hU : IsOpen U) (f : coefficientSections ρ U)
    {x : Coordinates} (hx : x ∈ liftedDomain U) :
    ((coefficientForm ρ hU f).val : RawForm Coordinates F 0) x = zeroEquiv (f.val ⟨x, hx⟩) := by
  rw [coefficientForm, ofFunction_apply _ _ hx, coefficientExtension_apply ρ f hx]

/-- Locally constant coefficient sections are closed under the literal exterior derivative. -/
theorem coefficientForm_closed (hU : IsOpen U) (f : coefficientSections ρ U) :
    differential ρ hU 0 (coefficientForm ρ hU f) = 0 := by
  apply Subtype.ext
  apply Form.ext
  intro x hx
  change (d (liftedDomain_isOpen hU) 0 (ofFunction (coefficientExtension ρ f) (coefficientExtension_smooth ρ hU f)) : RawForm Coordinates F 1) x = 0
  rw [d_ofFunction _ _ _ hx, (coefficientExtension_eventually ρ hU f ⟨x, hx⟩).fderiv_eq,
    fderiv_fun_const]
  exact oneEquiv.map_zero

/-- The actual coefficient-to-smooth augmentation is real linear. -/
def coefficientFormMap (hU : IsOpen U) : coefficientSections ρ U →ₗ[ℝ] EquivariantForm ρ U 0 where
  toFun := coefficientForm ρ hU
  map_add' f k := by
    apply Subtype.ext
    apply Form.ext
    intro x hx
    simp only [Submodule.coe_add, Pi.add_apply]
    rw [coefficientForm_apply ρ hU _ hx, coefficientForm_apply ρ hU _ hx,
      coefficientForm_apply ρ hU _ hx]
    exact map_add zeroEquiv _ _
  map_smul' a f := by
    apply Subtype.ext
    apply Form.ext
    intro x hx
    simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
    rw [coefficientForm_apply ρ hU _ hx, coefficientForm_apply ρ hU _ hx]
    exact map_smul zeroEquiv a _

end TernaryPoly.SmoothSingularGlobal
