module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CoefficientForms
public import Mathlib.Topology.Sheaves.Limits

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Opposite TopologicalSpace Set
open SmoothLocalDeRham SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F)

/-- The actual coefficient-to-form map commutes with quotient-open restriction. -/
theorem coefficientForm_restrict {U V : Set OrbitSpace} (hU : IsOpen U) (hV : IsOpen V)
    (hVU : V ⊆ U) (f : coefficientSections ρ U) :
    restrictEquivariant ρ hVU 0 (coefficientForm ρ hU f) =
      coefficientForm ρ hV (coefficientRestriction ρ hVU f) := by
  apply Subtype.ext
  apply Form.ext
  intro x hx
  rw [restrictEquivariant_apply ρ hVU _ hx,
    coefficientForm_apply ρ hU f (liftedDomain_mono hVU hx),
    coefficientForm_apply ρ hV _ hx]
  rfl

/-- Actual locally constant coefficient sections map naturally to genuine smooth zero-forms. -/
def coefficientToForm : coefficientPresheaf ρ ⟶ formPresheaf ρ 0 where
  app U := ModuleCat.ofHom (coefficientFormMap ρ U.unop.isOpen)
  naturality U V f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact (coefficientForm_restrict ρ U.unop.isOpen V.unop.isOpen f.unop.le s).symm

/-- The actual coefficient-to-form map has zero exterior derivative as a natural transformation. -/
theorem coefficientToForm_closed : coefficientToForm ρ ≫ formDifferential ρ 0 = 0 := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  exact coefficientForm_closed ρ U.unop.isOpen f

/-- The genuine degree-zero sheaf augmentation. -/
def coefficientToFormSheaf : coefficientSheaf ρ ⟶ formSheaf ρ 0 :=
  ⟨coefficientToForm ρ⟩

/-- The actual sheaf augmentation is closed before passing to cohomology. -/
theorem coefficientToFormSheaf_closed :
    coefficientToFormSheaf ρ ≫ formSheafDifferential ρ 0 = 0 := by
  apply ObjectProperty.hom_ext
  exact coefficientToForm_closed ρ

/-- The genuine augmentation of the smooth de Rham sheaf complex by its actual coefficients. -/
def formSheafAugmentation :
    (CochainComplex.single₀ ((TopCat.of OrbitSpace).Sheaf (ModuleCat ℝ))).obj (coefficientSheaf ρ) ⟶
      formSheafComplex ρ :=
  (CochainComplex.fromSingle₀Equiv (formSheafComplex ρ) (coefficientSheaf ρ)).symm
    ⟨coefficientToFormSheaf ρ, coefficientToFormSheaf_closed ρ⟩

/-- The complex augmentation retains the literal degree-zero coefficient map. -/
theorem formSheafAugmentation_f_zero :
    (formSheafAugmentation ρ).f 0 = coefficientToFormSheaf ρ :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

/-- The actual coefficient-to-form map is injective on every open set. -/
theorem coefficientForm_injective {U : Set OrbitSpace} (hU : IsOpen U) :
    Function.Injective (coefficientForm ρ hU) := by
  intro f g h
  apply Subtype.ext
  apply LocallyConstant.ext
  intro x
  have he := congrArg (fun w : EquivariantForm ρ U 0 => (w.val : RawForm Coordinates F 0) x.val) h
  rw [coefficientForm_apply ρ hU f x.property, coefficientForm_apply ρ hU g x.property] at he
  exact zeroEquiv.injective he

end TernaryPoly.SmoothSingularGlobal
