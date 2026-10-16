module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FrameData

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory TopologicalSpace Set
open SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts SymmetricSpacePositive
variable {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)
  {U : Set OrbitSpace} {Y : TopCat.{0}} (T : SingularFrame DeckGroup (TopCat.of (CoverOpen U)) Y)

/-- Restrict an actual local-system section to the actual selected covering sheet. -/
def frameCoefficientRestriction : coefficientSections ρ U →ₗ[ℝ] LocallyConstant Y F where
  toFun f := LocallyConstant.comap T.lift.hom f.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Extend a locally constant function by the actual locally constant sheet action. -/
def frameCoefficientExtension : LocallyConstant Y F →ₗ[ℝ] coefficientSections ρ U where
  toFun f := ⟨⟨fun x => ρ (T.label x) (f (T.base x)),
    T.label.isLocallyConstant.comp₂ (f.isLocallyConstant.comp_continuous T.base.hom.continuous)
      (fun g c => ρ g c)⟩, by
    intro g x
    change ρ (T.label (g • x)) (f (T.base (g • x))) = ρ g (ρ (T.label x) (f (T.base x)))
    rw [T.label_action, T.base_action, map_mul]
    rfl⟩
  map_add' f g := by
    apply Subtype.ext
    apply LocallyConstant.ext
    intro x
    change ρ (T.label x) (f (T.base x) + g (T.base x)) = _
    exact map_add (ρ (T.label x)) _ _
  map_smul' a f := by
    apply Subtype.ext
    apply LocallyConstant.ext
    intro x
    change ρ (T.label x) (a • f (T.base x)) = a • ρ (T.label x) (f (T.base x))
    exact map_smul (ρ (T.label x)) a _

/-- Actual frame extension reconstructs every genuine local-system section. -/
theorem frameCoefficientExtension_restriction (f : coefficientSections ρ U) :
    frameCoefficientExtension ρ T (frameCoefficientRestriction ρ T f) = f := by
  apply Subtype.ext
  apply LocallyConstant.ext
  intro x
  change ρ (T.label x) (f.val (T.lift (T.base x))) = f.val x
  rw [← f.property, T.reconstruction]

/-- The selected-sheet restriction recovers the original locally constant function. -/
theorem frameCoefficientRestriction_extension (f : LocallyConstant Y F) :
    frameCoefficientRestriction ρ T (frameCoefficientExtension ρ T f) = f := by
  apply LocallyConstant.ext
  intro y
  change ρ (T.label (T.lift y)) (f (T.base (T.lift y))) = f y
  rw [T.label_lift, T.base_lift, map_one]
  rfl

/-- The actual local coefficient module in a genuine covering frame, with explicit inverse formulas. -/
def frameCoefficientEquiv : coefficientSections ρ U ≃ₗ[ℝ] LocallyConstant Y F where
  __ := frameCoefficientRestriction ρ T
  invFun := frameCoefficientExtension ρ T
  left_inv := frameCoefficientExtension_restriction ρ T
  right_inv := frameCoefficientRestriction_extension ρ T

/-- Every actual coordinate covering chart trivializes the actual local coefficient sheaf on
all of its open coordinate subsets. -/
def chartCoefficientEquiv (S : Space) {V : Set Coordinates} (hVt : V ⊆ (quotientChart S).target) :
    coefficientSections ρ (chartOpen S V) ≃ₗ[ℝ] LocallyConstant V F :=
  frameCoefficientEquiv ρ (chartSingularFrame S hVt)

/-- The local coefficient identification uses the literal selected lift. -/
theorem chartCoefficientEquiv_apply (S : Space) {V : Set Coordinates}
    (hVt : V ⊆ (quotientChart S).target) (f : coefficientSections ρ (chartOpen S V)) (x : V) :
    chartCoefficientEquiv ρ S hVt f x =
      f.val ⟨x.val, SmoothSingularComparison.chartSubset_liftedDomain S hVt x.property⟩ := rfl

/-- The inverse local coefficient identification uses the true sheet element and true base coordinate. -/
theorem chartCoefficientEquiv_symm_apply (S : Space) {V : Set Coordinates}
    (hVt : V ⊆ (quotientChart S).target) (f : LocallyConstant V F)
    (x : CoverOpen (chartOpen S V)) :
    ((chartCoefficientEquiv ρ S hVt).symm f).val x =
      ρ (sheetElement S x.val) (f ⟨baseCoordinate S x.val, baseCoordinate_mem_chartOpen S x.property⟩) := rfl

end TernaryPoly.SmoothSingularGlobal
