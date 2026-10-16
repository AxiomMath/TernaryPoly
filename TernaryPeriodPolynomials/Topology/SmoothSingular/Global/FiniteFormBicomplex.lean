module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SubBicomplex
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FiniteFormExact
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CechTotalAugmentation
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.ChainMaps

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set CategoryTheory
open SmoothCoveringDeRham SymmetricSpaceCovering

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) (C : CompactConvexCover)

/-- The actual finite-tuple-support submodules of the genuine Čech–de Rham bicomplex. -/
def finiteFormSubmodules : BicomplexSubmodules (formCechBicomplex ρ
    (fun i => (C.sheet i).quotientDomain) (fun i => (C.sheet i).quotientDomain_isOpen)) where
  term p q := finiteFamilySubmodule (fun t : Fin (p+1) → C.Index =>
    EquivariantForm ρ (cechDomain (fun i => (C.sheet i).quotientDomain) t) q)
  horizontal_mem p q w hw := by
    change (familySupport (horizontal _ p q w)).Finite
    rw [formCechBicomplex_horizontal]
    exact formCechD_finiteSupport ρ C q p w hw
  vertical_mem p q w hw := by
    change (familySupport (vertical _ p q w)).Finite
    rw [formCechBicomplex_vertical]
    exact formCechVertical_finiteSupport ρ C q (p+1) w hw

/-- The genuine supported Čech–de Rham bicomplex on finite tuple families. -/
def finiteFormBicomplex : RealBicomplex := (finiteFormSubmodules ρ C).toBicomplex

/-- The actual compact global augmentation into finite tuple support. -/
def finiteFormAugment (n : ℕ) : CompactSupportForm ρ Set.univ n →ₗ[ℝ]
    (finiteFormSubmodules ρ C).term 0 n where
  toFun w := ⟨formCechAugmentationMap ρ (fun i => (C.sheet i).quotientDomain) n w.val,
    formCechAugmentationMap_finiteSupport ρ C n w.val w.property⟩
  map_add' w z := Subtype.ext (map_add _ w.val z.val)
  map_smul' c w := Subtype.ext (map_smul _ c w.val)

/-- Compact global forms map to the actual finite Čech column, commuting with the true d. -/
def finiteFormColumnAugmentation : globalCompactComplex ρ ⟶ (finiteFormBicomplex ρ C).X 0 :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (finiteFormAugment ρ C n)) (by
    intro n
    simp only [finiteFormBicomplex,BicomplexSubmodules.toBicomplex,BicomplexSubmodules.column,
      globalCompactComplex,compactCoveringComplex,CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    change vertical (formCechBicomplex ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen)) 0 n
      (formCechAugmentationMap ρ (fun i => (C.sheet i).quotientDomain) n w.val) =
      formCechAugmentationMap ρ (fun i => (C.sheet i).quotientDomain) (n+1)
        (differential ρ isOpen_univ n w.val)
    rw [formCechBicomplex_vertical]
    funext t
    change differential ρ (cechDomain_isOpen (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen) t) n
      (formCechAugmentationMap ρ (fun i => (C.sheet i).quotientDomain) n w.val t) = _
    rw [formCechAugmentationMap_apply,formCechAugmentationMap_apply]
    exact (restrictEquivariant_d ρ isOpen_univ _ (Set.subset_univ _) w.val).symm)

/-- The supported global augmentation is literally compatible with the old ordinary
augmentation and the true compact-support inclusion. -/
theorem finiteFormColumnAugmentation_forget : finiteFormColumnAugmentation ρ C ≫
    (finiteFormSubmodules ρ C).columnInclusion 0 =
      compactInclusion ρ isOpen_univ ≫ formCechColumnAugmentation ρ
        (fun i => (C.sheet i).quotientDomain) (fun i => (C.sheet i).quotientDomain_isOpen) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro w
  rfl

/-- Horizontal closedness survives passage to the genuine finite-support submodules. -/
theorem finiteFormColumnAugmentation_horizontal : finiteFormColumnAugmentation ρ C ≫
    (finiteFormBicomplex ρ C).d 0 1 = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  have h := (formCechTotalAugmentation ρ (fun i => (C.sheet i).quotientDomain)
    (fun i => (C.sheet i).quotientDomain_isOpen)).augment_horizontal n w.val
  change (horizontal (finiteFormBicomplex ρ C) 0 n (finiteFormAugment ρ C n w)).val = 0
  exact (congrArg (fun f => (f (finiteFormAugment ρ C n w)).val)
    ((finiteFormSubmodules ρ C).horizontal_eq 0 n)).trans h

/-- The actual compact de Rham complex augments the finite-support Čech bicomplex. -/
def finiteFormTotalAugmentation : TotalAugmentation (globalCompactComplex ρ) (finiteFormBicomplex ρ C) where
  map := finiteFormColumnAugmentation ρ C
  horizontal_zero := finiteFormColumnAugmentation_horizontal ρ C

end TernaryPoly.SmoothSingularGlobal
