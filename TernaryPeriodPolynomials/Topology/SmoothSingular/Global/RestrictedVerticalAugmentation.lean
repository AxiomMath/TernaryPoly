module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SubBicomplex
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.Subcomplex
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.TotalAugmentation

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory

variable {K : RealBicomplex} {A : CochainComplex (ModuleCat.{0} ℝ) ℕ}
  (P : BicomplexSubmodules K) (Q : CochainSubmodules A) (a : TotalAugmentation A K.flip)
  (ha : ∀ n (x : A.X n), x ∈ Q.term n → a.augment n x ∈ P.term n 0)

/-- Restrict a genuine vertical coefficient augmentation to actual stable submodules. -/
def restrictedVerticalAugmentationMap : Q.toComplex ⟶ P.toBicomplex.flip.X 0 :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom {
    toFun := fun x => ⟨a.augment n x.val,ha n x.val x.property⟩
    map_add' := fun x y => Subtype.ext (map_add _ x.val y.val)
    map_smul' := fun c x => Subtype.ext (map_smul _ c x.val) }) (by
      intro n
      simp only [CochainSubmodules.toComplex,CochainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change horizontal P.toBicomplex n 0 ⟨a.augment n x.val,ha n x.val x.property⟩ = _
      apply (congrArg (fun f => f ⟨a.augment n x.val,ha n x.val x.property⟩)
        (P.horizontal_eq n 0)).trans
      exact Subtype.ext (a.augment_vertical n x.val))

/-- The restricted genuine vertical augmentation is killed by the actual restricted d. -/
theorem restrictedVerticalAugmentation_horizontal : restrictedVerticalAugmentationMap P Q a ha ≫
    P.toBicomplex.flip.d 0 1 = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change vertical P.toBicomplex n 0 ⟨a.augment n x.val,ha n x.val x.property⟩ = 0
  apply (congrArg (fun f => f ⟨a.augment n x.val,ha n x.val x.property⟩) (P.vertical_eq n 0)).trans
  exact Subtype.ext (a.augment_horizontal n x.val)

/-- Actual vertical augmentation on the actual subcomplexes. -/
def restrictedVerticalAugmentation : TotalAugmentation Q.toComplex P.toBicomplex.flip where
  map := restrictedVerticalAugmentationMap P Q a ha
  horizontal_zero := restrictedVerticalAugmentation_horizontal P Q a ha

/-- The actual vertical restriction construction preserves its literal inclusion square. -/
theorem restrictedVerticalAugmentation_forget : restrictedVerticalAugmentationMap P Q a ha ≫
    ((HomologicalComplex₂.flipFunctor (ModuleCat ℝ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)).map P.inclusion).f 0 =
      Q.inclusion ≫ a.map := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

end TernaryPoly.SmoothSingularGlobal
