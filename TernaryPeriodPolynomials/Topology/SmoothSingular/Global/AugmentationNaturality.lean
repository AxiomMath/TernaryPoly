module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.TotalHomologyNaturality

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory

variable {A B : CochainComplex (ModuleCat.{0} ℝ) ℕ} {K L : RealBicomplex}

/-- The genuine all-row augmentation comparison, with its literal degree-two cochain homology source. -/
def augmentationDegreeTwoIso (a : TotalAugmentation A K) (ha : a.ExactRows) :
    A.homology 2 ≅ (totalWindow K).homology :=
  A.homologyIsoSc' 1 2 3 (by simp) (by simp) ≪≫ a.totalAugmentationHomologyIso ha

/-- Actual commuting augmentations yield the exact homology square for the finite staircase comparison. -/
theorem augmentationDegreeTwoIso_naturality (f : K ⟶ L)
    (a : TotalAugmentation A K) (b : TotalAugmentation B L) (ha : a.ExactRows) (hb : b.ExactRows)
    (g : A ⟶ B) (h : a.map ≫ f.f 0 = g ≫ b.map) :
    (augmentationDegreeTwoIso a ha).hom ≫ ShortComplex.homologyMap (totalWindowMap f) =
      HomologicalComplex.homologyMap g 2 ≫ (augmentationDegreeTwoIso b hb).hom := by
  have hh := congrArg (fun u => (ShortComplex.homologyMap u :
    (A.sc' 1 2 3).homology ⟶ (totalWindow L).homology))
      (totalAugmentationMap_naturality f a b g h)
  rw [ShortComplex.homologyMap_comp,ShortComplex.homologyMap_comp] at hh
  let iA := (A.homologyIsoSc' 1 2 3 (by simp) (by simp)).hom
  let iB := (B.homologyIsoSc' 1 2 3 (by simp) (by simp)).hom
  let hA := ShortComplex.homologyMap a.totalAugmentationMap
  let hB := ShortComplex.homologyMap b.totalAugmentationMap
  let sg := ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor'
    (ModuleCat ℝ) (ComplexShape.up ℕ) 1 2 3).map g)
  let hg := HomologicalComplex.homologyMap g 2
  calc
    _ = iA ≫ (hA ≫ ShortComplex.homologyMap (totalWindowMap f)) := Category.assoc _ _ _
    _ = iA ≫ (sg ≫ hB) := congrArg (fun u => iA ≫ u) hh
    _ = (iA ≫ sg) ≫ hB := (Category.assoc _ _ _).symm
    _ = (hg ≫ iB) ≫ hB := congrArg (fun u => u ≫ hB) (homologyIsoSc_degreeTwo_naturality g)
    _ = _ := Category.assoc _ _ _

end TernaryPoly.SmoothSingularGlobal
