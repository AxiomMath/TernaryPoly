module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.TotalMaps
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.TotalComparison

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory

/-- The canonical choice of the actual degree-two short window is natural on homology. -/
theorem homologyIsoSc_degreeTwo_naturality
    {A B : CochainComplex (ModuleCat.{0} ℝ) ℕ} (g : A ⟶ B) :
    (A.homologyIsoSc' 1 2 3 (by simp) (by simp)).hom ≫
      ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor' (ModuleCat ℝ) (ComplexShape.up ℕ) 1 2 3).map g) =
      HomologicalComplex.homologyMap g 2 ≫ (B.homologyIsoSc' 1 2 3 (by simp) (by simp)).hom := by
  have h := (HomologicalComplex.natIsoSc' (ModuleCat ℝ) (ComplexShape.up ℕ) 1 2 3
    (by simp) (by simp)).hom.naturality g
  have hh := congrArg (fun f => (ShortComplex.homologyMap f :
    (A.sc 2).homology ⟶ (B.sc' 1 2 3).homology)) h
  change ShortComplex.homologyMap
      ((HomologicalComplex.natIsoSc' (ModuleCat ℝ) (ComplexShape.up ℕ) 1 2 3
        (by simp) (by simp)).hom.app A) ≫
      ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor'
        (ModuleCat ℝ) (ComplexShape.up ℕ) 1 2 3).map g) =
    ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor
      (ModuleCat ℝ) (ComplexShape.up ℕ) 2).map g) ≫
      ShortComplex.homologyMap ((HomologicalComplex.natIsoSc' (ModuleCat ℝ)
        (ComplexShape.up ℕ) 1 2 3 (by simp) (by simp)).hom.app B)
  exact (ShortComplex.homologyMap_comp _ _).symm.trans
    (hh.symm.trans (ShortComplex.homologyMap_comp _ _))

end TernaryPoly.SmoothSingularGlobal
