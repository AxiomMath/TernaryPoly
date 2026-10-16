module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.ModuleClasses
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Limits HomologicalComplex

variable {J : Type} [SmallCategory J] [IsFiltered J]
  (D : J ⥤ CochainComplex (ModuleCat.{0} ℝ) ℕ) (s : Cocone D)
  (hinj : ∀ j n, Function.Injective ((s.ι.app j).f n))
  (hrep : ∀ n (x : s.pt.X n), ∃ j, ∃ y : (D.obj j).X n, (s.ι.app j).f n y = x)

include hinj hrep in
omit [IsFiltered J] in
/-- Every actual cocycle in a degreewise injective filtered union comes from an actual stage cocycle. -/
theorem filteredHomology_stage_exists (n : ℕ) (x : s.pt.homology n) :
    ∃ j, ∃ y : (D.obj j).homology n, homologyMap (s.ι.app j) n y = x := by
  obtain ⟨c,hc,rfl⟩ := moduleClass_surjective (s.pt.sc n) x
  obtain ⟨j,b,hb⟩ := hrep n c
  have hclosed : ((D.obj j).sc n).g.hom b = 0 := by
    apply hinj j ((ComplexShape.up ℕ).next n)
    have h := congrArg (fun f => f.hom b) ((s.ι.app j).comm n ((ComplexShape.up ℕ).next n))
    exact h.symm.trans ((congrArg ((s.pt.sc n).g.hom) hb).trans
      (hc.trans (map_zero ((s.ι.app j).f ((ComplexShape.up ℕ).next n)).hom).symm))
  refine ⟨j,moduleClass ((D.obj j).sc n) b hclosed,?_⟩
  change ShortComplex.homologyMap ((shortComplexFunctor (ModuleCat ℝ) (ComplexShape.up ℕ) n).map (s.ι.app j)) _ = _
  exact (moduleClass_natural
    ((shortComplexFunctor (ModuleCat ℝ) (ComplexShape.up ℕ) n).map (s.ι.app j)) b hclosed).trans
      (by cases hb; rfl)

include hinj hrep in
/-- A homology relation in an actual filtered union is already realized at a common later stage. -/
theorem filteredHomology_stage_zero (n : ℕ) (i : J) (x : (D.obj i).homology n)
    (hx : homologyMap (s.ι.app i) n x = 0) :
    ∃ j, ∃ f : i ⟶ j, homologyMap (D.map f) n x = 0 := by
  obtain ⟨c,hc,rfl⟩ := moduleClass_surjective ((D.obj i).sc n) x
  change ShortComplex.homologyMap ((shortComplexFunctor (ModuleCat ℝ) (ComplexShape.up ℕ) n).map (s.ι.app i)) _ = 0 at hx
  rw [moduleClass_natural,moduleClass_eq_zero_iff] at hx
  obtain ⟨b,hb⟩ := hx
  obtain ⟨k,a,ha⟩ := hrep ((ComplexShape.up ℕ).prev n) b
  let j := IsFiltered.max i k
  let f : i ⟶ j := IsFiltered.leftToMax i k
  let g : k ⟶ j := IsFiltered.rightToMax i k
  refine ⟨j,f,?_⟩
  change ShortComplex.homologyMap ((shortComplexFunctor (ModuleCat ℝ) (ComplexShape.up ℕ) n).map (D.map f)) _ = 0
  rw [moduleClass_natural,moduleClass_eq_zero_iff]
  refine ⟨(D.map g).f ((ComplexShape.up ℕ).prev n) a,?_⟩
  apply hinj j n
  have hcomm := congrArg (fun u => u.hom ((D.map g).f ((ComplexShape.up ℕ).prev n) a))
    ((s.ι.app j).comm ((ComplexShape.up ℕ).prev n) n)
  have hg := congrArg (fun u : D.obj k ⟶ s.pt => (u.f ((ComplexShape.up ℕ).prev n)).hom a) (s.w g)
  have hf := congrArg (fun u : D.obj i ⟶ s.pt => (u.f n).hom c) (s.w f)
  exact hcomm.symm.trans ((congrArg (s.pt.sc n).f.hom (hg.trans ha)).trans (hb.trans hf.symm))

/-- The actual map from the filtered stage cohomology colimit to the union's cohomology. -/
def filteredHomologyMap (n : ℕ) : colimit (D ⋙ homologyFunctor (ModuleCat ℝ) (ComplexShape.up ℕ) n) ⟶
    s.pt.homology n := colimit.desc _ ((homologyFunctor (ModuleCat ℝ) (ComplexShape.up ℕ) n).mapCocone s)

omit [IsFiltered J] in
/-- The genuine filtered cohomology map is induced by the actual stage inclusions. -/
theorem filteredHomologyMap_ι (n : ℕ) (j : J) :
    colimit.ι (D ⋙ homologyFunctor (ModuleCat ℝ) (ComplexShape.up ℕ) n) j ≫
      filteredHomologyMap D s n = homologyMap (s.ι.app j) n := colimit.ι_desc _ _

include hinj hrep in
omit [IsFiltered J] in
/-- Actual stage cocycle representatives make the genuine filtered cohomology map surjective. -/
theorem filteredHomologyMap_surjective (n : ℕ) : Function.Surjective (filteredHomologyMap D s n) := by
  intro x
  obtain ⟨j,y,hy⟩ := filteredHomology_stage_exists D s hinj hrep n x
  exact ⟨colimit.ι (D ⋙ homologyFunctor (ModuleCat ℝ) (ComplexShape.up ℕ) n) j y,(congrArg (fun f => f y) (filteredHomologyMap_ι D s n j)).trans hy⟩

include hinj hrep in
/-- Actual later-stage boundary witnesses make the genuine filtered cohomology map injective. -/
theorem filteredHomologyMap_injective (n : ℕ) : Function.Injective (filteredHomologyMap D s n) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro x hx
  change x = 0
  obtain ⟨i,y,rfl⟩ := Concrete.colimit_exists_rep (D ⋙ homologyFunctor (ModuleCat ℝ) (ComplexShape.up ℕ) n) x
  change filteredHomologyMap D s n (colimit.ι (D ⋙ homologyFunctor (ModuleCat ℝ) (ComplexShape.up ℕ) n) i y) = 0 at hx
  have hy : homologyMap (s.ι.app i) n y = 0 :=
    (congrArg (fun f => f y) (filteredHomologyMap_ι D s n i)).symm.trans hx
  obtain ⟨j,f,hf⟩ := filteredHomology_stage_zero D s hinj hrep n i y hy
  have h := congrArg (fun u => u y)
    (colimit.w (D ⋙ homologyFunctor (ModuleCat ℝ) (ComplexShape.up ℕ) n) f)
  exact h.symm.trans ((congrArg (colimit.ι (D ⋙ homologyFunctor (ModuleCat ℝ) (ComplexShape.up ℕ) n) j) hf).trans (map_zero _))

/-- Cohomology of a genuine degreewise injective filtered union is its actual cohomology colimit. -/
def filteredHomologyIso (n : ℕ) : colimit (D ⋙ homologyFunctor (ModuleCat ℝ) (ComplexShape.up ℕ) n) ≅
    s.pt.homology n :=
  (LinearEquiv.ofBijective (filteredHomologyMap D s n).hom
    ⟨filteredHomologyMap_injective D s hinj hrep n,filteredHomologyMap_surjective D s hinj hrep n⟩).toModuleIso

end TernaryPoly.SmoothSingularGlobal
