module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.ChainHomotopy

@[expose] public section

noncomputable section
namespace TernaryPoly.RelativeChainHomotopy
open CategoryTheory Limits HomologicalComplex

variable {C : Type*} [Category* C] [Abelian C] {ι : Type*} {c : ComplexShape ι}
  {K L K' L' : HomologicalComplex C c} (i : K ⟶ L) (j : K' ⟶ L')

/-- A compatible homotopy of subcomplex maps induces a homotopy between the literal
cokernel maps, with no degree or contractibility restriction. -/
def mapHomotopy {f g : L ⟶ L'} (H : Homotopy f g) (u v : K ⟶ K')
    (hf : i ≫ f = u ≫ j) (hg : i ≫ g = v ≫ j)
    (hH : ∀ p q, i.f p ≫ H.hom p q ≫ (cokernel.π j).f q = 0) :
    Homotopy (cokernel.map i j u f hf) (cokernel.map i j v g hg) :=
  descend i j H _ _ (by simp [cokernel.map]) (by simp [cokernel.map]) hH

/-- Componentwise compatibility with an actual homotopy on the subcomplex supplies the
vanishing condition needed to descend the ambient homotopy. -/
def mapHomotopyOfCompatible {f g : L ⟶ L'} (H : Homotopy f g)
    {u v : K ⟶ K'} (H' : Homotopy u v)
    (hf : i ≫ f = u ≫ j) (hg : i ≫ g = v ≫ j)
    (hH : ∀ p q, i.f p ≫ H.hom p q = H'.hom p q ≫ j.f q) :
    Homotopy (cokernel.map i j u f hf) (cokernel.map i j v g hg) := by
  apply mapHomotopy i j H u v hf hg
  intro p q
  rw [← Category.assoc, hH, Category.assoc]
  have hzero : j.f q ≫ (cokernel.π j).f q = 0 :=
    congrArg (fun m => m.f q) (cokernel.condition j)
  rw [hzero, comp_zero]

end TernaryPoly.RelativeChainHomotopy
