module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.ChainSequence
public import Mathlib.Algebra.Homology.Homotopy

@[expose] public section


noncomputable section
namespace TernaryPoly.RelativeChainHomotopy
open CategoryTheory Limits HomologicalComplex

variable {C : Type*} [Category* C] [Abelian C] {ι : Type*} {c : ComplexShape ι}
  {K L K' L' : HomologicalComplex C c} (i : K ⟶ L) (j : K' ⟶ L')

/-- Descent of a single degreewise morphism through the actual complex cokernel. -/
def degreeDesc (p : ι) {Z : C} (f : L.X p ⟶ Z) (hf : i.f p ≫ f = 0) :
    (cokernel i).X p ⟶ Z :=
  (PreservesCokernel.iso (eval C c p) i).hom ≫ cokernel.desc (i.f p) f hf

@[reassoc (attr := simp)]
theorem projection_degreeDesc (p : ι) {Z : C} (f : L.X p ⟶ Z)
    (hf : i.f p ≫ f = 0) :
    (cokernel.π i).f p ≫ degreeDesc i p f hf = f := by
  change (eval C c p).map (cokernel.π i) ≫
    (PreservesCokernel.iso (eval C c p) i).hom ≫ cokernel.desc ((eval C c p).map i) f hf = f
  rw [PreservesCokernel.π_iso_hom_assoc]
  exact cokernel.π_desc ((eval C c p).map i) f hf

/-- A chain homotopy descends through quotient complexes whenever its components preserve
those subcomplexes, expressed by their vanishing after the actual target projection. -/
def descend {f g : L ⟶ L'} (H : Homotopy f g)
    (f' g' : cokernel i ⟶ cokernel j)
    (hf : cokernel.π i ≫ f' = f ≫ cokernel.π j)
    (hg : cokernel.π i ≫ g' = g ≫ cokernel.π j)
    (hH : ∀ p q, i.f p ≫ H.hom p q ≫ (cokernel.π j).f q = 0) :
    Homotopy f' g' where
  hom p q := degreeDesc i p (H.hom p q ≫ (cokernel.π j).f q) (hH p q)
  zero p q hpq := by
    apply (cancel_epi ((cokernel.π i).f p)).mp
    simp only [projection_degreeDesc, H.zero p q hpq, zero_comp, comp_zero]
  comm p := by
    apply (cancel_epi ((cokernel.π i).f p)).mp
    have hf' := congrArg (fun m => m.f p) hf
    have hg' := congrArg (fun m => m.f p) hg
    dsimp only [comp_f] at hf' hg'
    have heq : (fun p q => (cokernel.π i).f p ≫
        degreeDesc i p (H.hom p q ≫ (cokernel.π j).f q) (hH p q)) =
        (fun p q => H.hom p q ≫ (cokernel.π j).f q) := by
      funext p q
      exact projection_degreeDesc i p _ _
    have hd := congrArg (dNext p) heq
    rw [dNext_comp_left, dNext_comp_right] at hd
    have hp := congrArg (prevD p) heq
    rw [prevD_comp_left, prevD_comp_right] at hp
    rw [Preadditive.comp_add, Preadditive.comp_add, hf', hg', hd, hp]
    simpa only [Preadditive.add_comp] using
      congrArg (fun a => a ≫ (cokernel.π j).f p) (H.comm p)

/-- Quotient maps related by a genuine subcomplex-preserving chain homotopy have the same
map on homology, in every degree. -/
theorem homologyMap_eq {f g : L ⟶ L'} (H : Homotopy f g)
    (f' g' : cokernel i ⟶ cokernel j)
    (hf : cokernel.π i ≫ f' = f ≫ cokernel.π j)
    (hg : cokernel.π i ≫ g' = g ≫ cokernel.π j)
    (hH : ∀ p q, i.f p ≫ H.hom p q ≫ (cokernel.π j).f q = 0) (p : ι) :
    homologyMap f' p = homologyMap g' p :=
  (descend i j H f' g' hf hg hH).homologyMap_eq p

end TernaryPoly.RelativeChainHomotopy
