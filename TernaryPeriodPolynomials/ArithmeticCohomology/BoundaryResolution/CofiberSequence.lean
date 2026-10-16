module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryResolution.Suspension
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

@[expose] public section

noncomputable section
namespace TernaryPoly.BoundaryFaceResolutionComparison.CofiberSequence
open CategoryTheory Category Limits HomologicalComplex Preadditive ZeroObject

variable {C : Type*} [Category* C] [Abelian C] {A B : ChainComplex C ℕ} (f : A ⟶ B)

def first (n : ℕ) : (homotopyCofiber f).X (n+1) ⟶ A.X n :=
  homotopyCofiber.fstX f (n+1) n (Cone.downRel n)
def left (n : ℕ) : A.X n ⟶ (homotopyCofiber f).X (n+1) :=
  homotopyCofiber.inlX f n (n+1) (Cone.downRel n)
def second (n : ℕ) : (homotopyCofiber f).X n ⟶ B.X n := homotopyCofiber.sndX f n
def right (n : ℕ) : B.X n ⟶ (homotopyCofiber f).X n := homotopyCofiber.inrX f n

@[simp] theorem left_first (n : ℕ) : left f n ≫ first f n=𝟙 _ := homotopyCofiber.inlX_fstX f n (n+1) _
@[simp] theorem left_second (n : ℕ) : left f n ≫ second f (n+1)=0 := homotopyCofiber.inlX_sndX f n (n+1) _
@[simp] theorem right_first (n : ℕ) : right f (n+1) ≫ first f n=0 := homotopyCofiber.inrX_fstX f (n+1) n _
@[simp] theorem right_second (n : ℕ) : right f n ≫ second f n=𝟙 _ := homotopyCofiber.inrX_sndX f n

def projection : homotopyCofiber f ⟶ Suspension.obj A where
  f | 0 => 0 | n+1 => first f n
  comm' i j hij := by
    obtain rfl : i=j+1 := hij.symm
    cases j with
    | zero =>
      change first f 0 ≫ (0 : A.X 0 ⟶ 0)=(homotopyCofiber f).d 1 0 ≫ 0
      simp only [comp_zero]
    | succ n =>
      change first f (n+1) ≫ (-A.d (n+1) n)=(homotopyCofiber f).d (n+2) (n+1) ≫ first f n
      exact (comp_neg _ _).trans (homotopyCofiber.d_fstX f (n+2) (n+1) n
        (Cone.downRel (n+1)) (Cone.downRel n)).symm

theorem inr_projection : homotopyCofiber.inr f ≫ projection f=0 := by
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero => exact comp_zero
  | succ n => exact right_first f n

/-- The actual cone short complex has middle inclusion and projection to the signed suspension. -/
def shortComplex : ShortComplex (ChainComplex C ℕ) :=
  ShortComplex.mk (homotopyCofiber.inr f) (projection f) (inr_projection f)

def sectionDegree : ∀ n, (Suspension.obj A).X n ⟶ (homotopyCofiber f).X n
  | 0 => 0
  | n+1 => left f n

/-- Its graded splitting is given by the actual cone summand maps. -/
def splitting (n : ℕ) :
    ((shortComplex f).map (HomologicalComplex.eval C (ComplexShape.down ℕ) n)).Splitting where
  r := second f n
  s := sectionDegree f n
  f_r := right_second f n
  s_g := by
    cases n with
    | zero => exact (isZero_zero C).eq_of_src _ _
    | succ n => exact left_first f n
  id := by
    cases n with
    | zero =>
      change second f 0 ≫ right f 0 + (0 : (homotopyCofiber f).X 0 ⟶ 0) ≫ (0 : (0 : C) ⟶ (homotopyCofiber f).X 0)=𝟙 ((homotopyCofiber f).X 0)
      rw [zero_comp,add_zero]
      exact homotopyCofiber.sndX_inrX f 0 (by simp [ComplexShape.down_Rel])
    | succ n =>
      change second f (n+1) ≫ right f (n+1) + first f n ≫ left f n=𝟙 _
      apply homotopyCofiber.ext_from_X f n (n+1) (Cone.downRel n)
      · change left f n ≫ (second f (n+1) ≫ right f (n+1) + first f n ≫ left f n)=left f n ≫ 𝟙 _
        simp only [comp_add,←Category.assoc,left_first,left_second,zero_comp,id_comp,zero_add,comp_id]
      · change right f (n+1) ≫ (second f (n+1) ≫ right f (n+1) + first f n ≫ left f n)=right f (n+1) ≫ 𝟙 _
        simp only [comp_add,←Category.assoc,right_first,right_second,zero_comp,id_comp,add_zero,comp_id]

theorem shortExact : (shortComplex f).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun n => (splitting f n).shortExact)

end TernaryPoly.BoundaryFaceResolutionComparison.CofiberSequence
