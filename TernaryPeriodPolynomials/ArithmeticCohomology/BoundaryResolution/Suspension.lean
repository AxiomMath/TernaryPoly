module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryResolution.Cone

@[expose] public section


noncomputable section
namespace TernaryPoly.BoundaryFaceResolutionComparison.Suspension
open CategoryTheory Category Limits HomologicalComplex Preadditive ZeroObject

variable {C : Type*} [Category* C] [Abelian C]

/-- The nonnegative chain suspension, with the literal negative differential. -/
def obj (A : ChainComplex C ℕ) : ChainComplex C ℕ where
  X | 0 => 0 | n+1 => A.X n
  d | 0, _ => 0 | _+1, 0 => 0 | n+1, m+1 => -A.d n m
  shape i j h := by
    cases i with
    | zero => rfl
    | succ i =>
      cases j with
      | zero => rfl
      | succ j =>
        change -A.d i j=0
        rw [A.shape i j (by simpa only [ComplexShape.down_Rel,Nat.add_right_cancel_iff] using h),neg_zero]
  d_comp_d' i j k _ _ := by
    cases i <;> cases j <;> cases k <;>
      simp only [zero_comp,comp_zero,neg_comp,comp_neg,A.d_comp_d,neg_zero]

def map {A B : ChainComplex C ℕ} (f : A ⟶ B) : obj A ⟶ obj B where
  f | 0 => 0 | n+1 => f.f n
  comm' i j hij := by
    obtain rfl : i=j+1 := hij.symm
    cases j with
    | zero =>
      change f.f 0 ≫ (0 : B.X 0 ⟶ 0)=(0 : A.X 0 ⟶ 0) ≫ (0 : (0 : C) ⟶ 0)
      simp only [comp_zero]
    | succ j =>
      change f.f (j+1) ≫ (-B.d (j+1) j)=(-A.d (j+1) j) ≫ f.f j
      simp only [comp_neg,neg_comp,f.comm]

@[simp] theorem map_comp {A B D : ChainComplex C ℕ} (f : A ⟶ B) (g : B ⟶ D) :
    map (f ≫ g)=map f ≫ map g := by
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero => simp only [map,HomologicalComplex.comp_f,zero_comp]
  | succ n => rfl

@[simp] theorem map_id (A : ChainComplex C ℕ) : map (𝟙 A)=𝟙 (obj A) := by
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero => exact (isZero_zero C).eq_of_src _ _
  | succ n => rfl

/-- Every chain homotopy suspends with the same negative sign as the differential. -/
def homotopy {A B : ChainComplex C ℕ} {f g : A ⟶ B} (h : Homotopy f g) :
    Homotopy (map f) (map g) where
  hom | 0, _ => 0 | _+1, 0 => 0 | n+1, m+1 => -h.hom n m
  zero i j hij := by
    cases i with
    | zero => rfl
    | succ i =>
      cases j with
      | zero => rfl
      | succ j =>
        change -h.hom i j=0
        rw [h.zero i j (by simpa only [ComplexShape.down_Rel,Nat.add_right_cancel_iff] using hij),neg_zero]
  comm n := by
    cases n with
    | zero => exact (isZero_zero C).eq_of_src _ _
    | succ n =>
      have hh := h.comm n
      rw [dNext_nat,prevD_eq _ (Cone.downRel n)] at hh
      rw [dNext_nat,prevD_eq _ (Cone.downRel (n+1))]
      cases n with
      | zero =>
        change f.f 0=(0 : A.X 0 ⟶ 0) ≫ (0 : (0 : C) ⟶ B.X 0) +
          (-h.hom 0 1) ≫ (-B.d 1 0) + g.f 0
        rw [zero_comp,neg_comp,comp_neg,neg_neg]
        simpa only [Nat.zero_sub,A.shape 0 0 (by simp [ComplexShape.down_Rel]),zero_comp] using hh
      | succ n =>
        change f.f (n+1)=(-A.d (n+1) n) ≫ (-h.hom n (n+1)) +
          (-h.hom (n+1) (n+2)) ≫ (-B.d (n+2) (n+1)) + g.f (n+1)
        rw [neg_comp,comp_neg,neg_neg,neg_comp,comp_neg,neg_neg]
        exact hh

/-- A chain homotopy equivalence suspends to an actual chain homotopy equivalence. -/
def equivalence {A B : ChainComplex C ℕ} (e : _root_.HomotopyEquiv A B) :
    _root_.HomotopyEquiv (obj A) (obj B) where
  hom := map e.hom
  inv := map e.inv
  homotopyHomInvId := by simpa only [map_comp,map_id] using homotopy e.homotopyHomInvId
  homotopyInvHomId := by simpa only [map_comp,map_id] using homotopy e.homotopyInvHomId

end TernaryPoly.BoundaryFaceResolutionComparison.Suspension
