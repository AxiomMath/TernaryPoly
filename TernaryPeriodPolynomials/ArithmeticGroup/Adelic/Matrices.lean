module

public import TernaryPeriodPolynomials.ArithmeticGroup.Adelic.Ring
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public section


noncomputable section
namespace GeneralEisenstein.Adelic
open Matrix
abbrev GL3 (R : Type*) [CommRing R] := GeneralLinearGroup (Fin 3) R

def InPlaneParabolic {R : Type*} [CommRing R] (g : GL3 R) : Prop :=
  g.val 2 0 = 0 ∧ g.val 2 1 = 0

/-- The actual associate-parabolic Weyl element. -/
def weyl {R : Type*} [CommRing R] : GL3 R :=
  ⟨!![0,0,1;1,0,0;0,1,0],!![0,1,0;0,0,1;1,0,0],by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_three],by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_three]⟩

def upperUnipotent {R : Type*} [CommRing R] (s t : R) : GL3 R :=
  ⟨!![1,s,t;0,1,0;0,0,1],!![1,-s,-t;0,1,0;0,0,1],by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_three],by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_three]⟩


end GeneralEisenstein.Adelic

end
