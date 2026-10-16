module

public import TernaryPeriodPolynomials.Polynomial.Homogeneous
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RepresentationTheory.Basic
public import Batteries.Data.List.Count
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.RingTheory.Finiteness.Lattice

@[expose] public section

open MvPolynomial Matrix
noncomputable section
namespace TernaryPoly.BinaryModularSymbolCoefficients

abbrev Poly := MvPolynomial (Fin 2) ℚ
abbrev GL2 := Matrix.GeneralLinearGroup (Fin 2) ℚ

/-- The literal linear coordinate form associated to a matrix row. -/
def linearForm (M : Matrix (Fin 2) (Fin 2) ℚ) (i : Fin 2) : Poly :=
  ∑ j, MvPolynomial.C (M i j)*X j

/-- Right polynomial substitution by the displayed matrix. -/
def substitute (M : Matrix (Fin 2) (Fin 2) ℚ) : Poly →ₐ[ℚ] Poly :=
  bind₁ (linearForm M)

theorem substitute_linearForm (M N : Matrix (Fin 2) (Fin 2) ℚ) (i : Fin 2) :
    substitute M (linearForm N i)=linearForm (N*M) i := by
  simp only [linearForm,substitute,map_sum,map_mul,bind₁_C_right,bind₁_X_right,
    Matrix.mul_apply,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem substitute_X (M : Matrix (Fin 2) (Fin 2) ℚ) (i : Fin 2) :
    substitute M (X i)=linearForm M i := by simp [substitute]

/-- Substitutions compose in the reverse matrix order. -/
theorem substitute_comp (M N : Matrix (Fin 2) (Fin 2) ℚ) :
    (substitute M).comp (substitute N)=substitute (N*M) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply,substitute_X]
  exact substitute_linearForm M N i

theorem substitute_one : substitute (1 : Matrix (Fin 2) (Fin 2) ℚ)=AlgHom.id ℚ Poly := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [substitute,linearForm,Matrix.one_apply]

/-- Inverse substitution is the genuine left action on polynomial coefficients. -/
def untwisted : Representation ℚ GL2 Poly where
  toFun g := (substitute (g⁻¹ : GL2)).toLinearMap
  map_one' := by
    simp only [inv_one,GeneralLinearGroup.coe_one,substitute_one]
    rfl
  map_mul' g h := by
    simp only [_root_.mul_inv_rev,GeneralLinearGroup.coe_mul]
    exact congrArg (fun q : Poly →ₐ[ℚ] Poly => q.toLinearMap)
      (substitute_comp (g⁻¹ : GL2) (h⁻¹ : GL2)).symm

/-- The exact rational determinant character; exponent -1 is the paper's scalar action. -/
def determinantCharacter (e : ℤ) : GL2 →* ℚ where
  toFun g := ((GeneralLinearGroup.det g : ℚˣ) : ℚ)^e
  map_one' := by simp
  map_mul' g h := by simp [mul_zpow]

/-- Polynomial coefficients with their actual determinant twist. -/
def action (e : ℤ) : Representation ℚ GL2 Poly where
  toFun g := determinantCharacter e g • untwisted g
  map_one' := by simp
  map_mul' g h := by
    apply LinearMap.ext
    intro f
    change determinantCharacter e (g*h) • untwisted (g*h) f =
      determinantCharacter e g • untwisted g (determinantCharacter e h • untwisted h f)
    rw [map_mul,map_mul,Module.End.mul_apply,map_smul,smul_smul]

theorem action_apply (e : ℤ) (g : GL2) (f : Poly) :
    action e g f=determinantCharacter e g • substitute (g⁻¹ : GL2) f := rfl

theorem linearForm_homogeneous (M : Matrix (Fin 2) (Fin 2) ℚ) (i : Fin 2) :
    (linearForm M i).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro j _
  exact isHomogeneous_C_mul_X _ _

theorem substitute_homogeneous (M : Matrix (Fin 2) (Fin 2) ℚ)
    {f : Poly} {n : ℕ} (hf : f.IsHomogeneous n) : (substitute M f).IsHomogeneous n :=
  isHomogeneous_bind₁_linear hf (linearForm M) (linearForm_homogeneous M)

theorem action_homogeneous (e : ℤ) (g : GL2) {f : Poly} {n : ℕ}
    (hf : f.IsHomogeneous n) : (action e g f).IsHomogeneous n := by
  rw [action_apply,Algebra.smul_def]
  exact (substitute_homogeneous _ hf).C_mul _

/-- The exact degree-`n` coefficient space, including the zero polynomial. -/
abbrev HomogeneousPoly (n : ℕ) := homogeneousSubmodule (Fin 2) ℚ n

/-- The genuine homogeneous coefficient representation. -/
def homogeneousAction (n : ℕ) (e : ℤ) : Representation ℚ GL2 (HomogeneousPoly n) :=
  (action e).subrepresentation (homogeneousSubmodule (Fin 2) ℚ n)
    (fun g _ hf => action_homogeneous e g hf)

@[simp] theorem homogeneousAction_coe (n : ℕ) (e : ℤ) (g : GL2)
    (f : HomogeneousPoly n) :
    ((homogeneousAction n e g f : HomogeneousPoly n) : Poly) = action e g f := rfl

/-- Restriction to integer matrices uses the actual coefficient-extension map. -/
def integralAction (n : ℕ) (e : ℤ) :
    Representation ℚ (Matrix.GeneralLinearGroup (Fin 2) ℤ) (HomogeneousPoly n) :=
  (homogeneousAction n e).comp (GeneralLinearGroup.map (Int.castRingHom ℚ))

@[simp] theorem integralAction_coe (n : ℕ) (e : ℤ)
    (g : Matrix.GeneralLinearGroup (Fin 2) ℤ) (f : HomogeneousPoly n) :
    ((integralAction n e g f : HomogeneousPoly n) : Poly) =
      action e (GeneralLinearGroup.map (Int.castRingHom ℚ) g) f := rfl

end TernaryPoly.BinaryModularSymbolCoefficients
