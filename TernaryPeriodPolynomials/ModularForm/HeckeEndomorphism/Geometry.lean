module

public import TernaryPeriodPolynomials.ModularForm.HeckeEndomorphism.Matrices
public import Mathlib.Geometry.Manifold.Notation

@[expose] public section


noncomputable section
open Matrix UpperHalfPlane Complex
open scoped Manifold MatrixGroups ModularForm
namespace TernaryPoly.BinaryCuspHeckeEndomorphism
open BinaryModularSymbol (GL2)
open BinaryRationalHeckePrime BinaryCuspPeriod BinaryCuspHecke

@[simp] theorem realify_apply (g : GL2) (i j : Fin 2) :
    (realify g).val i j = (g.val i j : ℝ) := rfl

@[simp] theorem real_upper_det (p : ℕ) [Fact p.Prime] (i : PrimeIndex p) :
    (realify (upper p i)).det.val = (p : ℝ) := by
  change ((upper p i).val.map (Rat.castHom ℝ)).det = _
  rw [upper_matrix]
  cases i <;> simp [Matrix.det_fin_two]

theorem real_upper_det_pos (p : ℕ) [Fact p.Prime] (i : PrimeIndex p) :
    0 < (realify (upper p i)).det.val := by
  rw [real_upper_det]
  exact_mod_cast (Fact.out : p.Prime).pos

@[simp] theorem real_upper_lowerleft (p : ℕ) [Fact p.Prime] (i : PrimeIndex p) :
    (realify (upper p i)).val 1 0 = 0 := by
  rw [realify_apply,upper_matrix]
  cases i <;> simp

theorem upper_smul_finite (p : ℕ) [Fact p.Prime] (b : ZMod p) (z : ℍ) :
    realify (upper p (.inl b)) • z =
      divideTranslate p (Fact.out : p.Prime).pos ⟨b.val,ZMod.val_lt b⟩ z := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos (real_upper_det_pos p (.inl b))]
  simp [num,denom,realify_apply,upper_matrix]
  simp only [ZMod.cast_eq_val]
  norm_cast

theorem upper_smul_infty (p : ℕ) [Fact p.Prime] (z : ℍ) :
    realify (upper p (.inr ())) • z = dilate p (Fact.out : p.Prime).pos z := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos (real_upper_det_pos p (.inr ()))]
  simp [num,denom,realify_apply,upper_matrix]

theorem upper_sigma (p : ℕ) [Fact p.Prime] (i : PrimeIndex p) (w : ℂ) :
    UpperHalfPlane.σ (realify (upper p i)) w = w := by
  rw [UpperHalfPlane.σ,ite_eq_left (real_upper_det_pos p i)]
  rfl

theorem upper_denom_finite (p : ℕ) [Fact p.Prime] (b : ZMod p) (z : ℍ) :
    denom (realify (upper p (.inl b))) z = (p : ℂ) := by
  simp [denom,realify_apply,upper_matrix]

theorem upper_denom_infty (p : ℕ) [Fact p.Prime] (z : ℍ) :
    denom (realify (upper p (.inr ()))) z = 1 := by
  simp [denom,realify_apply,upper_matrix]

/-- Each finite upper slash term has exactly the 1/p coefficient of the standard formula. -/
theorem slash_upper_finite {d : ℕ} (p : ℕ) [Fact p.Prime] (f : Forms d) (b : ZMod p) (z : ℍ) :
    ((f : ℍ → ℂ) ∣[(d : ℤ)+2] realify (upper p (.inl b))) z =
      (1 / (p : ℂ)) * f (divideTranslate p (Fact.out : p.Prime).pos ⟨b.val,ZMod.val_lt b⟩ z) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpow : (p : ℂ)^((d : ℤ)+2-1) * (p : ℂ)^(-((d : ℤ)+2)) = 1/(p : ℂ) := by
    rw [←zpow_add₀ hp0,show ((d : ℤ)+2-1) + (-((d : ℤ)+2)) = -1 by omega]
    simp
  rw [ModularForm.slash_apply,upper_sigma,upper_smul_finite,real_upper_det,
    abs_of_pos hp,upper_denom_finite]
  change _ * (p : ℂ)^((d : ℤ)+2-1) * (p : ℂ)^(-((d : ℤ)+2)) = _
  rw [mul_assoc,hpow,mul_comm]

/-- The infinite upper slash term is exactly p^(d+1) times dilation. -/
theorem slash_upper_infty {d : ℕ} (p : ℕ) [Fact p.Prime] (f : Forms d) (z : ℍ) :
    ((f : ℍ → ℂ) ∣[(d : ℤ)+2] realify (upper p (.inr ()))) z =
      (p : ℂ)^(d+1) * f (dilate p (Fact.out : p.Prime).pos z) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hpow : (p : ℂ)^((d : ℤ)+2-1) = (p : ℂ)^(d+1) := by
    rw [show (d : ℤ)+2-1 = ((d+1 : ℕ) : ℤ) by omega,zpow_natCast]
  rw [ModularForm.slash_apply,upper_sigma,upper_smul_infty,real_upper_det,
    abs_of_pos hp,upper_denom_infty,_root_.one_zpow,mul_one]
  change _ * (p : ℂ)^((d : ℤ)+2-1) = _
  rw [hpow,mul_comm]

/-- Each actual upper slash transform is holomorphic. -/
theorem slash_upper_holo {d : ℕ} (p : ℕ) [Fact p.Prime] (f : Forms d) (i : PrimeIndex p) :
    MDiff ((f : ℍ → ℂ) ∣[(d : ℤ)+2] realify (upper p i)) :=
  (CuspFormClass.holo f).slash _ _

/-- Each actual upper slash transform vanishes at infinity. -/
theorem slash_upper_zero_at_infty {d : ℕ} (p : ℕ) [Fact p.Prime] (f : Forms d) (i : PrimeIndex p) :
    IsZeroAtImInfty ((f : ℍ → ℂ) ∣[(d : ℤ)+2] realify (upper p i)) :=
  (CuspFormClass.zero_at_infty f).slash _ (real_upper_lowerleft p i)

end TernaryPoly.BinaryCuspHeckeEndomorphism
