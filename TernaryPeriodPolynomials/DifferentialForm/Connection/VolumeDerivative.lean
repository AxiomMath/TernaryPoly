module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.VolumeDeterminant
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section


/-! Determinant variation of an actual matrix congruence, in arbitrary finite dimension. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix ContinuousAlternatingMap
open scoped Matrix.Norms.Elementwise

theorem hasDerivAt_finite_matrix_product {m : ℕ} {A B : ℝ → Matrix (Fin m) (Fin m) ℝ}
    {R S : Matrix (Fin m) (Fin m) ℝ} {t : ℝ} (hA : HasDerivAt A R t) (hB : HasDerivAt B S t) :
    HasDerivAt (fun u => A u * B u) (R * B t + A t * S) t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have h := HasDerivAt.sum (u := Finset.univ) (fun k _ =>
    (hasDerivAt_pi.mp (hasDerivAt_pi.mp hA i) k).mul (hasDerivAt_pi.mp (hasDerivAt_pi.mp hB k) j))
  convert! h using 1
  · funext u
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.mul_apply]
  · simp only [Matrix.add_apply, Matrix.mul_apply, Finset.sum_add_distrib]

theorem hasDerivAt_finite_matrix_transpose {m : ℕ} {A : ℝ → Matrix (Fin m) (Fin m) ℝ}
    {R : Matrix (Fin m) (Fin m) ℝ} {t : ℝ} (hA : HasDerivAt A R t) :
    HasDerivAt (fun u => (A u).transpose) R.transpose t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  exact hasDerivAt_pi.mp (hasDerivAt_pi.mp hA j) i

theorem hasDerivAt_matrix_affine_identity (m : ℕ) (K : Matrix (Fin m) (Fin m) ℝ) :
    HasDerivAt (fun t : ℝ => (1 : Matrix (Fin m) (Fin m) ℝ) + t • K) K 0 := by
  convert! (hasDerivAt_const (0 : ℝ) (1 : Matrix (Fin m) (Fin m) ℝ)).add
    ((hasDerivAt_id (0 : ℝ)).smul_const K) using 1
  simp

theorem hasDerivAt_matrix_gram_congruence (m : ℕ) (G K : Matrix (Fin m) (Fin m) ℝ) :
    HasDerivAt (fun t : ℝ => ((1 : Matrix (Fin m) (Fin m) ℝ) + t • K).transpose * G *
      ((1 : Matrix (Fin m) (Fin m) ℝ) + t • K)) (K.transpose * G + G * K) 0 := by
  have h := hasDerivAt_finite_matrix_product
    (hasDerivAt_finite_matrix_product (hasDerivAt_finite_matrix_transpose (hasDerivAt_matrix_affine_identity m K))
      (hasDerivAt_const (0 : ℝ) G)) (hasDerivAt_matrix_affine_identity m K)
  convert! h using 1
  simp

theorem hasDerivAt_det_matrix_gram_congruence (m : ℕ) (G K : Matrix (Fin m) (Fin m) ℝ) :
    HasDerivAt (fun t : ℝ => (((1 : Matrix (Fin m) (Fin m) ℝ) + t • K).transpose * G *
      ((1 : Matrix (Fin m) (Fin m) ℝ) + t • K)).det) (2 * G.det * K.trace) 0 := by
  have hd := hasDerivAt_det_identity m _ K (hasDerivAt_matrix_affine_identity m K) (by simp)
  have h := (hd.mul_const G.det).mul hd
  convert! h using 1
  · funext t
    simp only [Matrix.det_mul, Matrix.det_transpose, Pi.mul_apply]
  · simp only [zero_smul, add_zero, Matrix.det_one, mul_one, one_mul]
    ring

/-- A metric with the actual congruence first variation has the corresponding determinant variation. -/
theorem hasDerivAt_det_of_gram_variation (m : ℕ) (A : ℝ → Matrix (Fin m) (Fin m) ℝ)
    (G K : Matrix (Fin m) (Fin m) ℝ) (hA : HasDerivAt A (K.transpose * G + G * K) 0)
    (h0 : A 0 = G) : HasDerivAt (fun t => (A t).det) (2 * G.det * K.trace) 0 := by
  have ha := (determinantRows m).hasFDerivAt G |>.comp_hasDerivAt_of_eq 0 hA h0.symm
  have hb := (determinantRows m).hasFDerivAt G |>.comp_hasDerivAt_of_eq 0
    (hasDerivAt_matrix_gram_congruence m G K) (by simp; rfl)
  have he := hb.unique (hasDerivAt_det_matrix_gram_congruence m G K)
  rw [he] at ha
  exact ha

end TernaryPoly.PolynomialFormConnection
