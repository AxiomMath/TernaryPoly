module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.TypeData
public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.MeanValue

@[expose] public section


/-!
# `SO(2)` as the range of the rotation matrices, and the weight character on rotations

`MeanValue.rot θ` is the rotation matrix `!![cos θ, -sin θ; sin θ, cos θ]`.  This file shows that
the subgroup `TypeData.so2 ⊆ GL₂(ℝ)` is exactly the set of the units `rotUnit θ`, and that the
weight character `TypeData.typeCharacter k K` takes the value `exp (k θ i)` on an element of
`typeGroup K` with archimedean part `rotUnit θ`.  These are the two facts connecting the abstract
type subspace of `AbstractIrreducibility` to the Fourier projection of `MeanValue.weight_projection`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.Automorphic.SmoothVectors
open TernaryPeriodPolynomials.Automorphic.TypeData
open TernaryPeriodPolynomials.Automorphic.MeanValue (rot)

namespace TernaryPeriodPolynomials.Automorphic.Weight

theorem rot_mul_rot_neg (θ : ℝ) : rot θ * rot (-θ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [Real.sin_sq_add_cos_sq θ]

/-- The rotation by `θ` as an element of `GL₂(ℝ)`. -/
def rotUnit (θ : ℝ) : BinaryRealGL where
  val := rot θ
  inv := rot (-θ)
  val_inv := rot_mul_rot_neg θ
  inv_val := by simpa using rot_mul_rot_neg (-θ)

theorem rotUnit_val (θ : ℝ) : (rotUnit θ).val = rot θ := rfl

theorem rotUnit_mem_so2 (θ : ℝ) : rotUnit θ ∈ so2 := by
  show (rot θ).transpose * rot θ = 1 ∧ (rot θ).det = 1
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rot, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [Real.sin_sq_add_cos_sq θ]
  · rw [Matrix.det_fin_two]
    simp [rot]
    nlinarith [Real.sin_sq_add_cos_sq θ]

/-- Every element of `SO(2)` is a rotation matrix. -/
theorem exists_rotUnit_of_mem_so2 {g : BinaryRealGL} (hg : g ∈ so2) : ∃ θ : ℝ, g = rotUnit θ := by
  obtain ⟨hT, hdet⟩ : g.val.transpose * g.val = 1 ∧ g.val.det = 1 := hg
  have h00 : g.val 0 0 * g.val 0 0 + g.val 1 0 * g.val 1 0 = 1 := by
    have := congrFun (congrFun hT 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h01 : g.val 0 0 * g.val 0 1 + g.val 1 0 * g.val 1 1 = 0 := by
    have := congrFun (congrFun hT 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have hd : g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0 = 1 := by
    rw [Matrix.det_fin_two] at hdet
    exact hdet
  have hd11 : g.val 1 1 = g.val 0 0 := by
    linear_combination g.val 0 0 * hd + g.val 1 0 * h01 - g.val 1 1 * h00
  have hb : g.val 0 1 = -g.val 1 0 := by
    linear_combination (-g.val 1 0) * hd + g.val 0 0 * h01 - g.val 0 1 * h00
  obtain ⟨z, hzre, hzim⟩ : ∃ z : ℂ, z.re = g.val 0 0 ∧ z.im = g.val 1 0 :=
    ⟨⟨g.val 0 0, g.val 1 0⟩, rfl, rfl⟩
  have hsq : ‖z‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hzre, hzim]
    exact h00
  have hnorm : ‖z‖ = 1 := by nlinarith [norm_nonneg z]
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hcos : Real.cos (Complex.arg z) = g.val 0 0 := by
    rw [Complex.cos_arg hz0, hnorm, div_one, hzre]
  have hsin : Real.sin (Complex.arg z) = g.val 1 0 := by
    rw [Complex.sin_arg, hnorm, div_one, hzim]
  refine ⟨Complex.arg z, Units.ext ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotUnit, rot, hcos, hsin, hd11, hb]

/-- `SO(2)` is the range of the rotations. -/
theorem mem_so2_iff {g : BinaryRealGL} : g ∈ so2 ↔ ∃ θ : ℝ, g = rotUnit θ :=
  ⟨exists_rotUnit_of_mem_so2, fun ⟨θ, h⟩ => h ▸ rotUnit_mem_so2 θ⟩

/-- The weight character on an element of the type group with archimedean part `rotUnit θ`. -/
theorem typeCharacter_of_realPart_eq (k : ℕ) (K : Subgroup BinaryFiniteGL) (c : typeGroup K)
    (θ : ℝ) (h : realPart c.val = rotUnit θ) :
    typeCharacter k K c = Complex.exp (k * θ * Complex.I) := by
  unfold typeCharacter
  rw [h]
  have h10 : (rotUnit θ).val 1 0 = Real.sin θ := by simp [rotUnit, rot]
  have h11 : (rotUnit θ).val 1 1 = Real.cos θ := by simp [rotUnit, rot]
  rw [h10, h11, show (k : ℂ) * θ * Complex.I = k * (θ * Complex.I) by ring, Complex.exp_nat_mul,
    Complex.exp_mul_I]
  push_cast
  congr 1
  ring

/-- The inverse weight character, `c ↦ j(c_∞, i)^(-k)`: the character by which the weight-`k`
holomorphic lifts transform under the right translation by `SO(2)`
(`Φ(x r_θ) = exp (-i k θ) Φ(x)`). -/
def typeCharacterInv (k : ℕ) (K : Subgroup BinaryFiniteGL) : typeGroup K → ℂ :=
  fun c => (typeCharacter k K c)⁻¹

theorem typeCharacterInv_of_realPart_eq (k : ℕ) (K : Subgroup BinaryFiniteGL) (c : typeGroup K)
    (θ : ℝ) (h : realPart c.val = rotUnit θ) :
    typeCharacterInv k K c = Complex.exp (-(k * θ * Complex.I)) := by
  unfold typeCharacterInv
  rw [typeCharacter_of_realPart_eq k K c θ h, Complex.exp_neg]

end TernaryPeriodPolynomials.Automorphic.Weight
