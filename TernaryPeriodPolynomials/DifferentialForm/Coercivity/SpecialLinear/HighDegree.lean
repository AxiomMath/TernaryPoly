module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.HodgeCasimir

@[expose] public section


/-! Direct Young-inequality coercivity in homogeneous degrees at least four. -/
noncomputable section
namespace TernaryPoly.SL3PolynomialCoercivity
open MvPolynomial

def compactCoefficientLift (a : TwoCoordinates) : TwoCoordinates :=
  fun i j => compactCoefficientCasimir (a i j)

def coefficientEnergy (a : TwoCoordinates) : ℝ :=
  ∑ k : Fin 3, twoPairing (coefficientLift (skewFrame k) a) (coefficientLift (skewFrame k) a)

def exteriorEnergy (a : TwoCoordinates) : ℝ :=
  ∑ k : Fin 3, twoPairing (compactExteriorAction k a) (compactExteriorAction k a)

def mixedEnergy (a : TwoCoordinates) : ℝ :=
  ∑ k : Fin 3, twoPairing (coefficientLift (skewFrame k) a) (compactExteriorAction k a)

theorem compactCoefficientLift_energy (a : TwoCoordinates) :
    twoPairing (compactCoefficientLift a) a = (1/2 : ℝ) * coefficientEnergy a := by
  simp only [twoPairing, compactCoefficientLift, compactCoefficientCasimir_energy,
    coefficientEnergy, coefficientLift, Fin.sum_univ_succ]
  ring

theorem coefficientEnergy_upper {n : ℕ} (a : TwoCoordinates)
    (ha : ∀ i j, (a i j).IsHomogeneous n) :
    coefficientEnergy a ≤ ((n : ℝ) * (n+1)) * twoPairing a a := by
  have h : twoPairing (compactCoefficientLift a) a ≤
      ((n : ℝ) * (n+1) / 2) * twoPairing a a := by
    unfold twoPairing compactCoefficientLift
    rw [mul_left_comm]
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1/2)
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hp := mul_le_mul_of_nonneg_left (compactCoefficientCasimir_upper (ha i j))
      (mul_nonneg (tangentWeight_pos i).le (tangentWeight_pos j).le)
    nlinarith
  rw [compactCoefficientLift_energy] at h
  linarith

theorem algebraicHodgeTwo_homogeneous_energy {n : ℕ} (a : TwoCoordinates)
    (ha : IsAlternatingTwo a) (hn : ∀ i j, (a i j).IsHomogeneous n) :
    twoPairing (algebraicHodgeTwo a) a =
      (2 * (n : ℝ) * (n+3) / 3) * twoPairing a a -
        (1/2 : ℝ) * coefficientEnergy a - (1/2 : ℝ) * mixedEnergy a := by
  have he : algebraicHodgeTwo a =
      (2 * (n : ℝ) * (n+3) / 3) • a - compactCoefficientLift a + hodgeCross a := by
    funext i j
    rw [algebraicHodgeTwo_split, fullCoefficientCasimir_homogeneous (hn i j)]
    rfl
  rw [he, twoPairing_add_left, twoPairing_sub_left, twoPairing_smul_left,
    compactCoefficientLift_energy, hodgeCross_energy a ha]
  simp [mixedEnergy, sub_eq_add_neg]

theorem twoPairing_young (a b : TwoCoordinates) (r s : ℝ) :
    0 ≤ r^2 * twoPairing a a + s^2 * twoPairing b b -
      2*r*s*twoPairing a b := by
  have hp := twoPairing_self_nonneg (r • a - s • b)
  rw [twoPairing_sub_left, twoPairing_smul_left, twoPairing_smul_left] at hp
  have h1 : twoPairing a (r • a - s • b) =
      r * twoPairing a a - s * twoPairing a b := by
    rw [twoPairing_symmetric, twoPairing_sub_left, twoPairing_smul_left,
      twoPairing_smul_left, twoPairing_symmetric b a]
  have h2 : twoPairing b (r • a - s • b) =
      r * twoPairing a b - s * twoPairing b b := by
    rw [twoPairing_symmetric, twoPairing_sub_left, twoPairing_smul_left,
      twoPairing_smul_left]
  rw [h1, h2] at hp
  nlinarith

theorem mixedEnergy_young (a : TwoCoordinates) (n : ℝ) :
    0 ≤ 9 * coefficientEnergy a + n^2 * exteriorEnergy a - 6*n*mixedEnergy a := by
  have h := Finset.sum_nonneg (s := Finset.univ) (fun k _ =>
    twoPairing_young (coefficientLift (skewFrame k) a) (compactExteriorAction k a) 3 n)
  norm_num [coefficientEnergy, exteriorEnergy, mixedEnergy, ← Finset.mul_sum,
    Finset.sum_add_distrib, Finset.sum_sub_distrib] at h ⊢
  exact h

theorem algebraicHodgeTwo_high_degree {n : ℕ} (hn : 4 ≤ n) (a : TwoCoordinates)
    (ha : IsAlternatingTwo a) (hd : ∀ i j, (a i j).IsHomogeneous n) :
    ((2*(n : ℝ)+3)*((n : ℝ)-3)/12)*twoPairing a a ≤
      twoPairing (algebraicHodgeTwo a) a := by
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hR := coefficientEnergy_upper a hd
  have hS : exteriorEnergy a ≤ 12 * twoPairing a a :=
    compactExteriorAction_energy_upper a ha
  have hY := mixedEnergy_young a (n : ℝ)
  rw [algebraicHodgeTwo_homogeneous_energy a ha hd]
  have hR' := mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ 2*(n:ℝ)+3)
  have hS' := mul_le_mul_of_nonneg_left hS (sq_nonneg (n:ℝ))
  apply (mul_le_mul_iff_right₀ (show 0 < 12*(n:ℝ) by positivity)).mp
  nlinarith

theorem homogeneousHodgeTwo_high_degree {n : ℕ} (hn : 4 ≤ n)
    (a : homogeneousTwoForms n) :
    ((2*(n : ℝ)+3)*((n : ℝ)-3)/12)*twoPairing a.val a.val ≤
      twoPairing (homogeneousHodgeTwo n a).val a.val :=
  algebraicHodgeTwo_high_degree hn a.val a.property.1 a.property.2

theorem homogeneousHodgeTwo_coercive_high_degree {n : ℕ} (hn : 4 ≤ n) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : homogeneousTwoForms n,
      c * twoPairing a.val a.val ≤ twoPairing (homogeneousHodgeTwo n a).val a.val := by
  refine ⟨(2*(n : ℝ)+3)*((n : ℝ)-3)/12, ?_, homogeneousHodgeTwo_high_degree hn⟩
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) < (n : ℝ)-3 := by linarith
  positivity

end TernaryPoly.SL3PolynomialCoercivity
