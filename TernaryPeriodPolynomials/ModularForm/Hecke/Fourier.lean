module

public import TernaryPeriodPolynomials.ModularForm.Hecke.Basic

@[expose] public section


noncomputable section
open Complex
open UpperHalfPlane hiding I

namespace TernaryPoly.BinaryCuspHecke
open BinaryCuspPeriod

/-- The finite average of translated Fourier monomials selects exactly multiples of p. -/
theorem average_monomial (p : ℕ) (hp : 0 < p) (z : ℍ) (n : ℕ) (a : ℂ) :
    (1 / (p : ℂ)) * (∑ b : Fin p, a * q (divideTranslate p hp b z) ^ n) =
      if p ∣ n then a * q (divideTranslate p hp ⟨0, hp⟩ z) ^ n else 0 := by
  have ht : (∑ b : Fin p, a * q (divideTranslate p hp b z) ^ n) =
      ∑ b : Fin p, a * (q (divideTranslate p hp ⟨0, hp⟩ z) * root p ^ b.val) ^ n := by
    apply Finset.sum_congr rfl
    intro b hb
    rw [q_divideTranslate]
  rw [ht]
  simp_rw [mul_pow, ← mul_assoc]
  rw [← Finset.mul_sum, root_power_sum_exp (Nat.ne_of_gt hp)]
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  split_ifs
  · field_simp
  · simp

/-- The p-to-one Fourier-index map is injective. -/
theorem mul_index_injective (p : ℕ) (hp : 0 < p) :
    Function.Injective (fun n : ℕ => p*n) := by
  intro m n h
  exact Nat.eq_of_mul_eq_mul_left hp h

/-- The translated average has precisely the U_p coefficient sequence a(p*n). -/
theorem hasSum_average {d : ℕ} (f : Forms d) (p : ℕ) (hp : 0 < p) (z : ℍ) :
    HasSum (fun n => coefficients f (p*n) * q z ^ n)
      ((1 / (p : ℂ)) * ∑ b : Fin p, f (divideTranslate p hp b z)) := by
  have hs := (hasSum_sum (s := Finset.univ)
    (fun b _ => hasSum_coefficients f (divideTranslate p hp b z))).mul_left (1 / (p : ℂ))
  simp only [average_monomial] at hs
  have hz : ∀ n ∉ Set.range (fun m : ℕ => p*m),
      (if p ∣ n then coefficients f n * q (divideTranslate p hp ⟨0, hp⟩ z) ^ n else 0) = 0 := by
    intro n hn
    have hnd : ¬p ∣ n := by
      rintro ⟨m, rfl⟩
      exact hn ⟨m, rfl⟩
    simp [hnd]
  have ht := ((mul_index_injective p hp).hasSum_iff hz).mpr hs
  simpa only [Function.comp_def, dvd_mul_right, ite_true, pow_mul, q_divide_pow] using ht

/-- Dilation inserts zeros at Fourier indices not divisible by p. -/
theorem hasSum_dilation {d : ℕ} (f : Forms d) (p : ℕ) (hp : 0 < p) (z : ℍ) :
    HasSum (fun n => (if p ∣ n then coefficients f (n/p) else 0) * q z ^ n)
      (f (dilate p hp z)) := by
  have hs := hasSum_coefficients f (dilate p hp z)
  rw [q_dilate] at hs
  have hz : ∀ n ∉ Set.range (fun m : ℕ => p*m),
      (if p ∣ n then coefficients f (n/p) else 0) * q z ^ n = 0 := by
    intro n hn
    have hnd : ¬p ∣ n := by
      rintro ⟨m, rfl⟩
      exact hn ⟨m, rfl⟩
    simp [hnd]
  apply ((mul_index_injective p hp).hasSum_iff hz).mp
  simpa only [Function.comp_def, dvd_mul_right, ite_true, Nat.mul_div_cancel_left _ hp,
    pow_mul] using hs

/-- Exact Fourier coefficients of the standard prime Hecke expression. -/
def transformedCoefficients {d : ℕ} (f : Forms d) (p n : ℕ) : ℂ :=
  coefficients f (p*n) + (p : ℂ) ^ (d+1) *
    (if p ∣ n then coefficients f (n/p) else 0)

/-- The standard pointwise Hecke expression has the claimed convergent Fourier expansion. -/
theorem hasSum_primeOperator {d : ℕ} (f : Forms d) (p : ℕ) (hp : 0 < p) (z : ℍ) :
    HasSum (fun n => transformedCoefficients f p n * q z ^ n) (primeOperator p hp f z) := by
  have hs := ((hasSum_dilation f p hp z).mul_left ((p : ℂ) ^ (d+1))).add
    (hasSum_average f p hp z)
  apply hs.congr_fun
  intro n
  dsimp only [transformedCoefficients]
  ring

end TernaryPoly.BinaryCuspHecke
