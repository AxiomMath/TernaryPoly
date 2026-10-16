module

public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.LevelOneEigenPair
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.DictionaryHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.PeterssonSemisimple

@[expose] public section


/-!
# Matching the level-one and level-three eigenvalues

A level-one Hecke eigenvalue is real (`T_p` is self-adjoint for the Petersson product). Hence if
`levelOneEigenvalue n σ p = (p + 1) p^{(n+1)/2} ω(diag(p,1))` is a level-one eigenvalue, then
`ω(diag(p,1))` is real, and given `ω(diag(p,1)⁻¹) = conj ω(diag(p,1))` (unitarity) the level-three
eigenvalue `levelThreeEigenvalue σ halfWeight p = p^{-halfWeight-1} (p + 1) ω(diag(p,1)⁻¹)` agrees
with it when `2 * halfWeight = -(n + 3)`.
-/

noncomputable section

open ComplexConjugate
open GeneralEisenstein
open TernaryPeriodPolynomials.HeckeEigen.Satake
open TernaryPeriodPolynomials.Spectral

namespace TernaryPeriodPolynomials.MultiplicityOne

/-- **Level-one Hecke eigenvalues are real.** -/
theorem levelOneHecke_eigenvalue_conj {k : ℤ} (p : Nat.Primes)
    {f : CuspForm LevelOneHecke.levelOne k} (hf0 : f ≠ 0) {μ : ℂ}
    (h : LevelOneHecke.levelOneHecke k p f = μ • f) : conj μ = μ := by
  have hpet := PeterssonHecke.pet_hecke k p f f
  rw [h, PeterssonSemisimple.pet_smul_left, PeterssonSemisimple.pet_smul_right] at hpet
  have hne : PeterssonHecke.pet k f f ≠ 0 :=
    fun h0 => hf0 (PeterssonSemisimple.pet_self_eq_zero k f h0)
  exact mul_right_cancel₀ hne hpet

/-- **The two eigenvalue normalizations agree** on a real level-one eigenvalue. -/
theorem levelThreeEigenvalue_eq_levelOneEigenvalue (σ : CuspidalRepresentation) {n : ℕ}
    (hodd : Odd n) {halfWeight : ℤ} (hw : 2 * halfWeight = -((n : ℤ) + 3)) (p : Nat.Primes)
    (hω : omega σ (Bo (dP p.property)⁻¹) = conj (omega σ (Bo (dP p.property))))
    (hreal : conj (levelOneEigenvalue n σ p) = levelOneEigenvalue n σ p) :
    levelThreeEigenvalue σ halfWeight p = levelOneEigenvalue n σ p := by
  obtain ⟨j, rfl⟩ := hodd
  have hdiv : (2 * j + 1 + 1) / 2 = j + 1 := by omega
  have hexp : -halfWeight - 1 = ((j + 1 : ℕ) : ℤ) := by push_cast; omega
  unfold levelOneEigenvalue at hreal ⊢
  unfold levelThreeEigenvalue levelThreeHeckeScalar
  rw [hdiv] at hreal ⊢
  rw [hexp, zpow_natCast, hω]
  set ω := omega σ (Bo (dP p.property))
  have hp0 : (p.val : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hA : ((p.val : ℂ) + 1) * (p.val : ℂ) ^ (j + 1) ≠ 0 :=
    mul_ne_zero (Nat.cast_add_one_ne_zero p.val) (pow_ne_zero _ hp0)
  have hconj : conj (((p.val : ℂ) + 1) * (p.val : ℂ) ^ (j + 1)) =
      ((p.val : ℂ) + 1) * (p.val : ℂ) ^ (j + 1) := by
    simp
  rw [map_mul, hconj] at hreal
  have hωr : conj ω = ω := mul_left_cancel₀ hA hreal
  rw [hωr]
  ring

end TernaryPeriodPolynomials.MultiplicityOne
