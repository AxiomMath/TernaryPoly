module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.ShearExponential

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

attribute [local instance] complexEndRationalAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Homogenize an infinitesimal affine action by adjoining one scalar coordinate. -/
def affineInfinitesimal (operator : Module.End ℂ V) (translation : V) :
    Module.End ℂ (V × ℂ) where
  toFun vector := (operator vector.1 + vector.2 • translation, 0)
  map_add' first second := by simp [map_add, add_smul]; abel
  map_smul' scalar vector := by simp [map_smul, smul_add, mul_smul]

theorem affineInfinitesimal_apply (operator : Module.End ℂ V) (translation : V)
    (vector : V × ℂ) :
    affineInfinitesimal operator translation vector =
      (operator vector.1 + vector.2 • translation, 0) := rfl

theorem affineInfinitesimal_add (first second : Module.End ℂ V) (alpha beta : V) :
    affineInfinitesimal (first + second) (alpha + beta) =
      affineInfinitesimal first alpha + affineInfinitesimal second beta := by
  apply LinearMap.ext
  intro vector
  simp only [affineInfinitesimal_apply, LinearMap.add_apply, smul_add, Prod.mk_add_mk, add_zero]
  congr 1
  abel

theorem affineInfinitesimal_smul (operator : Module.End ℂ V) (translation : V) (scalar : ℂ) :
    affineInfinitesimal (scalar • operator) (scalar • translation) =
      scalar • affineInfinitesimal operator translation := by
  apply LinearMap.ext
  intro vector
  simp [affineInfinitesimal_apply, smul_add, smul_comm scalar vector.2]

theorem affineInfinitesimal_commute (first second : Module.End ℂ V) (alpha beta : V)
    (commute : Commute first second) (closed : first beta = second alpha) :
    Commute (affineInfinitesimal first alpha) (affineInfinitesimal second beta) := by
  apply LinearMap.ext
  intro vector
  have actions := congrArg (fun operator : Module.End ℂ V => operator vector.1) commute.eq
  change first (second vector.1) = second (first vector.1) at actions
  simp only [Module.End.mul_apply, affineInfinitesimal_apply, map_add, map_smul,
    zero_smul, add_zero, actions, closed]

theorem affineInfinitesimal_power_succ (operator : Module.End ℂ V) (translation : V)
    (power : ℕ) (vector : V × ℂ) :
    (affineInfinitesimal operator translation ^ (power + 1)) vector =
      ((operator ^ (power + 1)) vector.1 + vector.2 • (operator ^ power) translation, 0) := by
  induction power with
  | zero => simp [affineInfinitesimal_apply]
  | succ power equality =>
    rw [pow_succ', Module.End.mul_apply, equality, affineInfinitesimal_apply]
    simp only [map_add, map_smul, zero_smul, add_zero]
    rw [pow_succ' operator (power + 1), pow_succ' operator power]
    rfl

theorem affineInfinitesimal_power_zero (operator : Module.End ℂ V) (translation : V)
    (cutoff : ℕ) (nilpotent : operator ^ cutoff = 0) :
    affineInfinitesimal operator translation ^ (cutoff + 1) = 0 := by
  apply LinearMap.ext
  intro vector
  rw [affineInfinitesimal_power_succ, pow_succ, nilpotent, zero_mul]
  simp

theorem affineInfinitesimal_nilpotent (operator : Module.End ℂ V) (translation : V)
    (nilpotent : IsNilpotent operator) : IsNilpotent (affineInfinitesimal operator translation) := by
  obtain ⟨cutoff, equality⟩ := nilpotent
  exact ⟨cutoff + 1, affineInfinitesimal_power_zero operator translation cutoff equality⟩

/-- The translation part of an affine exponential is the finite exponential average. -/
theorem affineInfinitesimal_exp_apply (operator : Module.End ℂ V) (translation : V)
    (cutoff : ℕ) (nilpotent : operator ^ (cutoff + 1) = 0) (vector : V × ℂ) :
    IsNilpotent.exp (affineInfinitesimal operator translation) vector =
      (IsNilpotent.exp operator vector.1 +
        vector.2 • nilpotentExponentialAverage operator (cutoff + 1) translation, vector.2) := by
  have expanded := affineInfinitesimal_power_zero operator translation (cutoff + 1) nilpotent
  have next : operator ^ (cutoff + 1 + 1) = 0 := by rw [pow_succ, nilpotent, zero_mul]
  have exp_formula : IsNilpotent.exp operator =
      (∑ index ∈ Finset.range (cutoff + 1),
        ((index + 1).factorial : ℚ)⁻¹ • operator ^ (index + 1)) + 1 := by
    rw [IsNilpotent.exp_eq_sum next, Finset.sum_range_succ']
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
  rw [IsNilpotent.exp_eq_sum expanded, Finset.sum_range_succ', exp_formula]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
    LinearMap.add_apply, Module.End.one_apply, LinearMap.sum_apply, rationalEnd_smul_apply,
    affineInfinitesimal_power_succ]
  apply Prod.ext
  · simp only [Prod.fst_add, Prod.fst_sum, Prod.smul_mk, nilpotentExponentialAverage,
      LinearMap.sum_apply, rationalEnd_smul_apply, smul_add, Finset.sum_add_distrib,
      Finset.smul_sum]
    have scalars : ∀ index : ℕ,
        (↑((↑(index + 1).factorial : ℚ)⁻¹) : ℂ) • (vector.2 • (operator ^ index) translation) =
          vector.2 • ((↑((↑(index + 1).factorial : ℚ)⁻¹) : ℂ) • (operator ^ index) translation) :=
      fun _ => smul_comm _ _ _
    simp only [scalars]
    abel
  · simp [Prod.snd_sum, Prod.smul_mk]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
