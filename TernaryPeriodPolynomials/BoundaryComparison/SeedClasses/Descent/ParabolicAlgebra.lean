module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.ESSpan
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.SymFixed

@[expose] public section


/-!
# Coinvariants of a shear on `Sym^m` (algebraic input for the parabolic triviality of seeds)

For a nontrivial upper shear `T = [[1, c], [0, 1]]` the image of `T - 1` on `Sym^m ⊗ det^e` is the
hyperplane of forms vanishing at `(1, 0)` (`movedSpace_upper_eq`, from the library's
`finrank_fixed_upper`), and `T` has no eigenvalue `-1` (`eq_zero_of_upper_eigen_neg`).

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open GeneralEisenstein Matrix MvPolynomial Module

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

open TernaryPeriodPolynomials.LevelThree.SymFixed

section Moved

variable {m : ℕ} (e : ℤ)

theorem finrank_ker_evalAt_one_zero :
    finrank ℂ (LinearMap.ker (evalAt (m := m) ![1, 0])) = m := by
  have hsurj : LinearMap.range (evalAt (m := m) ![1, 0]) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    refine ⟨z • powerVector 0 m, ?_⟩
    change eval ![1, 0] (z • powerVector 0 m).val = z
    simp [powerVector]
  have h := LinearMap.finrank_range_add_finrank_ker (evalAt (m := m) ![1, 0])
  rw [hsurj, finrank_top, Module.finrank_self, finrank_sym] at h
  omega

/-- For a nontrivial upper shear, `(T - 1) V = {w : w(1, 0) = 0}`. -/
theorem movedSpace_upper_eq {c : ℂ} (hc : c ≠ 0) :
    movedSpace (m := m) e (upperC c) = LinearMap.ker (evalAt (m := m) ![1, 0]) := by
  have hle : movedSpace (m := m) e (upperC c) ≤ LinearMap.ker (evalAt (m := m) ![1, 0]) := by
    intro w hw
    exact eval_upper_moved e c w hw
  apply Submodule.eq_of_le_of_finrank_eq hle
  have rank_nullity := LinearMap.finrank_range_add_finrank_ker
    (Binary.homogeneousAction m e (upperC c) - 1)
  rw [finrank_sym] at rank_nullity
  have fixedT := finrank_fixed_upper (m := m) e hc
  change finrank ℂ (movedSpace e (upperC c)) + finrank ℂ (fixedSpace e (upperC c)) = _
    at rank_nullity
  rw [finrank_ker_evalAt_one_zero]
  omega

/-- A nontrivial upper shear has no eigenvalue `-1` on `Sym^m`. -/
theorem eq_zero_of_upper_eigen_neg {c : ℂ} (hc : c ≠ 0) (Q : Binary.HomogeneousPoly m)
    (h : Binary.homogeneousAction m e (upperC c) Q = -Q) : Q = 0 := by
  have hmul : upperC c * upperC c = upperC (2 * c) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> (simp [upperC, Matrix.mul_apply, Fin.sum_univ_two]; all_goals ring)
  have h2 : Binary.homogeneousAction m e (upperC (2 * c)) Q = Q := by
    rw [← hmul, map_mul, Module.End.mul_apply, h, map_neg, h, neg_neg]
  have hQ : Q ∈ fixedSpace e (upperC (2 * c)) := (mem_fixedSpace e).mpr h2
  have hc2 : (2 * c) ≠ 0 := mul_ne_zero two_ne_zero hc
  have hpv : powerVector 1 m ∈ fixedSpace e (upperC (2 * c)) := powerVector_one_mem_upper e (2 * c)
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero'
    (⟨powerVector 1 m, hpv⟩ : fixedSpace (m := m) e (upperC (2 * c)))
    (fun h0 => powerVector_ne_zero 1 m (congrArg Subtype.val h0))).mp
    (finrank_fixed_upper (m := m) e hc2) ⟨Q, hQ⟩
  have hQa : Q = a • powerVector 1 m := (congrArg Subtype.val ha).symm
  have hfix : Binary.homogeneousAction m e (upperC c) (powerVector 1 m) = powerVector 1 m :=
    (mem_fixedSpace e).mp (powerVector_one_mem_upper e c)
  have hAQ : Binary.homogeneousAction m e (upperC c) Q = Q := by
    rw [hQa, map_smul, hfix]
  rw [hAQ] at h
  have : (2 : ℂ) • Q = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    simp
  exact (smul_eq_zero.mp this).resolve_left two_ne_zero

end Moved

end TernaryPeriodPolynomials.Argument.SeedC3S4c
