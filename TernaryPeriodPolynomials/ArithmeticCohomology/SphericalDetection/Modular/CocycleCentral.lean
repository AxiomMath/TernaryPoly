module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Modular.CocycleReflection

@[expose] public section


open GeneralEisenstein Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem modularBinaryRep_neg_one (degree : ℕ) (twist : ℤ) (even : Even degree)
    (polynomial : Binary.HomogeneousPoly degree) :
    (modularBinaryRep degree twist).ρ (-1) polynomial = polynomial := by
  apply Subtype.ext
  change ((arithmeticBinaryRep degree twist).ρ (SpecialLinearGroup.toGL (-1)) polynomial).val = _
  rw [arithmeticBinaryRep_specialLinear_coe]
  have matrix_eq : (((-1 : SpecialLinearGroup (Fin 2) ℤ)⁻¹).val.map (Int.castRingHom ℂ)) =
      Matrix.scalar (Fin 2) (-1 : ℂ) := by
    rw [SpecialLinearGroup.SL2_inv_expl]
    ext row column
    fin_cases row <;> fin_cases column <;> norm_num [Matrix.map]
  rw [matrix_eq, binary_substitute_scalar, even.neg_one_pow, one_smul]

theorem modularCocycle_neg_one (degree : ℕ) (twist : ℤ) (even : Even degree)
    (cycle : groupCohomology.cocycles₁ (modularBinaryRep degree twist)) :
    cycle (-1) = 0 := by
  let value : Binary.HomogeneousPoly degree := cycle (-1)
  let action : Module.End ℂ (Binary.HomogeneousPoly degree) :=
    (modularBinaryRep degree twist).ρ (-1)
  have fixed : action value = value := modularBinaryRep_neg_one degree twist even value
  have relation := (groupCohomology.mem_cocycles₁_iff _).mp cycle.property (-1) (-1)
  rw [neg_mul_neg, one_mul] at relation
  change cycle 1 = action value + value at relation
  rw [groupCohomology.cocycles₁_map_one] at relation
  change (0 : Binary.HomogeneousPoly degree) = action value + value at relation
  rw [fixed] at relation
  have scaled : (2 : ℂ) • value = 0 := by simpa only [two_smul] using relation.symm
  exact (smul_eq_zero.mp scaled).resolve_left (by norm_num)

theorem modularCocycle_S_inverse (degree : ℕ) (twist : ℤ) (even : Even degree)
    (cycle : groupCohomology.cocycles₁ (modularBinaryRep degree twist)) :
    cycle ModularGroup.S⁻¹ = cycle ModularGroup.S := by
  have relation := (groupCohomology.mem_cocycles₁_iff _).mp cycle.property (-1) ModularGroup.S
  rw [neg_one_mul, ← ModularGroup.S_inv] at relation
  change cycle ModularGroup.S⁻¹ = (modularBinaryRep degree twist).ρ (-1)
    (cycle ModularGroup.S) + cycle (-1) at relation
  rw [modularCocycle_neg_one degree twist even cycle, add_zero] at relation
  exact relation.trans (modularBinaryRep_neg_one degree twist even (cycle ModularGroup.S))

end TernaryPeriodPolynomials.SphericalDetection.Helpers
