module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Bad.LineCosets
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.HeckeH1
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.BinaryCentralCoefficient

@[expose] public section


/-!
# The Levi blocks of the bad-line cosets and the level-three Hecke operator

`B_j = p α_j⁻¹` for the level-three Hecke matrices `α_j` (`LevelThreeCosets.heckeRep`), so on the
trivial-twist representation `Sym^{n+1}`, `ρ(α_j)⁻¹ = p^{n+1} ρ(B_j)` (`rho_heckeRep_inv`). Hence the
cocycle `(T e)(A) = ∑_j ρ(α_j)⁻¹ e(δ_j(A))` of `LevelThreeHeckeH1` is `p^{n+1} ∑_j ρ(B_j) e(δ_j(A))`
(`levelHeckeCocycle_apply`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThree.BadLineLevel

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral
open IdentityPlaneCosets LevelOneCosets LevelThreeCosets BadLineCosets LevelThreeHeckeH1
open ParabolicBounds

variable (p : Nat.Primes)

theorem BQ_mul_rep (j : Option (Fin p.val)) :
    BQ p j * heckeRep p j =
      GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (p.val : ℚ) (p_ne_zero p)) := by
  apply Units.ext
  rw [Units.val_mul, BQ_val, heckeRep_val, ← Matrix.map_mul, Bl_mul_N]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [GeneralLinearGroup.scalar, Matrix.natCast_apply]

/-- `ρ(α_j)⁻¹ = p^{n+1} ρ(B_j)` on `Sym^{n+1}` with twist `0`. -/
theorem rho_heckeRep_inv (n : ℕ) (j : Option (Fin p.val)) (v : Binary.HomogeneousPoly (n + 1)) :
    rationalRho (n + 1) 0 (heckeRep p j)⁻¹ v =
      ((p.val : ℂ) ^ (n + 1)) • rationalRho (n + 1) 0 (BQ p j) v := by
  set u : ℚˣ := Units.mk0 (p.val : ℚ) (p_ne_zero p) with hu
  have hBQ := BQ_mul_rep p j
  have hinv : (heckeRep p j)⁻¹ = GeneralLinearGroup.scalar (Fin 2) u⁻¹ * BQ p j := by
    rw [map_inv, ← hBQ]
    group
  rw [hinv, map_mul, Module.End.mul_apply]
  change Binary.homogeneousAction (n + 1) 0
    (GeneralLinearGroup.map (algebraMap ℚ ℂ) (GeneralLinearGroup.scalar (Fin 2) u⁻¹))
      (rationalRho (n + 1) 0 (BQ p j) v) = _
  rw [GeneralLinearGroup.map_scalar]
  refine (EisensteinGraph.StandardConstruction.BinaryCentralCoefficient.homogeneousAction_scalar
    (n + 1) 0 _ _).trans ?_
  congr 1
  simp [u]

/-- The Hecke cocycle of `Γ₁'(3)` on `Sym^{n+1}`, in terms of the Levi blocks. -/
theorem levelHeckeCocycle_apply (n : ℕ) (hp3 : p.val ≠ 3)
    (e : crossedCocycles (binaryArithmeticRepresentation n)) (A : binaryArithmeticLevel) :
    (crossedHeckeCocycles (levelCosets p hp3) (rationalRho (n + 1) 0) (levelRep (n + 1) 0)
        (level_compat (n + 1) 0) levelEmbed_injective e).val A =
      ((p.val : ℂ) ^ (n + 1)) • ∑ j : Option (Fin p.val),
        rationalRho (n + 1) 0 (BQ p j) (e.val (levelDelta p hp3 A j)) := by
  have h0 : ((crossedHeckeCocycles (levelCosets p hp3) (rationalRho (n + 1) 0) (levelRep (n + 1) 0)
        (level_compat (n + 1) 0) levelEmbed_injective e).val A) =
      ∑ j : Option (Fin p.val),
        rationalRho (n + 1) 0 (heckeRep p j)⁻¹ (e.val (levelDelta p hp3 A j)) := rfl
  rw [h0, Finset.smul_sum]
  exact Finset.sum_congr rfl (fun j _ =>
    rho_heckeRep_inv p n j (e.val (levelDelta p hp3 A j)))

end TernaryPeriodPolynomials.LevelThree.BadLineLevel
