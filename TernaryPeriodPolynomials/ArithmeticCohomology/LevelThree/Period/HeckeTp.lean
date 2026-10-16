module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.HeckeFamily
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Hecke

@[expose] public section


/-!
# Hecke equivariance of the level-three period map for `T_p` (`p ≠ 3`)

For a prime `p ≠ 3`, the right cosets `coreCosets p` of `Γ₁(3) diag(1, p) Γ₁(3)` used for the
Hecke operator `coreHecke m e p` on `H¹(Γ₁(3), Sym^m ⊗ det^e)` have the same representatives as the
coset family `tpFamily` of the classical operator `T_p = levelThreeHecke` on `S_{m+2}(Γ₁(3))`
(`heckeRep_eq_tpRep`), and all have determinant `p`. Hence

**`periodMap_hecke_tp`**: `coreHecke m e p [c_f] = [c_{p^{-e} T_p f}]`, i.e.
`coreHecke ∘ levelThreePeriodMap = levelThreePeriodMap ∘ (p^{-e} T_p)`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein Matrix UpperHalfPlane
open scoped Manifold ModularForm MatrixGroups
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers
open TernaryPeriodPolynomials.LevelThree.GammaOneThree
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodHecke
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodHeckeFamily
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeH1
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeSum
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeCosets
open TernaryPeriodPolynomials.LevelThree.LevelThreeHecke
open TernaryPeriodPolynomials.LevelThree.LevelThreeCosets
open TernaryPeriodPolynomials.Spectral.LevelOneCosets

namespace TernaryPeriodPolynomials.LevelThree.LevelThreePeriodHeckeTp

variable (p : Nat.Primes) (hp3 : p.val ≠ 3)

theorem coreEmbed_real (k : core) : toReal (coreEmbed k) = coreReal k := by
  apply Units.ext
  ext i j
  simp [coreEmbed, levelEmbed, integralEmbed, toReal, coreReal, GeneralLinearGroup.map_apply]

theorem signMatrix_eq (h : p.val % 3 = 1 ∨ p.val % 3 = 2) :
    integralEmbed (signMatrix p) = toGLQ (heckeSign p none) := by
  rcases h with h | h
  · have hcast : (p.val : ZMod 3) = 1 := by
      rw [← ZMod.natCast_mod, h]
      simp
    have hsign : signP p = 1 := by
      unfold signP
      rw [ite_eq_left hcast]
    have hhs : heckeSign p none = 1 := by simp [heckeSign, h]
    rw [hhs, map_one]
    apply Units.ext
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [signMatrix, integralEmbed, hsign]
  · have hcast : (p.val : ZMod 3) ≠ 1 := by
      rw [← ZMod.natCast_mod, h]
      decide
    have hsign : signP p = -1 := by
      unfold signP
      rw [ite_eq_right hcast]
    have hhs : heckeSign p none = -1 := by simp [heckeSign, h]
    rw [hhs]
    apply Units.ext
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [signMatrix, integralEmbed, toGLQ, hsign]

include hp3 in
/-- The representatives `heckeRep` of `LevelThreeCosets` are those of `tpFamily`. -/
theorem heckeRep_eq_tpRep (j : Option (Fin p.val)) : heckeRep p j = tpRep p j := by
  unfold heckeRep tpRep
  congr 1
  cases j with
  | some i => simp [twist, heckeSign]
  | none => exact signMatrix_eq p (mod_three_cases hp3)

theorem heckeRep_det (j : Option (Fin p.val)) :
    (heckeRep p j).val.det = (p.val : ℚ) := by
  rw [heckeRep_val]
  have h := RingHom.map_det (Int.castRingHom ℚ) (N p j)
  rw [RingHom.mapMatrix_apply] at h
  rw [← h, N_det]
  simp

theorem heckeRep_det_pos (j : Option (Fin p.val)) :
    0 < (((heckeRep p j).det : ℚˣ) : ℚ) := by
  rw [GeneralLinearGroup.val_det_apply, heckeRep_det]
  exact_mod_cast p.property.pos

theorem toReal_heckeRep_det (j : Option (Fin p.val)) :
    (toReal (heckeRep p j)).val.det = (p.val : ℝ) := by
  rw [toReal_det, heckeRep_det]
  simp

variable {m : ℕ} (e : ℤ)

/-- The classical operator is the coset sum over `coreCosets`. -/
theorem sumOp_eq_levelThreeHecke (f : S m) :
    ((toCosetFamily (coreCosets p hp3) coreEmbed_real (heckeRep_det_pos p)).sumOp
        ((m : ℤ) + 2)) f = levelThreeHecke ((m : ℤ) + 2) p hp3 f := by
  apply CuspForm.ext
  intro τ
  change CosetFamily.sumFun
      (toCosetFamily (coreCosets p hp3) coreEmbed_real (heckeRep_det_pos p)) ((m : ℤ) + 2) f τ =
    CosetFamily.sumFun (tpFamily hp3) ((m : ℤ) + 2) f τ
  unfold CosetFamily.sumFun
  rw [Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  change (⇑f ∣[(m : ℤ) + 2] real (heckeRep p j)) τ = (⇑f ∣[(m : ℤ) + 2] real (tpRep p j)) τ
  rw [heckeRep_eq_tpRep p hp3 j]

/-- **Hecke equivariance of the period map for `T_p`.** -/
theorem periodMap_hecke_tp (f : S m) :
    coreHecke m e p hp3 (levelThreePeriodMap m e f) =
      levelThreePeriodMap m e (((p.val : ℂ) ^ (-e)) • levelThreeHecke ((m : ℤ) + 2) p hp3 f) := by
  have h := periodMap_hecke_sumOp (embed := coreEmbed) (coreCosets p hp3)
    coreEmbed_real (heckeRep_det_pos p) m e (D := (p.val : ℝ)) (toReal_heckeRep_det p)
    coreEmbed_injective f
  rw [sumOp_eq_levelThreeHecke p hp3 f] at h
  have hc : ((p.val : ℝ) : ℂ) = (p.val : ℂ) := by simp
  rw [hc] at h
  exact h

/-- **Eigenforms give Hecke eigenclasses.** If `T_p f = c f`, the period class of `f` is an
eigenvector of `coreHecke m e p` with eigenvalue `p^{-e} c`. -/
theorem coreHecke_period_of_eigen (f : S m) (c : ℂ)
    (h : levelThreeHecke ((m : ℤ) + 2) p hp3 f = c • f) :
    coreHecke m e p hp3 (levelThreePeriodMap m e f) =
      (((p.val : ℂ) ^ (-e)) * c) • levelThreePeriodMap m e f := by
  rw [periodMap_hecke_tp p hp3 e f, h, map_smul, map_smul, smul_smul]

end TernaryPeriodPolynomials.LevelThree.LevelThreePeriodHeckeTp
