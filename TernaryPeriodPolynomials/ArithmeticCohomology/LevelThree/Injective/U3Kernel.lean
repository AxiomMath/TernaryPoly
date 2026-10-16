module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Injective.U3Cosets

@[expose] public section


/-!
# The kernel of the parity-projected period map is stable under `U_3`

The operator `U_3 f = ∑_{j<3} f ∣ [[1,j],[0,3]]` on `S_{m+2}(Γ₁(3))` is the coset sum of the
symmetric right cosets `u3Sym` (the representative `[[1,2],[0,3]]` is replaced by
`[[1,-1],[0,3]]`, which gives the same slash operator because `f` is `1`-periodic). The
corresponding Hecke operator `u3Hecke` on `H¹(Γ₁(3), Sym^m ⊗ det^e)` satisfies
`u3Hecke ∘ levelThreePeriodMap = levelThreePeriodMap ∘ (3^{-e} U_3)` (`periodMap_u3`) and commutes
with the projection `π₊` (`PlusHecke.crossedHecke_plusMap`), because conjugation by
`ε = diag(-1,1)` permutes the symmetric representatives. Since
`restriction ∘ levelPeriodMap = π₊ ∘ levelThreePeriodMap` and `restriction` is injective for
`m > 0`:

**`levelPeriodMap_U3_eq_zero`**: if `levelPeriodMap m e f = 0` then
`levelPeriodMap m e (U_3 f) = 0`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein Matrix UpperHalfPlane
open scoped Manifold ModularForm MatrixGroups
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators
open TernaryPeriodPolynomials.LevelThree
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeCosets
open TernaryPeriodPolynomials.LevelThree.GammaOneThree
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodHecke
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodHeckeFamily
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodHeckeTp
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParityHecke
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeH1
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeSum
open TernaryPeriodPolynomials.LevelThree.LevelThreeHecke
open TernaryPeriodPolynomials.LevelThree.LevelThreeCosets
open TernaryPeriodPolynomials.LevelThreeInjective.PlusHecke
open TernaryPeriodPolynomials.LevelThreeInjective.U3Cosets

namespace TernaryPeriodPolynomials.LevelThreeInjective.U3Kernel

/-- The real points of the symmetric representatives have determinant `3`. -/
theorem u3Sym_toReal_det (j : Fin 3) : (toReal (u3Sym.rep j)).val.det = (3 : ℝ) := by
  rw [toReal_det, u3Sym_det]
  norm_num

theorem real_mul' (a b : GL (Fin 2) ℚ) : real (a * b) = real a * real b :=
  map_mul (GeneralLinearGroup.map (Rat.castHom ℝ)) a b

/-- The coset-sum operator of the symmetric cosets is `U_3`. -/
theorem sumOp_eq_levelThreeU3 {m : ℕ} (f : S m) :
    ((toCosetFamily u3Sym coreEmbed_real u3Sym_det_pos).sumOp ((m : ℤ) + 2)) f =
      levelThreeU3 ((m : ℤ) + 2) f := by
  apply CuspForm.ext
  intro τ
  change CosetFamily.sumFun (toCosetFamily u3Sym coreEmbed_real u3Sym_det_pos) ((m : ℤ) + 2) f τ =
    CosetFamily.sumFun u3Family ((m : ℤ) + 2) f τ
  unfold CosetFamily.sumFun
  rw [Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  change (⇑f ∣[(m : ℤ) + 2] real (coreEmbed (symTau j) * u3Rep j)) τ =
    (⇑f ∣[(m : ℤ) + 2] real (u3Rep j)) τ
  have hreal : real (coreEmbed (symTau j)) = coreReal (symTau j) := coreEmbed_real (symTau j)
  have hinv : (⇑f) ∣[(m : ℤ) + 2] coreReal (symTau j) = ⇑f := form_invariant f (symTau j)
  rw [real_mul', hreal, SlashAction.slash_mul, hinv]

/-- **The Hecke operator `U_3` on `H¹(Γ₁(3), Sym^m ⊗ det^e)`**, from the symmetric cosets. -/
def u3Hecke (m : ℕ) (e : ℤ) : Module.End ℂ (CrossedH1 (coreRep m e)) :=
  crossedHecke u3Sym (rationalRho m e) (coreRep m e) (compat_of m e coreEmbed_real)
    coreEmbed_injective

/-- **Period equivariance for `U_3`.** -/
theorem periodMap_u3 {m : ℕ} (e : ℤ) (f : S m) :
    u3Hecke m e (levelThreePeriodMap m e f) =
      levelThreePeriodMap m e
        ((((3 : ℝ) : ℂ) ^ (-e)) • levelThreeU3 ((m : ℤ) + 2) f) := by
  have h := periodMap_hecke_sumOp (embed := coreEmbed) u3Sym coreEmbed_real u3Sym_det_pos m e
    (D := (3 : ℝ)) u3Sym_toReal_det coreEmbed_injective f
  rw [sumOp_eq_levelThreeU3 f] at h
  exact h

/-- **`U_3` commutes with `π₊`.** -/
theorem u3Hecke_plusH1 (m : ℕ) (e : ℤ) (x : CrossedH1 (coreRep m e)) :
    u3Hecke m e (plusH1 m e x) = plusH1 m e (u3Hecke m e x) :=
  crossedHecke_plusMap u3Sym (rationalRho m e) (levelRep m e) (compat_of m e coreEmbed_real)
    coreEmbed_injective reflection_mul_self normalCore u3Symmetry
    (level_compat m e reflection).symm x

/-- **The kernel of the parity-projected period map is stable under `U_3`.** -/
theorem levelPeriodMap_U3_eq_zero (m : ℕ) (e : ℤ) (hm : 0 < m) (f : LevelThreePeriodCocycle.S m)
    (h : LevelThreePeriodParity.levelPeriodMap m e f = 0) :
    LevelThreePeriodParity.levelPeriodMap m e
      (LevelThreeHecke.levelThreeU3 ((m : ℤ) + 2) f) = 0 := by
  have h1 : plusH1 m e (levelThreePeriodMap m e f) = 0 := by
    rw [← res_levelPeriodMap e f, h, map_zero]
  have h2 : plusH1 m e (u3Hecke m e (levelThreePeriodMap m e f)) = 0 := by
    rw [← u3Hecke_plusH1, h1, map_zero]
  rw [periodMap_u3 e f, map_smul, map_smul] at h2
  have hc : (((3 : ℝ) : ℂ) ^ (-e)) ≠ 0 := zpow_ne_zero _ (by norm_num)
  have h3 : plusH1 m e (levelThreePeriodMap m e (levelThreeU3 ((m : ℤ) + 2) f)) = 0 :=
    (smul_eq_zero.mp h2).resolve_left hc
  apply restriction_injective e hm
  rw [res_levelPeriodMap e (levelThreeU3 ((m : ℤ) + 2) f), map_zero]
  exact h3

end TernaryPeriodPolynomials.LevelThreeInjective.U3Kernel
