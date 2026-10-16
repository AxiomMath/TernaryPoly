module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Parabolic

@[expose] public section


/-!
# Evaluation at `(z, 1)` and the cusp `0`

* `eval_equivariant`: for `M ∈ SL₂(ℝ)` and `v ∈ Sym^m ⊗ det^e`,
  `v^M(M z, 1) = j(M, z)^{-m} v(z, 1)` where `v^M` is the transform of `v` by `M`
  (this makes `z ↦ Q(z)(z, 1)` of weight `-m` for a `Γ`-equivariant `Q`);
* `coreL_smul_sG_smul`: `L · S · (ζ + 3) = S · ζ` (so `S T³ = L⁻¹ S`);
* `sC_conj`: `S⁻¹ L⁻¹ S = T³` as complex matrices;
* `eval_upperC`: `(T^c v)(s, 1) = v(s - c, 1)`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein Matrix MvPolynomial UpperHalfPlane
open scoped Manifold ModularForm MatrixGroups
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators
open TernaryPeriodPolynomials.LevelThree.GammaOneThree
open TernaryPeriodPolynomials.LevelThree.SymFixed
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodPrimitive
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParabolic
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers

namespace TernaryPeriodPolynomials.LevelThree.LevelThreePeriodEval

theorem inv_val_of_det_one (g : GL (Fin 2) ℂ) (h : g.val.det = 1) :
    ((g⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![g.val 1 1, -g.val 0 1; -g.val 1 0, g.val 0 0] := by
  rw [Matrix.coe_units_inv, Matrix.inv_def, h, Ring.inverse_one, one_smul,
    Matrix.adjugate_fin_two]

variable (m : ℕ) (e : ℤ)

/-- `(T^c v)(s, 1) = v(s - c, 1)`. -/
theorem eval_upperC (c s : ℂ) (v : V m) :
    eval ![s, 1] (Binary.homogeneousAction m e (upperC c) v).val = eval ![s - c, 1] v.val := by
  rw [Binary.homogeneousAction_coe, eval_upper]
  simp

/-- **Weight `-m` of the evaluation at `(z, 1)`.** -/
theorem eval_equivariant (M : GL (Fin 2) ℝ) (hdet : M.val.det = 1) (z : ℍ) (v : V m) :
    eval ![((M • z : ℍ) : ℂ), 1] (Binary.homogeneousAction m e (complexify M) v).val =
      (denom M z)⁻¹ ^ m * eval ![(z : ℂ), 1] v.val := by
  have hdetC : (GeneralLinearGroup.det (complexify M) : ℂ) = 1 := by
    rw [GeneralLinearGroup.val_det_apply, det_complexify, hdet, Complex.ofReal_one]
  have hdetC' : (complexify M).val.det = 1 := by
    rw [det_complexify, hdet, Complex.ofReal_one]
  have hpos : 0 < ((GeneralLinearGroup.det M : ℝˣ) : ℝ) := by
    rw [GeneralLinearGroup.val_det_apply, hdet]
    exact one_pos
  have hden : denom M z ≠ 0 := denom_ne_zero M z
  have hdet2 : (M.val 0 0 : ℂ) * (M.val 1 1 : ℂ) - (M.val 0 1 : ℂ) * (M.val 1 0 : ℂ) = 1 := by
    have h := hdet
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  have hw : ((M • z : ℍ) : ℂ) = ((M.val 0 0 : ℂ) * (z : ℂ) + (M.val 0 1 : ℂ)) /
      ((M.val 1 0 : ℂ) * (z : ℂ) + (M.val 1 1 : ℂ)) := by
    rw [coe_smul_of_det_pos hpos z, num_eq, denom_eq]
  have hden' : (M.val 1 0 : ℂ) * (z : ℂ) + (M.val 1 1 : ℂ) ≠ 0 := by
    rw [← denom_eq]; exact hden
  rw [Binary.homogeneousAction_coe, SymFixed.eval_action_of_det e _ hdetC]
  have hinv := inv_val_of_det_one (complexify M) hdetC'
  have hinv' : (((complexify M)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(M.val 1 1 : ℂ), -(M.val 0 1 : ℂ); -(M.val 1 0 : ℂ), (M.val 0 0 : ℂ)] := hinv
  have hwd : ((M • z : ℍ) : ℂ) * ((M.val 1 0 : ℂ) * (z : ℂ) + (M.val 1 1 : ℂ)) =
      (M.val 0 0 : ℂ) * (z : ℂ) + (M.val 0 1 : ℂ) := by
    rw [hw]
    exact div_mul_cancel₀ _ hden'
  have hvec : (fun i : Fin 2 => ∑ j : Fin 2,
      (((complexify M)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j *
        ![((M • z : ℍ) : ℂ), 1] j) = (denom M z)⁻¹ • ![(z : ℂ), 1] := by
    funext i
    rw [hinv', Fin.sum_univ_two]
    fin_cases i
    · show (M.val 1 1 : ℂ) * ((M • z : ℍ) : ℂ) + (-(M.val 0 1 : ℂ)) * 1 =
        (denom M z)⁻¹ * (z : ℂ)
      rw [inv_mul_eq_div, eq_div_iff hden, denom_eq]
      linear_combination (M.val 1 1 : ℂ) * hwd + (z : ℂ) * hdet2
    · show (-(M.val 1 0 : ℂ)) * ((M • z : ℍ) : ℂ) + (M.val 0 0 : ℂ) * 1 =
        (denom M z)⁻¹ * 1
      rw [inv_mul_eq_div, eq_div_iff hden, denom_eq]
      linear_combination (-(M.val 1 0 : ℂ)) * hwd + hdet2
  exact (congrArg (fun x => eval x v.val) hvec).trans
    (SymFixed.eval_smul_of_homogeneous (SymFixed.isHomogeneous v) _ _)

theorem sG_denom (z : ℍ) : denom sG z = (z : ℂ) := by
  rw [denom_eq]
  simp [binaryIntegral_mapGL_entry, ModularGroup.coe_S]

theorem sC_conj : sC⁻¹ * (lowerC 3)⁻¹ * sC = upperC 3 := by
  apply Units.ext
  change !![(0 : ℂ), 1; -1, 0] * !![1, 0; -3, 1] * !![0, -1; 1, 0] = !![1, 3; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- `L · S · (ζ + 3) = S · ζ`. -/
theorem coreL_smul_sG_smul (ζ : ℍ) :
    coreReal coreL • (sG • ((3 : ℝ) +ᵥ ζ : ℍ)) = sG • ζ := by
  apply UpperHalfPlane.ext
  have hζ : (ζ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero ζ
  have h3 : (3 : ℂ) + (ζ : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact absurd this ζ.im_pos.ne'
  have hv : (((3 : ℝ) +ᵥ ζ : ℍ) : ℂ) = 3 + (ζ : ℂ) := by
    rw [UpperHalfPlane.coe_vadd]
    simp
  rw [coreL_coe, sG_coe, sG_coe, hv]
  have hy : (3 : ℂ) * (-1 / (3 + (ζ : ℂ))) + 1 = (ζ : ℂ) / (3 + (ζ : ℂ)) := by
    first | (field_simp; done) | (field_simp; ring)
  rw [hy]
  field_simp

end TernaryPeriodPolynomials.LevelThree.LevelThreePeriodEval
