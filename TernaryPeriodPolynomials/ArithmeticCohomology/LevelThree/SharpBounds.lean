module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.ParabolicBounds
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.ReflectionBound

@[expose] public section


/-!
# Sharp parabolic bound for the level-three Levi `Γ₁'(3)`

For `Sym^m(ℂ²) ⊗ det^e` (`m > 0`, any twist `e`) as a representation of
`Γ₁'(3) = binaryArithmeticLevel`:

* **`finrank_level_parabolicH1_le`**: `dim H¹_par(Γ₁'(3), Sym^m ⊗ det^e) + 1 ≤ ⌊(m + 2)/3⌋`,
  i.e. at most the Eichler–Shimura value `dim S_{m+2}(Γ₁(3)) = ⌊(m+2)/3⌋ - 1` (one eigenspace of the
  reflection `diag(-1, 1)`);
* **`finrank_binaryParabolicH1_le_sharp`**: `dim binaryParabolicH1 degree + 1 ≤ ⌊(degree + 3)/3⌋`;
* **`finrank_innerBadLineClasses_le_sharp`**: `dim innerBadLineClasses degree + 1 ≤ ⌊(degree + 3)/3⌋`
  (`0 < degree`); in particular the inner bad-line classes form a space of dimension `≤ 1` for
  `degree ∈ {3, 4, 5}` (`finrank_innerBadLineClasses_le_one`).

The proof is `ReflectionBound` with `T = [[1,1],[0,1]]`, `L = [[1,0],[3,1]]`, `ε = diag(-1,1)`:
for even `e` the coboundary of `X₁^m ∈ V^T ∩ V^ε` is subtracted, for odd `e` the hyperplane
`(L - 1)V ⊆ {p(0,1) = 0}` cuts `K⁻` (witness `(1 - σ)(E - 1)X₁^m`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThree.SharpBounds

open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators LowDegreeParabolic
open TwoGenerator GammaOneThree SymFixed ParabolicBounds ReflectionBound
open GeneralEisenstein Module Matrix MvPolynomial

section Matrices

/-- `diag(-1, 1)`. -/
def reflectionC : Binary.GL2 :=
  ⟨!![-1, 0; 0, 1], !![-1, 0; 0, 1], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem reflectionC_det : ((GeneralLinearGroup.det reflectionC : ℂˣ) : ℂ) = -1 := by
  rw [GeneralLinearGroup.val_det_apply]
  change Matrix.det !![(-1 : ℂ), 0; 0, 1] = -1
  simp [Matrix.det_fin_two_of]

/-- The action of an arbitrary matrix, evaluated. -/
theorem eval_action (e : ℤ) (g : Binary.GL2) (p : Binary.Poly) (x : Fin 2 → ℂ) :
    eval x (Binary.action e g p) = ((GeneralLinearGroup.det g : ℂˣ) : ℂ) ^ e *
      eval (fun i => ∑ j, ((g⁻¹ : Binary.GL2) : Matrix (Fin 2) (Fin 2) ℂ) i j * x j) p := by
  rw [Binary.action_apply, MvPolynomial.smul_eval, Spectral.ModularSymDimension.eval_substitute]
  rfl

theorem eval_reflection (e : ℤ) (p : Binary.Poly) (a b : ℂ) :
    eval ![a, b] (Binary.action e reflectionC p) = (-1 : ℂ) ^ e * eval ![-a, b] p := by
  rw [eval_action, reflectionC_det]
  congr 3
  funext i
  fin_cases i <;> simp [reflectionC, Fin.sum_univ_two]

theorem eval_elliptic (e : ℤ) (p : Binary.Poly) (a b : ℂ) :
    eval ![a, b] (Binary.action e ellipticC p) = eval ![a - b, 3 * a - 2 * b] p := by
  have hdet : (GeneralLinearGroup.det ellipticC : ℂ) = 1 := by
    rw [GeneralLinearGroup.val_det_apply]
    change Matrix.det !![(-2 : ℂ), 1; -3, 1] = 1
    rw [Matrix.det_fin_two_of]
    norm_num
  rw [eval_action_of_det e _ hdet]
  congr 2
  funext i
  fin_cases i <;> (simp [ellipticC, Fin.sum_univ_two]; ring)

theorem integral_reflection : binaryIntegralComplex reflection.val = reflectionC := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [binaryIntegralComplex, reflection, reflectionC]

end Matrices

section Relations

theorem upper_inv' : (upper 1)⁻¹ = upper (-1) := by
  rw [upper_zpow (-1), _root_.zpow_neg_one]

theorem hεT : reflection * upper 1 * reflection = (upper 1)⁻¹ := by
  rw [reflection_conj_upper, upper_inv']

theorem hεL : reflection * lower 1 * reflection = (lower 1)⁻¹ := by
  rw [reflection_conj_lower, lower_inv]

theorem level_cube : (upper 1 * (lower 1)⁻¹) ^ 3 = 1 := by
  rw [lower_inv]
  exact elliptic_cube

theorem level_closure : Subgroup.closure ({upper 1, lower 1, reflection} : Set binaryArithmeticLevel) = ⊤ :=
  generators_span

end Relations

section Representation

variable (m : ℕ) (e : ℤ)

theorem levelRep_T : levelRep m e (upper 1) = Binary.homogeneousAction m e (upperC 1) := by
  change Binary.homogeneousAction m e (binaryIntegralComplex (upper 1).val) = _
  rw [integral_upper]

theorem levelRep_L : levelRep m e (lower 1) = Binary.homogeneousAction m e (lowerC 3) := by
  change Binary.homogeneousAction m e (binaryIntegralComplex (lower 1).val) = _
  rw [integral_lower]

theorem levelRep_ε : levelRep m e reflection = Binary.homogeneousAction m e reflectionC := by
  change Binary.homogeneousAction m e (binaryIntegralComplex reflection.val) = _
  rw [integral_reflection]

theorem levelRep_E :
    levelRep m e (upper 1 * (lower 1)⁻¹) = Binary.homogeneousAction m e ellipticC := by
  change Binary.homogeneousAction m e
    (binaryIntegralComplex ((upper 1 * (lower 1)⁻¹ : binaryArithmeticLevel).val)) = _
  rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, integral_upper, integral_lower,
    upper_mul_lower_inv]

variable {m}

theorem level_invariants (positive : 0 < m) :
    fixed (levelRep m e) (upper 1) ⊓ fixed (levelRep m e) (lower 1) = ⊥ := by
  unfold fixed
  rw [levelRep_T, levelRep_L]
  exact fixed_upper_inf_fixed_lower e positive one_ne_zero three_ne_zero

theorem finrank_level_kernelE (m : ℕ) :
    finrank ℂ (kernelE (ρ := levelRep m e) (upper 1) (lower 1)) + ellipticCount m ≤ m + 1 := by
  have h := finrank_ker_norm3_add_le (ρ := levelRep m e) (upper 1 * (lower 1)⁻¹)
  have hE : finrank ℂ (fixed (levelRep m e) (upper 1 * (lower 1)⁻¹)) = ellipticCount m := by
    unfold fixed
    rw [levelRep_E, ← card_fin_eq_ellipticCount, ← finrank_fixed_elliptic m e]
  rw [hE, finrank_sym] at h
  exact h

/-- Values at `(0, 1)` kill `(L - 1)V`. -/
theorem eval_moved_lower (w : Binary.HomogeneousPoly m) (hw : w ∈ moved (levelRep m e) (lower 1)) :
    eval ![0, 1] w.val = 0 := by
  obtain ⟨v, rfl⟩ := hw
  rw [levelRep_L]
  change eval ![0, 1] ((Binary.homogeneousAction m e (lowerC 3) v).val - v.val) = 0
  rw [map_sub, Binary.homogeneousAction_coe, eval_lower]
  simp

end Representation

section Bound

variable {m : ℕ} (e : ℤ)

theorem levelRep_apply_val (g : binaryArithmeticLevel) (v : Binary.HomogeneousPoly m) :
    (levelRep m e g v).val = Binary.action e (binaryIntegralComplex g.val) v.val := rfl

/-- For even twist, `X₁^m` is fixed by `T` and `ε`. -/
theorem one_le_finrank_fixed_T_ε (even : Even e) :
    1 ≤ finrank ℂ (fixed (levelRep m e) (upper 1) ⊓ fixed (levelRep m e) reflection :
      Submodule ℂ (Binary.HomogeneousPoly m)) := by
  apply one_le_finrank_of_mem _ (powerVector 1 m) _ (powerVector_ne_zero 1 m)
  refine ⟨?_, ?_⟩
  · have h := powerVector_one_mem_upper (m := m) e 1
    change powerVector 1 m ∈ LinearMap.ker (levelRep m e (upper 1) - 1)
    rw [levelRep_T]
    exact h
  · rw [SetLike.mem_coe, mem_fixed]
    apply Subtype.ext
    apply MvPolynomial.funext
    intro x
    rw [levelRep_ε, Binary.homogeneousAction_coe, eval_vec, eval_reflection, eval_vec _ x,
      even.neg_one_zpow, one_mul]
    simp [powerVector]

/-- For odd twist, `(1 - σ)(E - 1)X₁^m ∈ K⁻` has nonzero value at `(0, 1)`. -/
theorem exists_kernelMinus_not_moved (positive : 0 < m) (odd : Odd e) :
    ∃ w ∈ kernelMinus (ρ := levelRep m e) (upper 1) (lower 1) reflection,
      w ∉ moved (levelRep m e) (lower 1) := by
  set ρ := levelRep m e
  let u : Binary.HomogeneousPoly m := powerVector 1 m
  let y : Binary.HomogeneousPoly m := ρ (upper 1 * (lower 1)⁻¹) u - u
  have hy : y ∈ kernelE (ρ := ρ) (upper 1) (lower 1) := by
    rw [LinearMap.mem_ker]
    exact norm3_sub_eq_zero level_cube u
  refine ⟨y - ρ (lower 1 * reflection) y, sub_sigma_mem_kernelMinus hεT hεL level_cube hy, ?_⟩
  intro moved_mem
  have zero := eval_moved_lower e _ moved_mem
  have value_y : eval ![0, 1] y.val = (-2 : ℂ) ^ m - 1 := by
    change eval ![0, 1] ((ρ (upper 1 * (lower 1)⁻¹) u).val - u.val) = _
    rw [map_sub, levelRep_E, Binary.homogeneousAction_coe, eval_elliptic]
    simp [u, powerVector]
  have value_σ : eval ![0, 1] (ρ (lower 1 * reflection) y).val = -eval ![0, 1] y.val := by
    rw [map_mul, Module.End.mul_apply, levelRep_L, levelRep_ε, Binary.homogeneousAction_coe,
      eval_lower, Binary.homogeneousAction_coe, mul_zero, sub_zero, eval_reflection, neg_zero,
      odd.neg_one_zpow, neg_one_mul]
  have total : eval ![0, 1] (y - ρ (lower 1 * reflection) y).val = 2 * ((-2 : ℂ) ^ m - 1) := by
    rw [Submodule.coe_sub, map_sub, value_σ, value_y]
    ring
  rw [total] at zero
  have ne : (-2 : ℂ) ^ m - 1 ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have hnorm := congrArg (fun z : ℂ => ‖z‖) h
    simp only [norm_pow, norm_neg, norm_one] at hnorm
    have two : ‖(2 : ℂ)‖ = 2 := by simp
    rw [two] at hnorm
    have : (1 : ℝ) < 2 ^ m := one_lt_pow₀ (by norm_num) (by omega)
    linarith
  exact ne ((mul_eq_zero.mp zero).resolve_left two_ne_zero)

/-- **Sharp parabolic bound**: `dim H¹_par(Γ₁'(3), Sym^m ⊗ det^e) + 1 ≤ ⌊(m + 2)/3⌋` (`m > 0`). -/
theorem finrank_level_parabolicH1_le (positive : 0 < m) :
    finrank ℂ (parabolicH1 (levelRep m e) (upper 1) (lower 1)) + 1 ≤ (m + 2) / 3 := by
  have main := finrank_parabolicH1_reflection_le (ρ := levelRep m e) level_closure
    reflection_mul_self hεT hεL level_cube (level_invariants e positive)
  have halving := finrank_Kminus_add_le (ρ := levelRep m e) hεT hεL level_cube
  have kernel := finrank_level_kernelE e m
  have count := ellipticCount_add m
  have cut : finrank ℂ (parabolicH1 (levelRep m e) (upper 1) (lower 1)) + 1 ≤
      finrank ℂ (kernelMinus (ρ := levelRep m e) (upper 1) (lower 1) reflection) := by
    rcases Int.even_or_odd e with even | odd
    · have one := one_le_finrank_fixed_T_ε (m := m) e even
      have mono := Submodule.finrank_mono
        (inf_le_right : moved (levelRep m e) (lower 1) ⊓
          kernelMinus (ρ := levelRep m e) (upper 1) (lower 1) reflection ≤ _)
      omega
    · obtain ⟨w, hw, hnot⟩ := exists_kernelMinus_not_moved e positive odd
      have strict : moved (levelRep m e) (lower 1) ⊓
          kernelMinus (ρ := levelRep m e) (upper 1) (lower 1) reflection <
          kernelMinus (ρ := levelRep m e) (upper 1) (lower 1) reflection := by
        apply lt_of_le_of_ne inf_le_right
        intro h
        exact hnot (h ▸ hw : w ∈ moved (levelRep m e) (lower 1) ⊓ _).1
      have := Submodule.finrank_lt_finrank_of_lt strict
      omega
  omega

end Bound

section BadLine

theorem binaryParabolicH1_le (degree : ℕ) :
    binaryParabolicH1 degree ≤ parabolicH1 (binaryArithmeticRepresentation degree) (upper 1) (lower 1) := by
  intro x hx
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hx' : (crossedBoundaries (binaryArithmeticRepresentation degree)).mkQ z ∈
      binaryParabolicH1 degree := hx
  refine ⟨z, ⟨?_, ?_⟩, rfl⟩
  · obtain ⟨p, hp⟩ := parabolic_generator_primitive z hx' 1 (upper 1) upper_cusp
    exact ⟨p, hp.symm⟩
  · have membership : lower 1 ∈ binaryCuspLevel oppositeFrame := by
      rw [← inv_inv (lower 1), lower_inv]
      exact (binaryCuspLevel oppositeFrame).inv_mem lower_cusp
    obtain ⟨p, hp⟩ := parabolic_generator_primitive z hx' oppositeFrame (lower 1) membership
    exact ⟨p, hp.symm⟩

/-- **`dim binaryParabolicH1 degree + 1 ≤ ⌊(degree + 3)/3⌋`**. -/
theorem finrank_binaryParabolicH1_le_sharp (degree : ℕ) :
    finrank ℂ (binaryParabolicH1 degree) + 1 ≤ (degree + 3) / 3 := by
  have : FiniteDimensional ℂ (CrossedH1 (binaryArithmeticRepresentation degree)) :=
    level_H1_finiteDimensional 0 (Nat.succ_pos degree)
  have mono := Submodule.finrank_mono (binaryParabolicH1_le degree)
  have bound := finrank_level_parabolicH1_le (m := degree + 1) 0 (Nat.succ_pos degree)
  change finrank ℂ (parabolicH1 (binaryArithmeticRepresentation degree) (upper 1) (lower 1)) + 1 ≤ _
    at bound
  omega

/-- **Inner bad-line classes: `dim + 1 ≤ ⌊(degree + 3)/3⌋`** (`0 < degree`), the value
`dim S_{degree+3}(Γ₁(3)) = ⌊(degree + 3)/3⌋ - 1`. -/
theorem finrank_innerBadLineClasses_le_sharp (degree : ℕ) (positive : 0 < degree) :
    finrank ℂ (innerBadLineClasses degree) + 1 ≤ (degree + 3) / 3 := by
  have : FiniteDimensional ℂ (CrossedH1 (binaryArithmeticRepresentation degree)) :=
    level_H1_finiteDimensional 0 (Nat.succ_pos degree)
  have le := LinearMap.finrank_le_finrank_of_injective
    (innerBadLineParabolicMap_injective degree positive)
  have bound := finrank_binaryParabolicH1_le_sharp degree
  omega

/-- For `degree ∈ {3, 4, 5}` the inner bad-line classes span at most a line. -/
theorem finrank_innerBadLineClasses_le_one (degree : ℕ) (positive : 0 < degree)
    (small : degree ≤ 5) : finrank ℂ (innerBadLineClasses degree) ≤ 1 := by
  have bound := finrank_innerBadLineClasses_le_sharp degree positive
  omega

end BadLine

end TernaryPeriodPolynomials.LevelThree.SharpBounds
