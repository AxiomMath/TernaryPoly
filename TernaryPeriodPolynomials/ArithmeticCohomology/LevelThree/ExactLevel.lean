module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Existence
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.FullBound
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.TwistSplitting

@[expose] public section


/-!
# Exact cohomology of the level-three Levi `Γ₁'(3)`

The two twists `Sym^m ⊗ det^e` and `Sym^m ⊗ det^{e+1}` agree on `Γ₁(3)` and differ by sign on
`ε = diag(-1, 1)`, so `TwistSplitting` bounds the (exact) `Γ₁(3)` dimensions of `Existence` by the
sum of the two `Γ₁'(3)` dimensions; with the upper bounds of `SharpBounds` / `FullBound` every bound
is attained. For `m > 0` and every twist `e`:

* **`finrank_level_parabolicH1_eq`**: `dim H¹_par(Γ₁'(3), Sym^m ⊗ det^e) + 1 = ⌊(m + 2)/3⌋`
  (the Eichler–Shimura value `dim S_{m+2}(Γ₁(3))`);
* **`finrank_level_H1_eq`**: `dim H¹(Γ₁'(3), Sym^m ⊗ det^e) + 1 = ⌊(m + 2)/3⌋ + [e + m odd] + [e odd]`;
* **`finrank_binaryArithmetic_H1_eq`**: for the bad-line coefficient,
  `dim H¹(Γ₁'(3), Sym^{degree+1}) + 1 = ⌊(degree + 3)/3⌋ + [degree even]`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThree.ExactLevel

open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators GammaOneThree TwoGenerator ParabolicBounds SharpBounds
open GeneralEisenstein Module Matrix

/-- Elements of `Γ₁(3)` have determinant one. -/
theorem core_det (k : core) : GeneralLinearGroup.det (k : binaryArithmeticLevel).val = 1 := by
  obtain ⟨k, hk⟩ := k
  change GeneralLinearGroup.det k.val = 1
  induction hk using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · apply Units.ext
      simp [GeneralLinearGroup.val_det_apply, upper, Matrix.det_fin_two_of]
    · apply Units.ext
      simp [GeneralLinearGroup.val_det_apply, lower, Matrix.det_fin_two_of]
  | one => simp
  | mul x y _ _ hx hy => rw [Subgroup.coe_mul, map_mul, hx, hy, one_mul]
  | inv x _ hx => rw [Subgroup.coe_inv, map_inv, hx, inv_one]

theorem complex_det (k : core) :
    ((GeneralLinearGroup.det (binaryIntegralComplex (k : binaryArithmeticLevel).val) : ℂˣ) : ℂ) = 1 := by
  have h := core_det k
  rw [GeneralLinearGroup.val_det_apply]
  have hdet := RingHom.map_det (Int.castRingHom ℂ) (k : binaryArithmeticLevel).val.val
  change (RingHom.mapMatrix (Int.castRingHom ℂ) (k : binaryArithmeticLevel).val.val).det = 1
  rw [← hdet]
  have h' := congrArg (fun u : ℤˣ => (u : ℤ)) h
  simp only [GeneralLinearGroup.val_det_apply, Units.val_one] at h'
  rw [h', map_one]

variable (m : ℕ) (e : ℤ)

/-- The twists `e` and `e + 1` agree on `Γ₁(3)`. -/
theorem twist_agree (k : core) :
    levelRep m (e + 1) (k : binaryArithmeticLevel) = levelRep m e (k : binaryArithmeticLevel) := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  change Binary.action (e + 1) (binaryIntegralComplex (k : binaryArithmeticLevel).val) p.val =
    Binary.action e (binaryIntegralComplex (k : binaryArithmeticLevel).val) p.val
  rw [Binary.action_apply, Binary.action_apply]
  have h1 : Binary.determinantCharacter (e + 1) (binaryIntegralComplex (k : binaryArithmeticLevel).val) = 1 := by
    change ((GeneralLinearGroup.det _ : ℂˣ) : ℂ) ^ (e + 1) = 1
    rw [complex_det, _root_.one_zpow]
  have h2 : Binary.determinantCharacter e (binaryIntegralComplex (k : binaryArithmeticLevel).val) = 1 := by
    change ((GeneralLinearGroup.det _ : ℂˣ) : ℂ) ^ e = 1
    rw [complex_det, _root_.one_zpow]
  rw [h1, h2]

/-- The twists `e` and `e + 1` differ by sign on `ε`. -/
theorem twist_anti : levelRep m (e + 1) reflection = -(levelRep m e reflection) := by
  rw [levelRep_ε, levelRep_ε]
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  change Binary.action (e + 1) reflectionC p.val = -(Binary.action e reflectionC p.val)
  rw [Binary.action_apply, Binary.action_apply]
  change ((GeneralLinearGroup.det reflectionC : ℂˣ) : ℂ) ^ (e + 1) • _ =
    -(((GeneralLinearGroup.det reflectionC : ℂˣ) : ℂ) ^ e • _)
  rw [reflectionC_det, zpow_add_one₀ (by norm_num : (-1 : ℂ) ≠ 0), mul_neg_one, neg_smul]

variable {m}

theorem parity_count (n : ℤ) :
    (if Even n then 0 else 1) + (if Even (n + 1) then 0 else 1) = 1 := by
  by_cases h : Even n
  · rw [ite_eq_left h, ite_eq_right (by rw [Int.even_add_one]; exact not_not.mpr h)]
  · rw [ite_eq_right h, ite_eq_left (by rw [Int.even_add_one]; exact h)]

/-- **Exact parabolic cohomology of `Γ₁'(3)`**: `dim H¹_par + 1 = ⌊(m + 2)/3⌋`. -/
theorem finrank_level_parabolicH1_eq (positive : 0 < m) :
    finrank ℂ (parabolicH1 (levelRep m e) (upper 1) (lower 1)) + 1 = (m + 2) / 3 := by
  have := level_H1_finiteDimensional (m := m) e positive
  have := level_H1_finiteDimensional (m := m) (e + 1) positive
  have split := TwistSplitting.finrank_parabolicH1_le_add (levelRep m e) (levelRep m (e + 1))
    mem_core_or reflection_mul_self (fun _ hk => conj_mem_core hk) (twist_agree m e)
    (twist_anti m e) (upper 1) (lower 1) coreT.property coreL.property hεT hεL
  have exact := Existence.finrank_core_parabolicH1_sym_eq (m := m) e positive
  change finrank ℂ (parabolicH1 ((levelRep m e).comp core.subtype) ⟨upper 1, coreT.property⟩
    ⟨lower 1, coreL.property⟩) + 2 = _ at exact
  have upper₁ := finrank_level_parabolicH1_le e positive
  have upper₂ := finrank_level_parabolicH1_le (e + 1) positive
  omega

/-- **Exact cohomology of `Γ₁'(3)`**:
`dim H¹ + 1 = ⌊(m + 2)/3⌋ + [e + m odd] + [e odd]`. -/
theorem finrank_level_H1_eq (positive : 0 < m) :
    finrank ℂ (CrossedH1 (levelRep m e)) + 1 =
      (m + 2) / 3 + (if Even (e + m) then 0 else 1) + (if Even e then 0 else 1) := by
  have := level_H1_finiteDimensional (m := m) e positive
  have := level_H1_finiteDimensional (m := m) (e + 1) positive
  have split := TwistSplitting.finrank_H1_le_add (levelRep m e) (levelRep m (e + 1))
    mem_core_or reflection_mul_self (fun _ hk => conj_mem_core hk) (twist_agree m e)
    (twist_anti m e)
  have exact := Existence.finrank_core_H1_sym_eq (m := m) e positive
  change finrank ℂ (CrossedH1 ((levelRep m e).comp core.subtype)) = _ at exact
  have upper₁ := FullBound.finrank_level_H1_le_sharp e positive
  have upper₂ := FullBound.finrank_level_H1_le_sharp (e + 1) positive
  have p₁ := parity_count (e + m)
  have p₂ := parity_count e
  rw [show e + 1 + (m : ℤ) = e + m + 1 by ring] at upper₂
  omega

/-- **The bad-line Levi cohomology, exactly**:
`dim H¹(Γ₁'(3), Sym^{degree+1}) + 1 = ⌊(degree + 3)/3⌋ + [degree even]`. -/
theorem finrank_binaryArithmetic_H1_eq (degree : ℕ) :
    finrank ℂ (CrossedH1 (binaryArithmeticRepresentation degree)) + 1 =
      (degree + 3) / 3 + (if Even degree then 1 else 0) := by
  have h := finrank_level_H1_eq (m := degree + 1) 0 (Nat.succ_pos degree)
  change finrank ℂ (CrossedH1 (binaryArithmeticRepresentation degree)) + 1 = _ at h
  have parity : Even ((0 : ℤ) + ((degree + 1 : ℕ) : ℤ)) ↔ ¬ Even degree := by
    rw [zero_add, Int.even_coe_nat, Nat.even_add_one]
  have h0 : Even (0 : ℤ) := ⟨0, rfl⟩
  by_cases hd : Even degree
  · rw [ite_eq_right (by rw [parity]; exact not_not.mpr hd), ite_eq_left h0] at h
    rw [ite_eq_left hd]
    omega
  · rw [ite_eq_left (parity.mpr hd), ite_eq_left h0] at h
    rw [ite_eq_right hd]
    omega

end TernaryPeriodPolynomials.LevelThree.ExactLevel
