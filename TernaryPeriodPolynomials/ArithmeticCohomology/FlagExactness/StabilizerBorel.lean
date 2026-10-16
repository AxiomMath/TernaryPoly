module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section


/-!
# Arithmetic stabilizers of complete flags

If `γ` in the arithmetic level fixes the complete flag `q B`, then `β = q⁻¹ γ q` is a
rational upper-triangular matrix. Its diagonal entries are rational eigenvalues of
the integral matrix `γ`, hence integers. Their product is `det γ = ±1`, so each one
is `±1`.

So the stabilizer permutes the averaging families of `FlagExact`
(`translatedEvaluation_stabilizer`, `lineTranslatedEvaluation_stabilizer`) through
the sign changes `t ↦ ±t` only.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.FlagExactness

/-- The conjugate of a flag stabilizer lies in the rational Borel subgroup. -/
theorem stabilizer_mem_borel (q γ : RationalGL3)
    (h : γ • (QuotientGroup.mk q : Edges) = QuotientGroup.mk q) :
    q⁻¹ * γ * q ∈ parabolic .plane ⊓ parabolic .line := by
  have h' : (QuotientGroup.mk (γ * q) : Edges) = QuotientGroup.mk q := h
  have hmem := QuotientGroup.eq.mp h'
  have hinv := (parabolic .plane ⊓ parabolic .line).inv_mem hmem
  have heq : ((γ * q)⁻¹ * q)⁻¹ = q⁻¹ * γ * q := by group
  rwa [heq] at hinv

theorem borel_entries {β : RationalGL3} (h : β ∈ parabolic .plane ⊓ parabolic .line) :
    β.val 1 0 = 0 ∧ β.val 2 0 = 0 ∧ β.val 2 1 = 0 :=
  ⟨h.2.1, h.1.1, h.1.2⟩

theorem borel_charpoly_eval {β : RationalGL3} (h10 : β.val 1 0 = 0) (h20 : β.val 2 0 = 0)
    (h21 : β.val 2 1 = 0) (μ : ℚ) :
    (Matrix.scalar (Fin 3) μ - β.val).det =
      (μ - β.val 0 0) * (μ - β.val 1 1) * (μ - β.val 2 2) := by
  rw [Matrix.det_fin_three]
  simp [Matrix.sub_apply, h10, h20, h21]

theorem borel_det {β : RationalGL3} (h10 : β.val 1 0 = 0) (h20 : β.val 2 0 = 0)
    (h21 : β.val 2 1 = 0) :
    β.val.det = β.val 0 0 * β.val 1 1 * β.val 2 2 := by
  rw [Matrix.det_fin_three]
  simp [h10, h20, h21]

theorem scalar_eq_smul_one (μ : ℚ) : Matrix.scalar (Fin 3) μ = μ • (1 : Matrix (Fin 3) (Fin 3) ℚ) := by
  rw [Matrix.smul_one_eq_diagonal]
  rfl

/-- Conjugation invariance of `det (μ - M)`. -/
theorem det_scalar_sub_conj (q γ : RationalGL3) (μ : ℚ) :
    (Matrix.scalar (Fin 3) μ - (q⁻¹ * γ * q).val).det = (Matrix.scalar (Fin 3) μ - γ.val).det := by
  have hqq' : (q⁻¹).val * q.val = 1 := by
    rw [← GeneralLinearGroup.coe_mul, inv_mul_cancel, GeneralLinearGroup.coe_one]
  have hconj : Matrix.scalar (Fin 3) μ - (q⁻¹ * γ * q).val =
      (q⁻¹).val * (Matrix.scalar (Fin 3) μ - γ.val) * q.val := by
    rw [GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_mul, Matrix.mul_sub, Matrix.sub_mul,
      scalar_eq_smul_one, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hqq']
  rw [hconj, Matrix.det_mul, Matrix.det_mul, mul_comm (q⁻¹).val.det, mul_assoc,
    ← Matrix.det_mul, hqq', Matrix.det_one, mul_one]

/-- Diagonal entries of the conjugated stabilizer are integers. -/
theorem stabilizer_diag_integer (q : RationalGL3) (γ : rationalLevel)
    (h : γ.val • (QuotientGroup.mk q : Edges) = QuotientGroup.mk q) (i : Fin 3) :
    ∃ r : ℤ, (q⁻¹ * γ.val * q).val i i = r := by
  obtain ⟨h10, h20, h21⟩ := borel_entries (stabilizer_mem_borel q γ.val h)
  obtain ⟨g, hg⟩ := γ.property
  have hγ : γ.val.val = (g.val.val).map (Int.castRingHom ℚ) := by
    rw [← hg]
    rfl
  have hroot : Polynomial.aeval ((q⁻¹ * γ.val * q).val i i) (g.val.val).charpoly = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, ← Matrix.charpoly_map,
      Matrix.eval_charpoly]
    change (Matrix.scalar (Fin 3) _ - (g.val.val).map (Int.castRingHom ℚ)).det = 0
    rw [← hγ, ← det_scalar_sub_conj q γ.val, borel_charpoly_eval h10 h20 h21]
    fin_cases i <;> simp
  obtain ⟨r, hr, -⟩ := exists_integer_of_is_root_of_monic (Matrix.charpoly_monic _) hroot
  exact ⟨r, by rw [hr]; simp⟩

/-- Diagonal entries of the conjugated stabilizer are `±1`. -/
theorem stabilizer_diag_sign (q : RationalGL3) (γ : rationalLevel)
    (h : γ.val • (QuotientGroup.mk q : Edges) = QuotientGroup.mk q) (i : Fin 3) :
    (q⁻¹ * γ.val * q).val i i = 1 ∨ (q⁻¹ * γ.val * q).val i i = -1 := by
  obtain ⟨h10, h20, h21⟩ := borel_entries (stabilizer_mem_borel q γ.val h)
  obtain ⟨g, hg⟩ := γ.property
  obtain ⟨a, ha⟩ := stabilizer_diag_integer q γ h 0
  obtain ⟨b, hb⟩ := stabilizer_diag_integer q γ h 1
  obtain ⟨c, hc⟩ := stabilizer_diag_integer q γ h 2
  have hdetγ : (γ.val.val).det = ((GeneralLinearGroup.det g.val : ℤˣ) : ℤ) := by
    rw [← hg]
    change ((g.val.val).map (Int.castRingHom ℚ)).det = _
    rw [GeneralLinearGroup.val_det_apply]
    exact (RingHom.map_det (Int.castRingHom ℚ) g.val.val).symm
  have hdet : (q⁻¹ * γ.val * q).val.det = (γ.val.val).det := by
    rw [GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_mul, Matrix.det_mul, Matrix.det_mul,
      mul_comm (q⁻¹).val.det, mul_assoc, ← Matrix.det_mul, ← GeneralLinearGroup.coe_mul,
      inv_mul_cancel, GeneralLinearGroup.coe_one, Matrix.det_one, mul_one]
  rw [borel_det h10 h20 h21, ha, hb, hc, hdetγ] at hdet
  have hint : a * b * c = ((GeneralLinearGroup.det g.val : ℤˣ) : ℤ) := by exact_mod_cast hdet
  have hunit : IsUnit (a * b * c) := by rw [hint]; exact Units.isUnit _
  have hua : IsUnit a := isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hunit)
  have hub : IsUnit b := isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hunit)
  have huc : IsUnit c := isUnit_of_mul_isUnit_right hunit
  fin_cases i
  · rcases Int.isUnit_iff.mp hua with h | h <;> simp [ha, h]
  · rcases Int.isUnit_iff.mp hub with h | h <;> simp [hb, h]
  · rcases Int.isUnit_iff.mp huc with h | h <;> simp [hc, h]

end TernaryPeriodPolynomials.FlagExactness
