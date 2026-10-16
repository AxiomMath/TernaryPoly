module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.PrimeWeight

@[expose] public section


/-!
# The central Hecke operator `p · 1`

For a prime `p`, every correspondence of the scalar double coset `GL₃(ℤ) (p·1) GL₃(ℤ)` has a single
representative, and its plane eigenvalue is the weight of the scalar Levi datum `(p·1₂, p)`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.HeckeEigen.Satake

variable {n p : ℕ}

/-- The scalar `p · 1` in `GL₃(ℚ)`. -/
def pScalar (hp : p.Prime) : RationalGL3 :=
  ⟨(p : ℚ) • 1, (p : ℚ)⁻¹ • 1, by
    have : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ this, one_smul],
    by
    have : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, inv_mul_cancel₀ this, one_smul]⟩

/-- The scalar `p · 1` in `GL₂(ℚ)`. -/
def pScalar2 (hp : p.Prime) : GeneralLinearGroup (Fin 2) ℚ :=
  ⟨(p : ℚ) • 1, (p : ℚ)⁻¹ • 1, by
    have : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ this, one_smul],
    by
    have : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, inv_mul_cancel₀ this, one_smul]⟩

theorem pScalar_val (hp : p.Prime) : (pScalar hp).val = (p : ℚ) • 1 := rfl

theorem pScalar2_val (hp : p.Prime) : (pScalar2 hp).val = (p : ℚ) • 1 := rfl

theorem pScalar_central (hp : p.Prime) (x : RationalGL3) : pScalar hp * x = x * pScalar hp := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, pScalar_val, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one]

theorem pScalar_plane (hp : p.Prime) : pScalar hp = pU 0 * planeLevi (pScalar2 hp) (pUnit hp) := by
  apply Units.ext
  rw [plane_val, pScalar_val, pScalar2_val, pUnit_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- A scalar double coset has a single representative. -/
theorem pScalar_reps (hp : p.Prime) {t : HeckeCorrespondence} (ht : AwayThree t)
    (hg : t.g = pScalar hp) : ∃ r₀, t.representatives = {r₀} := by
  have hRS := repSet ht
  have hmem : pScalar hp ∈ DZ t.g := ⟨1, Γ.one_mem, 1, Γ.one_mem, by rw [hg, one_mul, mul_one]⟩
  obtain ⟨r₀, hr₀, -⟩ := hRS.cover _ hmem
  refine ⟨r₀, Finset.eq_singleton_iff_unique_mem.mpr ⟨hr₀, fun r hr => ?_⟩⟩
  apply hRS.disj r hr r₀ hr₀
  obtain ⟨a, ha, b, hb, hr⟩ := hRS.sub r hr
  obtain ⟨a', ha', b', hb', hr'⟩ := hRS.sub r₀ hr₀
  rw [hg] at hr hr'
  have hr2 : r = a * b * pScalar hp := by rw [hr, mul_assoc, pScalar_central, ← mul_assoc]
  have hr3 : r₀ = a' * b' * pScalar hp := by rw [hr', mul_assoc, pScalar_central, ← mul_assoc]
  rw [hr2, hr3]
  have hc := pScalar_central hp ((a * b)⁻¹ * (a' * b'))
  have : (a * b * pScalar hp)⁻¹ * (a' * b' * pScalar hp) = (a * b)⁻¹ * (a' * b') := by
    calc (a * b * pScalar hp)⁻¹ * (a' * b' * pScalar hp)
        = (pScalar hp)⁻¹ * (((a * b)⁻¹ * (a' * b')) * pScalar hp) := by group
      _ = (pScalar hp)⁻¹ * (pScalar hp * ((a * b)⁻¹ * (a' * b'))) := by rw [hc]
      _ = (a * b)⁻¹ * (a' * b') := by group
  rw [this]
  exact Γ.mul_mem (Γ.inv_mem (Γ.mul_mem ha hb)) (Γ.mul_mem ha' hb')

/-- **The central plane eigenvalue.** -/
theorem central_plane_eigenvalue (D : InducingData n) (hp : p.Prime) (t : HeckeCorrespondence)
    (ht : AwayThree t) (hg : t.g = pScalar hp) :
    ∀ f : AdelicGL → ℂ, IsInduced D .plane cohomologicalPoint f → ∀ g : AdelicGL,
      ∑ r ∈ t.representatives, f (g * atFinite (rationalFinite r)) =
        ratPlaneWeight D (pScalar2 hp) (pUnit hp) * f g := by
  classical
  have hdec : ∀ r ∈ t.representatives, ∃ γ : IntegralGL,
      r = pU 0 * planeLevi (pScalar2 hp) (pUnit hp) * integralRational γ := by
    intro r hr
    obtain ⟨a, ha, b, hb, hr'⟩ := (repSet ht).sub r hr
    rw [hg, mul_assoc, pScalar_central, ← mul_assoc] at hr'
    obtain ⟨γ, hγ⟩ := Γ.mul_mem ha hb
    exact ⟨γ, by rw [hr', hγ, ← pScalar_plane, pScalar_central]⟩
  choose! γP hγP using hdec
  have hform := plane_rational_formula D t ht (fun _ => 0) (fun _ => pScalar2 hp) (fun _ => pUnit hp)
    γP hγP
  intro f hf g
  rw [hform f hf g]
  obtain ⟨r₀, hr₀⟩ := pScalar_reps hp ht hg
  rw [hr₀, Finset.sum_singleton]

end TernaryPeriodPolynomials.HeckeEigen.Satake
