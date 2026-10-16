module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Cusp.Equivariance
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Instance

@[expose] public section


/-!
# Proposition C.4 at the other plane cusps of `Γ(N)`

All rational planes are obtained from the standard one by an integral change of basis
`h ∈ SL₃(ℤ)` (the paper's "rational conjugation of the finitely many other plane cusps"), and
`Γ(N)` is normal in `SL₃(ℤ)`. The cusp is `h⁻¹ P h` (`CuspData.ofSL h`), its stabilizer in `Γ(N)` is
`Γ(N) ∩ h⁻¹ P(ℚ) h` (`mem_stabRow_ofSL_iff_rational`), and the Levi data of the paper
(`Λ_P` is the Levi projection of `Γ_P`) is again `Λ_N = Γ₂(N)` (`mem_leviGroup_iff_cusp`,
`leviInCusp_gammaN`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

open scoped MatrixGroups
open Matrix

/-! ### Integral changes of basis -/

/-- The plane cusp `h⁻¹ P h` for an integral change of basis `h ∈ SL₃(ℤ)`: `a = h`, and `r` is the
bottom row of `h`. Every rational plane is of this form. -/
def CuspData.ofSL (h : SL(3, ℤ)) : CuspData where
  a := realMat h
  det_a := det_realMat h
  r := fun j => (h : Matrix (Fin 3) (Fin 3) ℤ) 2 j
  lam := 1
  row_a j := by simp [realMat_apply]

theorem planeStab_eq_stabRow : planeStab = stabRow ![0, 0, 1] := by
  ext γ
  constructor
  · rintro ⟨h0, h1, h2⟩
    show ![0, 0, 1] ᵥ* (γ : Matrix (Fin 3) (Fin 3) ℤ) = ![0, 0, 1]
    ext j
    fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, h0, h1, h2]
  · intro hγ
    have h' : ![0, 0, 1] ᵥ* (γ : Matrix (Fin 3) (Fin 3) ℤ) = ![0, 0, 1] := hγ
    have e0 := congrFun h' 0
    have e1 := congrFun h' 1
    have e2 := congrFun h' 2
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three] at e0 e1 e2
    exact ⟨e0, e1, e2⟩

theorem mem_stabRow_vecMul_iff (r : Fin 3 → ℤ) (h p : SL(3, ℤ)) :
    p ∈ stabRow (r ᵥ* (h : Matrix (Fin 3) (Fin 3) ℤ)) ↔ h * p * h⁻¹ ∈ stabRow r := by
  have hh : ((h⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) * (h : Matrix (Fin 3) (Fin 3) ℤ) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]; rfl
  have hh' : (h : Matrix (Fin 3) (Fin 3) ℤ) * ((h⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]; rfl
  show r ᵥ* (h : Matrix (Fin 3) (Fin 3) ℤ) ᵥ* (p : Matrix (Fin 3) (Fin 3) ℤ) =
      r ᵥ* (h : Matrix (Fin 3) (Fin 3) ℤ) ↔
    r ᵥ* ((h * p * h⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) = r
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [Matrix.vecMul_vecMul]
  constructor
  · intro hx
    rw [← Matrix.vecMul_vecMul, hx, Matrix.vecMul_vecMul, hh', Matrix.vecMul_one]
  · intro hx
    have := congrArg (fun v => v ᵥ* (h : Matrix (Fin 3) (Fin 3) ℤ)) hx
    simp only [Matrix.vecMul_vecMul, Matrix.mul_assoc, hh, Matrix.mul_one] at this
    exact this

theorem ofSL_r (h : SL(3, ℤ)) : (CuspData.ofSL h).r = ![0, 0, 1] ᵥ* (h : Matrix (Fin 3) (Fin 3) ℤ) := by
  ext j
  simp [CuspData.ofSL, Matrix.vecMul, dotProduct, Fin.sum_univ_three]

/-- The cusp stabilizer of `h⁻¹ P h`: `p ∈ Γ_P` iff `h p h⁻¹` fixes the plane. -/
theorem mem_stabRow_ofSL (h p : SL(3, ℤ)) :
    p ∈ stabRow (CuspData.ofSL h).r ↔ h * p * h⁻¹ ∈ planeStab := by
  rw [ofSL_r, mem_stabRow_vecMul_iff, planeStab_eq_stabRow]

theorem realMat_conj (h p : SL(3, ℤ)) :
    (CuspData.ofSL h).a * realMat p * (CuspData.ofSL h).a⁻¹ = realMat (h * p * h⁻¹) := by
  simp [CuspData.ofSL, realMat_mul, realMat_inv]

/-- **The Levi data of the integral cusps of `Γ(N)`**: for every integral change of basis `h`,
the Levi block of the conjugate of every element of the cusp stabilizer `Γ(N) ∩ h⁻¹ P h` lies in
`Λ_N = Γ₂(N)`. -/
theorem leviInCusp_gammaN (N : ℕ) (h : SL(3, ℤ)) :
    LeviInCusp (CuspData.ofSL h) (gammaN N) (leviGroup N) := by
  intro p hp hs
  have hq : h * p * h⁻¹ ∈ gammaN N := by
    have := (gammaN_normal N).conj_mem p hp h
    simpa [mul_assoc] using this
  have hq' := (mem_stabRow_ofSL h p).1 hs
  obtain ⟨g, hg, hge⟩ := leviIn_gammaN N _ hq hq'
  exact ⟨g, hg, by rw [realMat_conj]; exact hge⟩

/-- **`Λ_N` is the Levi projection of the cusp stabilizer at every integral cusp.** -/
theorem mem_leviGroup_iff_cusp (N : ℕ) (h : SL(3, ℤ)) (g : GL (Fin 2) ℝ) :
    g ∈ leviGroup N ↔ ∃ p ∈ gammaN N, p ∈ stabRow (CuspData.ofSL h).r ∧
      (g : Matrix (Fin 2) (Fin 2) ℝ) =
        topBlock ((CuspData.ofSL h).a * realMat p * (CuspData.ofSL h).a⁻¹) := by
  rw [mem_leviGroup_iff]
  constructor
  · rintro ⟨q, hq, hs, hg⟩
    refine ⟨h⁻¹ * q * h, ?_, ?_, ?_⟩
    · have := (gammaN_normal N).conj_mem q hq h⁻¹
      simpa using this
    · rw [mem_stabRow_ofSL]; simpa [mul_assoc] using hs
    · rw [realMat_conj]; simpa [mul_assoc] using hg
  · rintro ⟨p, hp, hs, hg⟩
    refine ⟨h * p * h⁻¹, ?_, (mem_stabRow_ofSL h p).1 hs, ?_⟩
    · have := (gammaN_normal N).conj_mem p hp h
      simpa [mul_assoc] using this
    · rw [← realMat_conj]; exact hg

/-- For `N ≥ 3`, the cusp stabilizer of `Γ(N)` is `Γ(N) ∩ h⁻¹ P(ℚ) h`: `p` stabilizes the cusp iff
`h p h⁻¹` has bottom row `(0, 0, *)`. -/
theorem mem_stabRow_ofSL_iff_rational {N : ℕ} (hN : 3 ≤ N) (h : SL(3, ℤ)) {p : SL(3, ℤ)}
    (hp : p ∈ gammaN N) :
    p ∈ stabRow (CuspData.ofSL h).r ↔
      ((h * p * h⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0 ∧
        ((h * p * h⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = 0 := by
  have hq : h * p * h⁻¹ ∈ gammaN N := by
    have := (gammaN_normal N).conj_mem p hp h
    simpa [mul_assoc] using this
  rw [mem_stabRow_ofSL]
  exact gammaN_inf_rationalPlane hN hq

end TernaryPeriodPolynomials.Argument.ConvergenceC4
