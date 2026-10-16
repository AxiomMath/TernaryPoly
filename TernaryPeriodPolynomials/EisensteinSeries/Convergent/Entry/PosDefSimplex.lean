module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.CholeskyContinuity
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.TriangleGreen

@[expose] public section


/-!
# Positive definite Gram triangles lie in the Cholesky domain

A positive definite symmetric `3 × 3` matrix lies in `cholDomain` (`posDef_mem_cholDomain`); convex combinations of
positive definite matrices are positive definite (`posDef_convex3`), so the affine triangle of three positive
definite Gram matrices lies in the Cholesky domain (`affTri_mem_cholDomain`); Gram matrices of invertible matrices and
their congruences by invertible matrices are positive definite (`posDef_gram`, `posDef_congr`).

Formalized by Claude Sonnet 5.5.
-/

open scoped Matrix.Norms.Elementwise
open Matrix

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

theorem posDef_mem_cholDomain {P : Mat3} (hP : P.PosDef) : P ∈ cholDomain := by
  refine ⟨hP.diag_pos, ?_, hP.det_pos⟩
  have h2 := (hP.submatrix (e := ![1, 2]) (by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all)).det_pos
  rw [Matrix.det_fin_two] at h2
  have hs : P 2 1 = P 1 2 := by
    have := hP.isHermitian
    have := congrFun (congrFun this.eq 1) 2
    simpa using this
  simpa [Matrix.submatrix, hs, sq] using h2

theorem posDef_convex3 {A B C : Mat3} (hA : A.PosDef) (hB : B.PosDef) (hC : C.PosDef) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a + b + c = 1) : (a • A + b • B + c • C).PosDef := by
  have sA : (a • A).PosSemidef := hA.posSemidef.smul ha
  have sB : (b • B).PosSemidef := hB.posSemidef.smul hb
  have sC : (c • C).PosSemidef := hC.posSemidef.smul hc
  rcases (show 0 < a ∨ 0 < b ∨ 0 < c by
    by_contra hcon
    push Not at hcon
    linarith [hcon.1, hcon.2.1, hcon.2.2]) with h1 | h1 | h1
  · exact ((hA.smul h1).add_posSemidef sB).add_posSemidef sC
  · have := ((hB.smul h1).add_posSemidef sA).add_posSemidef sC
    convert this using 1
    abel
  · have := ((hC.smul h1).add_posSemidef sA).add_posSemidef sB
    convert this using 1
    abel

theorem posDef_affTri {Γ₀ Γ₁ Γ₂ : Mat3} (h₀ : Γ₀.PosDef) (h₁ : Γ₁.PosDef) (h₂ : Γ₂.PosDef)
    {p : ℝ × ℝ} (hp : p ∈ stdTriangle) : (affTri Γ₀ Γ₁ Γ₂ p).PosDef := by
  obtain ⟨hp1, hp2, hp3⟩ := hp
  have e : affTri Γ₀ Γ₁ Γ₂ p = (1 - p.1 - p.2) • Γ₀ + p.1 • Γ₁ + p.2 • Γ₂ := by
    unfold affTri; module
  rw [e]
  exact posDef_convex3 h₀ h₁ h₂ (by linarith) hp1 hp2 (by ring)

theorem affTri_mem_cholDomain {Γ₀ Γ₁ Γ₂ : Mat3} (h₀ : Γ₀.PosDef) (h₁ : Γ₁.PosDef) (h₂ : Γ₂.PosDef) :
    ∀ p ∈ stdTriangle, affTri Γ₀ Γ₁ Γ₂ p ∈ cholDomain :=
  fun _ hp => posDef_mem_cholDomain (posDef_affTri h₀ h₁ h₂ hp)

theorem injective_vecMul_of_det_ne {g : Mat3} (hg : g.det ≠ 0) : Function.Injective fun v : Fin 3 → ℝ => v ᵥ* g := by
  have hu : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).mpr (isUnit_iff_ne_zero.mpr hg)
  exact Matrix.vecMul_injective_iff_isUnit.mpr hu

theorem posDef_gram {g : Mat3} (hg : g.det ≠ 0) : (g * gᵀ).PosDef := by
  have := Matrix.PosDef.mul_conjTranspose_self g (injective_vecMul_of_det_ne hg)
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this

theorem posDef_congr {P : Mat3} (hP : P.PosDef) {M : Mat3} (hM : M.det ≠ 0) : (M * P * Mᵀ).PosDef := by
  have := hP.mul_mul_conjTranspose_same (injective_vecMul_of_det_ne hM)
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
