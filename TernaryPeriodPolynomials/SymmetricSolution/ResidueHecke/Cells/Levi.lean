module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.HomModel

@[expose] public section


/-!
# Lemma B.1: the stabilizer `P_H`, its radical and the factor `λ²`

Formalized by Claude Sonnet 5.5.
Paper: Appendix A.3: "The stabilizer of `a = 0` in `GL₃(ℚ)` consists of `g = (λ 0; u C)`.  On the
determinant-twisted residue its action is `q ↦ det(C) q(C(b,c))`.  Its integral radical `U = ℤ²`
acts trivially on that fiber.  Right homology acts on `H₂(U,ℚ)` by inverse conjugation, with factor
`λ²/det C`.  The combined factor is therefore `λ²`.  On the integral Levi this is one."
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open TernaryPoly TernaryPoly.ModThreeGoodAction
open scoped Matrix
open TernaryPoly.OrdinaryResidueSupport (rowAction axis normalOfRow normalOfRow_eq_iff
  rowAction_normalOfRow axis_primitive)
open TernaryPoly.OrdinaryResidueParabolic (blockMatrix)

/-- `P_H` is the group of integral matrices with first row `(±1, 0, 0)`: those preserving the
hyperplane `H = {a = 0}`, i.e. the integral points of `(λ 0; u C)`. -/
theorem mem_PH_iff_row (g : IntegralGL) : g ∈ PH ↔ g.val 0 1 = 0 ∧ g.val 0 2 = 0 := by
  have hrow : ∀ j : Fin 3, Matrix.vecMul (Pi.single 0 (1 : ℤ)) g.val j = g.val 0 j := by
    intro j
    simp [Matrix.vecMul, dotProduct, Pi.single_apply]
  rw [mem_PH]
  change rowAction g (normalOfRow (Pi.single 0 1) (axis_primitive 0)) =
    normalOfRow (Pi.single 0 1) (axis_primitive 0) ↔ _
  rw [rowAction_normalOfRow, normalOfRow_eq_iff]
  constructor
  · rintro (h | h)
    · exact ⟨by rw [← hrow, h]; simp, by rw [← hrow, h]; simp⟩
    · exact ⟨by rw [← hrow, h]; simp, by rw [← hrow, h]; simp⟩
  · rintro ⟨h1, h2⟩
    have hdet : IsUnit g.val.det := (Matrix.isUnit_iff_isUnit_det g.val).mp g.isUnit
    have hd : g.val.det = g.val 0 0 * (g.val 1 1 * g.val 2 2 - g.val 1 2 * g.val 2 1) := by
      rw [Matrix.det_fin_three, h1, h2]; ring
    have hu : IsUnit (g.val 0 0) := by
      rw [hd] at hdet
      exact isUnit_of_mul_isUnit_left hdet
    have hrow' : Matrix.vecMul (Pi.single 0 (1 : ℤ)) g.val = Pi.single 0 (g.val 0 0) := by
      funext j
      rw [hrow]
      fin_cases j
      · simp
      · simpa using h1
      · simpa using h2
    rcases Int.isUnit_iff.mp hu with h | h
    · left; rw [hrow', h]
    · right
      rw [hrow', h]
      funext j
      fin_cases j <;> simp

/-- The unipotent radical element `U(v) = (1 0; v 1)` of `P_H`. -/
def radical (v : Fin 2 → ℚ) : OrdinaryResidueParabolic.Mat3 := !![1, 0, 0; v 0, 1, 0; v 1, 0, 1]

/-- `U(v)` is the literal block matrix with `λ = 1`, `u = v`, `C = 1`. -/
theorem radical_eq (v : Fin 2 → ℚ) : radical v = blockMatrix 1 v 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [radical, blockMatrix]

theorem blockMatrix_eq (lam : ℚˣ) (u : Fin 2 → ℚ) (C : OrdinaryResidueParabolic.GL2) :
    blockMatrix lam u C = !![(lam : ℚ), 0, 0; u 0, C.val 0 0, C.val 0 1; u 1, C.val 1 0, C.val 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Conjugation of the radical by `g = (λ 0; u C)`: `g U(v) g⁻¹ = U(λ⁻¹ C v)`.  In particular the
radical `ℤ² = {U(v) : v ∈ ℤ²}` is normalized by the integral Levi. -/
theorem radical_conj (g : OrdinaryFullAction.GL3) (lam : ℚˣ) (u : Fin 2 → ℚ)
    (C : OrdinaryResidueParabolic.GL2) (hg : g.val = blockMatrix lam u C) (v : Fin 2 → ℚ) :
    g.val * radical v * (g⁻¹).val = radical ((lam : ℚ)⁻¹ • (C.val *ᵥ v)) := by
  have hl : (lam : ℚ) ≠ 0 := Units.ne_zero lam
  have key : g.val * radical v = radical ((lam : ℚ)⁻¹ • (C.val *ᵥ v)) * g.val := by
    rw [hg, blockMatrix_eq]
    simp only [radical, Matrix.mul_fin_three]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> field_simp <;> ring
  calc g.val * radical v * (g⁻¹).val
      = radical ((lam : ℚ)⁻¹ • (C.val *ᵥ v)) * (g.val * (g⁻¹).val) := by
        rw [key, Matrix.mul_assoc]
    _ = _ := by
        have : g.val * (g⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        rw [this, Matrix.mul_one]

/-- **The factor `λ²`.**  The conjugation by `g` acts on `U ≅ ℚ²` by `λ⁻¹ C`, hence on
`H₂(U, ℚ) = Λ² ℚ²` by `det(λ⁻¹ C) = λ⁻² det C`; right (inverse) action on homology has factor
`λ² / det C`, and times the determinant `det C` of the twisted residue action the combined factor
is `λ²`. -/
theorem H2_factor (lam : ℚˣ) (C : OrdinaryResidueParabolic.GL2) :
    (Matrix.det ((lam : ℚ)⁻¹ • C.val))⁻¹ * C.val.det = (lam : ℚ) ^ 2 := by
  have hl : (lam : ℚ) ≠ 0 := Units.ne_zero lam
  have hC : C.val.det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det C.val).mp C.isUnit
    exact this.ne_zero
  rw [Matrix.det_smul]
  simp only [Fintype.card_fin]
  field_simp

/-- On the integral Levi (`λ = ±1`) the combined factor is one. -/
theorem H2_factor_integral (lam : ℚˣ) (hlam : (lam : ℚ) = 1 ∨ (lam : ℚ) = -1)
    (C : OrdinaryResidueParabolic.GL2) :
    (Matrix.det ((lam : ℚ)⁻¹ • C.val))⁻¹ * C.val.det = 1 := by
  rw [H2_factor]
  rcases hlam with h | h <;> rw [h] <;> norm_num

end TernaryPeriodPolynomials.Argument.AppendixBResidue
