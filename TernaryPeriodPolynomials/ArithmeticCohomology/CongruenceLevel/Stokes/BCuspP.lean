module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BCusp

@[expose] public section


/-!
# The element `Q⁻¹ T^{6k} Q` of `Γ(6)` and the cusp value of additive functions

Formalized by Claude Sonnet 5.5.

`PK q k = Q⁻¹ [[1, 6k], [0, 1]] Q ∈ Γ(6)` for the block `Q` of an element `q` of the Borel of the line.  It is additive in `k` (`PK_add`), so an additive function `φ` on `Γ(6)` is linear on it (`phi_PK`), and
`φ(posPar (qVec q)) = q₀₀ · φ(PK q 1)` (`phi_posPar`).
-/

open scoped MatrixGroups
open CongruenceSubgroup Matrix

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.ConvergenceC4

/-- The matrix `Q⁻¹ [[1, 6k], [0, 1]] Q`. -/
def PKmat (q : SL(3, ℤ)) (k : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := blockQinv q * !![1, 6 * k; 0, 1] * blockQ q

theorem PKmat_det (q : SL(3, ℤ)) (hq : q ∈ lineBorel) (k : ℤ) : (PKmat q k).det = 1 := by
  obtain ⟨-, a2⟩ := blockQ_mul_inv q hq
  have hd : (blockQinv q).det * (blockQ q).det = 1 := by rw [← Matrix.det_mul, a2, Matrix.det_one]
  rw [PKmat, Matrix.det_mul, Matrix.det_mul, Matrix.det_fin_two_of]
  simp only [mul_one, mul_zero, sub_zero]
  linarith

theorem PKmat_mem (q : SL(3, ℤ)) (hq : q ∈ lineBorel) (k : ℤ) :
    (⟨PKmat q k, PKmat_det q hq k⟩ : SL(2, ℤ)) ∈ Gamma 6 := by
  obtain ⟨-, a2⟩ := blockQ_mul_inv q hq
  refine Gamma_mem.2 ?_
  have hT : (!![1, 6 * k; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) = 1 + (6 * k) • !![0, 1; 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  set X : Matrix (Fin 2) (Fin 2) ℤ := blockQinv q * !![0, 1; 0, 0] * blockQ q with hX
  have hP : PKmat q k = 1 + (6 * k) • X := by
    rw [PKmat, hT, hX, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, a2, Matrix.mul_smul, Matrix.smul_mul]
  have h6 : (6 : ZMod 6) = 0 := by decide
  show ((PKmat q k 0 0 : ℤ) : ZMod 6) = 1 ∧ ((PKmat q k 0 1 : ℤ) : ZMod 6) = 0 ∧ ((PKmat q k 1 0 : ℤ) : ZMod 6) = 0 ∧
    ((PKmat q k 1 1 : ℤ) : ZMod 6) = 1
  have hent : ∀ i j, PKmat q k i j = (1 : Matrix (Fin 2) (Fin 2) ℤ) i j + 6 * (k * X i j) := by
    intro i j
    rw [hP, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [hent, hent, hent, hent]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [h6]

/-- The element `Q⁻¹ [[1, 6k], [0, 1]] Q` of `Γ(6)` attached to the block `Q` of an element of the Borel of the line. -/
def PK (q : SL(3, ℤ)) (hq : q ∈ lineBorel) (k : ℤ) : Gamma 6 := ⟨⟨PKmat q k, PKmat_det q hq k⟩, PKmat_mem q hq k⟩

theorem PK_val (q : SL(3, ℤ)) (hq : q ∈ lineBorel) (k : ℤ) :
    (((PK q hq k : Gamma 6) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = PKmat q k := rfl

theorem PK_add (q : SL(3, ℤ)) (hq : q ∈ lineBorel) (k l : ℤ) : PK q hq (k + l) = PK q hq k * PK q hq l := by
  obtain ⟨a1, a2⟩ := blockQ_mul_inv q hq
  apply Subtype.ext
  apply Subtype.ext
  show blockQinv q * !![1, 6 * (k + l); 0, 1] * blockQ q =
    blockQinv q * !![1, 6 * k; 0, 1] * blockQ q * (blockQinv q * !![1, 6 * l; 0, 1] * blockQ q)
  have : blockQinv q * !![1, 6 * k; 0, 1] * blockQ q * (blockQinv q * !![1, 6 * l; 0, 1] * blockQ q) =
      blockQinv q * (!![1, 6 * k; 0, 1] * (blockQ q * blockQinv q) * !![1, 6 * l; 0, 1]) * blockQ q := by
    simp only [Matrix.mul_assoc]
  rw [this, a1, Matrix.mul_one]
  congr 2
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]; ring

/-- Additive functions on `Γ(6)` are linear on the powers of the cusp element. -/
theorem phi_PK (φ : Gamma 6 → ℚ) (hφ : ∀ a b, φ (a * b) = φ a + φ b) (q : SL(3, ℤ)) (hq : q ∈ lineBorel) (k : ℤ) :
    φ (PK q hq k) = k * φ (PK q hq 1) := by
  let ψ : ℤ →+ ℚ := AddMonoidHom.mk' (fun k => φ (PK q hq k)) (fun k l => by rw [PK_add, hφ])
  have := map_zsmul ψ k 1
  simpa [ψ] using this

theorem posPar_eq_PK (q : SL(3, ℤ)) (hq : q ∈ lineBorel) (h1 : (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 = 1) :
    posParSL (qVec q) = PK q hq 1 := by
  obtain ⟨-, hdet⟩ := lineBorel_sign q hq
  have hd : (q : Matrix (Fin 3) (Fin 3) ℤ) 1 1 * (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2 -
      (q : Matrix (Fin 3) (Fin 3) ℤ) 1 2 * (q : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = 1 := by
    have : (blockQ q).det = (q : Matrix (Fin 3) (Fin 3) ℤ) 1 1 * (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2 -
        (q : Matrix (Fin 3) (Fin 3) ℤ) 1 2 * (q : Matrix (Fin 3) (Fin 3) ℤ) 2 1 := by
      simp [blockQ, Matrix.det_fin_two]
    rw [← this, hdet, h1]
  apply Subtype.ext
  apply Subtype.ext
  show (posPar (qVec q) : Matrix (Fin 2) (Fin 2) ℤ) = PKmat q 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [posPar, qVec_apply, PKmat, blockQinv, blockQ, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, h1] <;>
    first | ring1 | linear_combination (-1 : ℤ) * hd

theorem posPar_mul_PK (q : SL(3, ℤ)) (hq : q ∈ lineBorel) (h1 : (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 = -1) :
    posParSL (qVec q) * PK q hq 1 = 1 := by
  obtain ⟨-, hdet⟩ := lineBorel_sign q hq
  have hd : (q : Matrix (Fin 3) (Fin 3) ℤ) 1 1 * (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2 -
      (q : Matrix (Fin 3) (Fin 3) ℤ) 1 2 * (q : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = -1 := by
    have : (blockQ q).det = (q : Matrix (Fin 3) (Fin 3) ℤ) 1 1 * (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2 -
        (q : Matrix (Fin 3) (Fin 3) ℤ) 1 2 * (q : Matrix (Fin 3) (Fin 3) ℤ) 2 1 := by
      simp [blockQ, Matrix.det_fin_two]
    rw [← this, hdet, h1]
  apply Subtype.ext
  apply Subtype.ext
  show (posPar (qVec q) : Matrix (Fin 2) (Fin 2) ℤ) * PKmat q 1 = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [posPar, qVec_apply, PKmat, blockQinv, blockQ, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, h1]
  · linear_combination (-1 - 6 * (q : Matrix (Fin 3) (Fin 3) ℤ) 2 1 * (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2) * hd
  · linear_combination (-6 * (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2 ^ 2) * hd
  · linear_combination (6 * (q : Matrix (Fin 3) (Fin 3) ℤ) 2 1 ^ 2) * hd
  · linear_combination (-1 + 6 * (q : Matrix (Fin 3) (Fin 3) ℤ) 2 1 * (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2) * hd

/-- **The cusp value of an additive function: `φ(posPar (qVec q)) = q₀₀ · φ(Q⁻¹ T⁶ Q)`.** -/
theorem phi_posPar (φ : Gamma 6 → ℚ) (hφ : ∀ a b, φ (a * b) = φ a + φ b) (q : SL(3, ℤ)) (hq : q ∈ lineBorel) :
    φ (posParSL (qVec q)) = ((q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 : ℚ) * φ (PK q hq 1) := by
  obtain ⟨hε, -⟩ := lineBorel_sign q hq
  have h0 : φ 1 = 0 := by
    have := hφ 1 1
    rw [mul_one] at this
    linarith
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hε with h | h
  · rw [posPar_eq_PK q hq h, h]
    simp
  · have := posPar_mul_PK q hq h
    have h2 := hφ (posParSL (qVec q)) (PK q hq 1)
    rw [this, h0] at h2
    rw [h]
    push_cast
    linarith

end TernaryPeriodPolynomials.Argument.GammaNStokes
