module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BMat
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BSL2
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Faces.LineGroup

@[expose] public section


/-!
# The cusp vector of an element of the Borel of a line

Formalized by Claude Sonnet 5.5.

For `q ∈ lineBorel` (first column `(ε, 0, 0)ᵗ`) with lower right block `Q` (`det Q = ε`), `qVec q = Q⁻¹ e₁` is a primitive vector (`qPrim`).  Its class in `Cusp6` is invariant under
`q ↦ b q m` for `b` upper triangular and `m ∈ Γ(6) ∩ lineBorel` (`qVec_change`); every primitive vector is some `qVec q` (`exists_q_of_prim`); and if `qVec q₁ ~ qVec q₂` there is
`n ∈ Γ(6) ∩ lineBorel` with `q₂ n q₁⁻¹` upper triangular (`exists_n_of_cuspRel`).
-/

open scoped MatrixGroups
open CongruenceSubgroup Matrix

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.ConvergenceC4

theorem blockQ_mul_inv (q : SL(3, ℤ)) (hq : q ∈ lineBorel) :
    blockQ q * blockQinv q = 1 ∧ blockQinv q * blockQ q = 1 := by
  obtain ⟨hε, hdet⟩ := lineBorel_sign q hq
  refine ⟨?_, ?_⟩
  · rw [blockQinv, Matrix.mul_smul, Matrix.mul_adjugate, hdet, smul_smul, hε, one_smul]
  · rw [blockQinv, Matrix.smul_mul, Matrix.adjugate_mul, hdet, smul_smul, hε, one_smul]

theorem blockQ_mul (q q' : SL(3, ℤ)) (hq : q ∈ lineBorel) :
    blockQ (q * q') = blockQ q * blockQ q' := by
  obtain ⟨h1, h2⟩ := hq
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockQ, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, h1, h2]

/-- The vector `Q⁻¹ e₁` attached to an element of the Borel of the line. -/
def qVec (q : SL(3, ℤ)) : Fin 2 → ℤ := blockQinv q *ᵥ ![1, 0]

theorem qVec_apply (q : SL(3, ℤ)) : qVec q = ![(q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 * (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2,
    -((q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 * (q : Matrix (Fin 3) (Fin 3) ℤ) 2 1)] := by
  ext i
  fin_cases i <;> simp [qVec, blockQinv, blockQ, Matrix.adjugate_fin_two, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem qVec_coprime (q : SL(3, ℤ)) (hq : q ∈ lineBorel) : IsCoprime ((qVec q) 0) ((qVec q) 1) := by
  obtain ⟨hε, hdet⟩ := lineBorel_sign q hq
  rw [qVec_apply]
  refine ⟨(q : Matrix (Fin 3) (Fin 3) ℤ) 1 1, (q : Matrix (Fin 3) (Fin 3) ℤ) 1 2, ?_⟩
  have hd : (blockQ q).det = (q : Matrix (Fin 3) (Fin 3) ℤ) 1 1 * (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2 -
      (q : Matrix (Fin 3) (Fin 3) ℤ) 1 2 * (q : Matrix (Fin 3) (Fin 3) ℤ) 2 1 := by
    simp [blockQ, Matrix.det_fin_two]
  rw [hd] at hdet
  simp
  linear_combination ((q : Matrix (Fin 3) (Fin 3) ℤ) 0 0) * hdet + hε

/-- The primitive vector of an element of the Borel of the line. -/
def qPrim (q : SL(3, ℤ)) (hq : q ∈ lineBorel) : Prim2 := ⟨qVec q, qVec_coprime q hq⟩

theorem borel_le_lineBorel {b : SL(3, ℤ)} (hb : b ∈ borelStab) : b ∈ lineBorel := ⟨hb.1, hb.2.1⟩

/-- An element of `Γ(6) ∩ lineBorel` has first diagonal entry `1`. -/
theorem lineBorel_gammaN_00 {m : SL(3, ℤ)} (hm : m ∈ lineBorel) (hN : m ∈ gammaN 6) :
    (m : Matrix (Fin 3) (Fin 3) ℤ) 0 0 = 1 := by
  obtain ⟨hε, -⟩ := lineBorel_sign m hm
  have h := mem_gammaN.1 hN 0 0
  simp only [Matrix.one_apply_eq] at h
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hε with h1 | h1
  · exact h1
  · rw [h1] at h; omega

/-- The block of an element of `Γ(6) ∩ lineBorel` as an element of `Γ(6) ⊂ SL₂(ℤ)`. -/
def blockSL (m : SL(3, ℤ)) (hm : m ∈ lineBorel) (hN : m ∈ gammaN 6) : SL(2, ℤ) :=
  ⟨blockQ m, by rw [(lineBorel_sign m hm).2, lineBorel_gammaN_00 hm hN]⟩

theorem blockSL_mem (m : SL(3, ℤ)) (hm : m ∈ lineBorel) (hN : m ∈ gammaN 6) : blockSL m hm hN ∈ Gamma 6 := by
  rw [Gamma_mem]
  have h := fun i j => mem_gammaN.1 hN i j
  have d : ∀ x y : ℤ, (6 : ℤ) ∣ x - y → (x : ZMod 6) = (y : ZMod 6) := fun x y hxy => by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (x - y) 6).2 hxy
    rw [Int.cast_sub, sub_eq_zero] at this
    exact this
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [blockSL, blockQ] using d _ 1 (by simpa using h 1 1)
  · simpa [blockSL, blockQ] using d _ 0 (by simpa using h 1 2)
  · simpa [blockSL, blockQ] using d _ 0 (by simpa using h 2 1)
  · simpa [blockSL, blockQ] using d _ 1 (by simpa using h 2 2)

/-- **The cusp vector changes by `±` an element of `Γ(6)` under `q ↦ b q m`.** -/
theorem qVec_change (b q m : SL(3, ℤ)) (hb : b ∈ borelStab) (hq : q ∈ lineBorel) (hm : m ∈ lineBorel) (hmN : m ∈ gammaN 6) :
    CuspRel (qPrim (b * q * m) (lineBorel.mul_mem (lineBorel.mul_mem (borel_le_lineBorel hb) hq) hm)) (qPrim q hq) := by
  have hbL := borel_le_lineBorel hb
  have hbq : b * q ∈ lineBorel := lineBorel.mul_mem hbL hq
  have hq1 : b * q * m ∈ lineBorel := lineBorel.mul_mem hbq hm
  obtain ⟨b1, b2⟩ := blockQ_mul_inv b hbL
  obtain ⟨q1, q2⟩ := blockQ_mul_inv q hq
  obtain ⟨m1, m2⟩ := blockQ_mul_inv m hm
  obtain ⟨c1, c2⟩ := blockQ_mul_inv (b * q * m) hq1
  have hblock : blockQ (b * q * m) = blockQ b * blockQ q * blockQ m := by
    rw [blockQ_mul _ _ hbq, blockQ_mul _ _ hbL]
  have hinv : blockQinv (b * q * m) = blockQinv m * blockQinv q * blockQinv b := by
    refine left_inv_eq_right_inv c2 ?_
    rw [hblock]
    calc blockQ b * blockQ q * blockQ m * (blockQinv m * blockQinv q * blockQinv b)
        = blockQ b * blockQ q * (blockQ m * blockQinv m) * blockQinv q * blockQinv b := by simp only [Matrix.mul_assoc]
      _ = blockQ b * (blockQ q * blockQinv q) * blockQinv b := by rw [m1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [q1, Matrix.mul_one, b1]
  -- the sign
  obtain ⟨-, hdb⟩ := lineBorel_sign b hbL
  have hb2 : (b : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = 0 := hb.2.2
  have hbsign : (b : Matrix (Fin 3) (Fin 3) ℤ) 0 0 * (b : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = 1 ∨
      (b : Matrix (Fin 3) (Fin 3) ℤ) 0 0 * (b : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = -1 := by
    have hdet := b.2
    rw [Matrix.det_fin_three] at hdet
    simp only [hb.1, hb.2.1, hb2] at hdet
    have h00 : (b : Matrix (Fin 3) (Fin 3) ℤ) 0 0 * ((b : Matrix (Fin 3) (Fin 3) ℤ) 1 1 * (b : Matrix (Fin 3) (Fin 3) ℤ) 2 2) = 1 := by
      linarith
    have u0 := Int.eq_one_or_neg_one_of_mul_eq_one h00
    have h22 : (b : Matrix (Fin 3) (Fin 3) ℤ) 2 2 * ((b : Matrix (Fin 3) (Fin 3) ℤ) 0 0 * (b : Matrix (Fin 3) (Fin 3) ℤ) 1 1) = 1 := by
      linarith
    have u2 := Int.eq_one_or_neg_one_of_mul_eq_one h22
    rcases u0 with h | h <;> rcases u2 with h' | h' <;> rw [h, h'] <;> simp
  have hBi : blockQinv b *ᵥ ![1, 0] = ((b : Matrix (Fin 3) (Fin 3) ℤ) 0 0 * (b : Matrix (Fin 3) (Fin 3) ℤ) 2 2) • ![1, 0] := by
    have := qVec_apply b
    unfold qVec at this
    rw [this, hb2]
    ext i; fin_cases i <;> simp
  have hw : qVec (b * q * m) = ((b : Matrix (Fin 3) (Fin 3) ℤ) 0 0 * (b : Matrix (Fin 3) (Fin 3) ℤ) 2 2) •
      (blockQinv m *ᵥ qVec q) := by
    unfold qVec
    rw [hinv, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hBi, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_mulVec]
  refine ⟨blockSL m hm hmN, blockSL_mem m hm hmN, (b : Matrix (Fin 3) (Fin 3) ℤ) 0 0 * (b : Matrix (Fin 3) (Fin 3) ℤ) 2 2, hbsign, ?_⟩
  show blockQ m *ᵥ qVec (b * q * m) = _ • qVec q
  rw [hw, Matrix.mulVec_smul, Matrix.mulVec_mulVec, m1, Matrix.one_mulVec]

theorem lineStab_le_lineBorel {n : SL(3, ℤ)} (hn : n ∈ lineStab) : n ∈ lineBorel := ⟨hn.2.1, hn.2.2⟩

/-- **Every primitive vector is the cusp vector of an element of the Borel of the line.** -/
theorem exists_q_of_prim (v : Prim2) :
    ∃ q : SL(3, ℤ), q ∈ lineBorel ∧ qVec q = v.1 := by
  obtain ⟨x, y, hxy⟩ := v.2
  let q : SL(3, ℤ) := ⟨!![1, 0, 0; 0, x, y; 0, -(v.1 1), v.1 0], by
    rw [Matrix.det_fin_three]
    simp
    linear_combination hxy⟩
  have hq : q ∈ lineBorel := ⟨by simp [q], by simp [q]⟩
  refine ⟨q, hq, ?_⟩
  rw [qVec_apply]
  ext i
  fin_cases i <;> simp [q]

/-- **Equal cusps give an element `n ∈ Γ(6) ∩ lineBorel` with `q₂ n q₁⁻¹` upper triangular.** -/
theorem exists_n_of_cuspRel (q₁ q₂ : SL(3, ℤ)) (h₁ : q₁ ∈ lineBorel) (h₂ : q₂ ∈ lineBorel)
    (h : CuspRel (qPrim q₁ h₁) (qPrim q₂ h₂)) :
    ∃ n : SL(3, ℤ), n ∈ lineBorel ∧ n ∈ gammaN 6 ∧ q₂ * n * q₁⁻¹ ∈ borelStab := by
  obtain ⟨γ, hγ, s, hs, e⟩ := h
  refine ⟨blockDiagQ γ, lineStab_le_lineBorel (blockDiagQ_mem_lineStab γ), blockDiagQ_mem_gammaN hγ, ?_⟩
  have hn : blockDiagQ γ ∈ lineBorel := lineStab_le_lineBorel (blockDiagQ_mem_lineStab γ)
  have hi : q₁⁻¹ ∈ lineBorel := lineBorel.inv_mem h₁
  have hb : q₂ * blockDiagQ γ * q₁⁻¹ ∈ lineBorel := lineBorel.mul_mem (lineBorel.mul_mem h₂ hn) hi
  obtain ⟨a1, a2⟩ := blockQ_mul_inv q₁ h₁
  obtain ⟨c1, c2⟩ := blockQ_mul_inv q₂ h₂
  have hinv : blockQinv q₁ = blockQ q₁⁻¹ := by
    refine left_inv_eq_right_inv a2 ?_
    have := blockQ_mul q₁ q₁⁻¹ h₁
    rw [mul_inv_cancel] at this
    have h1 : blockQ (1 : SL(3, ℤ)) = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [blockQ]
    rw [h1] at this
    exact this.symm
  have hblock : blockQ (q₂ * blockDiagQ γ * q₁⁻¹) = blockQ q₂ * (γ : Matrix (Fin 2) (Fin 2) ℤ) * blockQinv q₁ := by
    rw [blockQ_mul _ _ (lineBorel.mul_mem h₂ hn), blockQ_mul _ _ h₂, hinv]
    congr 2
    ext i j; fin_cases i <;> fin_cases j <;> simp [blockQ, blockDiagQ]
  refine ⟨hb.1, hb.2, ?_⟩
  have hv1 : blockQinv q₁ *ᵥ ![1, 0] = (qPrim q₁ h₁).1 := rfl
  have hv2 : blockQinv q₂ *ᵥ ![1, 0] = (qPrim q₂ h₂).1 := rfl
  have hcol : blockQ (q₂ * blockDiagQ γ * q₁⁻¹) *ᵥ ![1, 0] = s • ![1, 0] := by
    rw [hblock, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv1, e, Matrix.mulVec_smul, ← hv2,
      Matrix.mulVec_mulVec, c1, Matrix.one_mulVec]
  have h10 := congrFun hcol 1
  simp [blockQ, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h10
  simpa [blockQ] using h10

end TernaryPeriodPolynomials.Argument.GammaNStokes
