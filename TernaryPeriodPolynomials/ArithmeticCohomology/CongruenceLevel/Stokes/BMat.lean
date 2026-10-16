module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BHeis
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.LineConj

@[expose] public section


/-!
# Line data from matrices, and the change of frame

Formalized by Claude Sonnet 5.5.

A homomorphism `M : G →* SL₃(ℤ)` whose values have first column `(1, 0, 0)ᵗ` gives a line datum `matLineData M` (`A` the lower right block, `v` the rest of the first row).
For two such homomorphisms related by `q M_h = M_g q` with `q` in the Borel `lineBorel` of the line (first column `(ε, 0, 0)ᵗ`), the data are related by
`A_h = Q⁻¹ A_g Q`, `v_h = ε (v_g + w' (1 - A_g)) Q`, where `Q` is the lower right block of `q`, `det Q = ε` and `w'` a row vector (`frame_relation`).
-/

open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open Matrix TernaryPeriodPolynomials.Argument.FlagH3 TernaryPeriodPolynomials.Argument.GammaNFacesFull

variable {G : Type} [Group G]

/-- The hypothesis that `M s` has first column `(1, 0, 0)ᵗ`. -/
def LineType (M : G →* SL(3, ℤ)) : Prop :=
  ∀ s, (M s : Matrix (Fin 3) (Fin 3) ℤ) 1 0 = 0 ∧ (M s : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0 ∧
    (M s : Matrix (Fin 3) (Fin 3) ℤ) 0 0 = 1

/-- The line datum of a homomorphism of line type. -/
def matLineData (M : G →* SL(3, ℤ)) (hM : LineType M) : LineData G where
  A s := !![(M s : Matrix (Fin 3) (Fin 3) ℤ) 1 1, (M s : Matrix (Fin 3) (Fin 3) ℤ) 1 2;
    (M s : Matrix (Fin 3) (Fin 3) ℤ) 2 1, (M s : Matrix (Fin 3) (Fin 3) ℤ) 2 2]
  v s := ![(M s : Matrix (Fin 3) (Fin 3) ℤ) 0 1, (M s : Matrix (Fin 3) (Fin 3) ℤ) 0 2]
  A_mul g h := by
    obtain ⟨g10, g20, g00⟩ := hM g
    ext i j
    fin_cases i <;> fin_cases j <;> simp [map_mul, Matrix.mul_apply, Fin.sum_univ_three, g10, g20]
  det_one s := by
    obtain ⟨s10, s20, s00⟩ := hM s
    have h := (M s).2
    rw [Matrix.det_fin_three] at h
    simp only [s10, s20, s00] at h
    simp [Matrix.det_fin_two]
    linarith
  v_mul g h := by
    obtain ⟨g10, g20, g00⟩ := hM g
    ext i
    fin_cases i <;> simp [map_mul, Matrix.mul_apply, Fin.sum_univ_three, g00] <;> ring

/-- The block `Q` of an element of `lineBorel`, and the sign `ε = q₀₀`. -/
def blockQ (q : SL(3, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(q : Matrix (Fin 3) (Fin 3) ℤ) 1 1, (q : Matrix (Fin 3) (Fin 3) ℤ) 1 2;
    (q : Matrix (Fin 3) (Fin 3) ℤ) 2 1, (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2]

theorem lineBorel_sign (q : SL(3, ℤ)) (hq : q ∈ lineBorel) :
    (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 * (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 = 1 ∧
      (blockQ q).det = (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 := by
  obtain ⟨h1, h2⟩ := hq
  have h := q.2
  rw [Matrix.det_fin_three] at h
  simp only [h1, h2] at h
  have hd : (blockQ q).det = (q : Matrix (Fin 3) (Fin 3) ℤ) 1 1 * (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2 -
      (q : Matrix (Fin 3) (Fin 3) ℤ) 1 2 * (q : Matrix (Fin 3) (Fin 3) ℤ) 2 1 := by
    simp [blockQ, Matrix.det_fin_two]
  have hprod : (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 * (blockQ q).det = 1 := by
    rw [hd]; linarith
  have hu : (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 * (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hprod with h | h <;> rw [h] <;> norm_num
  refine ⟨hu, ?_⟩
  have : (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 * ((q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 * (blockQ q).det) =
      (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 := by rw [hprod, mul_one]
  rw [← mul_assoc, hu, one_mul] at this
  exact this

/-- The integer inverse `ε adj(Q)` of the block `Q` (`ε = q₀₀ = ± 1`). -/
def blockQinv (q : SL(3, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ := (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 • (blockQ q).adjugate

/-- The translation vector of the change of frame. -/
def frameW (q : SL(3, ℤ)) : Fin 2 → ℤ :=
  ![(q : Matrix (Fin 3) (Fin 3) ℤ) 0 1, (q : Matrix (Fin 3) (Fin 3) ℤ) 0 2] ᵥ* blockQinv q

/-- **Change of frame**: if `q M_h = M_g q` with `q` in the Borel of the line, the line data of `M_h` and `M_g` are related by the block `Q` of `q`, its sign `ε`, and a translation. -/
theorem frame_relation (Mg Mh : G →* SL(3, ℤ)) (hg : LineType Mg) (hh : LineType Mh) (q : SL(3, ℤ)) (hq : q ∈ lineBorel)
    (hrel : ∀ s, (q : Matrix (Fin 3) (Fin 3) ℤ) * (Mh s : Matrix (Fin 3) (Fin 3) ℤ) =
      (Mg s : Matrix (Fin 3) (Fin 3) ℤ) * (q : Matrix (Fin 3) (Fin 3) ℤ)) :
    blockQ q * blockQinv q = 1 ∧ (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 * (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 = 1 ∧
      (blockQ q).det = (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 ∧
      (∀ s, (matLineData Mh hh).A s = blockQinv q * (matLineData Mg hg).A s * blockQ q) ∧
      ∀ s, (matLineData Mh hh).v s = (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 •
        (((matLineData Mg hg).v s + frameW q ᵥ* (1 - (matLineData Mg hg).A s)) ᵥ* blockQ q) := by
  obtain ⟨hε, hdet⟩ := lineBorel_sign q hq
  obtain ⟨q10, q20⟩ := hq
  set ε : ℤ := (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 with hεdef
  set Q : Matrix (Fin 2) (Fin 2) ℤ := blockQ q with hQ
  set Q' : Matrix (Fin 2) (Fin 2) ℤ := ε • Q.adjugate with hQ'
  have hQ'def : blockQinv q = Q' := rfl
  have hQQ' : Q * Q' = 1 := by
    rw [hQ', Matrix.mul_smul, Matrix.mul_adjugate, hdet, smul_smul, hε, one_smul]
  have hQ'Q : Q' * Q = 1 := by
    rw [hQ', Matrix.smul_mul, Matrix.adjugate_mul, hdet, smul_smul, hε, one_smul]
  set w0 : Fin 2 → ℤ := ![(q : Matrix (Fin 3) (Fin 3) ℤ) 0 1, (q : Matrix (Fin 3) (Fin 3) ℤ) 0 2] with hw0
  have hblock : ∀ s, Q * (matLineData Mh hh).A s = (matLineData Mg hg).A s * Q := by
    intro s
    obtain ⟨g10, g20, g00⟩ := hg s
    have e := hrel s
    ext i j
    have e' := fun a b => congrArg (fun m : Matrix (Fin 3) (Fin 3) ℤ => m a b) e
    fin_cases i <;> fin_cases j
    · have := e' 1 1
      simp [Matrix.mul_apply, Fin.sum_univ_three, q10, g10] at this
      simp [hQ, blockQ, matLineData, Matrix.mul_apply, Fin.sum_univ_two]
      linarith
    · have := e' 1 2
      simp [Matrix.mul_apply, Fin.sum_univ_three, q10, g10] at this
      simp [hQ, blockQ, matLineData, Matrix.mul_apply, Fin.sum_univ_two]
      linarith
    · have := e' 2 1
      simp [Matrix.mul_apply, Fin.sum_univ_three, q20, g20] at this
      simp [hQ, blockQ, matLineData, Matrix.mul_apply, Fin.sum_univ_two]
      linarith
    · have := e' 2 2
      simp [Matrix.mul_apply, Fin.sum_univ_three, q20, g20] at this
      simp [hQ, blockQ, matLineData, Matrix.mul_apply, Fin.sum_univ_two]
      linarith
  have hA : ∀ s, (matLineData Mh hh).A s = Q' * (matLineData Mg hg).A s * Q := by
    intro s
    calc (matLineData Mh hh).A s = (Q' * Q) * (matLineData Mh hh).A s := by rw [hQ'Q, Matrix.one_mul]
      _ = Q' * (Q * (matLineData Mh hh).A s) := by rw [Matrix.mul_assoc]
      _ = Q' * (matLineData Mg hg).A s * Q := by rw [hblock s, Matrix.mul_assoc]
  have hrow : ∀ s, w0 + (matLineData Mg hg).v s ᵥ* Q = ε • (matLineData Mh hh).v s + w0 ᵥ* (matLineData Mh hh).A s := by
    intro s
    obtain ⟨g10, g20, g00⟩ := hg s
    have e := hrel s
    have e' := fun a b => congrArg (fun m : Matrix (Fin 3) (Fin 3) ℤ => m a b) e
    ext j
    fin_cases j
    · have := e' 0 1
      simp [Matrix.mul_apply, Fin.sum_univ_three, g00] at this
      simp [hw0, hQ, blockQ, matLineData, hεdef]
      linarith
    · have := e' 0 2
      simp [Matrix.mul_apply, Fin.sum_univ_three, g00] at this
      simp [hw0, hQ, blockQ, matLineData, hεdef]
      linarith
  have hwdef : frameW q = w0 ᵥ* Q' := rfl
  refine ⟨hQQ', hε, hdet, hA, ?_⟩
  intro s
  rw [hwdef]
  have h1 : ((matLineData Mg hg).v s + (w0 ᵥ* Q') ᵥ* (1 - (matLineData Mg hg).A s)) ᵥ* Q =
      ε • (matLineData Mh hh).v s := by
    have h2 : Q' * ((1 - (matLineData Mg hg).A s) * Q) = 1 - (matLineData Mh hh).A s := by
      rw [hA s, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, hQ'Q, Matrix.mul_assoc Q' ((matLineData Mg hg).A s) Q]
    rw [Matrix.add_vecMul, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, h2, Matrix.vecMul_sub, Matrix.vecMul_one]
    ext j
    have := congrFun (hrow s) j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    linarith
  rw [h1, smul_smul, hε, one_smul]

end TernaryPeriodPolynomials.Argument.GammaNStokes
