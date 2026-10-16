module

public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.Defs
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Real
public import Batteries.Data.List.Count
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence

@[expose] public section


/-!
# Plane coordinates of the symmetric space (Appendix C.3, `ar:sec:series`)

Paper: §C.3. A point of
`𝒳 = SL₃(ℝ)/SO(3)` is `p SO(3)` with `p = [[A, t u],[0, t]]`, `det A = t⁻¹`, `τ = A i`. We model
`𝒳` by the Gram matrices `G = p pᵀ` of determinant one and identify it, through the plane
coordinates `(u₁, u₂, x, y, t)` (with `τ = x + i y`), with the open set
`Ω = {p : Fin 5 → ℝ | 0 < p 3, 0 < p 4}`.

This file proves that `planeGram : Ω → {det-one positive definite}` is a bijection with inverse
`planePoint` and gives the algebraic round-trip identities. Smoothness and the group action are in
`Action.lean`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

open Matrix MvPolynomial

/-- The plane-coordinate domain `Ω`: `0 < y` and `0 < t`. -/
def Omega : Set (Fin 5 → ℝ) := {p | 0 < p 3 ∧ 0 < p 4}

/-- The base point `o = (0, 0, 0, 1, 1)`, i.e. `u = 0`, `τ = i`, `t = 1` (Gram matrix `1`). -/
def basePt : Fin 5 → ℝ := ![0, 0, 0, 1, 1]

theorem basePt_mem : basePt ∈ Omega := by simp [Omega, basePt]

/-- The Gram matrix `p pᵀ` of the plane coordinates `p = (u₁, u₂, x, y, t)`: with `C = A Aᵀ`
equal to `(t y)⁻¹ [[x²+y², x],[x, 1]]`, it is `[[C + t² u uᵀ, t² u],[t² uᵀ, t²]]`. -/
def planeGram (p : Fin 5 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![((p 2) ^ 2 + (p 3) ^ 2) / (p 4 * p 3) + (p 4) ^ 2 * (p 0) ^ 2,
     p 2 / (p 4 * p 3) + (p 4) ^ 2 * (p 0) * (p 1), (p 4) ^ 2 * p 0;
     p 2 / (p 4 * p 3) + (p 4) ^ 2 * (p 0) * (p 1),
     1 / (p 4 * p 3) + (p 4) ^ 2 * (p 1) ^ 2, (p 4) ^ 2 * p 1;
     (p 4) ^ 2 * p 0, (p 4) ^ 2 * p 1, (p 4) ^ 2]

/-- The upper triangular square root `P(p) = [[A, t u],[0, t]]` of `planeGram p`, with
`A = t^{-1/2} [[√y, x/√y],[0, 1/√y]]` (so `A i = x + i y`, `det A = t⁻¹`). -/
def planeP (p : Fin 5 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.sqrt (p 3) / Real.sqrt (p 4), p 2 / (Real.sqrt (p 3) * Real.sqrt (p 4)), p 4 * p 0;
     0, 1 / (Real.sqrt (p 3) * Real.sqrt (p 4)), p 4 * p 1;
     0, 0, p 4]

/-- The plane coordinates of a Gram matrix `G`: `u = G_{·3}/G₃₃`, `τ = C₁₂/C₂₂ + i/(√G₃₃ C₂₂)` with
the Schur complement `C = G_{··} - G_{·3}G_{3·}/G₃₃`, and `t = √G₃₃`. -/
def planePoint (G : Matrix (Fin 3) (Fin 3) ℝ) : Fin 5 → ℝ :=
  ![G 0 2 / G 2 2, G 1 2 / G 2 2,
    (G 0 1 - G 0 2 * G 1 2 / G 2 2) / (G 1 1 - G 1 2 * G 1 2 / G 2 2),
    1 / (Real.sqrt (G 2 2) * (G 1 1 - G 1 2 * G 1 2 / G 2 2)), Real.sqrt (G 2 2)]

/-- Square-root parametrization of `Ω`: `y = a²`, `t = b²` with `a, b > 0`. -/
theorem exists_sqrt_param {p : Fin 5 → ℝ} (hp : p ∈ Omega) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ p 3 = a ^ 2 ∧ p 4 = b ^ 2 :=
  ⟨Real.sqrt (p 3), Real.sqrt (p 4), Real.sqrt_pos.2 hp.1, Real.sqrt_pos.2 hp.2,
    (Real.sq_sqrt hp.1.le).symm, (Real.sq_sqrt hp.2.le).symm⟩

theorem planeP_mul_transpose {p : Fin 5 → ℝ} (hp : p ∈ Omega) :
    planeP p * (planeP p).transpose = planeGram p := by
  obtain ⟨a, b, ha, hb, e3, e4⟩ := exists_sqrt_param hp
  have ha0 : a ≠ 0 := ha.ne'
  have hb0 : b ≠ 0 := hb.ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeP, planeGram, Matrix.mul_apply, Fin.sum_univ_three, e3, e4,
      Real.sqrt_sq ha.le, Real.sqrt_sq hb.le]
  all_goals field_simp
  all_goals ring

theorem det_planeP {p : Fin 5 → ℝ} (hp : p ∈ Omega) : (planeP p).det = 1 := by
  obtain ⟨a, b, ha, hb, e3, e4⟩ := exists_sqrt_param hp
  have ha0 : a ≠ 0 := ha.ne'
  have hb0 : b ≠ 0 := hb.ne'
  simp [planeP, Matrix.det_fin_three, e3, e4, Real.sqrt_sq ha.le, Real.sqrt_sq hb.le]
  field_simp

theorem det_planeGram {p : Fin 5 → ℝ} (hp : p ∈ Omega) : (planeGram p).det = 1 := by
  rw [← planeP_mul_transpose hp, Matrix.det_mul, Matrix.det_transpose, det_planeP hp]; norm_num

/-- Determinant-one positive definite real symmetric `3 × 3` matrices (the points of `𝒳`). -/
def IsGram (G : Matrix (Fin 3) (Fin 3) ℝ) : Prop := G.PosDef ∧ G.det = 1

theorem planeGram_isGram {p : Fin 5 → ℝ} (hp : p ∈ Omega) : IsGram (planeGram p) := by
  refine ⟨?_, det_planeGram hp⟩
  rw [← planeP_mul_transpose hp]
  have hdet : IsUnit (planeP p).det := by rw [det_planeP hp]; exact isUnit_one
  have := Matrix.PosDef.mul_conjTranspose_self (planeP p)
    (Matrix.vecMul_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hdet))
  simpa using this

theorem IsGram.symm {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : IsGram G) (i j : Fin 3) :
    G i j = G j i := by
  have := hG.1.isHermitian
  have h := congrFun (congrFun this j) i
  simpa [Matrix.conjTranspose_apply] using h

theorem IsGram.quad_pos {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : IsGram G) (v : Fin 3 → ℝ)
    (hv : v ≠ 0) : 0 < v ⬝ᵥ G *ᵥ v := by
  have := (Matrix.posDef_iff_dotProduct_mulVec.1 hG.1).2 hv
  simpa using this

theorem IsGram.s_pos {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : IsGram G) : 0 < G 2 2 := by
  have := hG.quad_pos ![0, 0, 1] (by intro h; simpa using congrFun h 2)
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this

theorem IsGram.minor_pos {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : IsGram G) :
    0 < G 1 1 * G 2 2 - G 1 2 * G 1 2 := by
  have h := hG.quad_pos ![0, G 2 2, -G 1 2] (by
    intro h
    have h1 := congrFun h 1
    have := hG.s_pos
    simp at h1; linarith)
  have e : ![0, G 2 2, -G 1 2] ⬝ᵥ G *ᵥ ![0, G 2 2, -G 1 2] =
      G 2 2 * (G 1 1 * G 2 2 - G 1 2 * G 1 2) := by
    have h21 := hG.symm 2 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    rw [h21]
    ring
  rw [e] at h
  exact (pos_iff_pos_of_mul_pos h).1 hG.s_pos

/-- The Schur complement entry `C₂₂ = G₁₁ - G₁₂²/G₃₃` of a Gram matrix is positive. -/
theorem IsGram.schur_pos {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : IsGram G) :
    0 < G 1 1 - G 1 2 * G 1 2 / G 2 2 := by
  have hs := hG.s_pos
  have h := hG.minor_pos
  have : G 1 1 - G 1 2 * G 1 2 / G 2 2 = (G 1 1 * G 2 2 - G 1 2 * G 1 2) / G 2 2 := by
    field_simp
  rw [this]
  exact div_pos h hs

/-- Round trip `p ↦ planeGram p ↦ planePoint`. -/
theorem planePoint_planeGram {p : Fin 5 → ℝ} (hp : p ∈ Omega) :
    planePoint (planeGram p) = p := by
  obtain ⟨hy, ht⟩ := hp
  have hy' : p 3 ≠ 0 := hy.ne'
  have ht' : p 4 ≠ 0 := ht.ne'
  have hsq : Real.sqrt (p 4 ^ 2) = p 4 := Real.sqrt_sq ht.le
  funext i
  fin_cases i <;> simp [planePoint, planeGram, hsq]
  · field_simp
  · field_simp
  · field_simp
    ring
  · field_simp
    ring

/-- Round trip `G ↦ planePoint G ↦ planeGram`. -/
theorem planeGram_planePoint {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : IsGram G) :
    planeGram (planePoint G) = G := by
  have hs := hG.s_pos
  have hmin := hG.minor_pos
  have hdet := hG.2
  have h01 := hG.symm 0 1
  have h02 := hG.symm 0 2
  have h12 := hG.symm 1 2
  rw [Matrix.det_fin_three, ← h12, ← h02, ← h01] at hdet
  obtain ⟨t, ht, hts⟩ : ∃ t : ℝ, 0 < t ∧ G 2 2 = t ^ 2 :=
    ⟨Real.sqrt (G 2 2), Real.sqrt_pos.2 hs, (Real.sq_sqrt hs.le).symm⟩
  have hsq : Real.sqrt (G 2 2) = t := by rw [hts]; exact Real.sqrt_sq ht.le
  have ht0 : t ≠ 0 := ht.ne'
  have hm : 0 < t ^ 2 * G 1 1 - G 1 2 ^ 2 := by rw [← hts]; nlinarith
  have hm0 : t ^ 2 * G 1 1 - G 1 2 ^ 2 ≠ 0 := hm.ne'
  have hc : G 1 1 - G 1 2 * G 1 2 / t ^ 2 = (t ^ 2 * G 1 1 - G 1 2 ^ 2) / t ^ 2 := by
    field_simp
  have key : (t ^ 2 * G 0 0 - G 0 2 ^ 2) * (t ^ 2 * G 1 1 - G 1 2 ^ 2)
      - (t ^ 2 * G 0 1 - G 0 2 * G 1 2) ^ 2 = t ^ 2 := by
    rw [hts] at hdet; linear_combination t ^ 2 * hdet
  have e00 : G 0 0 = ((t ^ 2 * G 0 1 - G 0 2 * G 1 2) ^ 2 + t ^ 2 +
      G 0 2 ^ 2 * (t ^ 2 * G 1 1 - G 1 2 ^ 2)) / (t ^ 2 * (t ^ 2 * G 1 1 - G 1 2 ^ 2)) := by
    rw [eq_div_iff (by positivity)]; linear_combination key
  have E : ∀ i j : Fin 3, planeGram (planePoint G) i j = G i j := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [planePoint, planeGram, hts, hc, Real.sqrt_sq ht.le]
    all_goals try (first | rw [e00] | rw [← h01] | rw [← h02] | rw [← h12])
    all_goals (try field_simp)
    all_goals ring
  ext i j
  exact E i j

end TernaryPeriodPolynomials.Argument.ConvergenceC4
