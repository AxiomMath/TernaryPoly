module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Model

@[expose] public section


/-!
# The action of `SL₃(ℝ)` on plane coordinates (Appendix C.3, `ar:sec:series`)

`planeAct g p = planePoint (g · planeGram p · gᵀ)` is the action `p SO(3) ↦ g p SO(3)` of
`g ∈ SL₃(ℝ)` on `𝒳 = SL₃(ℝ)/SO(3)` in plane coordinates. It preserves `Ω`, satisfies the group
law, and is jointly smooth in `(g, p)`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

open Matrix MvPolynomial

/-! ### The action of `SL₃(ℝ)` on plane coordinates -/

/-- The action of a real `3 × 3` matrix `g` on plane coordinates, `G ↦ g G gᵀ` on Gram matrices. -/
def planeAct (g : Matrix (Fin 3) (Fin 3) ℝ) (p : Fin 5 → ℝ) : Fin 5 → ℝ :=
  planePoint (g * planeGram p * g.transpose)

theorem IsGram.conj {G g : Matrix (Fin 3) (Fin 3) ℝ} (hG : IsGram G) (hg : g.det = 1) :
    IsGram (g * G * g.transpose) := by
  refine ⟨?_, ?_⟩
  · have hu : IsUnit g.det := by rw [hg]; exact isUnit_one
    have := Matrix.PosDef.mul_mul_conjTranspose_same hG.1
      (Matrix.vecMul_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hu))
    simpa using this
  · rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hg, hG.2]; norm_num

theorem planePoint_mem {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : IsGram G) : planePoint G ∈ Omega := by
  have hs := hG.s_pos
  have hc := hG.schur_pos
  constructor
  · show 0 < 1 / (Real.sqrt (G 2 2) * (G 1 1 - G 1 2 * G 1 2 / G 2 2))
    have := Real.sqrt_pos.2 hs
    positivity
  · show 0 < Real.sqrt (G 2 2)
    exact Real.sqrt_pos.2 hs

theorem planeAct_mem {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1) {p : Fin 5 → ℝ}
    (hp : p ∈ Omega) : planeAct g p ∈ Omega :=
  planePoint_mem ((planeGram_isGram hp).conj hg)

theorem planeGram_planeAct {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1) {p : Fin 5 → ℝ}
    (hp : p ∈ Omega) : planeGram (planeAct g p) = g * planeGram p * g.transpose :=
  planeGram_planePoint ((planeGram_isGram hp).conj hg)

theorem planeAct_one {p : Fin 5 → ℝ} (hp : p ∈ Omega) : planeAct 1 p = p := by
  simp [planeAct, planePoint_planeGram hp]

theorem planeAct_mul {g h : Matrix (Fin 3) (Fin 3) ℝ} (hh : h.det = 1)
    {p : Fin 5 → ℝ} (hp : p ∈ Omega) : planeAct (g * h) p = planeAct g (planeAct h p) := by
  have := planeGram_planeAct hh hp
  have e : planeAct (g * h) p = planePoint (g * h * planeGram p * (g * h).transpose) := rfl
  have e2 : planeAct g (planeAct h p) =
      planePoint (g * planeGram (planeAct h p) * g.transpose) := rfl
  rw [e, e2, this]
  congr 1
  simp [Matrix.mul_assoc, Matrix.transpose_mul]

theorem planeGram_basePt : planeGram basePt = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [planeGram, basePt]

theorem planePoint_one : planePoint 1 = basePt := by
  funext i
  fin_cases i <;> simp [planePoint, basePt]

theorem planeAct_basePt_of_orthogonal {k : Matrix (Fin 3) (Fin 3) ℝ} (hk : k * k.transpose = 1) :
    planeAct k basePt = basePt := by
  simp [planeAct, planeGram_basePt, hk, planePoint_one]

/-! ### Smoothness -/

theorem contDiffAt_planePoint_comp {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {F : X → Matrix (Fin 3) (Fin 3) ℝ} {x : X}
    (hF : ∀ i j, ContDiffAt ℝ ⊤ (fun y => F y i j) x) (hs : 0 < F x 2 2)
    (hc : 0 < F x 1 1 - F x 1 2 * F x 1 2 / F x 2 2) :
    ContDiffAt ℝ ⊤ (fun y => planePoint (F y)) x := by
  have h22 : ContDiffAt ℝ ⊤ (fun y => F y 2 2) x := hF 2 2
  have hsq : ContDiffAt ℝ ⊤ (fun y => Real.sqrt (F y 2 2)) x := h22.sqrt hs.ne'
  have hc' : ContDiffAt ℝ ⊤ (fun y => F y 1 1 - F y 1 2 * F y 1 2 / F y 2 2) x :=
    (hF 1 1).sub (((hF 1 2).mul (hF 1 2)).div h22 hs.ne')
  rw [contDiffAt_pi]
  intro k
  fin_cases k
  · exact (hF 0 2).div h22 hs.ne'
  · exact (hF 1 2).div h22 hs.ne'
  · exact ((hF 0 1).sub (((hF 0 2).mul (hF 1 2)).div h22 hs.ne')).div hc' hc.ne'
  · exact contDiffAt_const.div (hsq.mul hc') (mul_ne_zero (Real.sqrt_pos.2 hs).ne' hc.ne')
  · exact hsq

theorem contDiffAt_planeGram_entry {p : Fin 5 → ℝ} (hp : p ∈ Omega) (i j : Fin 3) :
    ContDiffAt ℝ ⊤ (fun q : Fin 5 → ℝ => planeGram q i j) p := by
  obtain ⟨hy, ht⟩ := hp
  have c : ∀ k : Fin 5, ContDiffAt ℝ ⊤ (fun q : Fin 5 → ℝ => q k) p :=
    fun k => (contDiff_apply ℝ ℝ k).contDiffAt
  have hd : p 4 * p 3 ≠ 0 := mul_ne_zero ht.ne' hy.ne'
  have hd' : ContDiffAt ℝ ⊤ (fun q : Fin 5 → ℝ => q 4 * q 3) p := (c 4).mul (c 3)
  have hA : ContDiffAt ℝ ⊤ (fun q : Fin 5 → ℝ => ((q 2) ^ 2 + (q 3) ^ 2) / (q 4 * q 3)) p :=
    (((c 2).pow 2).add ((c 3).pow 2)).div hd' hd
  have hB : ContDiffAt ℝ ⊤ (fun q : Fin 5 → ℝ => q 2 / (q 4 * q 3)) p := (c 2).div hd' hd
  have hC : ContDiffAt ℝ ⊤ (fun q : Fin 5 → ℝ => 1 / (q 4 * q 3)) p := contDiffAt_const.div hd' hd
  fin_cases i <;> fin_cases j <;> simp only [planeGram, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk]
  · exact hA.add (((c 4).pow 2).mul ((c 0).pow 2))
  · exact hB.add ((((c 4).pow 2).mul (c 0)).mul (c 1))
  · exact ((c 4).pow 2).mul (c 0)
  · exact hB.add ((((c 4).pow 2).mul (c 0)).mul (c 1))
  · exact hC.add (((c 4).pow 2).mul ((c 1).pow 2))
  · exact ((c 4).pow 2).mul (c 1)
  · exact ((c 4).pow 2).mul (c 0)
  · exact ((c 4).pow 2).mul (c 1)
  · exact (c 4).pow 2

/-- `Fin 3 → Fin 3 → ℝ` viewed as a matrix (definitional). -/
def matOfFun (f : Fin 3 → Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ := f

/-- A matrix viewed as a function (definitional). -/
def matToFun (g : Matrix (Fin 3) (Fin 3) ℝ) : Fin 3 → Fin 3 → ℝ := g

theorem matOfFun_apply (f : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) : matOfFun f i j = f i j := rfl

/-- The joint action map `(g, p) ↦ g · p` is smooth at every pair with `p ∈ Ω`, `det g = 1`. -/
theorem contDiffAt_planeAct_pair {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1)
    {p : Fin 5 → ℝ} (hp : p ∈ Omega) :
    ContDiffAt ℝ ⊤ (fun z : (Fin 3 → Fin 3 → ℝ) × (Fin 5 → ℝ) =>
      planeAct (matOfFun z.1) z.2) (matToFun g, p) := by
  have hGg := (planeGram_isGram hp).conj hg
  have gz : ∀ a b : Fin 3, ContDiffAt ℝ ⊤ (fun z : (Fin 3 → Fin 3 → ℝ) × (Fin 5 → ℝ) =>
      z.1 a b) (matToFun g, p) := fun a b =>
    (((contDiff_apply ℝ ℝ b).comp (contDiff_apply ℝ (Fin 3 → ℝ) a)).comp contDiff_fst).contDiffAt
  have pz : ∀ a b : Fin 3, ContDiffAt ℝ ⊤ (fun z : (Fin 3 → Fin 3 → ℝ) × (Fin 5 → ℝ) =>
      planeGram z.2 a b) (matToFun g, p) := fun a b =>
    (contDiffAt_planeGram_entry hp a b).comp (matToFun g, p) contDiffAt_snd
  have hent : ∀ i j, ContDiffAt ℝ ⊤ (fun z : (Fin 3 → Fin 3 → ℝ) × (Fin 5 → ℝ) =>
      (matOfFun z.1 * planeGram z.2 * (matOfFun z.1).transpose) i j)
      (matToFun g, p) := by
    intro i j
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, matOfFun_apply]
    fun_prop
  exact contDiffAt_planePoint_comp (F := fun z : (Fin 3 → Fin 3 → ℝ) × (Fin 5 → ℝ) =>
      (matOfFun z.1 * planeGram z.2 * (matOfFun z.1).transpose)) hent
    (by exact hGg.s_pos) (by exact hGg.schur_pos)

end TernaryPeriodPolynomials.Argument.ConvergenceC4
