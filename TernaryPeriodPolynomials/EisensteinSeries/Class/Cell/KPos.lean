module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Cell.K

@[expose] public section


open scoped MatrixGroups
open MvPolynomial
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham
open TernaryPeriodPolynomials.Argument.SeedC3.Psi TernaryPeriodPolynomials.Argument.Statements.EisensteinClass
open TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4

section Pos

variable (N : ℕ) (k : SL(3, ℤ)) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

/-- The integral matrix `k γ` of the representative of a coset. -/
def cellMat (c₀ : Ck N k) : SL(3, ℤ) := k * (Quotient.out c₀).1

theorem cellMat_mem_planeStab {c₀ : Ck N k} (hc : IsCellK N k c₀)
    (h22 : ((cellMat N k c₀ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = 1) :
    cellMat N k c₀ ∈ planeStab := by
  obtain ⟨h0, h1⟩ := hc
  rw [cuspRow_out] at h0 h1
  exact ⟨h0, h1, h22⟩

/-- **The cell of bottom entry `+1` is the seed of `f|A`**: for `k γ ∈ P(ℤ)` with Levi block
`A ∈ SL₂(ℤ)`, the summand of the cell is the seed of the cusp form `f|A`. -/
theorem cell_pos_coeff [NeZero N] (hN : 3 ≤ N) {c₀ : Ck N k} (hc : IsCellK N k c₀)
    (h22 : ((cellMat N k c₀ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = 1)
    {y : Fin 5 → ℝ} (hy : y ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ) :
    cellCoeffK N k n f y i j m =
      (seedForm n (cuspH (leviGroup N) n
        (cuspSlash N n (leviBlock (cellMat N k c₀) (cellMat_mem_planeStab N k hc h22)) f))
          y i j).coeff m := by
  have hps := cellMat_mem_planeStab N k hc h22
  rw [cellCoeffK_eq N k n f hN hc y i j m]
  change (summandPoly n (hfun f) (realMat (cellMat N k c₀)) y i j).coeff m = _
  have e1 : realMat (cellMat N k c₀) = parabolicMatrix (topBlock (realMat (cellMat N k c₀)))
      (sideVec (realMat (cellMat N k c₀))) * 1 := by
    rw [Matrix.mul_one]; exact realMat_stab_eq hps
  have hone : (1 : Matrix (Fin 3) (Fin 3) ℝ).det = 1 := Matrix.det_one
  rw [e1, summandPoly_parabolic_mul n (hfun f) _ (det_topBlock hps) _ hone hy i j]
  have e2 : summandPoly n (slashTwisted (n + 3) (topBlock (realMat (cellMat N k c₀))) (hfun f))
      (1 : Matrix (Fin 3) (Fin 3) ℝ) y i j =
      seedForm n (slashTwisted (n + 3) (topBlock (realMat (cellMat N k c₀))) (hfun f)) y i j := by
    rw [← realMat_one]; exact summandPoly_one n _ hy i j
  rw [e2]
  congr 2
  refine seedForm_congr_value n _ _ y ?_ i j
  have hτ := seedTau_im_pos hy
  rw [← coe_mapGL_leviBlock (cellMat N k c₀) hps]
  have := slashTwisted_cuspSlash N n (leviBlock (cellMat N k c₀) hps) f hτ
  exact this

/-- **The class of the face form at a cusp with a positive cell is the seed class of `f|A`.** -/
theorem faceSeriesK_class_pos [NeZero N] (hN : 3 ≤ N) (hn : 4 ≤ n) {c₀ : Ck N k}
    (hc : IsCellK N k c₀)
    (h22 : ((cellMat N k c₀ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = 1) :
    ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (gammaNPlaneData N).action
        ((gammaNPlaneData N).rhoR n) (faceSeriesK N k n f hn) =
      ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (gammaNPlaneData N).action
        ((gammaNPlaneData N).rhoR n)
        (cuspSeedInv (gammaNPlaneData N) (gammaNPlaneData_lam_mem N)
          (f := cuspSlash N n (leviBlock (cellMat N k c₀) (cellMat_mem_planeStab N k hc h22)) f)) := by
  refine classK_eq N k n f hn _ ?_
  intro y hy i j m
  have h2 := PlaneData.toPoly_d_etaForm (cuspH (leviGroup N) n
    (cuspSlash N n (leviBlock (cellMat N k c₀) (cellMat_mem_planeStab N k hc h22)) f)) n
    (cuspH_holo (leviGroup N) n
      (cuspSlash N n (leviBlock (cellMat N k c₀) (cellMat_mem_planeStab N k hc h22)) f)) hy i j
  rw [cell_pos_coeff N k n f hN hc h22 (ptOf_mem hy)]
  exact congrArg (·.coeff m) h2

end Pos

end TernaryPeriodPolynomials.Argument.EisensteinClass
