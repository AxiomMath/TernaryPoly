module

public import TernaryPeriodPolynomials.EisensteinSeries.Dual.CuspRows
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Cell.KConj

@[expose] public section


open CategoryTheory MvPolynomial UpperHalfPlane ModularForm
open scoped UpperHalfPlane MatrixGroups ContDiff

/-!
# The dual rows at every pair of cusps: cross-cusp line values of `ℰ_Q^∨`

Formalized by Claude Sonnet 5.5.

the cell values (`CellKClass`, `CellKConj`: `faceClass_none/pos/neg`, `faceClass_true_*`) give the
restriction to the plane face of the cusp `h` of the series at the plane cusp `h'`, with `k = h' h⁻¹`: zero if no cell, the transported seed of `f|A` or the conjugate
seed of `(f|A)^*` otherwise.  Through `ȷ` (`dual_restrictions_transport`) they become the values of the line restriction of the dual series at the line cusp `h⁻¹Qh`
of the dual series at the line cusp `h'` (`ȷ̃^*` of the series at the plane cusp `ȷ(h')`), with `k = ȷ(h') ȷ(h)⁻¹`:

* `dual_rQ_cross_none` / `dual_rQ_cross_true_none`: zero when there is no cell;
* `dual_rQ_cross_pos` / `_neg` and `dual_rQ_cross_true_pos` / `_neg`: `dualSeedClassAt` of the slashed form (resp. `(f|A)^*`), for both seeds.

Own-cusp case: `CuspRows.dual_rQ_at`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinDual

open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.ConvergenceC4
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.Statements.EisensteinClass
open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPoly.SmoothLocalDeRham

variable (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n)
  (h h' : SL(3, ℤ))

/-- The line restriction at the cusp `h⁻¹Qh` of the dual series at the line cusp `h'` is the `ȷ`-pullback of the plane face class of the series at `ȷ(h')`. -/
theorem dual_rQ_cross_eq (b : Bool) :
    resTo (gammaNQAt N h) (gammaNQAt_le_N N h) (dualRhoN N n) (dualSeriesAtClass_gammaN N n f hn b h') =
      pullQP N n h (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (cuspFaceAction N (jmath h))
        (rhoAt N (jmath h) n)
        (cuspFaceForm N (jmath h) (planeEisensteinAtComponents b (CuspData.ofSL (jmath h')) (gammaN N)
          (leviGroup N) n f hn (leviInCusp_gammaN N (jmath h'))))) := by
  rw [dualSeriesAtClass_gammaN_eq]
  refine ((dual_restrictions_transport (N := N) (n := n) (eisensteinAtClass_gammaN N n f (jmath h') b hn)).1 h).trans ?_
  rw [resTo_cuspFace N n f hn (jmath h') b (jmath h)]

/-- **No cell: the dual series at `h'` has zero line restriction at `h`** (holomorphic seed). -/
theorem dual_rQ_cross_none (hN : 3 ≤ N) (hnone : ∀ c : Ck N (jmath h' * (jmath h)⁻¹), ¬ IsCellK N (jmath h' * (jmath h)⁻¹) c) :
    resTo (gammaNQAt N h) (gammaNQAt_le_N N h) (dualRhoN N n) (dualSeriesAtClass_gammaN N n f hn false h') = 0 := by
  rw [dual_rQ_cross_eq N n f hn h h' false, faceClass_none N n f hn (jmath h) (jmath h') hN hnone]
  exact map_zero (pullQP N n h)

/-- **No cell, antiholomorphic seed.** -/
theorem dual_rQ_cross_true_none (hN : 3 ≤ N) (hnone : ∀ c : Ck N (jmath h' * (jmath h)⁻¹), ¬ IsCellK N (jmath h' * (jmath h)⁻¹) c) :
    resTo (gammaNQAt N h) (gammaNQAt_le_N N h) (dualRhoN N n) (dualSeriesAtClass_gammaN N n f hn true h') = 0 := by
  rw [dual_rQ_cross_eq N n f hn h h' true, faceClass_true_none N n f hn (jmath h) (jmath h') hN hnone]
  exact map_zero (pullQP N n h)

/-- **Cell of bottom entry `1`, holomorphic seed**: the dual seed class of `f|A`. -/
theorem dual_rQ_cross_pos (hN : 3 ≤ N) {c₀ : Ck N (jmath h' * (jmath h)⁻¹)} (hc : IsCellK N (jmath h' * (jmath h)⁻¹) c₀)
    (h22 : ((cellMat N (jmath h' * (jmath h)⁻¹) c₀ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = 1) :
    resTo (gammaNQAt N h) (gammaNQAt_le_N N h) (dualRhoN N n) (dualSeriesAtClass_gammaN N n f hn false h') =
      dualSeedClassAt N n (cuspSlash N n (leviBlock (cellMat N (jmath h' * (jmath h)⁻¹) c₀)
        (cellMat_mem_planeStab N (jmath h' * (jmath h)⁻¹) hc h22)) f) false h := by
  rw [dual_rQ_cross_eq N n f hn h h' false, faceClass_pos N n f hn (jmath h) (jmath h') hN hc h22]
  rfl

/-- **Cell of bottom entry `-1`, holomorphic seed**: the dual conjugate seed class of `(f|A)^*`. -/
theorem dual_rQ_cross_neg (hN : 3 ≤ N) {c₀ : Ck N (jmath h' * (jmath h)⁻¹)} (hc : IsCellK N (jmath h' * (jmath h)⁻¹) c₀)
    (h22 : ((cellMat N (jmath h' * (jmath h)⁻¹) c₀ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = -1) :
    resTo (gammaNQAt N h) (gammaNQAt_le_N N h) (dualRhoN N n) (dualSeriesAtClass_gammaN N n f hn false h') =
      dualSeedClassAt N n (fStarGen (leviGroup N) (leviGroup_J_stable N)
        (cuspSlash N n (leviBlock (cellMat N (jmath h' * (jmath h)⁻¹) c₀ * rPrime)
          (cellMat_mul_rPrime_mem N (jmath h' * (jmath h)⁻¹) hc h22)) f)) true h := by
  rw [dual_rQ_cross_eq N n f hn h h' false, faceClass_neg N n f hn (jmath h) (jmath h') hN hc h22]
  rfl

/-- **Cell of bottom entry `1`, antiholomorphic seed**: the dual conjugate seed class of `f|A`. -/
theorem dual_rQ_cross_true_pos (hN : 3 ≤ N) {c₀ : Ck N (jmath h' * (jmath h)⁻¹)} (hc : IsCellK N (jmath h' * (jmath h)⁻¹) c₀)
    (h22 : ((cellMat N (jmath h' * (jmath h)⁻¹) c₀ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = 1) :
    resTo (gammaNQAt N h) (gammaNQAt_le_N N h) (dualRhoN N n) (dualSeriesAtClass_gammaN N n f hn true h') =
      dualSeedClassAt N n (cuspSlash N n (leviBlock (cellMat N (jmath h' * (jmath h)⁻¹) c₀)
        (cellMat_mem_planeStab N (jmath h' * (jmath h)⁻¹) hc h22)) f) true h := by
  rw [dual_rQ_cross_eq N n f hn h h' true, faceClass_true_pos N n f hn (jmath h) (jmath h') hN hc h22]
  rfl

/-- **Cell of bottom entry `-1`, antiholomorphic seed**: the dual seed class of `(f|A)^*`. -/
theorem dual_rQ_cross_true_neg (hN : 3 ≤ N) {c₀ : Ck N (jmath h' * (jmath h)⁻¹)} (hc : IsCellK N (jmath h' * (jmath h)⁻¹) c₀)
    (h22 : ((cellMat N (jmath h' * (jmath h)⁻¹) c₀ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = -1) :
    resTo (gammaNQAt N h) (gammaNQAt_le_N N h) (dualRhoN N n) (dualSeriesAtClass_gammaN N n f hn true h') =
      dualSeedClassAt N n (fStarGen (leviGroup N) (leviGroup_J_stable N)
        (cuspSlash N n (leviBlock (cellMat N (jmath h' * (jmath h)⁻¹) c₀ * rPrime)
          (cellMat_mul_rPrime_mem N (jmath h' * (jmath h)⁻¹) hc h22)) f)) false h := by
  rw [dual_rQ_cross_eq N n f hn h h' true, faceClass_true_neg N n f hn (jmath h) (jmath h') hN hc h22]
  rfl

end TernaryPeriodPolynomials.Argument.EisensteinDual
