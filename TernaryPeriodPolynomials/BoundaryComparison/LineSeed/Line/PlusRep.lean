module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Line.PlusData

@[expose] public section


/-!
# The pivot intertwiner of the coefficient representations of `Λ₁⁺` (LS11c)

`lmat_linePlus : lmat g = Π g Π` (entrywise `lmat g i j = g_{rev i, rev j}`), `sigma_linePlus : σ g = Π · g · Π` in `GL₃(ℝ)`, and the isomorphism
`linePlusRepIso n : Rep.of (linePlusData.rhoC n) ≅ Rep.res Lam1Plus.subtype (goodLineCoefficientRep n)` of complex representations, given by the
involution `T = ρ(Π)` (`pivotT n`).

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.LineSeed

/-- The pivot `Π` (the permutation `e₁ ↔ e₃`) as a real matrix. -/
def pivotR : GL (Fin 3) ℝ := GeneralLinearGroup.map (algebraMap ℚ ℝ) rationalGoodLine

/-- The real matrix of an element of `Λ₁⁺` (as an element of `GL₃(ℝ)`). -/
def lineRealMat (g : Lam1Plus) : GL (Fin 3) ℝ :=
  GeneralLinearGroup.map (algebraMap ℚ ℝ) ((g : Lam1) : RationalGL3)

theorem pivotR_mul_self : pivotR * pivotR = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pivotR, rationalGoodLine, Matrix.mul_apply, Fin.sum_univ_three]

theorem lmat_linePlus (g : Lam1Plus) (i j : Fin 3) :
    linePlusData.lmat g i j = ((((g : Lam1) : RationalGL3).val i.rev j.rev : ℚ) : ℝ) := by
  obtain ⟨g02, g12, g22, -⟩ := lam1_entries (g : Lam1)
  obtain ⟨l00, l01, l10, l11⟩ := linePlusLam_entry g
  fin_cases i <;> fin_cases j <;>
    simp [LineData.lmat, linePlusData, linePlusV, TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry.lineParabolic, l00, l01, l10, l11, g02, g12, g22, Fin.rev]

theorem sigma_linePlus (g : Lam1Plus) : linePlusData.sigma g = pivotR * lineRealMat g * pivotR := by
  apply Units.ext
  ext i j
  rw [LineData.sigma_val, lmat_linePlus]
  fin_cases i <;> fin_cases j <;>
    simp [pivotR, lineRealMat, rationalGoodLine, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.rev]

/-- The pivot intertwiner `T = ρ(Π)` of the coefficient spaces. -/
def pivotT (n : ℕ) : HomogeneousPoly n →ₗ[ℂ] HomogeneousPoly n := GeneralEisenstein.realCoefficient n pivotR

theorem pivotT_mul_self (n : ℕ) (q : HomogeneousPoly n) : pivotT n (pivotT n q) = q := by
  have h := congrArg (fun x => GeneralEisenstein.realCoefficient n x q) pivotR_mul_self
  simpa [pivotT, map_mul, map_one] using h

theorem goodLine_rep_eq (n : ℕ) (g : Lam1Plus) :
    (goodLineCoefficientRep n).ρ (g : Lam1) = GeneralEisenstein.realCoefficient n (lineRealMat g) := by
  change rationalCoefficientComponent n trivialCharacter ((g : Lam1) : RationalGL3) = _
  change componentCharacter trivialCharacter _ • GeneralEisenstein.realCoefficient n _ = _
  have h1 : componentCharacter trivialCharacter
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) ((g : Lam1) : RationalGL3)) = 1 := rfl
  rw [h1, one_smul]
  rfl

theorem rhoC_linePlus (n : ℕ) (g : Lam1Plus) (q : HomogeneousPoly n) :
    linePlusData.rhoC n g q = pivotT n ((goodLineCoefficientRep n).ρ (g : Lam1) (pivotT n q)) := by
  rw [goodLine_rep_eq]
  change GeneralEisenstein.realCoefficient n (linePlusData.sigma g) q = _
  rw [sigma_linePlus, map_mul, map_mul]
  rfl

/-- The linear involution `T` as a linear equivalence. -/
def pivotEquiv (n : ℕ) : HomogeneousPoly n ≃ₗ[ℂ] HomogeneousPoly n :=
  LinearEquiv.ofLinearMap (pivotT n) (pivotT n) (LinearMap.ext (pivotT_mul_self n))
    (LinearMap.ext (pivotT_mul_self n))

/-- **The pivot isomorphism of coefficient representations of `Λ₁⁺`.** -/
def linePlusRepIso (n : ℕ) :
    Rep.of (linePlusData.rhoC n) ≅ Rep.res Lam1Plus.subtype (goodLineCoefficientRep n) :=
  Rep.mkIso (Representation.Equiv.mk (pivotEquiv n) (by
    intro g
    apply LinearMap.ext
    intro q
    change pivotT n (linePlusData.rhoC n g q) = (goodLineCoefficientRep n).ρ (g : Lam1) (pivotT n q)
    rw [rhoC_linePlus]
    exact pivotT_mul_self n _))

end TernaryPeriodPolynomials.Argument.LineSeed
