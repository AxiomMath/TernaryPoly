module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Passage.Stab

@[expose] public section


/-!
# The reflection `κ = diag(-1, 1, -1)` acting on the line parabolic `Q⁺(ℤ)` (Passage 8)

`κ ∈ SL₃(ℤ)` normalizes `Q⁺(ℤ) = lineStab` (it has first column `(-1, 0, 0)ᵗ`); `kapConj x = κ x κ⁻¹` changes the radical row `v ↦ (-v₀, v₁)` and the Levi block `C = [[a, b], [c, d]] ↦ [[a, -b], [-c, d]]`
(conjugation by `diag(1, -1)`), so `(κ C κ)·i = -\overline{C·i}`.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open GeneralEisenstein Matrix MvPolynomial ComplexConjugate

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.Argument.LineSeed
open TernaryPeriodPolynomials.Argument.SeedC3 hiding toPoly_cuspSeedCochain cuspSeedCochain cuspSeedInv cuspSeedClass
  cuspSeedConjClass cuspSeedConjInv cuspSeedCochain_cocycle cuspSeedConjCochain cuspSeedConjCochain_eq
  cuspSeedConjCochain_cocycle deRhamClass_cuspSeed deRhamClass_cuspSeedConj cuspSeedDatum
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.SeedC3S4c (Lvl1 ambRep)
open TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- The signs `(-1, 1, -1)` of `κ`. -/
def kapSign : Fin 3 → ℤ := ![-1, 1, -1]

/-- `κ = diag(-1, 1, -1) ∈ SL₃(ℤ)`. -/
def kapSL : SL(3, ℤ) :=
  ⟨Matrix.diagonal kapSign, by simp [kapSign, Matrix.det_diagonal, Fin.prod_univ_three]⟩

theorem kapSign_mul_self (a : Fin 3) : kapSign a * kapSign a = 1 := by
  fin_cases a <;> simp [kapSign]

theorem kapSL_mul_self : kapSL * kapSL = 1 := by
  apply Subtype.ext
  ext a b
  change (Matrix.diagonal kapSign * Matrix.diagonal kapSign) a b = _
  rw [Matrix.diagonal_mul_diagonal]
  by_cases hab : a = b
  · subst hab; simp [kapSign_mul_self]
  · simp [hab]

theorem kapSL_conj_apply (x : SL(3, ℤ)) (a b : Fin 3) :
    ((kapSL * x * kapSL : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) a b = kapSign a * (x : Matrix (Fin 3) (Fin 3) ℤ) a b * kapSign b := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  change (Matrix.diagonal kapSign * (x : Matrix (Fin 3) (Fin 3) ℤ) * Matrix.diagonal kapSign) a b = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem kapSL_conj_mem {x : SL(3, ℤ)} (hx : x ∈ lineStab) : kapSL * x * kapSL ∈ lineStab := by
  obtain ⟨h0, h1, h2⟩ := hx
  refine ⟨?_, ?_, ?_⟩ <;> simp [kapSL_conj_apply, kapSign, h0, h1, h2]

/-- Conjugation by `κ` on `Q⁺(ℤ)`. -/
def kapConj : ↥lineStab →* ↥lineStab where
  toFun x := ⟨kapSL * x.1 * kapSL, kapSL_conj_mem x.2⟩
  map_one' := Subtype.ext (by simp [kapSL_mul_self])
  map_mul' x y := Subtype.ext (by
    simp only [Subgroup.coe_mul]
    calc kapSL * (x.1 * y.1) * kapSL = kapSL * x.1 * (kapSL * kapSL) * y.1 * kapSL := by
          rw [kapSL_mul_self]; group
      _ = _ := by group)

theorem kapConj_entry (x : ↥lineStab) (a b : Fin 3) :
    ((kapConj x).1 : Matrix (Fin 3) (Fin 3) ℤ) a b = kapSign a * (x.1 : Matrix (Fin 3) (Fin 3) ℤ) a b * kapSign b :=
  kapSL_conj_apply x.1 a b

theorem kapConj_v (x : ↥lineStab) : lineStabData.v (kapConj x) = ![-(lineStabData.v x 0), lineStabData.v x 1] := by
  funext j
  fin_cases j <;> simp [lineStabData, lineStabV, kapConj_entry, kapSign]

theorem kapConj_lam_entry (x : ↥lineStab) (i j : Fin 2) :
    ((lineStabData.lam (kapConj x) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j =
      (if i = j then 1 else -1) * ((lineStabData.lam x : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j := by
  change ((lineStabLam (kapConj x) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = _
  change _ = _ * ((lineStabLam x : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j
  rw [lineStabLam_entry, lineStabLam_entry, kapConj_entry]
  fin_cases i <;> fin_cases j <;> simp [kapSign]

/-- `(κ C κ)·i = -\overline{C·i}`. -/
theorem mob_kapConj (x : ↥lineStab) :
    mob (lineStabData.lam (kapConj x)) Complex.I = -conj (mob (lineStabData.lam x) Complex.I) := by
  unfold mob
  rw [kapConj_lam_entry, kapConj_lam_entry, kapConj_lam_entry, kapConj_lam_entry]
  simp [map_div₀, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

end TernaryPeriodPolynomials.Argument.LineSeed
