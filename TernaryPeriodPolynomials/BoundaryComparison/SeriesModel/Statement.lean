module

public import TernaryPeriodPolynomials.DifferentialForm.CochainComparison.Gram
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.EndpointEisensteinCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelTransfer.Bridge

@[expose] public section


open scoped Matrix.Norms.Elementwise MatrixGroups
open Matrix
open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormSeriesModel

open TernaryPeriodPolynomials.Argument.ConvergenceC4

theorem gammaN_mem_arithmeticLevel {N : ℕ} (h3 : 3 ∣ N) {γ : SL(3, ℤ)} (hγ : γ ∈ gammaN N) :
    Matrix.SpecialLinearGroup.toGL γ ∈ arithmeticLevel := by
  change reductionThree (Matrix.SpecialLinearGroup.toGL γ) ∈ rowStabilizer
  change lastRow ᵥ* (reductionThree (Matrix.SpecialLinearGroup.toGL γ)).val = lastRow
  ext j
  have h : ∀ i j, ((γ : Matrix (Fin 3) (Fin 3) ℤ) i j : ZMod 3) = (1 : Matrix (Fin 3) (Fin 3) ℤ) i j := by
    intro i j
    have := mem_gammaN.1 hγ i j
    have h3' : (3 : ℤ) ∣ (γ : Matrix (Fin 3) (Fin 3) ℤ) i j - (1 : Matrix (Fin 3) (Fin 3) ℤ) i j :=
      dvd_trans (by exact_mod_cast h3) this
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr h3'
    rwa [Int.cast_sub, sub_eq_zero] at this
  simp [lastRow, Matrix.vecMul, dotProduct, reductionThree, Fin.sum_univ_three]
  rw [h 2 j]
  fin_cases j <;> simp [Matrix.one_apply]

/-- The inclusion `Γ(N) ↪ K† = arithmeticLevel` (`3 ∣ N`). -/
def levelHom (N : ℕ) (h3 : 3 ∣ N) : gammaN N →* arithmeticLevel :=
  ((Matrix.SpecialLinearGroup.toGL).comp (gammaN N).subtype).codRestrict arithmeticLevel
    (fun γ => gammaN_mem_arithmeticLevel h3 γ.2)

/-- The inclusion `Γ(N) ↪ rationalLevel`, the literal rational image of the congruence level. -/
def toRationalLevel (N : ℕ) (h3 : 3 ∣ N) : gammaN N →* rationalLevel :=
  (rationalInclusion.rangeRestrict).comp (levelHom N h3)

theorem map_toGL_val (γ : SL(3, ℤ)) :
    Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
        (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) (Matrix.SpecialLinearGroup.toGL γ)) =
      Matrix.SpecialLinearGroup.mapGL ℝ γ := by
  apply Units.ext
  ext i j
  simp [Matrix.GeneralLinearGroup.map, Matrix.SpecialLinearGroup.mapGL]

theorem realComp_eq (n : ℕ) (χ : RankOneCharacter) (hc : ∀ g : RealGL3, componentCharacter χ g = 1)
    (g : RealGL3) : realCoefficientComponent n χ g = GeneralEisenstein.realCoefficient n g :=
  LinearMap.ext fun v => by
    change componentCharacter χ g • GeneralEisenstein.realCoefficient n g v = _
    rw [hc, one_smul]

open TernaryPeriodPolynomials.Argument.EisensteinClass in
theorem rat_rep_eq (N : ℕ) (h3 : 3 ∣ N) (n : ℕ) (χ : RankOneCharacter)
    (hc : ∀ g : RealGL3, componentCharacter χ g = 1) (γ : gammaN N) :
    gammaRhoC (gammaN N) n γ = rationalCoefficientComponent n χ (toRationalLevel N h3 γ).1 := by
  have e : ((toRationalLevel N h3 γ).1 : RationalGL3) =
      Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) (Matrix.SpecialLinearGroup.toGL γ.1) := rfl
  rw [e]
  change (GeneralEisenstein.realCoefficient n) (gammaSigma (gammaN N) γ) =
    realCoefficientComponent n χ (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
      (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) (Matrix.SpecialLinearGroup.toGL γ.1)))
  rw [map_toGL_val]
  exact (realComp_eq n χ hc _).symm

open TernaryPeriodPolynomials.Argument.EisensteinClass in
/-- The comparison of coefficient modules for the restriction `Γ(N) ↪ rationalLevel`. -/
def repMor (N : ℕ) (h3 : 3 ∣ N) (n : ℕ) (χ : RankOneCharacter)
    (hc : ∀ g : RealGL3, componentCharacter χ g = 1) :
    Rep.res (toRationalLevel N h3)
        (Rep.of ((rationalCoefficientComponent n χ).comp rationalLevel.subtype)) ⟶
      gammaRep (gammaN N) n :=
  Rep.ofHom ⟨LinearMap.id, fun g => LinearMap.ext fun v =>
    (congrArg (fun L => L v) (rat_rep_eq N h3 n χ hc g)).symm⟩

end TernaryPeriodPolynomials.Argument.FormSeriesModel
