module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.AwayParts

@[expose] public section


/-!
# Hecke eigenvalues in terms of rational Iwasawa data

For an away-from-three correspondence whose representatives are written as
`r = n(v) m γ` with `γ ∈ GL₃(ℤ)`, the Hecke sum of every plane (line) induced section is
`∑ᵣ Φ(mᵣ)` times the section, with `Φ` an explicit function of the rational Levi part.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.RepresentationTheory
open TernaryPeriodPolynomials.HeckeEigen

namespace TernaryPeriodPolynomials.HeckeEigen.Satake

variable {n : ℕ}

/-- The adelic away-from-three idele of a rational unit. -/
def sAd (s : ℚˣ) : Adelesˣ := SphericalDetection.Helpers.finiteAdeleUnit (unitAway (unitF s))

/-- The away-from-three finite `GL₂` element of a rational matrix. -/
def Bo (B : GeneralLinearGroup (Fin 2) ℚ) : BinaryFiniteGL := glAway2 (glF B)

/-- The plane weight of rational Levi data `(B, s)`. -/
def ratPlaneWeight (D : InducingData n) (B : GeneralLinearGroup (Fin 2) ℚ) (s : ℚˣ) : ℂ :=
  planeWeight D (sAd s) (Bo B)

/-- The line weight of rational Levi data `(d, A)`. -/
def ratLineWeight (D : InducingData n) (A : GeneralLinearGroup (Fin 2) ℚ) (d : ℚˣ) : ℂ :=
  lineWeight D (sAd d) (Bo A)

theorem atFinite_planeUnipotent (a b : FiniteAdeles) :
    atFinite (planeUnipotent a b) = planeUnipotent ((0 : ℝ), a) ((0 : ℝ), b) := by
  apply Units.ext
  refine Matrix.ext fun i j => Prod.ext ?_ ?_ <;>
    fin_cases i <;> fin_cases j <;>
    simp [atFinite, combineGL, pairMatrix, planeUnipotent]

theorem atFinite_lineUnipotent (a b : FiniteAdeles) :
    atFinite (lineUnipotent a b) = lineUnipotent ((0 : ℝ), a) ((0 : ℝ), b) := by
  apply Units.ext
  refine Matrix.ext fun i j => Prod.ext ?_ ?_ <;>
    fin_cases i <;> fin_cases j <;>
    simp [atFinite, combineGL, pairMatrix, lineUnipotent, upperUnipotent]

theorem atFinite_lineLeviScalar (s : FiniteAdelesˣ) :
    atFinite (lineLevi s 1) = lineLevi (SphericalDetection.Helpers.finiteAdeleUnit s) 1 := by
  apply Units.ext
  rw [lineLevi_val]
  refine Matrix.ext fun i j => Prod.ext ?_ ?_ <;>
    fin_cases i <;> fin_cases j <;>
    simp [atFinite, combineGL, pairMatrix, lineLevi_val, SphericalDetection.Helpers.finiteAdeleUnit]

/-- **Plane eigenvalue from rational Iwasawa data.** -/
theorem plane_rational_formula (D : InducingData n) (t : HeckeCorrespondence) (ht : AwayThree t)
    (vP : RationalGL3 → ℚ × ℚ) (BP : RationalGL3 → GeneralLinearGroup (Fin 2) ℚ)
    (sP : RationalGL3 → ℚˣ) (γP : RationalGL3 → IntegralGL)
    (hP : ∀ r ∈ t.representatives,
      r = pU (vP r) * planeLevi (BP r) (sP r) * integralRational (γP r)) :
    ∀ f : AdelicGL → ℂ, IsInduced D .plane cohomologicalPoint f → ∀ g : AdelicGL,
      ∑ r ∈ t.representatives, f (g * atFinite (rationalFinite r)) =
        (∑ r ∈ t.representatives, ratPlaneWeight D (BP r) (sP r)) * f g := by
  classical
  have hκ : ∀ r ∈ t.representatives, ∃ κ : finiteLevel, rationalFinite r =
      glAway3 (rationalFinite (pU (vP r) * planeLevi (BP r) (sP r))) * κ.val :=
    fun r hr => level_factor ht hr _ _ (hP r hr)
  choose! κ hκ using hκ
  exact plane_hecke_formula D t (fun r => glAway3 (rationalFinite (pU (vP r) * planeLevi (BP r) (sP r))))
    κ (fun r => ((0 : ℝ), adeleAway (algebraMap ℚ FiniteAdeles (vP r).1) 0))
    (fun r => ((0 : ℝ), adeleAway (algebraMap ℚ FiniteAdeles (vP r).2) 0))
    (fun r => sAd (sP r)) (fun r => Bo (BP r))
    (fun r _ => glAway3_three _) hκ
    (fun r _ => by
      rw [glAway3_plane, ← HeckeTranslate.HeckeInvariance.atFinite_mul,
        ← HeckeTranslate.HeckeInvariance.atFinite_mul, atFinite_planeUnipotent,
        atFinite_planeLeviScalar, atFinite_planeLevi]
      rfl)
    (fun r _ => glAway2_mem _)

/-- **Line eigenvalue from rational Iwasawa data.** -/
theorem line_rational_formula (D : InducingData n) (t : HeckeCorrespondence) (ht : AwayThree t)
    (wL : RationalGL3 → ℚ × ℚ) (dL : RationalGL3 → ℚˣ)
    (AL : RationalGL3 → GeneralLinearGroup (Fin 2) ℚ) (γL : RationalGL3 → IntegralGL)
    (hL : ∀ r ∈ t.representatives,
      r = lU (wL r) * lineLevi (dL r) (AL r) * integralRational (γL r)) :
    ∀ f : AdelicGL → ℂ, IsInduced D .line cohomologicalPoint f → ∀ g : AdelicGL,
      ∑ r ∈ t.representatives, f (g * atFinite (rationalFinite r)) =
        (∑ r ∈ t.representatives, ratLineWeight D (AL r) (dL r)) * f g := by
  classical
  have hκ : ∀ r ∈ t.representatives, ∃ κ : finiteLevel, rationalFinite r =
      glAway3 (rationalFinite (lU (wL r) * lineLevi (dL r) (AL r))) * κ.val :=
    fun r hr => level_factor ht hr _ _ (hL r hr)
  choose! κ hκ using hκ
  exact line_hecke_formula D t (fun r => glAway3 (rationalFinite (lU (wL r) * lineLevi (dL r) (AL r))))
    κ (fun r => ((0 : ℝ), adeleAway (algebraMap ℚ FiniteAdeles (wL r).1) 0))
    (fun r => ((0 : ℝ), adeleAway (algebraMap ℚ FiniteAdeles (wL r).2) 0))
    (fun r => sAd (dL r)) (fun r => Bo (AL r))
    (fun r _ => glAway3_three _) hκ
    (fun r _ => by
      rw [glAway3_line, ← HeckeTranslate.HeckeInvariance.atFinite_mul,
        ← HeckeTranslate.HeckeInvariance.atFinite_mul, atFinite_lineUnipotent,
        atFinite_lineLeviScalar, atFinite_lineLevi]
      rfl)
    (fun r _ => glAway2_mem _)

end TernaryPeriodPolynomials.HeckeEigen.Satake
