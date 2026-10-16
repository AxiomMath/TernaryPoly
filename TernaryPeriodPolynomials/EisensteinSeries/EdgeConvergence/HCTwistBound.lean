module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.SectionMultipliersXiSmooth
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Smooth.Continuity
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.MaximalCompact

@[expose] public section


/-!
# The height multiplier `ρ_h` is uniformly bounded above and below

Original work by Claude Sonnet 5.5.

For a function `logXi` satisfying the transformation law `HeightLaw` of `log Ξ` and a real element
`h`, the difference `log Ξ (y h) - log Ξ y` is bounded uniformly in the adelic argument `y`
(`logXi_translate_bounded`). By the Iwasawa decomposition `y = n · planeLevi(B, t) · κ` and the
`HeightLaw`, the difference equals `log Ξ (κ_∞ h)` where `κ_∞` is the real orthogonal part of the
maximal compact factor `κ`; `X ↦ log Ξ (atInfinity X)` is continuous (real smoothness) and the
orthogonal group is compact. Consequently `ρ_h(y)^z = exp (z (log Ξ (y h) - log Ξ y))` has modulus at
most `exp (|z| C_h)` (`norm_heightMultiplier_le`).
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.EdgeConvergence.SectionMultipliers

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence.HCTwistBound

/-- `X ↦ log Ξ (atInfinity X)` is continuous on `GL₃(ℝ)`. -/
theorem logXi_atInfinity_continuous {logXi : AdelicGL → ℝ} (law : HeightLaw logXi) :
    Continuous (fun X : RealGL3 => logXi (atInfinity X)) := by
  have base := SmoothContinuity.smooth_continuous _ (law.smooth 1)
  have constantTuple : Continuous (fun X : RealGL3 => fun _ : Fin 1 => X) :=
    continuous_pi (fun _ => continuous_id)
  simpa only [Function.comp_def, one_mul] using base.comp constantTuple

/-- A maximal compact element times a real translation, split into real and finite parts. -/
theorem compact_mul_atInfinity (compact : AdelicGL) (X : RealGL3) :
    compact * atInfinity X =
      atInfinity (realGroup compact * X) * atFinite (finiteGroup compact) := by
  have split : compact = atInfinity (realGroup compact) * atFinite (finiteGroup compact) := by
    apply InducedContinuity.adelic_ext
    · simp only [map_mul, InducedContinuity.realGroup_atInfinity,
        InducedContinuity.realGroup_atFinite, mul_one]
    · simp only [map_mul, InducedContinuity.finiteGroup_atInfinity,
        InducedContinuity.finiteGroup_atFinite, one_mul]
  calc compact * atInfinity X
      = (atInfinity (realGroup compact) * atFinite (finiteGroup compact)) * atInfinity X := by
        rw [← split]
    _ = atInfinity (realGroup compact) * (atFinite (finiteGroup compact) * atInfinity X) :=
        mul_assoc _ _ _
    _ = atInfinity (realGroup compact) * (atInfinity X * atFinite (finiteGroup compact)) := by
        rw [RealTranslations.atFinite_atInfinity_commute]
    _ = atInfinity (realGroup compact * X) * atFinite (finiteGroup compact) := by
        rw [RealTranslations.atInfinity_mul, mul_assoc]

/-- The change of `log Ξ` under right translation by a real element is `log Ξ` of the translate of
the real part of the maximal compact factor of the Iwasawa decomposition. -/
theorem logXi_translate_eq_compact {logXi : AdelicGL → ℝ} (law : HeightLaw logXi)
    (real : RealGL3) (y : AdelicGL) :
    ∃ compact : AdelicGL, inMaximalCompact compact ∧
      logXi (y * atInfinity real) - logXi y = logXi (atInfinity (realGroup compact * real)) := by
  obtain ⟨first, second, binary, unit, compact, membership, rfl⟩ :=
    AdelicDecomposition.adelic_planeDecomposition y
  refine ⟨compact, membership, ?_⟩
  have finiteCompact : inMaximalCompact (atFinite (finiteGroup compact)) :=
    SectionMultipliersXiSmooth.atFinite_compact_of_range _ membership.2
  have zeroLog : logXi compact = 0 := by
    have rightInvariance := law.rightCompact 1 compact membership
    rwa [one_mul, law.one] at rightInvariance
  have regroup : planeUnipotent first second * planeLevi binary unit * compact * atInfinity real =
      planeUnipotent first second * (planeLevi binary unit *
        (atInfinity (realGroup compact * real) * atFinite (finiteGroup compact))) := by
    calc planeUnipotent first second * planeLevi binary unit * compact * atInfinity real
        = planeUnipotent first second * planeLevi binary unit * (compact * atInfinity real) :=
          mul_assoc _ _ _
      _ = planeUnipotent first second * planeLevi binary unit *
            (atInfinity (realGroup compact * real) * atFinite (finiteGroup compact)) := by
          rw [compact_mul_atInfinity compact real]
      _ = _ := mul_assoc _ _ _
  have shifted : logXi (planeUnipotent first second * planeLevi binary unit * compact *
        atInfinity real) =
      logXi (atInfinity (realGroup compact * real)) +
        (1 / 3) * Real.log (adeleNorm (GeneralLinearGroup.det binary) : ℝ) -
          (2 / 3) * Real.log (adeleNorm unit : ℝ) := by
    rw [regroup, law.radical, law.levi, law.rightCompact _ _ finiteCompact]
  have original : logXi (planeUnipotent first second * planeLevi binary unit * compact) =
      logXi compact + (1 / 3) * Real.log (adeleNorm (GeneralLinearGroup.det binary) : ℝ) -
        (2 / 3) * Real.log (adeleNorm unit : ℝ) := by
    rw [mul_assoc (planeUnipotent first second) (planeLevi binary unit) compact, law.radical,
      law.levi]
  rw [shifted, original, zeroLog]
  ring

/-- **`logXi_translate_bounded`.** For a fixed real element `h`, `log Ξ (y h) - log Ξ y` is bounded
uniformly in the adelic argument `y`. -/
theorem logXi_translate_bounded {logXi : AdelicGL → ℝ} (law : HeightLaw logXi) (real : RealGL3) :
    ∃ bound : ℝ, 0 ≤ bound ∧
      ∀ y : AdelicGL, |logXi (y * atInfinity real) - logXi y| ≤ bound := by
  have continuous : Continuous (fun k : RealGL3 => logXi (atInfinity (k * real))) :=
    (logXi_atInfinity_continuous law).comp (continuous_id.mul continuous_const)
  obtain ⟨bound, bounded⟩ :=
    TernaryPeriodPolynomials.EisensteinRegularization.Helpers.realOrthogonal_isCompact.exists_bound_of_continuousOn
      continuous.continuousOn
  refine ⟨max bound 0, le_max_right _ _, fun y => ?_⟩
  obtain ⟨compact, membership, equality⟩ := logXi_translate_eq_compact law real y
  rw [equality]
  have atCompact := bounded (realGroup compact) membership.1
  rw [Real.norm_eq_abs] at atCompact
  exact atCompact.trans (le_max_left _ _)

/-- The modulus of the height multiplier is at most `exp (|z| C)` when the exponent of `Ξ` changes by
at most `C` under right translation. -/
theorem norm_heightMultiplier_le (logXi : AdelicGL → ℝ) (real : RealGL3) (z : ℂ) (y : AdelicGL)
    (width bound : ℝ) (difference : |logXi (y * atInfinity real) - logXi y| ≤ bound)
    (small : ‖z‖ ≤ width) :
    ‖heightMultiplier logXi real z y‖ ≤ Real.exp (width * bound) := by
  unfold heightMultiplier
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have realPart : (z * ((logXi (y * atInfinity real) - logXi y : ℝ) : ℂ)).re =
      z.re * (logXi (y * atInfinity real) - logXi y) := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [realPart]
  have realBound : |z.re| ≤ width := (Complex.abs_re_le_norm z).trans small
  calc z.re * (logXi (y * atInfinity real) - logXi y)
      ≤ |z.re * (logXi (y * atInfinity real) - logXi y)| := le_abs_self _
    _ = |z.re| * |logXi (y * atInfinity real) - logXi y| := abs_mul _ _
    _ ≤ width * bound :=
        mul_le_mul realBound difference (abs_nonneg _) ((abs_nonneg _).trans realBound)

end TernaryPeriodPolynomials.EdgeConvergence.HCTwistBound
