module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REGeneral
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REMajorant
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REBad2
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REBad4
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.PlaneTransfer

@[expose] public section


/-!
# R-e: The bad-plane entry integral at a good-line matrix

`entryPlaneIntegral_bad_general` and the measurability of the weight along the radical.

Formalized by Claude Sonnet 5.5.
-/


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.HeckeEigen
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open scoped ENNReal NNReal

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

theorem map_planeOpposite {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b : R) :
    GeneralLinearGroup.map φ (planeOppositeStandardMatrix a b) = planeOppositeStandardMatrix (φ a) (φ b) := by
  apply Units.ext
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [planeOppositeStandardMatrix, GeneralLinearGroup.map_apply]

theorem inLocalThreeLevel_one : InLocalThreeLevel (1 : LocalThreeGL) := ⟨1, by simp, by simp⟩

open Classical in
theorem badPlaneSet_indicator (s t : ℚ_[3]) :
    badPlaneSet (weyl⁻¹ * lineUnipotent s t * localGoodLine) ↔ (‖s‖ < 1 ∧ ‖t‖ < 1) := by
  let φ : LocalThreeGL → ℂ := fun g => if badPlaneSet g then 1 else 0
  have support : LocalBadPlaneSupport φ := by
    intro g hg
    have : ¬ badPlaneSet g := hg
    simp [φ, this]
  have invariant : LocalRightInvariant φ := by
    intro g k hk
    simp only [φ]
    exact if_congr (badPlaneSet_mul_level_iff hk) rfl rfl
  have one : φ 1 = 1 := by
    have : badPlaneSet (1 : LocalThreeGL) := ⟨1, 1, inLocalThreeLevel_one, by simp⟩
    simp [φ, this]
  have h := congrFun (TernaryPeriodPolynomials.LocalThreeBadPlaneEntry.Helpers.integrand_indicator φ
    support invariant) (s, t)
  change φ (weyl⁻¹ * lineUnipotent s t * localGoodLine) = _ at h
  rw [one] at h
  simp only [φ] at h
  by_cases member : ‖s‖ < 1 ∧ ‖t‖ < 1
  · have inside : (s, t) ∈ TernaryPeriodPolynomials.LocalThreeBadPlaneEntry.Helpers.smallBall ×ˢ
        TernaryPeriodPolynomials.LocalThreeBadPlaneEntry.Helpers.smallBall := member
    rw [Set.indicator_of_mem inside] at h
    constructor
    · intro _; exact member
    · intro _
      by_contra no
      rw [ite_eq_right no] at h
      exact zero_ne_one h
  · have outside : (s, t) ∉ TernaryPeriodPolynomials.LocalThreeBadPlaneEntry.Helpers.smallBall ×ˢ
        TernaryPeriodPolynomials.LocalThreeBadPlaneEntry.Helpers.smallBall := member
    rw [Set.indicator_of_notMem outside] at h
    constructor
    · intro yes
      rw [ite_eq_left yes] at h
      exact absurd h one_ne_zero
    · intro yes; exact absurd yes member

open Classical in
/-- The bad-plane weight of the opposite matrix is the indicator of the small `3`-adic box. -/
theorem badPlaneWeight_planeOpposite (a b : FiniteAdeles) :
    badPlaneWeight (atFinite (planeOppositeStandardMatrix a b)) =
      if ‖finiteThree a‖ < 1 ∧ ‖finiteThree b‖ < 1 then 1 else 0 := by
  unfold badPlaneWeight
  rw [adelicThreeGroup_atFinite, map_planeOpposite, ← weyl_inv_lineUnipotent_perm, permMatrix_local]
  exact if_congr (badPlaneSet_indicator (finiteThree a) (finiteThree b)) rfl rfl

open Classical in
/-- **The bad-plane entry integral at a finite matrix of the good-line class.** -/
theorem entryPlaneIntegral_bad_general (cusp : CuspidalRepresentation) (χ : RankOneCharacter) (b : ℂ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    (vec : cusp.smooth) (nonzero : vec ≠ 0) (spherical : vec.val ∈ sphericalSubspace cusp)
    (convergent : 3 < b.re) (eigenvalues : FinitePlace → ℂ)
    (eigen : ∀ place, place ≠ placeThree →
      cuspLocalPadicSphereOperator cusp place 1 vec = eigenvalues place • vec)
    (value : ℂ) (product : HasProd (fun place : {place : FinitePlace // place ≠ placeThree} =>
      cuspLocalPadicEulerFactor cusp place.val (eigenvalues place.val) b) value)
    (f : FiniteGL) (hf : goodLineSet (GeneralLinearGroup.map finiteThree f)) (y : BinaryAdelicGL) :
    entryPlaneIntegral cusp χ b (fun h => badPlaneWeight (atFinite h)) vec.val f y =
      value * (1 / 9 : ℂ) * entryRz cusp (finiteLineVector cusp χ 2 (b - 1) f vec.val) y := by
  obtain ⟨a, a', d, B, k, h01, hk, hf'⟩ := finite_goodLine_lowerTriangular f hf
  obtain ⟨u₀, u₁, h₀, h₁, hdet⟩ := unit_of_lower_triangular B h01
  have hk' := hk
  obtain ⟨κk, _, hκk⟩ := hk
  subst hf'
  have hw : ∀ p ∈ planeParabolic FiniteAdeles, ∀ g : FiniteGL,
      (fun h : FiniteGL => badPlaneWeight (atFinite h)) (p * g) = (fun h : FiniteGL => badPlaneWeight (atFinite h)) g := by
    intro p hp g
    show badPlaneWeight (atFinite (p * g)) = badPlaneWeight (atFinite g)
    rw [atFinite_mul]
    exact badPlaneWeight_parabolic (atFinite p) (atFinite_mem_plane hp) (atFinite g)
  have plane := entryPlaneIntegral_lineParabolic cusp χ b hχ (fun h => badPlaneWeight (atFinite h)) hw
    vec.property spherical a a' d B h01 (d⁻¹ * u₀) (d⁻¹ * u₁) (by rw [Units.val_mul, h₀])
    (by rw [Units.val_mul, h₁]) (permMatrix FiniteAdeles * k) y
  have base : ∀ y' : BinaryAdelicGL,
      entryPlaneIntegral cusp χ b (fun h => badPlaneWeight (atFinite h)) vec.val (permMatrix FiniteAdeles * k) y' =
        value * (1 / 9 : ℂ) * cusp.realize vec y' := by
    intro y'
    have pointwise : ∀ v : FiniteAdeles × FiniteAdeles,
        badPlaneWeight (atFinite (weyl⁻¹ * lineUnipotent v.1 v.2 * (permMatrix FiniteAdeles * k))) *
          entryRz cusp (finitePlaneVector cusp χ 0 b
            (weyl⁻¹ * lineUnipotent v.1 v.2 * (permMatrix FiniteAdeles * k)) vec.val) y' =
        badRegion.indicator (fun v => entryRz cusp (finitePlaneVector cusp χ 0 b
          (planeOppositeStandardMatrix v.1 v.2) vec.val) y') v := by
      intro v
      have e : weyl⁻¹ * lineUnipotent v.1 v.2 * (permMatrix FiniteAdeles * k) =
          planeOppositeStandardMatrix v.1 v.2 * k := by
        rw [← weyl_inv_lineUnipotent_perm]
        simp only [mul_assoc]
      rw [e, atFinite_mul, badPlaneWeight_level ⟨k, hk'⟩, badPlaneWeight_planeOpposite, ← hκk,
        finitePlaneVector_mul_integral χ 0 b hχ spherical]
      by_cases member : v ∈ badRegion
      · have member' : ‖finiteThree v.1‖ < 1 ∧ ‖finiteThree v.2‖ < 1 := member
        rw [Set.indicator_of_mem member, ite_eq_left member']
        ring
      · have member' : ¬ (‖finiteThree v.1‖ < 1 ∧ ‖finiteThree v.2‖ < 1) := member
        rw [Set.indicator_of_notMem member, ite_eq_right member']
        ring
    unfold entryPlaneIntegral
    simp_rw [pointwise]
    rw [integral_indicator badRegion_measurable]
    exact integral_planeOpposite_bad cusp χ b hχ vec nonzero spherical convergent eigenvalues eigen value
      product y'
  have hp := lineUnip_levi_mem a a' d B
  have line : entryRz cusp (finiteLineVector cusp χ 2 (b - 1)
      (lineUnipotent a a' * lineLevi d B * permMatrix FiniteAdeles * k) vec.val) y =
      finiteLineFactor χ 2 (b - 1) (lineUnipotent a a' * lineLevi d B) hp *
        cusp.realize vec (y * atFinite B) := by
    have e : lineUnipotent a a' * lineLevi d B * permMatrix FiniteAdeles * k =
        lineUnipotent a a' * lineLevi d B *
          GeneralLinearGroup.map integralEmbedding (permMatrix IntegralAdeles * κk) := by
      rw [map_mul, permMatrix_map, hκk, mul_assoc]
    rw [e, finiteLineVector_eq χ 2 (b - 1) hχ spherical hp (permMatrix IntegralAdeles * κk) rfl,
      entryRz_smul (cusp.smooth_stable _ _ vec.property), entryRz_pi vec.property,
      entryRz_of_mem vec.property, lineBlockGL_unip_levi]
  have assoc : lineUnipotent a a' * lineLevi d B * permMatrix FiniteAdeles * k =
      lineUnipotent a a' * lineLevi d B * (permMatrix FiniteAdeles * k) := mul_assoc _ _ _
  rw [assoc] at line ⊢
  rw [plane, base, line]
  have factorL : finiteLineFactor χ 2 (b - 1) (lineUnipotent a a' * lineLevi d B) hp =
      χ.toMonoidHom (Norm.finiteAdeleUnit d) * normPower (Norm.finiteAdeleUnit d) 2 *
        normPower (Norm.finiteAdeleUnit (u₀ * u₁)) (b - 1) := by
    unfold finiteLineFactor
    rw [lineCornerUnit_unip_levi, lineBlockGL_unip_levi, hdet]
  have factorP : finitePlaneFactor χ 0 b (planeLevi B d) (planeLevi_mem B d) =
      χ.toMonoidHom (Norm.finiteAdeleUnit d) * normPower (Norm.finiteAdeleUnit d) 0 *
        normPower (Norm.finiteAdeleUnit (u₀ * u₁)) b := by
    rw [finitePlaneFactor_planeLevi', hdet]
  rw [factorL, factorP, Complex.real_smul]
  have scalar := scalar_identity χ b d u₀ u₁
  linear_combination (value * (1 / 9 : ℂ) * cusp.realize vec (y * atFinite B)) * scalar

open Classical in
/-- Along the radical the bad-plane weight of a good-line matrix is the indicator of a measurable set. -/
theorem badPlaneWeight_radical_measurable (f : FiniteGL)
    (hf : goodLineSet (GeneralLinearGroup.map finiteThree f)) :
    Measurable (fun v : FiniteAdeles × FiniteAdeles =>
      badPlaneWeight (atFinite (weyl⁻¹ * lineUnipotent v.1 v.2 * f))) := by
  obtain ⟨a, a', d, B, k, h01, hk, hf'⟩ := finite_goodLine_lowerTriangular f hf
  obtain ⟨u₀, u₁, h₀, h₁, hdet⟩ := unit_of_lower_triangular B h01
  have hk' := hk
  obtain ⟨κk, _, hκk⟩ := hk
  subst hf'
  let α₁ : FiniteAdelesˣ := d⁻¹ * u₀
  let α₃ : FiniteAdelesˣ := d⁻¹ * u₁
  have e₁ : α₁.val = (d⁻¹).val * B.val 0 0 := by simp only [α₁, Units.val_mul, h₀]
  have e₃ : α₃.val = (d⁻¹).val * B.val 1 1 := by simp only [α₃, Units.val_mul, h₁]
  let T := finiteAffine α₁ α₃ ((d⁻¹).val * B.val 1 0) ((d⁻¹).val * (a * B.val 0 0 + a' * B.val 1 0))
    ((d⁻¹).val * (a' * B.val 1 1))
  have pointwise : ∀ v : FiniteAdeles × FiniteAdeles,
      badPlaneWeight (atFinite (weyl⁻¹ * lineUnipotent v.1 v.2 *
        (lineUnipotent a a' * lineLevi d B * permMatrix FiniteAdeles * k))) =
      if T v ∈ badRegion then 1 else 0 := by
    intro v
    have assoc : lineUnipotent a a' * lineLevi d B * permMatrix FiniteAdeles * k =
        lineUnipotent a a' * lineLevi d B * (permMatrix FiniteAdeles * k) := mul_assoc _ _ _
    rw [assoc, radical_levi_identity v a a' d B h01 α₁ α₃ e₁ e₃ (permMatrix FiniteAdeles * k), atFinite_mul,
      badPlaneWeight_parabolic _ (atFinite_mem_plane (planeLevi_mem B d))]
    have e : weyl⁻¹ * lineUnipotent (T v).1 (T v).2 * (permMatrix FiniteAdeles * k) =
        planeOppositeStandardMatrix (T v).1 (T v).2 * k := by
      rw [← weyl_inv_lineUnipotent_perm]
      simp only [mul_assoc]
    rw [e, atFinite_mul, badPlaneWeight_level ⟨k, hk'⟩, badPlaneWeight_planeOpposite]
    exact if_congr Iff.rfl rfl rfl
  have measurable : Measurable (fun v : FiniteAdeles × FiniteAdeles => if T v ∈ badRegion then (1 : ℂ) else 0) :=
    Measurable.ite (badRegion_measurable.preimage T.measurable) measurable_const measurable_const
  rw [funext pointwise]
  exact measurable

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
