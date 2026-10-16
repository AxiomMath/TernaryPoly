module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.ConditionalFlagExact

@[expose] public section


/-!
# `FlagExact` from rational translate invariance (line sources)

Line-side analogue of `ConditionalFlagExact`. The translated flag evaluations are along the unipotent of the `GL₂` block of the line Levi. All analytic and automorphic
input is discharged; what remains is the purely cohomological hypothesis
`translateInvariance`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.GraphPieces
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.FlagExactness

theorem lineLevi_binaryUnipotent_zero :
    lineLevi 1 (binaryUnipotent (((0 : ℝ), (0 : FiniteAdeles)) : Adeles)) = 1 := by
  have hz : (((0 : ℝ), (0 : FiniteAdeles)) : Adeles) = 0 := rfl
  rw [hz, binaryUnipotent_zero']
  exact lineLevi_one_one

/-- The line translated flag evaluation. -/
def lineTranslate {degree : ℕ} (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (q : RationalGL3) (t : ℝ) (x : Fin 3 → RealGL3) : HomogeneousPoly degree :=
  source x (lineLevi 1 (binaryUnipotent ((t, 0) : Adeles)) * rationalGroup q⁻¹)

theorem lineTranslate_zero {degree : ℕ} (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (q : RationalGL3) (x : Fin 3 → RealGL3) :
    lineTranslate source q 0 x = source x (rationalGroup q⁻¹) := by
  rw [lineTranslate, lineLevi_binaryUnipotent_zero, one_mul]

theorem lineTranslate_coeff_continuous {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .line source) (q : RationalGL3) (x : Fin 3 → RealGL3)
    (monomial : Fin 3 →₀ ℕ) :
    Continuous (fun t : ℝ => (lineTranslate source q t x).val.coeff monomial) :=
  (induced_continuous (isSource.1 x monomial)).comp ((lineLeviUnipotent_continuous.comp
    (continuous_id.prodMk continuous_const)).mul continuous_const)

theorem lineTranslate_functional_continuous {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .line source) (q : RationalGL3) (x : Fin 3 → RealGL3)
    (functional : HomogeneousPoly degree →ₗ[ℂ] ℂ) :
    Continuous (fun t : ℝ => functional (lineTranslate source q t x)) := by
  obtain ⟨weight, hweight⟩ := homogeneous_functional_eq_sum degree functional
  simp_rw [hweight]
  exact continuous_finsetSum _ (fun s _ =>
    (lineTranslate_coeff_continuous data source isSource q x s.val).mul continuous_const)

/-- Vanishing averages of functionals of line translates, in both directions. -/
theorem lineTranslate_functional_average {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .line source) (q : RationalGL3) (M : ℕ)
    (hper : ∀ (t : ℝ) (vertices : Fin 3 → RealGL3),
      source vertices (lineLevi 1 (binaryUnipotent (((t + M : ℝ), 0) : Adeles)) * rationalGroup q⁻¹) =
        source vertices (lineLevi 1 (binaryUnipotent ((t, 0) : Adeles)) * rationalGroup q⁻¹))
    (hint : ∀ (vertices : Fin 3 → RealGL3) (monomial : Fin 3 →₀ ℕ),
      (∫ t in Set.Ico (0 : ℝ) 1, (source vertices (lineLevi 1 (binaryUnipotent ((((M : ℝ) * t), 0) : Adeles)) *
          rationalGroup q⁻¹)).val.coeff monomial) = 0)
    (x : Fin 3 → RealGL3) (functional : HomogeneousPoly degree →ₗ[ℂ] ℂ) :
    (∫ t in Set.Ico (0 : ℝ) 1, functional (lineTranslate source q ((M : ℝ) * t) x)) = 0 ∧
    (∫ t in Set.Ico (0 : ℝ) 1, functional (lineTranslate source q (-((M : ℝ) * t)) x)) = 0 := by
  obtain ⟨weight, hweight⟩ := homogeneous_functional_eq_sum degree functional
  have hcoeff : ∀ s : degreeExponents (Fin 3) degree,
      Continuous (fun t : ℝ => (lineTranslate source q ((M : ℝ) * t) x).val.coeff s.val) :=
    fun s => (lineTranslate_coeff_continuous data source isSource q x s.val).comp
      (continuous_const.mul continuous_id)
  have first : (∫ t in Set.Ico (0 : ℝ) 1, functional (lineTranslate source q ((M : ℝ) * t) x)) = 0 := by
    simp_rw [hweight]
    rw [integral_finsetSum]
    · apply Finset.sum_eq_zero
      intro s _
      rw [integral_mul_const]
      have := hint x s.val
      simp only [lineTranslate] at this ⊢
      rw [this, zero_mul]
    · intro s _
      exact (((hcoeff s).mul continuous_const).integrableOn_Icc).mono_set Set.Ico_subset_Icc_self
  refine ⟨first, ?_⟩
  have reflect := integral_reflect_periodic (fun s => functional (lineTranslate source q s x)) M
    (fun s => by simp only [lineTranslate]; rw [hper s x])
  rw [reflect, first]

/-- The symmetrized translate `½ (F_u + F_{-u})` on an inhomogeneous pair. -/
def lineSymmetricTranslate {degree : ℕ} (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (q : RationalGL3) (u : ℝ) (pair : edgeStabilizer q × edgeStabilizer q) : HomogeneousPoly degree :=
  (1 / 2 : ℂ) • (lineTranslate source q u (pairVertices pair.1.val pair.2.val) +
    lineTranslate source q (-u) (pairVertices pair.1.val pair.2.val))

theorem functional_lineSymmetricTranslate {degree : ℕ}
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree) (q : RationalGL3) (u : ℝ)
    (pair : edgeStabilizer q × edgeStabilizer q) (functional : HomogeneousPoly degree →ₗ[ℂ] ℂ) :
    functional (lineSymmetricTranslate source q u pair) =
      (1 / 2 : ℂ) * (functional (lineTranslate source q u (pairVertices pair.1.val pair.2.val)) +
        functional (lineTranslate source q (-u) (pairVertices pair.1.val pair.2.val))) := by
  rw [lineSymmetricTranslate, map_smul, map_add, smul_eq_mul]

/-- **`FlagExact` from rational translate invariance.** All analytic and automorphic
input (continuity, cuspidal averages) is discharged here; the hypothesis is purely
cohomological. -/
theorem line_flagExact_of_translateInvariance {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .line source) (q : RationalGL3)
    (translateInvariance : ∀ r : ℚ, ∃ b : edgeStabilizer q → HomogeneousPoly degree,
      ∀ γ₁ γ₂ : edgeStabilizer q,
        rationalCoefficientComponent degree data.chi γ₁.val (b γ₂) - b (γ₁ * γ₂) + b γ₁ =
          lineSymmetricTranslate source q (r : ℝ) (γ₁, γ₂) -
          lineTranslate source q 0 (pairVertices γ₁.val γ₂.val)) :
    EndpointReduction.FlagExact data source q := by
  have : FiniteDimensional ℂ (HomogeneousPoly degree) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 3) ℂ degree)
  rw [flagExact_iff_H2_zero data .line source isSource q, groupCohomology.H2π_eq_zero_iff]
  set A := SphericalDetection.Helpers.subgroupCoefficientRep (edgeStabilizer q)
    (rationalCoefficientComponent degree data.chi)
  have : FiniteDimensional ℂ A := ‹FiniteDimensional ℂ (HomogeneousPoly degree)›
  set z := SphericalDetection.Helpers.ambientCocycleToGroup (edgeStabilizer q)
    (rationalCoefficientComponent degree data.chi) (flagCocycle data .line source isSource q)
  have hz : ∀ pair : edgeStabilizer q × edgeStabilizer q,
      z pair = lineTranslate source q 0 (pairVertices pair.1.val pair.2.val) := by
    intro pair
    rw [lineTranslate_zero]
    rfl
  obtain ⟨M, hM, hper, hint⟩ := line_flag_averaging_data data source isSource q
  let G : ℝ → (edgeStabilizer q × edgeStabilizer q → A) := fun u pair =>
    lineSymmetricTranslate source q u pair
  have hG : ∀ u pair, G u pair = lineSymmetricTranslate source q u pair := fun _ _ => rfl
  have hterm : ∀ (u : ℝ) (pair : edgeStabilizer q × edgeStabilizer q) (functional : Module.Dual ℂ A),
      functional (G u pair) =
        (1 / 2 : ℂ) * (functional (lineTranslate source q u (pairVertices pair.1.val pair.2.val)) +
          functional (lineTranslate source q (-u) (pairVertices pair.1.val pair.2.val))) :=
    fun u pair functional => by rw [hG]; exact functional_lineSymmetricTranslate source q u pair functional
  have key : ∀ chain : DualChains₂ A, dualBoundary A chain = 0 → pairing₂ A z chain = 0 := by
    intro chain hcycle
    have hrat : ∀ r : ℚ, pairing₂ A (G r) chain = pairing₂ A z chain := by
      intro r
      obtain ⟨b, hb⟩ := translateInvariance r
      let b' : edgeStabilizer q → A := b
      have hfun : G r = (groupCohomology.d₁₂ A).hom b' + z := by
        funext pair
        rw [Pi.add_apply, groupCohomology.d₁₂_hom_apply, hz, hG]
        have hpair := hb pair.1 pair.2
        rw [eq_sub_iff_add_eq] at hpair
        exact hpair.symm
      rw [hfun, pairing₂_add, pairing₂_d₁₂, hcycle, map_zero, zero_add]
    have hcont : Continuous (fun u : ℝ => pairing₂ A (G u) chain) := by
      simp_rw [pairing₂_eq_sum, hterm]
      apply continuous_finsetSum
      intro pair _
      have h1 := lineTranslate_functional_continuous data source isSource q
        (pairVertices pair.1.val pair.2.val) (chain pair)
      exact continuous_const.mul (h1.add (h1.comp continuous_neg))
    have hall : ∀ u : ℝ, pairing₂ A (G u) chain = pairing₂ A z chain := by
      have heq := Continuous.ext_on Rat.denseRange_cast hcont continuous_const
        (by rintro _ ⟨r, rfl⟩; exact hrat r)
      exact fun u => congrFun heq u
    have havg : (∫ t in Set.Ico (0 : ℝ) 1, pairing₂ A (G ((M : ℝ) * t)) chain) = 0 := by
      simp_rw [pairing₂_eq_sum, hterm]
      have h1 : ∀ pair : edgeStabilizer q × edgeStabilizer q, Continuous (fun t : ℝ =>
          chain pair (lineTranslate source q t (pairVertices pair.1.val pair.2.val))) :=
        fun pair => lineTranslate_functional_continuous data source isSource q
          (pairVertices pair.1.val pair.2.val) (chain pair)
      rw [integral_finsetSum]
      · apply Finset.sum_eq_zero
        intro pair _
        obtain ⟨first, second⟩ := lineTranslate_functional_average data source isSource q M hper hint
          (pairVertices pair.1.val pair.2.val) (chain pair)
        have e1 : (∫ a in Set.Ico (0 : ℝ) 1, (chain pair)
            (lineTranslate source q ((M : ℝ) * a) (pairVertices pair.1.val pair.2.val))) = 0 := first
        have e2 : (∫ a in Set.Ico (0 : ℝ) 1, (chain pair)
            (lineTranslate source q (-((M : ℝ) * a)) (pairVertices pair.1.val pair.2.val))) = 0 := second
        rw [integral_const_mul, integral_add, e1, e2, add_zero, mul_zero]
        · exact (((h1 pair).comp (continuous_const.mul continuous_id)).integrableOn_Icc).mono_set
            Set.Ico_subset_Icc_self
        · exact (((h1 pair).comp ((continuous_const.mul continuous_id).neg)).integrableOn_Icc).mono_set
            Set.Ico_subset_Icc_self
      · intro pair _
        exact ((continuous_const.mul (((h1 pair).comp (continuous_const.mul continuous_id)).add
          ((h1 pair).comp ((continuous_const.mul continuous_id).neg)))).integrableOn_Icc).mono_set
            Set.Ico_subset_Icc_self
    have hconst : (∫ t in Set.Ico (0 : ℝ) 1, pairing₂ A (G ((M : ℝ) * t)) chain) =
        pairing₂ A z chain := by
      simp_rw [hall]
      simp
    rw [← hconst, havg]
  obtain ⟨b, hb⟩ := mem_coboundaries₂_of_pairing A z key
  exact ⟨b, hb⟩

end TernaryPeriodPolynomials.FlagExactness
