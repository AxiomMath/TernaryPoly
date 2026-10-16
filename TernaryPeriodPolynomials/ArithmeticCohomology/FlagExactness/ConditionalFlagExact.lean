module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.GroupCohomology
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.AveragingData
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.PairingCriterion
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.HomogeneousFunctionals
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.BinaryCuspRestriction

@[expose] public section


/-!
# `FlagExact` from rational translate invariance (plane sources)

Let `c` be a plane source cocycle and `q` a rational flag. Consider the symmetrized
translated evaluations `G_u = ½ (F_u + F_{-u})`, where
`F_u(x) = c(x)(n(u)·q⁻¹)`. Suppose that for every rational `r` the stabilizer
cocycle of `G_r` is cohomologous to that of `F_0`. Then `FlagExact` holds at `q`.

This removes all analytic and automorphic input from `FlagExact`:
* pairing with finite 2-cycles (`mem_coboundaries₂_of_pairing`);
* continuity of the pairings in `u`, plus density of `ℚ`;
* vanishing of the averages, by cuspidality (`flag_averaging_data`).

What is left, the hypothesis `translateInvariance`, is a purely cohomological
statement about rational Levi-unipotent translates. Its expected proof is the algebraic
(Mal'cev/Nomizu) triviality of the unipotent conjugation action.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.GraphPieces
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.FlagExactness

/-- The real vertices `(1, γ₁, γ₁γ₂)` of an inhomogeneous pair. -/
def pairVertices (γ₁ γ₂ : RationalGL3) : Fin 3 → RealGL3 :=
  fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (![1, γ₁, γ₁ * γ₂] i)

/-- The plane translated flag evaluation. -/
def planeTranslate {degree : ℕ} (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (q : RationalGL3) (t : ℝ) (x : Fin 3 → RealGL3) : HomogeneousPoly degree :=
  source x (planeLevi (binaryUnipotent ((t, 0) : Adeles)) 1 * rationalGroup q⁻¹)

theorem planeLevi_binaryUnipotent_zero :
    planeLevi (binaryUnipotent (((0 : ℝ), (0 : FiniteAdeles)) : Adeles)) 1 = 1 := by
  have hz : (((0 : ℝ), (0 : FiniteAdeles)) : Adeles) = 0 := rfl
  rw [hz, binaryUnipotent_zero']
  exact (planeLeviHom Adeles).map_one

theorem planeTranslate_zero {degree : ℕ} (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (q : RationalGL3) (x : Fin 3 → RealGL3) :
    planeTranslate source q 0 x = source x (rationalGroup q⁻¹) := by
  rw [planeTranslate, planeLevi_binaryUnipotent_zero, one_mul]

theorem planeTranslate_coeff_continuous {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .plane source) (q : RationalGL3) (x : Fin 3 → RealGL3)
    (monomial : Fin 3 →₀ ℕ) :
    Continuous (fun t : ℝ => (planeTranslate source q t x).val.coeff monomial) :=
  (induced_continuous (isSource.1 x monomial)).comp ((planeLeviUnipotent_continuous.comp
    (continuous_id.prodMk continuous_const)).mul continuous_const)

theorem planeTranslate_functional_continuous {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .plane source) (q : RationalGL3) (x : Fin 3 → RealGL3)
    (functional : HomogeneousPoly degree →ₗ[ℂ] ℂ) :
    Continuous (fun t : ℝ => functional (planeTranslate source q t x)) := by
  obtain ⟨weight, hweight⟩ := homogeneous_functional_eq_sum degree functional
  simp_rw [hweight]
  exact continuous_finsetSum _ (fun s _ =>
    (planeTranslate_coeff_continuous data source isSource q x s.val).mul continuous_const)

/-- Reflection for integrals of periodic continuous functions. -/
theorem integral_reflect_periodic (h : ℝ → ℂ) (M : ℝ)
    (periodic : ∀ s, h (s + M) = h s) :
    (∫ t in Set.Ico (0 : ℝ) 1, h (-(M * t))) = ∫ t in Set.Ico (0 : ℝ) 1, h (M * t) := by
  have hshift : ∀ t, h (-(M * t)) = h (M * (1 - t)) := by
    intro t
    rw [← periodic (-(M * t))]
    congr 1
    ring
  simp_rw [hshift]
  rw [integral_Ico_eq_integral_Ioc, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one, ← intervalIntegral.integral_of_le zero_le_one]
  rw [intervalIntegral.integral_comp_sub_left (fun t => h (M * t)) 1]
  norm_num

theorem pairing₂_add {G : Type} [Group G] (A : Rep ℂ G) (f g : G × G → A) (chain : DualChains₂ A) :
    pairing₂ A (f + g) chain = pairing₂ A f chain + pairing₂ A g chain := by
  induction chain using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
    rw [map_add, map_add, map_add, ha, hb]
    ring
  | single pair μ => rw [pairing₂_single, pairing₂_single, pairing₂_single, Pi.add_apply, map_add]

theorem pairing₂_eq_sum {G : Type} [Group G] (A : Rep ℂ G) (f : G × G → A) (chain : DualChains₂ A) :
    pairing₂ A f chain = ∑ pair ∈ chain.support, chain pair (f pair) := by
  rw [pairing₂, Finsupp.lsum_apply, Finsupp.sum]
  rfl

/-- Vanishing averages of functionals of plane translates, in both directions. -/
theorem planeTranslate_functional_average {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .plane source) (q : RationalGL3) (M : ℕ)
    (hper : ∀ (t : ℝ) (vertices : Fin 3 → RealGL3),
      source vertices (planeLevi (binaryUnipotent (((t + M : ℝ), 0) : Adeles)) 1 * rationalGroup q⁻¹) =
        source vertices (planeLevi (binaryUnipotent ((t, 0) : Adeles)) 1 * rationalGroup q⁻¹))
    (hint : ∀ (vertices : Fin 3 → RealGL3) (monomial : Fin 3 →₀ ℕ),
      (∫ t in Set.Ico (0 : ℝ) 1, (source vertices (planeLevi (binaryUnipotent ((((M : ℝ) * t), 0) : Adeles)) 1 *
          rationalGroup q⁻¹)).val.coeff monomial) = 0)
    (x : Fin 3 → RealGL3) (functional : HomogeneousPoly degree →ₗ[ℂ] ℂ) :
    (∫ t in Set.Ico (0 : ℝ) 1, functional (planeTranslate source q ((M : ℝ) * t) x)) = 0 ∧
    (∫ t in Set.Ico (0 : ℝ) 1, functional (planeTranslate source q (-((M : ℝ) * t)) x)) = 0 := by
  obtain ⟨weight, hweight⟩ := homogeneous_functional_eq_sum degree functional
  have hcoeff : ∀ s : degreeExponents (Fin 3) degree,
      Continuous (fun t : ℝ => (planeTranslate source q ((M : ℝ) * t) x).val.coeff s.val) :=
    fun s => (planeTranslate_coeff_continuous data source isSource q x s.val).comp
      (continuous_const.mul continuous_id)
  have first : (∫ t in Set.Ico (0 : ℝ) 1, functional (planeTranslate source q ((M : ℝ) * t) x)) = 0 := by
    simp_rw [hweight]
    rw [integral_finsetSum]
    · apply Finset.sum_eq_zero
      intro s _
      rw [integral_mul_const]
      have := hint x s.val
      simp only [planeTranslate] at this ⊢
      rw [this, zero_mul]
    · intro s _
      exact (((hcoeff s).mul continuous_const).integrableOn_Icc).mono_set Set.Ico_subset_Icc_self
  refine ⟨first, ?_⟩
  have reflect := integral_reflect_periodic (fun s => functional (planeTranslate source q s x)) M
    (fun s => by simp only [planeTranslate]; rw [hper s x])
  rw [reflect, first]

/-- The symmetrized translate `½ (F_u + F_{-u})` on an inhomogeneous pair. -/
def symmetricTranslate {degree : ℕ} (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (q : RationalGL3) (u : ℝ) (pair : edgeStabilizer q × edgeStabilizer q) : HomogeneousPoly degree :=
  (1 / 2 : ℂ) • (planeTranslate source q u (pairVertices pair.1.val pair.2.val) +
    planeTranslate source q (-u) (pairVertices pair.1.val pair.2.val))

theorem functional_symmetricTranslate {degree : ℕ}
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree) (q : RationalGL3) (u : ℝ)
    (pair : edgeStabilizer q × edgeStabilizer q) (functional : HomogeneousPoly degree →ₗ[ℂ] ℂ) :
    functional (symmetricTranslate source q u pair) =
      (1 / 2 : ℂ) * (functional (planeTranslate source q u (pairVertices pair.1.val pair.2.val)) +
        functional (planeTranslate source q (-u) (pairVertices pair.1.val pair.2.val))) := by
  rw [symmetricTranslate, map_smul, map_add, smul_eq_mul]

/-- **`FlagExact` from rational translate invariance.** All analytic and automorphic
input (continuity, cuspidal averages) is discharged here; the hypothesis is purely
cohomological. -/
theorem flagExact_of_translateInvariance {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .plane source) (q : RationalGL3)
    (translateInvariance : ∀ r : ℚ, ∃ b : edgeStabilizer q → HomogeneousPoly degree,
      ∀ γ₁ γ₂ : edgeStabilizer q,
        rationalCoefficientComponent degree data.chi γ₁.val (b γ₂) - b (γ₁ * γ₂) + b γ₁ =
          symmetricTranslate source q (r : ℝ) (γ₁, γ₂) -
          planeTranslate source q 0 (pairVertices γ₁.val γ₂.val)) :
    EndpointReduction.FlagExact data source q := by
  have : FiniteDimensional ℂ (HomogeneousPoly degree) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 3) ℂ degree)
  rw [flagExact_iff_H2_zero data .plane source isSource q, groupCohomology.H2π_eq_zero_iff]
  set A := SphericalDetection.Helpers.subgroupCoefficientRep (edgeStabilizer q)
    (rationalCoefficientComponent degree data.chi)
  have : FiniteDimensional ℂ A := ‹FiniteDimensional ℂ (HomogeneousPoly degree)›
  set z := SphericalDetection.Helpers.ambientCocycleToGroup (edgeStabilizer q)
    (rationalCoefficientComponent degree data.chi) (flagCocycle data .plane source isSource q)
  have hz : ∀ pair : edgeStabilizer q × edgeStabilizer q,
      z pair = planeTranslate source q 0 (pairVertices pair.1.val pair.2.val) := by
    intro pair
    rw [planeTranslate_zero]
    rfl
  obtain ⟨M, hM, hper, hint⟩ := flag_averaging_data data source isSource q
  let G : ℝ → (edgeStabilizer q × edgeStabilizer q → A) := fun u pair =>
    symmetricTranslate source q u pair
  have hG : ∀ u pair, G u pair = symmetricTranslate source q u pair := fun _ _ => rfl
  have hterm : ∀ (u : ℝ) (pair : edgeStabilizer q × edgeStabilizer q) (functional : Module.Dual ℂ A),
      functional (G u pair) =
        (1 / 2 : ℂ) * (functional (planeTranslate source q u (pairVertices pair.1.val pair.2.val)) +
          functional (planeTranslate source q (-u) (pairVertices pair.1.val pair.2.val))) :=
    fun u pair functional => by rw [hG]; exact functional_symmetricTranslate source q u pair functional
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
      have h1 := planeTranslate_functional_continuous data source isSource q
        (pairVertices pair.1.val pair.2.val) (chain pair)
      exact continuous_const.mul (h1.add (h1.comp continuous_neg))
    have hall : ∀ u : ℝ, pairing₂ A (G u) chain = pairing₂ A z chain := by
      have heq := Continuous.ext_on Rat.denseRange_cast hcont continuous_const
        (by rintro _ ⟨r, rfl⟩; exact hrat r)
      exact fun u => congrFun heq u
    have havg : (∫ t in Set.Ico (0 : ℝ) 1, pairing₂ A (G ((M : ℝ) * t)) chain) = 0 := by
      simp_rw [pairing₂_eq_sum, hterm]
      have h1 : ∀ pair : edgeStabilizer q × edgeStabilizer q, Continuous (fun t : ℝ =>
          chain pair (planeTranslate source q t (pairVertices pair.1.val pair.2.val))) :=
        fun pair => planeTranslate_functional_continuous data source isSource q
          (pairVertices pair.1.val pair.2.val) (chain pair)
      rw [integral_finsetSum]
      · apply Finset.sum_eq_zero
        intro pair _
        obtain ⟨first, second⟩ := planeTranslate_functional_average data source isSource q M hper hint
          (pairVertices pair.1.val pair.2.val) (chain pair)
        have e1 : (∫ a in Set.Ico (0 : ℝ) 1, (chain pair)
            (planeTranslate source q ((M : ℝ) * a) (pairVertices pair.1.val pair.2.val))) = 0 := first
        have e2 : (∫ a in Set.Ico (0 : ℝ) 1, (chain pair)
            (planeTranslate source q (-((M : ℝ) * a)) (pairVertices pair.1.val pair.2.val))) = 0 := second
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
