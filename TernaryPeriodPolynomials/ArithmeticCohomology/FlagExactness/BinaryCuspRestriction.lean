module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.BinaryRealConstantTerm
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.SectionContinuity

@[expose] public section


/-!
# Cuspidal binary cocycles restrict trivially to the cusp, without regularity

Let `c` be a binary cocycle with cuspidal values, as in `Cohomological`. For a suitable
`M > 0`, every functional `λ` on the coefficient module that is invariant under the
real unipotent group kills the cusp value `c(n(M))(1)`. This is the vanishing
obstruction in `H¹(N(Mℤ), V)`.

The proof uses no continuity of `realize` in the vector variable.
* The cocycle identity for the commuting elements `n(u)`, `n(M)` gives algebraically
  that `u ↦ λ(c(n(M))(n(u)_∞))` is constant.
* Cuspidality of the single cusp function `λ ∘ c(n(M))` then forces the constant to be
  zero. This uses only an integral in the group argument.

This technique avoids the vertex-regularity gap noted for `FlagExact`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.FlagExactness

theorem binaryUnipotent_zero' {R : Type*} [CommRing R] : binaryUnipotent (0 : R) = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [binaryUnipotent]

theorem binaryUnipotent_neg' {R : Type*} [CommRing R] (a : R) :
    binaryUnipotent (-a) = (binaryUnipotent a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← binaryUnipotent_add, neg_add_cancel, binaryUnipotent_zero']

theorem binaryUnipotent_finite_continuous :
    Continuous (fun w : FiniteAdeles => binaryUnipotent w) := by
  apply Units.continuous_iff.mpr
  constructor <;> apply continuous_pi <;> intro row <;> apply continuous_pi <;> intro column <;>
    fin_cases row <;> fin_cases column <;> simp [binaryUnipotent] <;> fun_prop

/-- Integral adeles whose finite unipotent lies in `U`. -/
def unipotentLevelSubgroup (U : Subgroup BinaryFiniteGL) : AddSubgroup IntegralAdeles where
  carrier := {z | binaryUnipotent (integralEmbedding z) ∈ U}
  zero_mem' := by
    change binaryUnipotent (integralEmbedding 0) ∈ U
    rw [map_zero, binaryUnipotent_zero']
    exact U.one_mem
  add_mem' := by
    intro a b ha hb
    change binaryUnipotent (integralEmbedding (a + b)) ∈ U
    rw [map_add, binaryUnipotent_add]
    exact U.mul_mem ha hb
  neg_mem' := by
    intro a ha
    change binaryUnipotent (integralEmbedding (-a)) ∈ U
    rw [map_neg, binaryUnipotent_neg']
    exact U.inv_mem ha

/-- An open subgroup of `GL₂(𝔸_f)` contains the finite unipotents of some `M·Ẑ`. -/
theorem exists_unipotent_level (U : Subgroup BinaryFiniteGL) (hU : IsOpen (U : Set BinaryFiniteGL)) :
    ∃ M : ℕ, 0 < M ∧ ∀ z : IntegralAdeles,
      binaryUnipotent ((M : FiniteAdeles) * integralEmbedding z) ∈ U := by
  set H := unipotentLevelSubgroup U
  have hopen : IsOpen (H : Set IntegralAdeles) :=
    hU.preimage (binaryUnipotent_finite_continuous.comp integralEmbedding_isOpenEmbedding.continuous)
  have : Finite (IntegralAdeles ⧸ H) := AddSubgroup.quotient_finite_of_isOpen H hopen
  refine ⟨H.index, Nat.pos_of_ne_zero AddSubgroup.index_ne_zero_of_finite, ?_⟩
  intro z
  have hmem := H.nsmul_index_mem z
  have heq : integralEmbedding (H.index • z) = (H.index : FiniteAdeles) * integralEmbedding z := by
    rw [map_nsmul, nsmul_eq_mul]
  rw [← heq]
  exact hmem

/-- Cuspidal polynomial values are invariant under left rational translation. -/
theorem binaryValues_leftRational {D : CuspidalRepresentation} {n : ℕ}
    {f : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)} (values : BinaryValues D n f)
    (γ : BinaryRationalGL) (x : BinaryAdelicGL) :
    f (GeneralLinearGroup.map rationalAdele γ * x) = f x := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  obtain ⟨vector, hvector⟩ := values monomial
  have invariance := D.leftRational γ vector x
  rw [hvector] at invariance
  exact invariance

theorem atInfinity_binaryUnipotent (u : ℝ) :
    atInfinity (binaryUnipotent u) = binaryUnipotent ((u, (0 : FiniteAdeles)) : Adeles) := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  apply Prod.ext <;> fin_cases i <;> fin_cases j <;>
    simp [atInfinity, combineGL, pairMatrix, binaryUnipotent]

theorem atFinite_binaryUnipotent (w : FiniteAdeles) :
    atFinite (binaryUnipotent w) = binaryUnipotent (((0 : ℝ), w) : Adeles) := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  apply Prod.ext <;> fin_cases i <;> fin_cases j <;>
    simp [atFinite, combineGL, pairMatrix, binaryUnipotent]

theorem atInfinity_binaryUnipotent_rational (r : ℚ) :
    atInfinity (binaryUnipotent (r : ℝ)) =
      GeneralLinearGroup.map rationalAdele (binaryUnipotent r) *
        atFinite (binaryUnipotent (-(algebraMap ℚ FiniteAdeles r))) := by
  rw [map_binaryUnipotent, atInfinity_binaryUnipotent, atFinite_binaryUnipotent,
    ← binaryUnipotent_add]
  congr 1
  apply Prod.ext
  · change (r : ℝ) = (algebraMap ℚ ℝ r) + 0
    simp
  · change (0 : FiniteAdeles) = algebraMap ℚ FiniteAdeles r + -(algebraMap ℚ FiniteAdeles r)
    simp

theorem det_atInfinity_binaryUnipotent (u : ℝ) :
    GeneralLinearGroup.det (atInfinity (binaryUnipotent u)) = 1 := by
  rw [atInfinity_binaryUnipotent, det_binaryUnipotent]

/-- Monomials of degree `k` in two variables. -/
def degreeMonomials (k : ℕ) : Finset (Fin 2 →₀ ℕ) :=
  (Finset.range (k + 1)).image (fun a => Finsupp.single 0 a + Finsupp.single 1 (k - a))

theorem mem_degreeMonomials {k : ℕ} {d : Fin 2 →₀ ℕ} (h : d.degree = k) : d ∈ degreeMonomials k := by
  have hsum : d 0 + d 1 = k := by rw [← h, Finsupp.degree_eq_sum, Fin.sum_univ_two]
  simp only [degreeMonomials, Finset.mem_image, Finset.mem_range]
  refine ⟨d 0, by omega, ?_⟩
  ext i
  fin_cases i
  · simp
  · simp only [Fin.mk_one, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
    simp
    omega

/-- The coefficient vector of a binary homogeneous polynomial. -/
def coefficientVector (k : ℕ) :
    Binary.HomogeneousPoly k →ₗ[ℂ] (degreeMonomials k → ℂ) where
  toFun p := fun s => p.val.coeff s.val
  map_add' p q := by
    funext s
    simp
  map_smul' a p := by
    funext s
    simp

theorem coefficientVector_injective (k : ℕ) : Function.Injective (coefficientVector k) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro p hp
  apply Subtype.ext
  apply MvPolynomial.ext
  intro d
  have homogeneous : p.val.IsHomogeneous k := (MvPolynomial.mem_homogeneousSubmodule k p.val).mp p.property
  by_cases hd : d.degree = k
  · exact congrFun hp ⟨d, mem_degreeMonomials hd⟩
  · rw [homogeneous.coeff_eq_zero hd]
    rfl

/-- Every linear functional on binary homogeneous polynomials is a finite combination of
coefficients. -/
theorem functional_eq_sum_coeff {k : ℕ} (functional : Binary.HomogeneousPoly k →ₗ[ℂ] ℂ) :
    ∃ weight : degreeMonomials k → ℂ, ∀ p : Binary.HomogeneousPoly k,
      functional p = ∑ s, p.val.coeff s.val * weight s := by
  obtain ⟨inverse, hinverse⟩ := LinearMap.exists_leftInverse_of_injective (coefficientVector k)
    (LinearMap.ker_eq_bot.mpr (coefficientVector_injective k))
  refine ⟨fun s => (functional.comp inverse) (fun j => if s = j then 1 else 0), fun p => ?_⟩
  have hp : functional p = (functional.comp inverse) (coefficientVector k p) := by
    rw [LinearMap.comp_apply, ← LinearMap.comp_apply inverse, hinverse, LinearMap.id_apply]
  rw [hp, LinearMap.pi_apply_eq_sum_univ]
  rfl

theorem binaryUnipotent_real_continuous : Continuous (fun u : ℝ => binaryUnipotent u) := by
  apply Units.continuous_iff.mpr
  constructor <;> apply continuous_pi <;> intro row <;> apply continuous_pi <;> intro column <;>
    fin_cases row <;> fin_cases column <;> simp [binaryUnipotent] <;> fun_prop

/-- Real constant term of one cusp function along `n(M t)`, given `M·Ẑ`-invariance. -/
theorem cusp_real_constant_term (D : CuspidalRepresentation) (vector : D.smooth) (M : ℕ) (hM : 0 < M)
    (finiteInvariant : ∀ (x : BinaryAdelicGL) (z : IntegralAdeles),
      D.realize vector (x * atFinite (binaryUnipotent ((M : FiniteAdeles) * integralEmbedding z))) =
        D.realize vector x) :
    Continuous (fun t : ℝ => D.realize vector (atInfinity (binaryUnipotent ((M : ℝ) * t)))) ∧
    (∫ t in Set.Ico (0 : ℝ) 1, D.realize vector (atInfinity (binaryUnipotent ((M : ℝ) * t)))) = 0 := by
  set ψ : ℝ → ℂ := fun t => D.realize vector (atInfinity (binaryUnipotent ((M : ℝ) * t)))
  have hψ : Continuous ψ := by
    have smooth := smooth_continuous (D.scalarSmooth vector 1)
    have curve : Continuous (fun t : ℝ => (fun _ : Fin 1 => binaryUnipotent ((M : ℝ) * t))) :=
      continuous_pi (fun _ => binaryUnipotent_real_continuous.comp (continuous_const.mul continuous_id))
    convert smooth.comp curve using 1
    funext t
    simp only [Function.comp_apply, one_mul, ψ]
  refine ⟨hψ, ?_⟩
  set φ : Adeles → ℂ := fun a => D.realize vector (binaryUnipotent a * 1)
  have periodic : ∀ r : ℚ, ∀ a, φ (rationalAdele r + a) = φ a := by
    intro r a
    simp only [φ, mul_one]
    rw [binaryUnipotent_add, ← map_binaryUnipotent rationalAdele r]
    have := D.leftRational (binaryUnipotent r) vector (binaryUnipotent a)
    exact this
  have cusp := (D.cuspidal vector 1).2
  have scaled := adele_periodic_integral_rational_scaling φ periodic
    (Units.mk0 (M : ℚ) (by exact_mod_cast hM.ne'))
  change (∫ a in additiveDomain, φ (rationalAdele (M : ℚ) * a) ∂adeleMeasure) =
    ∫ a in additiveDomain, φ a ∂adeleMeasure at scaled
  rw [show (∫ a in additiveDomain, φ a ∂adeleMeasure) = 0 from cusp] at scaled
  have measurable_domain : MeasurableSet additiveDomain :=
    measurableSet_Ico.prod integralLattice_isCompact.measurableSet
  have pointwise : ∀ a ∈ additiveDomain, φ (rationalAdele (M : ℚ) * a) = ψ a.1 := by
    intro a member
    obtain ⟨z, hz⟩ := member.2
    have ha : rationalAdele (M : ℚ) * a =
        (((M : ℝ) * a.1, (0 : FiniteAdeles)) : Adeles) +
          (((0 : ℝ), (M : FiniteAdeles) * integralEmbedding z) : Adeles) := by
      apply Prod.ext
      · change ((M : ℚ) : ℝ) * a.1 = (M : ℝ) * a.1 + 0
        push_cast
        ring
      · change algebraMap ℚ FiniteAdeles (M : ℚ) * a.2 = 0 + (M : FiniteAdeles) * integralEmbedding z
        rw [map_natCast, hz, zero_add]
    simp only [φ, ψ, mul_one]
    rw [ha, binaryUnipotent_add, ← atInfinity_binaryUnipotent, ← atFinite_binaryUnipotent]
    exact finiteInvariant _ z
  have hcongr := setIntegral_congr_fun (μ := adeleMeasure) measurable_domain pointwise
  rw [hcongr] at scaled
  have projection := integral_map additiveDomain_real_projection.measurable.aemeasurable
    (hψ.measurable.aestronglyMeasurable (μ := Measure.map (Prod.fst : Adeles → ℝ)
      (adeleMeasure.restrict additiveDomain)))
  rw [additiveDomain_real_projection.map_eq] at projection
  rw [← projection] at scaled
  exact scaled

/-- **Regularity-free vanishing of the cusp obstruction.** For a binary cocycle with
cuspidal values, finite level, and the cocycle identity of `Cohomological`, there is
`M > 0` such that every unipotent-invariant functional kills `c(n(M))(1)`. -/
theorem binary_cusp_restriction_of_level (D : CuspidalRepresentation) (n : ℕ)
    (c : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (values : ∀ g, BinaryValues D n (c g))
    (U : Subgroup BinaryFiniteGL)
    (level : ∀ u : U, ∀ g x, c g (x * atFinite u.val) = c g x)
    (cocycle : ∀ g h x, c (g * h) x = c g x + binaryCohomologicalAction n g (c h) x)
    (M : ℕ) (hM : 0 < M)
    (hlev : ∀ z : IntegralAdeles, binaryUnipotent ((M : FiniteAdeles) * integralEmbedding z) ∈ U) :
    ∀ functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ,
      (∀ u : ℝ, functional ∘ₗ binaryCoefficient n (binaryUnipotent u) = functional) →
      functional (c (binaryUnipotent (M : ℝ)) 1) = 0 := by
  intro functional hinv
  have hfin : ∀ g (x : BinaryAdelicGL) (z : IntegralAdeles),
      c g (x * atFinite (binaryUnipotent ((M : FiniteAdeles) * integralEmbedding z))) = c g x :=
    fun g x z => level ⟨_, hlev z⟩ g x
  -- right translation by the real cusp generator is invisible at the identity
  have hshift : ∀ g, c g (atInfinity (binaryUnipotent (M : ℝ))) = c g 1 := by
    intro g
    have key := atInfinity_binaryUnipotent_rational (M : ℚ)
    rw [Rat.cast_natCast] at key
    have hneg : -(algebraMap ℚ FiniteAdeles (M : ℚ)) = (M : FiniteAdeles) * integralEmbedding (-1) := by
      rw [map_neg, map_one, map_natCast]
      ring
    rw [key, hneg, hfin g _ (-1)]
    calc c g (GeneralLinearGroup.map rationalAdele (binaryUnipotent (M : ℚ)))
        = c g (GeneralLinearGroup.map rationalAdele (binaryUnipotent (M : ℚ)) * 1) := by rw [mul_one]
      _ = c g 1 := binaryValues_leftRational (values g) _ 1
  -- algebraic constancy along the real unipotent
  have hconst : ∀ u : ℝ, functional (c (binaryUnipotent (M : ℝ)) (atInfinity (binaryUnipotent u))) =
      functional (c (binaryUnipotent (M : ℝ)) 1) := by
    intro u
    have hcomm : binaryUnipotent u * binaryUnipotent (M : ℝ) =
        binaryUnipotent (M : ℝ) * binaryUnipotent u := by
      rw [← binaryUnipotent_add, ← binaryUnipotent_add, add_comm]
    have h1 := cocycle (binaryUnipotent u) (binaryUnipotent (M : ℝ)) 1
    have h2 := cocycle (binaryUnipotent (M : ℝ)) (binaryUnipotent u) 1
    rw [hcomm, h2] at h1
    unfold binaryCohomologicalAction at h1
    rw [det_atInfinity_binaryUnipotent, det_atInfinity_binaryUnipotent, normPower_one, one_smul,
      one_smul, one_mul, one_mul, hshift] at h1
    have equation := congrArg functional h1
    rw [map_add, map_add] at equation
    have e1 := LinearMap.congr_fun (hinv (M : ℝ)) (c (binaryUnipotent u) 1)
    have e2 := LinearMap.congr_fun (hinv u) (c (binaryUnipotent (M : ℝ)) (atInfinity (binaryUnipotent u)))
    simp only [LinearMap.comp_apply] at e1 e2
    rw [e1, e2] at equation
    linear_combination -equation
  -- every coefficient has vanishing real constant term
  have hcoeff : ∀ monomial : Fin 2 →₀ ℕ,
      Continuous (fun t : ℝ => (c (binaryUnipotent (M : ℝ)) (atInfinity (binaryUnipotent ((M : ℝ) * t)))).val.coeff monomial) ∧
      (∫ t in Set.Ico (0 : ℝ) 1, (c (binaryUnipotent (M : ℝ)) (atInfinity (binaryUnipotent ((M : ℝ) * t)))).val.coeff monomial) = 0 := by
    intro monomial
    obtain ⟨vector, hvector⟩ := values (binaryUnipotent (M : ℝ)) monomial
    have result := cusp_real_constant_term D vector M hM (fun x z => by
      rw [hvector]
      exact congrArg (fun p : Binary.HomogeneousPoly (n + 1) => p.val.coeff monomial)
        (hfin _ x z))
    rw [hvector] at result
    exact result
  obtain ⟨weight, hweight⟩ := functional_eq_sum_coeff functional
  have hzero : (∫ t in Set.Ico (0 : ℝ) 1,
      functional (c (binaryUnipotent (M : ℝ)) (atInfinity (binaryUnipotent ((M : ℝ) * t))))) = 0 := by
    simp_rw [hweight]
    rw [integral_finsetSum]
    · apply Finset.sum_eq_zero
      intro s _
      rw [integral_mul_const, (hcoeff s.val).2, zero_mul]
    · intro s _
      exact (((hcoeff s.val).1.mul continuous_const).integrableOn_Icc).mono_set Set.Ico_subset_Icc_self
  have hvalue : (∫ t in Set.Ico (0 : ℝ) 1,
      functional (c (binaryUnipotent (M : ℝ)) (atInfinity (binaryUnipotent ((M : ℝ) * t))))) =
      functional (c (binaryUnipotent (M : ℝ)) 1) := by
    simp_rw [hconst]
    simp
  rw [← hvalue, hzero]

/-- **Regularity-free vanishing of the cusp obstruction.** -/
theorem binary_cusp_restriction (D : CuspidalRepresentation) (n : ℕ)
    (c : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (values : ∀ g, BinaryValues D n (c g))
    (U : Subgroup BinaryFiniteGL) (hU : IsOpen (U : Set BinaryFiniteGL))
    (level : ∀ u : U, ∀ g x, c g (x * atFinite u.val) = c g x)
    (cocycle : ∀ g h x, c (g * h) x = c g x + binaryCohomologicalAction n g (c h) x) :
    ∃ M : ℕ, 0 < M ∧ ∀ functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ,
      (∀ u : ℝ, functional ∘ₗ binaryCoefficient n (binaryUnipotent u) = functional) →
      functional (c (binaryUnipotent (M : ℝ)) 1) = 0 := by
  obtain ⟨M, hM, hlev⟩ := exists_unipotent_level U hU
  exact ⟨M, hM, binary_cusp_restriction_of_level D n c values U level cocycle M hM hlev⟩

/-- Right translation by real cusp elements `n(kM)` is invisible at the identity. -/
theorem cusp_shift_invariant {D : CuspidalRepresentation} {n : ℕ}
    {c : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    (values : ∀ g, BinaryValues D n (c g)) (U : Subgroup BinaryFiniteGL)
    (level : ∀ u : U, ∀ g x, c g (x * atFinite u.val) = c g x) (M : ℕ)
    (hlev : ∀ z : IntegralAdeles, binaryUnipotent ((M : FiniteAdeles) * integralEmbedding z) ∈ U)
    (k : ℕ) (g : BinaryRealGL) :
    c g (atInfinity (binaryUnipotent ((k : ℝ) * M))) = c g 1 := by
  have key := atInfinity_binaryUnipotent_rational ((k : ℚ) * M)
  have hcast : (((k : ℚ) * M : ℚ) : ℝ) = (k : ℝ) * M := by push_cast; ring
  rw [hcast] at key
  have hneg : -(algebraMap ℚ FiniteAdeles ((k : ℚ) * M)) =
      (M : FiniteAdeles) * integralEmbedding (-(k : IntegralAdeles)) := by
    rw [map_neg, map_natCast, map_mul, map_natCast, map_natCast]
    ring
  rw [key, hneg, level ⟨_, hlev _⟩ g _]
  calc c g (GeneralLinearGroup.map rationalAdele (binaryUnipotent ((k : ℚ) * M)))
      = c g (GeneralLinearGroup.map rationalAdele (binaryUnipotent ((k : ℚ) * M)) * 1) := by
        rw [mul_one]
    _ = c g 1 := binaryValues_leftRational (values g) _ 1

end TernaryPeriodPolynomials.FlagExactness
