module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.AwayCompressionMeasure
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.Hilbert
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.Omega

@[expose] public section


/-!
# Arguments that are integral away from three, and the Iwasawa decomposition of the opposite radical

`awayCompact` is `GL₃(Ẑ^{(3)})`: the finite matrices that are integral at every place and trivial at
three. An adelic element `y` is *stable* when left translation by `awayCompact` is right translation
by `awayCompact`. Stability is inherited by `w⁻¹ n(u) y` for local coordinates `u`, and it holds for
every argument of the form `real · (matrix at three) · (integral matrix)`.

Every element of the opposite radical with coordinates away from `∞` and `3` is a plane parabolic
element with block trivial at three times an element of `awayCompact`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.RepresentationTheory
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

/-- `GL₃(Ẑ^{(3)})` inside `GL₃(𝔸_f)`. -/
def awayCompact : Subgroup FiniteGL :=
  finiteIntegralGLLevel 3 ⊓
    (GeneralLinearGroup.map (n := Fin 3) (finiteEvaluation placeThree)).ker

theorem mem_awayCompact {k : FiniteGL} :
    k ∈ awayCompact ↔ k ∈ finiteIntegralGLLevel 3 ∧
      GeneralLinearGroup.map (finiteEvaluation placeThree) k = 1 := by
  rw [awayCompact, Subgroup.mem_inf, MonoidHom.mem_ker]

theorem awayCompact_mem_finiteLevel {k : FiniteGL} (hk : k ∈ awayCompact) : k ∈ finiteLevel := by
  rw [mem_awayCompact] at hk
  apply finiteLevel_of_integral_of_three k hk.1
  rw [(HeckeEigen.finiteThree_eq_one_iff k).mpr hk.2]
  exact ⟨1, by simp, by simp⟩

/-- Left translation by `GL₃(Ẑ^{(3)})` is right translation by `GL₃(Ẑ^{(3)})`. -/
def AwayStable (y : AdelicGL) : Prop :=
  ∀ k ∈ awayCompact, ∃ k' ∈ awayCompact, atFinite k * y = y * atFinite k'

/-- An adelic element with arbitrary real part, arbitrary matrix at three and integral matrix at all
places. -/
def AwayGood (g : AdelicGL) : Prop :=
  ∃ (r : RealGL3) (c₃ : GeneralLinearGroup (Fin 3) (placeThree.adicCompletion ℚ))
    (c : GeneralLinearGroup (Fin 3) IntegralAdeles),
    g = atInfinity r * atFinite (finiteAtPlaceGL 3 placeThree c₃ *
      GeneralLinearGroup.map integralEmbedding c)

theorem realGroup_atFinite' (k : FiniteGL) : realGroup (atFinite k) = 1 := by
  apply Units.ext
  rfl

theorem finiteGroup_atFinite' (k : FiniteGL) : finiteGroup (atFinite k) = k := by
  apply Units.ext
  rfl

theorem adelicGroup_ext' {first second : AdelicGL}
    (real_equal : realGroup first = realGroup second)
    (finite_equal : finiteGroup first = finiteGroup second) : first = second := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  apply Prod.ext
  · exact congrArg (fun matrix : RealGL3 => matrix.val row column) real_equal
  · exact congrArg (fun matrix : FiniteGL => matrix.val row column) finite_equal

theorem awayStable_of_good {g : AdelicGL} (hg : AwayGood g) : AwayStable g := by
  obtain ⟨r, c₃, c, rfl⟩ := hg
  intro k hk
  have hk3 : GeneralLinearGroup.map (finiteEvaluation placeThree) k = 1 :=
    (mem_awayCompact.mp hk).2
  have hkint : k ∈ finiteIntegralGLLevel 3 := (mem_awayCompact.mp hk).1
  have hci : (GeneralLinearGroup.map integralEmbedding c : FiniteGL) ∈ finiteIntegralGLLevel 3 :=
    ⟨c, rfl⟩
  refine ⟨(GeneralLinearGroup.map integralEmbedding c)⁻¹ * k *
    GeneralLinearGroup.map integralEmbedding c, ?_, ?_⟩
  · rw [mem_awayCompact]
    constructor
    · exact (finiteIntegralGLLevel 3).mul_mem
        ((finiteIntegralGLLevel 3).mul_mem ((finiteIntegralGLLevel 3).inv_mem hci) hkint) hci
    · rw [map_mul, map_mul, map_inv, hk3, mul_one, inv_mul_cancel]
  · have hcomm := HeckeEigen.threePart_commute c₃ hk3
    have hfin : k * (finiteAtPlaceGL 3 placeThree c₃ * GeneralLinearGroup.map integralEmbedding c) =
        finiteAtPlaceGL 3 placeThree c₃ * GeneralLinearGroup.map integralEmbedding c *
          ((GeneralLinearGroup.map integralEmbedding c)⁻¹ * k *
            GeneralLinearGroup.map integralEmbedding c) := by
      calc k * (finiteAtPlaceGL 3 placeThree c₃ * GeneralLinearGroup.map integralEmbedding c)
          = (k * finiteAtPlaceGL 3 placeThree c₃) * GeneralLinearGroup.map integralEmbedding c :=
            (mul_assoc _ _ _).symm
        _ = (finiteAtPlaceGL 3 placeThree c₃ * k) * GeneralLinearGroup.map integralEmbedding c := by
            rw [← hcomm]
        _ = _ := by group
    calc atFinite k * (atInfinity r * atFinite (finiteAtPlaceGL 3 placeThree c₃ *
          GeneralLinearGroup.map integralEmbedding c))
        = atInfinity r * (atFinite k * atFinite (finiteAtPlaceGL 3 placeThree c₃ *
          GeneralLinearGroup.map integralEmbedding c)) := by
          rw [← mul_assoc, HeckeTranslate.HeckeInvariance.atFinite_comm_atInfinity, mul_assoc]
      _ = atInfinity r * atFinite (k * (finiteAtPlaceGL 3 placeThree c₃ *
          GeneralLinearGroup.map integralEmbedding c)) := by
          rw [HeckeTranslate.HeckeInvariance.atFinite_mul]
      _ = atInfinity r * atFinite (finiteAtPlaceGL 3 placeThree c₃ *
          GeneralLinearGroup.map integralEmbedding c *
          ((GeneralLinearGroup.map integralEmbedding c)⁻¹ * k *
            GeneralLinearGroup.map integralEmbedding c)) := by rw [hfin]
      _ = _ := by
          rw [← HeckeTranslate.HeckeInvariance.atFinite_mul]
          exact (mul_assoc _ _ _).symm

theorem awayGood_of_finite_integral {g : AdelicGL}
    (hg : finiteGroup g ∈ Set.range
      (GeneralLinearGroup.map integralEmbedding : GeneralLinearGroup (Fin 3) IntegralAdeles →* FiniteGL)) :
    AwayGood g := by
  obtain ⟨c, hc⟩ := hg
  refine ⟨realGroup g, 1, c, ?_⟩
  rw [map_one, one_mul, hc]
  exact HeckeEigen.gl3_real_finite g

theorem awayGood_of_integral {g : AdelicGL}
    (h : ∃ integral : GeneralLinearGroup (Fin 3) IntegralAdeles,
      finiteGroup g = GeneralLinearGroup.map integralEmbedding integral) : AwayGood g := by
  obtain ⟨c, hc⟩ := h
  exact awayGood_of_finite_integral ⟨c, hc.symm⟩

theorem awayGood_of_inMaximalCompact {g : AdelicGL} (hg : inMaximalCompact g) : AwayGood g :=
  awayGood_of_finite_integral hg.2

theorem awayGood_mul_atInfinity {g : AdelicGL} (hg : AwayGood g) (x : RealGL3) :
    AwayGood (g * atInfinity x) := by
  obtain ⟨r, c₃, c, rfl⟩ := hg
  refine ⟨r * x, c₃, c, ?_⟩
  rw [mul_assoc, HeckeTranslate.HeckeInvariance.atFinite_comm_atInfinity, ← mul_assoc,
    HeckeTranslate.HeckeInvariance.atInfinity_mul]

theorem awayGood_atInfinity_mul (x : RealGL3) {g : AdelicGL} (hg : AwayGood g) :
    AwayGood (atInfinity x * g) := by
  obtain ⟨r, c₃, c, rfl⟩ := hg
  refine ⟨x * r, c₃, c, ?_⟩
  rw [← mul_assoc, HeckeTranslate.HeckeInvariance.atInfinity_mul]

theorem awayStable_of_finite {y : AdelicGL}
    (h : ∀ k ∈ awayCompact, ∃ k' ∈ awayCompact, k * finiteGroup y = finiteGroup y * k') :
    AwayStable y := by
  intro k hk
  obtain ⟨k', hk', e⟩ := h k hk
  refine ⟨k', hk', ?_⟩
  apply adelicGroup_ext'
  · rw [map_mul, map_mul, realGroup_atFinite', realGroup_atFinite', one_mul, mul_one]
  · rw [map_mul, map_mul, finiteGroup_atFinite', finiteGroup_atFinite', e]

theorem finiteGroup_stable {y : AdelicGL} (hy : AwayStable y) :
    ∀ k ∈ awayCompact, ∃ k' ∈ awayCompact, k * finiteGroup y = finiteGroup y * k' := by
  intro k hk
  obtain ⟨k', hk', e⟩ := hy k hk
  refine ⟨k', hk', ?_⟩
  have h := congrArg finiteGroup e
  rw [map_mul, map_mul, finiteGroup_atFinite', finiteGroup_atFinite'] at h
  exact h

theorem map_lineUnipotent {R S : Type*} [CommRing R] [CommRing S]
    (hom : R →+* S) (first second : R) :
    GeneralLinearGroup.map hom (lineUnipotent first second) =
      lineUnipotent (hom first) (hom second) := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [GeneralLinearGroup.map_apply, lineUnipotent, upperUnipotent]

theorem lineUnipotent_zero_zero {R : Type*} [CommRing R] :
    lineUnipotent (0 : R) 0 = 1 := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;> simp [lineUnipotent, upperUnipotent]

theorem finiteRadical_commute (first second : ℚ_[3]) {x : FiniteGL}
    (hx : GeneralLinearGroup.map (finiteEvaluation placeThree) x = 1) :
    lineUnipotent (finiteAtThreeScalar first) (finiteAtThreeScalar second) * x =
      x * lineUnipotent (finiteAtThreeScalar first) (finiteAtThreeScalar second) := by
  apply finiteGeneralLinearGroup_ext
  intro place
  rw [map_mul, map_mul]
  by_cases h : place = placeThree
  · subst h
    rw [hx, one_mul, mul_one]
  · rw [map_lineUnipotent, finiteAtThreeScalar_away first place h,
      finiteAtThreeScalar_away second place h, lineUnipotent_zero_zero, one_mul, mul_one]

theorem finiteGroup_weyl : finiteGroup (weyl : AdelicGL) = weyl :=
  map_weyl (RingHom.snd ℝ FiniteAdeles)

theorem finiteGroup_localRadical (u : LocalLine × LocalLine) :
    finiteGroup (localRadical u) =
      lineUnipotent (finiteAtThreeScalar u.1.2) (finiteAtThreeScalar u.2.2) :=
  map_lineUnipotent (RingHom.snd ℝ FiniteAdeles) (localAdele u.1) (localAdele u.2)

theorem weyl_mem_integral : (weyl : FiniteGL) ∈ finiteIntegralGLLevel 3 :=
  ⟨weyl, map_weyl integralEmbedding⟩

/-- Stability is preserved by `w⁻¹ n(u)` for local coordinates `u`. -/
theorem awayStable_weyl_radical {g : AdelicGL} (hg : AwayStable g) (u : LocalLine × LocalLine) :
    AwayStable (weyl⁻¹ * localRadical u * g) := by
  apply awayStable_of_finite
  intro k hk
  have hk3 : GeneralLinearGroup.map (finiteEvaluation placeThree) k = 1 :=
    (mem_awayCompact.mp hk).2
  have hkint : k ∈ finiteIntegralGLLevel 3 := (mem_awayCompact.mp hk).1
  obtain ⟨k₁, hk₁⟩ : ∃ k₁ : FiniteGL, k₁ = (weyl : FiniteGL) * k * (weyl : FiniteGL)⁻¹ :=
    ⟨_, rfl⟩
  have hk₁mem : k₁ ∈ awayCompact := by
    rw [mem_awayCompact, hk₁]
    constructor
    · exact (finiteIntegralGLLevel 3).mul_mem
        ((finiteIntegralGLLevel 3).mul_mem weyl_mem_integral hkint)
        ((finiteIntegralGLLevel 3).inv_mem weyl_mem_integral)
    · rw [map_mul, map_mul, map_inv, hk3, mul_one, mul_inv_cancel]
  have hk₁3 : GeneralLinearGroup.map (finiteEvaluation placeThree) k₁ = 1 :=
    (mem_awayCompact.mp hk₁mem).2
  obtain ⟨k₂, hk₂, e⟩ := finiteGroup_stable hg k₁ hk₁mem
  refine ⟨k₂, hk₂, ?_⟩
  rw [map_mul, map_mul, map_inv, finiteGroup_weyl, finiteGroup_localRadical]
  have hcomm := finiteRadical_commute u.1.2 u.2.2 hk₁3
  calc k * ((weyl : FiniteGL)⁻¹ *
        lineUnipotent (finiteAtThreeScalar u.1.2) (finiteAtThreeScalar u.2.2) * finiteGroup g)
      = (weyl : FiniteGL)⁻¹ * (k₁ *
        lineUnipotent (finiteAtThreeScalar u.1.2) (finiteAtThreeScalar u.2.2)) *
          finiteGroup g := by
        rw [hk₁]; group
    _ = (weyl : FiniteGL)⁻¹ *
        (lineUnipotent (finiteAtThreeScalar u.1.2) (finiteAtThreeScalar u.2.2) * k₁) *
          finiteGroup g := by rw [hcomm]
    _ = (weyl : FiniteGL)⁻¹ *
        lineUnipotent (finiteAtThreeScalar u.1.2) (finiteAtThreeScalar u.2.2) *
          (k₁ * finiteGroup g) := by simp only [mul_assoc]
    _ = _ := by rw [e]; simp only [mul_assoc]

/-! ### The opposite radical away from `∞` and `3` -/

theorem awayAdele_continuous : Continuous awayAdele :=
  continuous_const.prodMk continuous_subtype_val

theorem awayOpposite_continuous : Continuous awayOpposite := by
  have h : awayOpposite = fun u : FiniteAwayThree × FiniteAwayThree =>
      (weyl : AdelicGL)⁻¹ * lineUnipotent (awayAdele u.1) (awayAdele u.2) * weyl := by
    funext u
    exact (_root_.GeneralEisenstein.Adelic.weyl_inverse_lineUnipotent _ _).symm
  rw [h]
  exact (continuous_const.mul (InducedContinuity.lineUnipotent_continuous.comp
    ((awayAdele_continuous.comp continuous_fst).prodMk
      (awayAdele_continuous.comp continuous_snd)))).mul continuous_const

/-- The finite matrix of the coordinates of the opposite radical. -/
def awayLower (u : FiniteAwayThree × FiniteAwayThree) : FiniteGL :=
  lowerPlaneUnipotent u.1.val u.2.val

theorem awayOpposite_eq_atFinite (u : FiniteAwayThree × FiniteAwayThree) :
    awayOpposite u = atFinite (awayLower u) := by
  apply Units.ext
  refine Matrix.ext fun i j => Prod.ext ?_ ?_ <;> fin_cases i <;> fin_cases j <;>
    simp [awayOpposite, awayLower, awayAdele, atFinite, combineGL, pairMatrix, lowerPlaneUnipotent]

theorem lowerPlaneUnipotent_zero_zero {R : Type*} [CommRing R] :
    lowerPlaneUnipotent (0 : R) 0 = 1 := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;> simp [lowerPlaneUnipotent]

theorem eval_three_awayLower (u : FiniteAwayThree × FiniteAwayThree) :
    GeneralLinearGroup.map (finiteEvaluation placeThree) (awayLower u) = 1 := by
  rw [← HeckeEigen.finiteThree_eq_one_iff, awayLower, map_lowerPlaneUnipotent,
    finiteThree_away u.1, finiteThree_away u.2, lowerPlaneUnipotent_zero_zero]

/-- **Iwasawa decomposition of the opposite radical away from three.** -/
theorem awayOpposite_iwasawa (u : FiniteAwayThree × FiniteAwayThree) :
    ∃ (a b : Adeles) (s : Adelesˣ) (Bf : BinaryFiniteGL) (κ : FiniteGL),
      κ ∈ awayCompact ∧ Bf ∈ awayGroup placeThree ∧
      awayOpposite u =
        planeUnipotent a b * (planeLevi 1 s * planeLevi (atFinite Bf) 1) * atFinite κ := by
  have hL3 := eval_three_awayLower u
  obtain ⟨p, κ0, hp3, hfac⟩ := finiteGL_plane_level_factorization (awayLower u)
    (by
      rw [(HeckeEigen.finiteThree_eq_one_iff _).mpr hL3]
      exact ⟨1, by simp, by simp⟩)
  have hp3' : GeneralLinearGroup.map (finiteEvaluation placeThree) p.val = 1 :=
    (HeckeEigen.finiteThree_eq_one_iff _).mp hp3
  obtain ⟨_, _, _, Bf, hBf⟩ := planeParabolic_exists_decomposition p
  obtain ⟨a, b, s, B, hB⟩ := planeParabolic_exists_decomposition
    (⟨atFinite p.val, HeckeEigen.atFinite_mem_plane p.property⟩ : planeParabolic Adeles)
  have hB' : atFinite p.val = planeUnipotent a b * (planeLevi 1 s * planeLevi B 1) := hB
  have hBeq : B = atFinite Bf := HeckeEigen.block_atFinite hBf (congrArg Units.val hB')
  have hBaway : Bf ∈ awayGroup placeThree := HeckeEigen.block_awayGroup hp3' hBf
  refine ⟨a, b, s, Bf, κ0.val, ?_, hBaway, ?_⟩
  · rw [mem_awayCompact]
    constructor
    · obtain ⟨y, _, hy⟩ := κ0.property
      exact ⟨y, hy⟩
    · have h := congrArg (GeneralLinearGroup.map (finiteEvaluation placeThree)) hfac
      rw [map_mul, hL3, hp3', one_mul] at h
      exact h.symm
  · rw [awayOpposite_eq_atFinite, hfac, ← HeckeTranslate.HeckeInvariance.atFinite_mul, hB', hBeq]

theorem planeLevi_mem_awayCompact {m : BinaryFiniteGL} (hm : m ∈ awayLevel placeThree) :
    planeLevi m 1 ∈ awayCompact := by
  rw [mem_awayCompact]
  constructor
  · obtain ⟨m₀, hm₀⟩ := hm.2
    refine ⟨planeLevi m₀ 1, ?_⟩
    rw [HeckeEigen.planeLevi_map, map_one, hm₀]
  · exact HeckeEigen.eval_planeLevi_one hm.1

/-- Conjugating the opposite radical by the spherical `GL₂` Levi moves its coordinates. -/
theorem planeLevi_mul_awayLower (m : BinaryFiniteGL) (u : FiniteAwayThree × FiniteAwayThree) :
    planeLevi m 1 * awayLower u = awayLower (awayRowAction m⁻¹ u) * planeLevi m 1 := by
  have h := lowerPlaneUnipotent_planeLevi_commute m⁻¹ u.1.val u.2.val
  rw [planeLevi_one_inverse] at h
  calc planeLevi m 1 * awayLower u
      = planeLevi m 1 * (lowerPlaneUnipotent u.1.val u.2.val * (planeLevi m 1)⁻¹) *
          planeLevi m 1 := by
        unfold awayLower; group
    _ = planeLevi m 1 * ((planeLevi m 1)⁻¹ *
          lowerPlaneUnipotent (u.1.val * m⁻¹.val 0 0 + u.2.val * m⁻¹.val 1 0)
            (u.1.val * m⁻¹.val 0 1 + u.2.val * m⁻¹.val 1 1)) * planeLevi m 1 := by
        rw [h]
    _ = awayLower (awayRowAction m⁻¹ u) * planeLevi m 1 := by
        unfold awayLower
        rw [awayRowAction_fst_val, awayRowAction_snd_val]
        group

theorem atFinite_planeLevi_mul_awayOpposite (m : BinaryFiniteGL)
    (u : FiniteAwayThree × FiniteAwayThree) :
    atFinite (planeLevi m 1) * awayOpposite u =
      awayOpposite (awayRowAction m⁻¹ u) * atFinite (planeLevi m 1) := by
  rw [awayOpposite_eq_atFinite, awayOpposite_eq_atFinite,
    HeckeTranslate.HeckeInvariance.atFinite_mul, HeckeTranslate.HeckeInvariance.atFinite_mul,
    planeLevi_mul_awayLower]

end TernaryPeriodPolynomials.EdgeConvergence
