module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.FiniteEntries.ReflectionHecke
public import TernaryPeriodPolynomials.BoundaryComparison.BadPlaneInjectivity.PlaneSpanDecomposition
public import TernaryPeriodPolynomials.BoundaryComparison.FiniteEntries
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.OrbitDetection

@[expose] public section



/-!
# CMP-7: the reduction to the trivial sector

The `bad_plane_data_injective` is stated in the
sector `trivialCharacter` (the coefficient system `E_n = E_{n,1}` and data of trivial normal inducing character).  The paper
argues that this loses nothing: any datum with a nonzero bad-plane class whose class extends over `⟨K†, -I₃⟩` has trivial normal
character.  This file assembles the extended-class argument of `ManuscriptC6/ReflectionSign` and `ReflectionHecke` into the
statement about the actual span of data, and derives the bad-plane injectivity for data of an ARBITRARY normal character.

* `planeDatumSpan n χ`: the span of the plane summands of all cohomological data with normal inducing character `χ`;
  `automorphicPlaneSpan_eq_planeDatumSpan` : the `automorphicPlaneSpan n` is the case `χ = trivialCharacter`.
* `chi_eq_trivial_of_extended_span`: an extended class of `planeDatumSpan n χ` with a nonzero bad-plane coordinate forces
  `χ = trivialCharacter`.
* `chi_eq_trivial_of_global_plane_coordinate`: the plane coordinate of a global `K†`-class of the sector `χ` with
  `reflScalar n χ = 1` (for the trivial sector and odd `n`, every class) is extended automatically, so a nonzero bad-plane
  component in the span forces `χ = trivialCharacter`.
* `appendix_C6_anySector`, `appendix_C6_anySector_of_global`: the injectivity of `bad_plane_data_injective` for the sector of an arbitrary
  normal character, derived from the `bad_plane_data_injective`.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.FiniteEntries
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.SphericalDetection.Helpers Matrix

noncomputable section

namespace TernaryPeriodPolynomials.Argument.KDaggerComparison

/-- `c • x = 0` over `ℂ` (proved for an arbitrary module so that the instance problem is not
re-solved on the concrete cohomology space). -/
private theorem complex_smul_eq_zero {V : Type*} [AddCommGroup V] [Module ℂ V] {c : ℂ} {x : V}
    (h : c • x = 0) : c = 0 ∨ x = 0 :=
  smul_eq_zero.mp h


/-- The data of a fixed cohomological type: a cuspidal representation with a cohomological vector of weight `n`. -/
abbrev CohomologicalCusp (n : ℕ) : Type _ := {c : CuspidalRepresentation // Cohomological c n}

/-- The plane summands of the data with normal inducing character `χ`, as a family of submodules of the stratum. -/
def planeDatumFamily (n : ℕ) (χ : RankOneCharacter) :
    CohomologicalCusp n → Submodule ℂ (StratumH2 n χ .plane) :=
  fun d => boundarySummand (⟨d.1, χ, d.2⟩ : InducingData n) .plane

/-- The span of the plane summands of all cohomological data of normal inducing character `χ`. -/
def planeDatumSpan (n : ℕ) (χ : RankOneCharacter) : Submodule ℂ (StratumH2 n χ .plane) :=
  ⨆ d : CohomologicalCusp n, planeDatumFamily n χ d

/-- **The span is the trivial-character case.** -/
theorem automorphicPlaneSpan_eq_planeDatumSpan (n : ℕ) :
    automorphicPlaneSpan n = planeDatumSpan n trivialCharacter := by
  rw [BadPlaneInjectivity.automorphicPlaneSpan_eq_iSup]
  apply le_antisymm
  · exact iSup_le fun D => le_iSup (planeDatumFamily n trivialCharacter) ⟨D.cusp, D.cohomological⟩
  · exact iSup_le fun d => le_iSup (BadPlaneInjectivity.planeSummandFamily n) ⟨d.1, d.2⟩

/-- Membership in `planeDatumSpan n χ` is a finite sum of elements of plane summands. -/
theorem exists_sum_of_mem_planeDatumSpan (n : ℕ) (χ : RankOneCharacter) (ξ : StratumH2 n χ .plane)
    (hξ : ξ ∈ planeDatumSpan n χ) :
    ∃ (S : Finset (CohomologicalCusp n)) (f : CohomologicalCusp n → StratumH2 n χ .plane),
      (∀ d ∈ S, f d ∈ boundarySummand (⟨d.1, χ, d.2⟩ : InducingData n) .plane) ∧ ξ = ∑ d ∈ S, f d := by
  have hobtain1 := (Submodule.mem_iSup_iff_exists_finsupp (planeDatumFamily n χ) ξ).mp hξ
  obtain ⟨g, hg, hsum⟩ := hobtain1
  refine ⟨g.support, fun d => g d, fun d _ => hg d, ?_⟩
  rw [← hsum]
  rfl

/-- **The extended-class argument for the span of data.**  A class of the span of the plane summands of data of
normal inducing character `χ` which extends over `⟨K†, -I₃⟩` and has a nonzero bad-plane coordinate has `χ = trivialCharacter`. -/
theorem chi_eq_trivial_of_extended_span {n : ℕ} {χ : RankOneCharacter} {ξ : StratumH2 n χ .plane}
    (hspan : ξ ∈ planeDatumSpan n χ) (hext : IsReflExtended ξ) (hbad : cuspRes n χ .plane false ξ ≠ 0) :
    χ = trivialCharacter := by
  have hobtain2 := exists_sum_of_mem_planeDatumSpan n χ ξ hspan
  obtain ⟨S, f, hf, rfl⟩ := hobtain2
  exact chi_eq_trivial_of_extended_sum_bad_plane χ S (fun d => d.1) (fun d => d.2) f hf hext hbad

/-- A class that extends over `⟨K†, -I₃⟩` is zero unless the reflection scalar is `1`. -/
theorem eq_zero_of_extended_of_reflScalar_ne_one {n : ℕ} {χ : RankOneCharacter} {s : Side}
    {a : StratumH2 n χ s} (hext : IsReflExtended a) (h : reflScalar n χ ≠ 1) : a = 0 := by
  obtain ⟨c', hc'⟩ := hext
  have := reflScalar_sub_one_smul_extended n χ s c'
  rw [hc'] at this
  exact (complex_smul_eq_zero this).resolve_left (sub_ne_zero.mpr h)

/-- **The plane coordinate of a global class of a sector with `reflScalar n χ = 1` is extended** and, when it lies in the span of
the data of normal character `χ` with a nonzero bad-plane component, forces `χ = trivialCharacter`. -/
theorem chi_eq_trivial_of_global_plane_coordinate {n : ℕ} {χ : RankOneCharacter} (hrefl : reflScalar n χ = 1)
    (c : cocycles rationalLevel (rationalCoefficientComponent n χ))
    (hspan : (globalCoordinates n χ c).1 ∈ planeDatumSpan n χ)
    (hbad : cuspRes n χ .plane false (globalCoordinates n χ c).1 ≠ 0) : χ = trivialCharacter :=
  chi_eq_trivial_of_extended_span hspan (globalCoordinates_extended n χ hrefl c .plane) hbad

/-- In the trivial sector with `n` odd every global class has extended plane and line coordinates. -/
theorem globalCoordinates_trivial_extended {n : ℕ} (hn : Odd n)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)) :
    IsReflExtended (globalCoordinates n trivialCharacter c).1 ∧
      IsReflExtended (globalCoordinates n trivialCharacter c).2 :=
  ⟨globalCoordinates_extended n trivialCharacter (reflScalar_trivial_odd hn) c .plane,
    globalCoordinates_extended n trivialCharacter (reflScalar_trivial_odd hn) c .line⟩

/-- A plane class vanishing at the good planes and at the reference bad plane is zero (two `K†`-orbits of rational planes). -/
theorem eq_zero_of_good_and_cuspRes_false {n : ℕ} {χ : RankOneCharacter} {ξ : StratumH2 n χ .plane}
    (hgood : VanishesOnGood n χ .plane ξ) (hbad : cuspRes n χ .plane false ξ = 0) : ξ = 0 := by
  apply coordinate_eq_zero_of_good_and_badRestrictions χ .plane ξ hgood
  intro flag hflag
  have hF : ∃ γ : rationalLevel, γ.val • TernaryPeriodPolynomials.Spectral.CuspOrbits.cuspFlag .plane false = flag :=
    TernaryPeriodPolynomials.Spectral.CuspOrbits.cuspFlag_transporter .plane false flag
      (by simpa using hflag)
  have := TernaryPeriodPolynomials.BoundaryDuality.CuspSeparation.fixedPointH2_eq_zero_of_cuspRes hF hbad
  exact this

/-- For odd `n` the reflection scalar `χ_∞(-1)(-1)^{n+1}` is `χ_∞(-1)`: it is `1` exactly for the even normal characters. -/
theorem reflScalar_eq_one_iff_even {n : ℕ} (hn : Odd n) (χ : RankOneCharacter) :
    reflScalar n χ = 1 ↔ χ.toMonoidHom (realAdeleUnit (-1)) = 1 := by
  unfold reflScalar
  rw [(hn.add_one).neg_one_pow, mul_one]

/-- An even normal character has trivial archimedean component character: every `GL₃(ℝ)`-component sign is `1`. -/
theorem componentCharacter_eq_one_of_even (χ : RankOneCharacter) (h : χ.toMonoidHom (realAdeleUnit (-1)) = 1)
    (g : RealGL3) : componentCharacter χ g = 1 := by
  change χ.toMonoidHom (realUnitHom (GeneralLinearGroup.det g)) = 1
  set t : ℝˣ := GeneralLinearGroup.det g
  rcases lt_or_gt_of_ne t.ne_zero with hneg | hpos
  · have hpos' : 0 < (-t).val := by simpa using hneg
    have : t = (-1 : ℝˣ) * (-t) := by simp
    rw [this, map_mul]
    change χ.toMonoidHom (realAdeleUnit (-1) * realAdeleUnit (-t)) = 1
    have h2 := χ.positiveReal (-t) hpos'
    rw [map_mul, h, h2, one_mul]
  · exact χ.positiveReal t hpos

/-- **The coefficient system `E_n = E_{n,1}` is the coefficient system of every even normal character.** -/
theorem rationalCoefficientComponent_eq_of_even (n : ℕ) (χ : RankOneCharacter)
    (h : χ.toMonoidHom (realAdeleUnit (-1)) = 1) :
    rationalCoefficientComponent n χ = rationalCoefficientComponent n trivialCharacter := by
  have h1 : ∀ g, componentCharacter trivialCharacter g = 1 := fun g => by
    change trivialCharacter.toMonoidHom (realUnitHom (GeneralLinearGroup.det g)) = 1
    rfl
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  change componentCharacter χ (GeneralLinearGroup.map (algebraMap ℚ ℝ) g) •
      realCoefficient n (GeneralLinearGroup.map (algebraMap ℚ ℝ) g) v =
    componentCharacter trivialCharacter (GeneralLinearGroup.map (algebraMap ℚ ℝ) g) •
      realCoefficient n (GeneralLinearGroup.map (algebraMap ℚ ℝ) g) v
  rw [componentCharacter_eq_one_of_even χ h, h1]

/-- **Bad-plane injectivity for data of an arbitrary normal inducing character** (derived from the `bad_plane_data_injective`).
Let `χ` be any rank-one character, `T` and `hT` the line constant term of Proposition C.5 in the sector `χ`, and `ξ` an inner
plane class of the span of the data of normal character `χ`, vanishing at every good plane, whose image vanishes at every good
line.  If `ξ` extends over `⟨K†, -I₃⟩` (as the plane coordinate of a global class does when `reflScalar n χ = 1`; see
`appendix_C6_anySector_of_global`) then `ξ = 0`.  For `χ ≠ trivialCharacter` this is the statement that a nonzero extended
bad-plane class forces the trivial character; for `χ = trivialCharacter` it is `bad_plane_data_injective`. -/
theorem appendix_C6_anySector (n : ℕ) (hn : 4 ≤ n) (χ : RankOneCharacter)
    (T : StratumH2 n χ .plane →ₗ[ℂ] StratumH2 n χ .line)
    (hT : ∀ ξ, InnerBoundary n χ .plane ξ →
      ∃ c : cocycles rationalLevel (rationalCoefficientComponent n χ), globalCoordinates n χ c = (ξ, T ξ))
    (ξ : StratumH2 n χ .plane) (hξ : InnerBoundary n χ .plane ξ) (hgood : VanishesOnGood n χ .plane ξ)
    (hline : VanishesOnGood n χ .line (T ξ)) (hspan : ξ ∈ planeDatumSpan n χ) (hext : IsReflExtended ξ) : ξ = 0 := by
  by_contra hne
  have hbad : cuspRes n χ .plane false ξ ≠ 0 := fun h => hne (eq_zero_of_good_and_cuspRes_false hgood h)
  have hχ := chi_eq_trivial_of_extended_span hspan hext hbad
  subst hχ
  exact hne (TernaryPeriodPolynomials.bad_plane_data_injective n hn T hT ξ hξ hgood hline)

/-- **The same, with the extension hypothesis discharged by the global class**: if `reflScalar n χ = 1` (for odd `n`: `χ` even,
`reflScalar_eq_one_iff_even`), the plane coordinate of the global class supplied by `hT` extends over `⟨K†, -I₃⟩`. -/
theorem appendix_C6_anySector_of_global (n : ℕ) (hn : 4 ≤ n) (χ : RankOneCharacter) (hrefl : reflScalar n χ = 1)
    (T : StratumH2 n χ .plane →ₗ[ℂ] StratumH2 n χ .line)
    (hT : ∀ ξ, InnerBoundary n χ .plane ξ →
      ∃ c : cocycles rationalLevel (rationalCoefficientComponent n χ), globalCoordinates n χ c = (ξ, T ξ))
    (ξ : StratumH2 n χ .plane) (hξ : InnerBoundary n χ .plane ξ) (hgood : VanishesOnGood n χ .plane ξ)
    (hline : VanishesOnGood n χ .line (T ξ)) (hspan : ξ ∈ planeDatumSpan n χ) : ξ = 0 := by
  have hobtain3 := hT ξ hξ
  obtain ⟨c, hc⟩ := hobtain3
  have hext : IsReflExtended ξ := by
    have h := globalCoordinates_extended n χ hrefl c .plane
    change IsReflExtended (globalCoordinates n χ c).1 at h
    rw [hc] at h
    exact h
  exact appendix_C6_anySector n hn χ T hT ξ hξ hgood hline hspan hext

/-- **The trivial-sector reduction, assembled.**  For odd `n ≥ 5` and every even normal character `χ`, the bad-plane injectivity
holds for data of normal character `χ`; a nonzero bad-plane class of an odd or even-weight datum forces `χ = trivialCharacter`,
so the restriction of the `bad_plane_data_injective` to `trivialCharacter` is no restriction. -/
theorem appendix_C6_even_character (n : ℕ) (hn : 4 ≤ n) (hodd : Odd n) (χ : RankOneCharacter)
    (heven : χ.toMonoidHom (realAdeleUnit (-1)) = 1)
    (T : StratumH2 n χ .plane →ₗ[ℂ] StratumH2 n χ .line)
    (hT : ∀ ξ, InnerBoundary n χ .plane ξ →
      ∃ c : cocycles rationalLevel (rationalCoefficientComponent n χ), globalCoordinates n χ c = (ξ, T ξ))
    (ξ : StratumH2 n χ .plane) (hξ : InnerBoundary n χ .plane ξ) (hgood : VanishesOnGood n χ .plane ξ)
    (hline : VanishesOnGood n χ .line (T ξ)) (hspan : ξ ∈ planeDatumSpan n χ) : ξ = 0 :=
  appendix_C6_anySector_of_global n hn χ ((reflScalar_eq_one_iff_even hodd χ).mpr heven) T hT ξ hξ hgood hline hspan

/-- **The binary datum has level one and even weight.**  A datum of any normal character with a nonzero bad-plane
class is spherical (fixed by `GL₂(Ẑ)`, i.e. of level one) and `n` is odd, i.e. the weight `k = n + 3` is even. -/
theorem spherical_and_odd_of_bad_plane {n : ℕ} (D : InducingData n) {a : StratumH2 n D.chi .plane}
    (ha : a ∈ boundarySummand D .plane) (hbad : cuspRes n D.chi .plane false a ≠ 0) :
    SphericalCusp D.cusp ∧ Odd n := by
  have hsph : SphericalCusp D.cusp := by
    by_contra hns
    exact hbad (TernaryPeriodPolynomials.Separation.cuspRes_plane_false_eq_zero_of_not_spherical
      D hns ha)
  exact ⟨hsph, TernaryPeriodPolynomials.LevelOneCohomologicalParity.Helpers.cohomological_spherical_odd n D.cusp
      D.cohomological hsph⟩

end TernaryPeriodPolynomials.Argument.KDaggerComparison
