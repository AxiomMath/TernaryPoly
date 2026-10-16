module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REMajorant
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Class.LevelStatements
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.GlobalEntryBridge

@[expose] public section


/-!
# R-e: R-e, the spherical finite entry identity

`SphericalEntryData D` (the hypotheses on the inducing datum and section) and `finiteEntryIdentity_spherical`: `FiniteEntryIdentity D (fun _ => 1) ιL S.F S.rFull` for every guard `ιL`, with `S.rFull` the product of the local Euler factors at all places.

Formalized by Claude Sonnet 5.5.
-/


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

theorem finiteGroup_entryElement (v : FiniteAdeles × FiniteAdeles) (g : AdelicGL) :
    finiteGroup (finiteEntryElement v g) = weyl⁻¹ * lineUnipotent v.1 v.2 * finiteGroup g := by
  unfold finiteEntryElement
  rw [map_mul, map_mul, map_inv]
  change (GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) weyl)⁻¹ *
    GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) (lineUnipotent (0, v.1) (0, v.2)) *
      finiteGroup g = _
  rw [map_weyl, map_lineUnipotent']
  rfl

theorem cF_mul_F_eq_planeCoeff {n : ℕ} (D : InducingData n) (hw : ℤ) (vec : D.cusp.smooth) (x : BinaryAdelicGL)
    (h : AdelicGL) (z : ℂ) :
    cF D h * cuspScalarWeightedRealization D.cusp hw vec (x * bF h) z =
      planeCoeff D.cusp D.chi (((n : ℂ) + 3) / 2) hw vec x (finiteGroup h) z := rfl

theorem cFLine_mul_F_eq_lineCoeff {n : ℕ} (D : InducingData n) (hw : ℤ) (vec : D.cusp.smooth)
    (x : BinaryAdelicGL) (g : AdelicGL) (z : ℂ) :
    cFLine D g * cuspScalarWeightedRealization D.cusp hw vec (x * bFLine g) z =
      lineCoeff D.cusp D.chi (TernaryPeriodPolynomials.SourceConstruction.lineBeta n) hw vec x (finiteGroup g) z := rfl

/-- The hypotheses on the inducing datum and the section under which the finite entry identity is proved: the
character is trivial on the integral units, `3 < n`, and `F` is the scalar function of a nonzero spherical vector
which is a prime Hecke eigenvector for the eigenvalues of a normalized level-one eigenform of weight `n + 3`. -/
structure SphericalEntryData {n : ℕ} (D : InducingData n) where
  hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1
  large : 3 < n
  halfWeight : ℤ
  weight : 2 * halfWeight = -((n : ℤ) + 3)
  form : CuspForm levelOne (-2 * halfWeight)
  normalized : fourierCoeff form 1 = 1
  eigenvalues : Nat.Primes → ℂ
  relations : HasPrimeHeckeRelations (-2 * halfWeight) form eigenvalues
  vector : D.cusp.smooth
  nonzero : vector ≠ 0
  spherical : vector.val ∈ cuspSphericalValues D.cusp
  eigen : ∀ prime : Nat.Primes, cuspPrimeHeckeSum D.cusp prime vector =
    ((prime.val : ℂ) ^ (halfWeight + 1) * eigenvalues prime) • vector

theorem entryExponent_eq (n : ℕ) : ((n : ℂ) / 2 + 3 + cohomologicalPoint) = ((n : ℂ) + 3) / 2 := by
  norm_num [cohomologicalPoint]
  ring

namespace SphericalEntryData

variable {n : ℕ} {D : InducingData n} (S : SphericalEntryData D)

include S

/-- The scalar function of the spherical vector. -/
def F : BinaryAdelicGL → ℂ → ℂ := cuspScalarWeightedRealization D.cusp S.halfWeight S.vector

/-- The local eigenvalues of the sphere operator at the places. -/
def localEigenvalue (place : FinitePlace) : ℂ :=
  ((Rat.HeightOneSpectrum.primesEquiv place).val : ℂ) ^ (S.halfWeight + 1) *
    S.eigenvalues (Rat.HeightOneSpectrum.primesEquiv place)

theorem sphericalCusp : SphericalCusp D.cusp := ⟨S.vector, S.nonzero, S.spherical⟩

theorem exponent_gt : 3 < (((n : ℂ) + 3) / 2).re := by
  have large : (3 : ℝ) < n := by exact_mod_cast S.large
  have : (((n : ℂ) + 3) / 2).re = ((n : ℝ) + 3) / 2 := by
    simp
  rw [this]
  linarith

theorem eigen_place (place : FinitePlace) :
    cuspLocalPadicSphereOperator D.cusp place 1 S.vector = S.localEigenvalue place • S.vector := by
  have := cuspLocalPadicSphereOperator_one_of_hecke_eigen D.cusp S.vector S.spherical place _
    (S.eigen (Rat.HeightOneSpectrum.primesEquiv place))
  unfold localEigenvalue
  simpa only [cohomological_cuspLocalPadicCentralChar_eq_one D.cusp S.sphericalCusp D.cohomological place,
    one_mul] using this

theorem form_ne_zero : S.form ≠ 0 := by
  intro zero
  have normalized := S.normalized
  rw [zero] at normalized
  simp [fourierCoeff, UpperHalfPlane.qExpansion_zero] at normalized

/-- The ratio of the `L`-values with the Euler factor at `3` omitted: the product of the local Euler factors at
the places other than `3`. -/
def value : ℂ :=
  LSeries (removeEulerCoefficients (fun index => (UpperHalfPlane.qExpansion 1 S.form).coeff index) 3)
      (((-2 * S.halfWeight : ℤ) : ℂ) - 2) /
    LSeries (removeEulerCoefficients (fun index => (UpperHalfPlane.qExpansion 1 S.form).coeff index) 3)
      (((-2 * S.halfWeight : ℤ) : ℂ) - 1)

/-- The local Euler factor at the place `3`. -/
def euler3 : ℂ :=
  cuspLocalPadicEulerFactor D.cusp placeThree (S.localEigenvalue placeThree) (((n : ℂ) + 3) / 2)

/-- **The scalar `r`** of the finite entry identity of the spherical section: the product of the local Euler
factors at all places (the one at `3` included). -/
def rFull : ℂ := S.value * S.euler3

theorem product :
    HasProd (fun place : {place : FinitePlace // place ≠ placeThree} =>
      cuspLocalPadicEulerFactor D.cusp place.val (S.localEigenvalue place.val) (((n : ℂ) + 3) / 2)) S.value := by
  have := cuspCriticalEulerProduct_hasProd D.cusp S.sphericalCusp D.cohomological S.halfWeight S.weight S.form
    S.form_ne_zero S.eigenvalues S.relations
  rw [entryExponent_eq] at this
  exact this

end SphericalEntryData

/-- **R-e, spherical case.**  For the spherical section the finite entry identity holds at every `g` (so for any
guard `ιL`), with `r = S.rFull`, the product of the local Euler factors at all places. -/
theorem finiteEntryIdentity_spherical {n : ℕ} {D : InducingData n} (S : SphericalEntryData D)
    (ιL : AdelicGL → ℂ) :
    FiniteEntryIdentity D (fun _ => 1) ιL S.F S.rFull := by
  intro g _ x
  have convergent := S.exponent_gt
  have eigen := S.eigen_place
  have integrand : ∀ (v : FiniteAdeles × FiniteAdeles) (z : ℂ),
      (fun _ : AdelicGL => (1 : ℂ)) (finiteEntryElement v g) *
        (cF D (finiteEntryElement v g) * S.F (x * bF (finiteEntryElement v g)) z) =
      planeCoeff D.cusp D.chi (((n : ℂ) + 3) / 2) S.halfWeight S.vector x
        (weyl⁻¹ * lineUnipotent v.1 v.2 * finiteGroup g) z := by
    intro v z
    rw [one_mul]
    exact (cF_mul_F_eq_planeCoeff D S.halfWeight S.vector x (finiteEntryElement v g) z).trans
      (by rw [finiteGroup_entryElement])
  refine ⟨?_, ?_, ?_⟩
  · simp_rw [integrand]
    exact planeCoeff_measurable D.cusp D.chi _ S.halfWeight S.hχ S.vector S.spherical x (finiteGroup g)
  · intro Z hZ hZ'
    obtain ⟨φ, hφ, bound⟩ := planeCoeff_majorant D.cusp D.chi _ S.halfWeight S.hχ S.vector S.spherical
      convergent x (finiteGroup g) Z hZ hZ'
    refine ⟨φ, hφ, fun v z hz => ?_⟩
    rw [integrand]
    exact bound v z hz
  · intro z _
    simp_rw [integrand]
    rw [planeCoeff_integral D.cusp D.chi _ S.halfWeight S.hχ S.vector S.nonzero S.spherical convergent
      S.localEigenvalue eigen S.value S.product x (finiteGroup g) z]
    unfold SphericalEntryData.rFull SphericalEntryData.euler3 SphericalEntryData.F
    rw [cFLine_mul_F_eq_lineCoeff]
    have : (((n : ℂ) + 3) / 2 - 1) = TernaryPeriodPolynomials.SourceConstruction.lineBeta n := by
      unfold TernaryPeriodPolynomials.SourceConstruction.lineBeta; ring
    rw [this]

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
