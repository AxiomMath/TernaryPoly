module

public import TernaryPeriodPolynomials.BoundaryComparison.GlobalEntry
public import TernaryPeriodPolynomials.ModularForm.Periods.OuterLValues
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.EulerProduct
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFiniteEndpointValue

@[expose] public section


/-!
# The library's finite entry is the global-entry ratio

The library computes the finite part of the good-line entry at the cohomological point as
`goodLineFiniteVectorIntegral_endpointValue`:
`∫ = L^{(3)}(h, k-2)/L^{(3)}(h, k-1) · (cusp vector at 1)`, where `L^{(3)} = LSeries (removeEulerCoefficients a 3)`
omits the Euler factor at `3` on the series side.  The target `global_entry_ne_zero`
(Appendix C.6, `ar:eq:globalentry`) states the same ratio as
`(L(h, k-2)(1 - a₃3^{-(k-2)} + 3^{k-1-2(k-2)})) / (L(h, k-1)(1 - a₃3^{-(k-1)} + 3^{k-1-2(k-1)}))`.
This file proves that the two expressions agree (the `L^{(3)}` part), for a normalized
level-one eigenform of weight `k = n + 3 > 6`, and deduces

* `lSeries_removeEulerThree_eq`: `L^{(3)}(s) = L(s)(1 - a₃3^{-s} + 3^{k-1-2s})` at `s = k-2, k-1`
  (from the library's Euler products over primes `p ∤ m`, split at `p = 3`);
* `goodLineFiniteVectorIntegral_eq_globalEntryRatio`: the library's finite integral at the
  cohomological point equals the ratio times `cusp.realize vector 1`;
* `goodLineFiniteVectorIntegral_ne_zero`: the finite integral is nonzero as soon as
  `cusp.realize vector 1 ≠ 0` (by `global_entry_ne_zero`'s nonvanishing of the ratio).

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

open TernaryPeriodPolynomials.Argument
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)

/-- Splitting the Euler product at one prime: `L^{(q)}(s) = L(s) · P_q(s)` for a normalized
level-one eigenform, at a real argument `s > k/2 + 1` where the local polynomial `P_q` does not
vanish. -/
theorem lSeries_removeEuler_prime_eq {weight : ℤ} (form : CuspForm levelOne weight)
    (weight_positive : 0 < weight) (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations weight form eigenvalues)
    (initial : (UpperHalfPlane.qExpansion 1 form).coeff 1 = 1) (q : Nat.Primes) (argument : ℝ)
    (argument_bound : (weight : ℝ) / 2 + 1 < argument)
    (nonzero : classicalPrimeEulerPolynomial q.val weight (eigenvalues q) argument ≠ 0) :
    LSeries (removeEulerCoefficients (fun index => (UpperHalfPlane.qExpansion 1 form).coeff index)
        q.val) argument =
      LSeries (fun index => (UpperHalfPlane.qExpansion 1 form).coeff index) argument *
        classicalPrimeEulerPolynomial q.val weight (eigenvalues q) argument := by
  set factor : Nat.Primes → ℂ := fun place =>
    (classicalPrimeEulerPolynomial place.val weight (eigenvalues place) argument)⁻¹ with hfactor
  have whole := levelOneCuspForm_classicalEuler_hasProd form weight_positive eigenvalues relations
    initial 1 argument argument_bound
  have partial_ := levelOneCuspForm_classicalEuler_hasProd form weight_positive eigenvalues
    relations initial q.val argument argument_bound
  have coefficients_one : removeEulerCoefficients
      (fun index => (UpperHalfPlane.qExpansion 1 form).coeff index) 1 =
      fun index => (UpperHalfPlane.qExpansion 1 form).coeff index := by
    funext index
    simp [removeEulerCoefficients]
  rw [coefficients_one] at whole
  have whole' : HasProd factor
      (LSeries (fun index => (UpperHalfPlane.qExpansion 1 form).coeff index) argument) := by
    have mulIndicator := (hasProd_subtype_iff_mulIndicator (f := factor)
      (s := {place : Nat.Primes | place.val.Coprime 1})).mp whole
    have everything : {place : Nat.Primes | place.val.Coprime 1}.mulIndicator factor = factor :=
      Set.mulIndicator_eq_self.mpr (fun place _ => Nat.coprime_one_right _)
    rwa [everything] at mulIndicator
  have partial' := (hasProd_subtype_iff_mulIndicator (f := factor)
    (s := {place : Nat.Primes | place.val.Coprime q.val})).mp partial_
  have single : HasProd (fun place : Nat.Primes => if place = q then factor q else 1)
      (factor q) := hasProd_ite_eq q (factor q)
  have combined := partial'.mul single
  have notCoprime : ¬ q.val.Coprime q.val := by
    rw [Nat.coprime_self]
    exact q.property.one_lt.ne'
  have equality : (fun place : Nat.Primes =>
      {place : Nat.Primes | place.val.Coprime q.val}.mulIndicator factor place *
        (if place = q then factor q else 1)) = factor := by
    funext place
    by_cases same : place = q
    · subst same
      simp [Set.mulIndicator, notCoprime]
    · have coprime : place.val.Coprime q.val :=
        (Nat.coprime_primes place.property q.property).mpr (fun h => same (Subtype.ext h))
      simp [Set.mulIndicator, coprime, same]
  rw [equality] at combined
  have unique := whole'.unique combined
  rw [unique, hfactor]
  field_simp

/-- The local Euler polynomial in the shape of the global-entry statement. -/
theorem classicalPrimeEulerPolynomial_eq (p : ℕ) (hp : 0 < p) (k : ℤ) (a s : ℂ) :
    classicalPrimeEulerPolynomial p k a s =
      1 - a * (p : ℂ) ^ (-s) + (p : ℂ) ^ ((k : ℂ) - 1 - 2 * s) := by
  have nonzero : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have exponent_eq : (p : ℂ) ^ (k - 1) * ((p : ℂ) ^ (-s)) ^ 2 = (p : ℂ) ^ ((k : ℂ) - 1 - 2 * s) := by
    rw [← Complex.cpow_intCast, ← Complex.cpow_mul_nat, ← Complex.cpow_add _ _ nonzero]
    congr 1
    push_cast
    ring
  rw [classicalPrimeEulerPolynomial, exponent_eq]

/-- The Fourier coefficient of the definitions is the library's `q`-expansion coefficient. -/
theorem fourierCoeff_eq {k : ℤ} (h : CuspForm levelOne k) :
    (fun m => fourierCoeff h m) = fun m => (UpperHalfPlane.qExpansion 1 h).coeff m := by
  funext m
  simp [fourierCoeff, Subgroup.strictWidthInfty_SL2Z]

/-- The omitted-factor `L`-value `L^{(3)}(h, s)` equals `L(h, s)(1 - a₃3^{-s} + 3^{k-1-2s})` at
`s = k - 2, k - 1` (`L^{(3)}` part): the library's `LSeries (removeEulerCoefficients a 3)` is the
global-entry numerator/denominator. -/
theorem lSeries_removeEulerThree_eq {k : ℤ} (hk : 6 < k) (h : CuspForm levelOne k)
    (hh : IsNormalizedEigenform h) (s : ℂ) (hs : s = (k : ℂ) - 2 ∨ s = (k : ℂ) - 1) :
    LSeries (removeEulerCoefficients (fun m => fourierCoeff h m) 3) s =
      LSeries (fun m => fourierCoeff h m) s *
        (1 - fourierCoeff h 3 * (3 : ℂ) ^ (-s) + (3 : ℂ) ^ ((k : ℂ) - 1 - 2 * s)) := by
  have nonzero := lemma_2_5' hk h hh {primeThree} s hs
  simp only [Finset.prod_singleton, show (primeThree : ℕ) = 3 from rfl, Nat.cast_ofNat] at nonzero
  have factor_ne := (mul_ne_zero_iff.mp nonzero).2
  obtain ⟨initial, eigenvalue, relations⟩ := hh
  have heq := fourierCoeff_eq h
  have c1 : fourierCoeff h 1 = (UpperHalfPlane.qExpansion 1 h).coeff 1 := congrFun heq 1
  have initial' : (UpperHalfPlane.qExpansion 1 h).coeff 1 = 1 := c1.symm.trans initial
  have period : (1 : ℝ) ∈ levelOne.strictPeriods := by
    simpa only [Subgroup.strictWidthInfty_SL2Z] using levelOne.strictWidthInfty_mem_strictPeriods
  have first : (UpperHalfPlane.qExpansion 1 h).coeff 3 = eigenvalue primeThree :=
    cuspForm_hecke_prime_coefficient h period primeThree (eigenvalue primeThree)
      (relations primeThree) initial'
  have c3 : fourierCoeff h 3 = eigenvalue primeThree := (congrFun heq 3).trans first
  have hk' : (6 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  obtain ⟨argument, bound, hargument⟩ : ∃ argument : ℝ, (k : ℝ) / 2 + 1 < argument ∧
      (argument : ℂ) = s := by
    rcases hs with rfl | rfl
    · exact ⟨(k : ℝ) - 2, by linarith, by push_cast; ring⟩
    · exact ⟨(k : ℝ) - 1, by linarith, by push_cast; ring⟩
  subst hargument
  have polynomial := classicalPrimeEulerPolynomial_eq 3 (by norm_num) k (eigenvalue primeThree)
    (argument : ℂ)
  simp only [Nat.cast_ofNat] at polynomial
  have factor_ne' : classicalPrimeEulerPolynomial 3 k (eigenvalue primeThree) argument ≠ 0 := by
    rw [polynomial, ← c3]
    exact factor_ne
  have bridge := lSeries_removeEuler_prime_eq h (by omega) eigenvalue relations initial'
    primeThree argument bound factor_ne'
  rw [heq, c3]
  rw [show (primeThree : ℕ) = 3 from rfl, polynomial] at bridge
  exact bridge

/-- **The global entry ratio** `L(h,k-2)(1 - a₃3^{-(k-2)} + 3^{k-1-2(k-2)}) /
(L(h,k-1)(1 - a₃3^{-(k-1)} + 3^{k-1-2(k-1)}))` of Appendix C.6 (`ar:eq:globalentry`, without the
constant `-2πi/(9(n+1))`). -/
def globalEntryRatio {k : ℤ} (h : CuspForm levelOne k) : ℂ :=
  (LSeries (fun m => fourierCoeff h m) ((k : ℂ) - 2) *
      (1 - fourierCoeff h 3 * (3 : ℂ) ^ (-((k : ℂ) - 2)) +
        (3 : ℂ) ^ ((k : ℂ) - 1 - 2 * ((k : ℂ) - 2)))) /
    (LSeries (fun m => fourierCoeff h m) ((k : ℂ) - 1) *
      (1 - fourierCoeff h 3 * (3 : ℂ) ^ (-((k : ℂ) - 1)) +
        (3 : ℂ) ^ ((k : ℂ) - 1 - 2 * ((k : ℂ) - 1))))

/-- The ratio of the omitted-factor `L`-values of the library is the global entry ratio. -/
theorem removeEulerThree_ratio_eq {k : ℤ} (hk : 6 < k) (h : CuspForm levelOne k)
    (hh : IsNormalizedEigenform h) :
    LSeries (removeEulerCoefficients (fun index => (UpperHalfPlane.qExpansion 1 h).coeff index) 3)
        ((k : ℂ) - 2) /
      LSeries (removeEulerCoefficients (fun index => (UpperHalfPlane.qExpansion 1 h).coeff index) 3)
        ((k : ℂ) - 1) = globalEntryRatio h := by
  have first := lSeries_removeEulerThree_eq hk h hh ((k : ℂ) - 2) (Or.inl rfl)
  have second := lSeries_removeEulerThree_eq hk h hh ((k : ℂ) - 1) (Or.inr rfl)
  rw [fourierCoeff_eq] at first second
  rw [first, second]
  rw [globalEntryRatio, fourierCoeff_eq]

/-- The global entry ratio is nonzero (Lemma 2.5 with the omitted Euler factor at `3`). -/
theorem globalEntryRatio_ne_zero {k : ℤ} (hk : 6 < k) (h : CuspForm levelOne k)
    (hh : IsNormalizedEigenform h) : globalEntryRatio h ≠ 0 := by
  have lower := lemma_2_5' hk h hh {primeThree} ((k : ℂ) - 2) (Or.inl rfl)
  have upper := lemma_2_5' hk h hh {primeThree} ((k : ℂ) - 1) (Or.inr rfl)
  simp only [Finset.prod_singleton, show (primeThree : ℕ) = 3 from rfl, Nat.cast_ofNat] at lower upper
  exact div_ne_zero lower upper

/-- The global entry ratio at weight `n + 3` is the inner ratio of the `global_entry_ne_zero`. -/
theorem globalEntryRatio_eq_frozen (n : ℕ) (h : CuspForm levelOne ((n : ℤ) + 3)) :
    globalEntryRatio h =
      (LSeries (fun m => fourierCoeff h m) ((n : ℂ) + 1) *
          (1 - fourierCoeff h 3 * (3 : ℂ) ^ (-((n : ℂ) + 1)) +
            (3 : ℂ) ^ ((n : ℂ) + 2 - 2 * ((n : ℂ) + 1)))) /
        (LSeries (fun m => fourierCoeff h m) ((n : ℂ) + 2) *
          (1 - fourierCoeff h 3 * (3 : ℂ) ^ (-((n : ℂ) + 2)) +
            (3 : ℂ) ^ ((n : ℂ) + 2 - 2 * ((n : ℂ) + 2)))) := by
  have cast : ((((n : ℤ) + 3 : ℤ)) : ℂ) = (n : ℂ) + 3 := by push_cast; ring
  have e1 : (n : ℂ) + 3 - 2 = (n : ℂ) + 1 := by ring
  have e2 : (n : ℂ) + 3 - 1 = (n : ℂ) + 2 := by ring
  unfold globalEntryRatio
  rw [cast, e1, e2]

/-- **The library's finite entry at the cohomological point is the global-entry ratio.**
`goodLineFiniteVectorIntegral_endpointValue` with the omitted-factor `L`-values rewritten as the
`global_entry_ne_zero` ratio, for a normalized level-one eigenform `form` of weight
`-2 * halfWeight = degree + 3`. -/
theorem goodLineFiniteVectorIntegral_eq_globalEntryRatio (cusp : CuspidalRepresentation)
    (spherical_cusp : SphericalCusp cusp) {degree : ℕ} (large : 3 < degree)
    (cohomological : Cohomological cusp degree) (halfWeight : ℤ)
    (weight : 2 * halfWeight = -((degree : ℤ) + 3))
    (form : CuspForm levelOne (-2 * halfWeight)) (normalized : fourierCoeff form 1 = 1)
    (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations (-2 * halfWeight) form eigenvalues)
    (vector : cusp.smooth) (nonzero : vector ≠ 0) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (eigen : ∀ prime : Nat.Primes, cuspPrimeHeckeSum cusp prime vector =
      ((prime.val : ℂ) ^ (halfWeight + 1) * eigenvalues prime) • vector) :
    goodLineFiniteVectorIntegral degree cusp cohomologicalPoint vector =
      globalEntryRatio form * cusp.realize vector 1 := by
  have form_nonzero : form ≠ 0 := by
    intro zero
    rw [zero] at normalized
    simp [fourierCoeff, UpperHalfPlane.qExpansion_zero] at normalized
  have hk : 6 < -2 * halfWeight := by omega
  rw [goodLineFiniteVectorIntegral_endpointValue cusp spherical_cusp large cohomological
    halfWeight weight form form_nonzero eigenvalues relations vector nonzero spherical eigen,
    removeEulerThree_ratio_eq hk form ⟨normalized, eigenvalues, relations⟩]

/-- The finite entry is nonzero on a vector with `cusp.realize vector 1 ≠ 0`. -/
theorem goodLineFiniteVectorIntegral_ne_zero (cusp : CuspidalRepresentation)
    (spherical_cusp : SphericalCusp cusp) {degree : ℕ} (large : 3 < degree)
    (cohomological : Cohomological cusp degree) (halfWeight : ℤ)
    (weight : 2 * halfWeight = -((degree : ℤ) + 3))
    (form : CuspForm levelOne (-2 * halfWeight)) (normalized : fourierCoeff form 1 = 1)
    (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations (-2 * halfWeight) form eigenvalues)
    (vector : cusp.smooth) (nonzero : vector ≠ 0) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (eigen : ∀ prime : Nat.Primes, cuspPrimeHeckeSum cusp prime vector =
      ((prime.val : ℂ) ^ (halfWeight + 1) * eigenvalues prime) • vector)
    (realize_ne : cusp.realize vector 1 ≠ 0) :
    goodLineFiniteVectorIntegral degree cusp cohomologicalPoint vector ≠ 0 := by
  rw [goodLineFiniteVectorIntegral_eq_globalEntryRatio cusp spherical_cusp large cohomological
    halfWeight weight form normalized eigenvalues relations vector nonzero spherical eigen]
  exact mul_ne_zero (globalEntryRatio_ne_zero (by omega) form ⟨normalized, eigenvalues, relations⟩)
    realize_ne

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
