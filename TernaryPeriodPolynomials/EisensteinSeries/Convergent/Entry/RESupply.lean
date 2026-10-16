module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Class.LevelSpherical
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REValue
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Period.Eigen
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelOneParity
public import TernaryPeriodPolynomials.ArithmeticCohomology.BadPlane.SupportSphericity

@[expose] public section


/-!
# R-e supply: the entry data `SphericalEntryData` exists for the actual datum

`FiniteEntryIdentity` is proved under `SphericalEntryData D` (`Entry/REMain`).  This file shows that the data the
class level actually consumes provide such an `S`, together with the lowest-weight (Eichler) input whose scalar
function is `S.F`, hence the holomorphy and the decay of `S.F` needed by `classLevel_badPlane`.

* The paper's argument (ms., odd `n`) that the normal character is globally trivial and that the binary
  datum is finite-spherical of level one and even weight `k = n + 3` is, in this development, split into the closed
  pieces consumed by the per-datum detection: the data are `CohomologicalCuspData` (character `trivialCharacter` by
  definition), `bad_plane_support_sphericity` (a nonzero bad-plane class forces `SphericalCusp D.cusp`),
  `level_one_cohomological_parity` (spherical and cohomological force `n` odd).  They are the hypotheses
  `D.chi = trivialCharacter`, `SphericalCusp D.cusp`, `Odd n` of `exists_sphericalEntryPackage`.
* `exists_sphericalEntryPackage`: for such a `D` there are a `SphericalEntryData D` and an `EichlerInput D.cusp n` with
  the same vector and half weight (a nonzero spherical lowest-weight prime Hecke eigenvector of a level-one eigenform),
  the form of `S` being the normalization of the classical form of the vector.
* `SphericalEntryPackage.holomorphic`, `.decay`: `S.F x` is holomorphic on the upper half plane for every adelic base
  `x` (`cuspScalarWeightedRealization_holomorphic`, from the orbit holomorphy of the lowest-weight vector), and
  satisfies `‖S.F x z‖² (Im z)^(n+3) ≤ M`.

* Scope of the finite entry (item 1): the paper evaluates the bad-plane integral only at the good-line
  cusp `g₀` (ms., `(T₃φ)(g₀) = v₀/9`; ms. combines it with the Euler factors; ms. and
 use only "the image at the good-line cusp" and the good-line component).  The other `K₁`-orbit of lines is
  never evaluated, so no integral there is needed; `finiteEntryIdentity_mono_guard` and `badPlaneEntryIdentity_of_support`
  record that `FiniteEntryIdentity` quantifies only over the support of the line guard.

A bare `SphericalEntryData D` does not determine holomorphy (it does not record the archimedean weight of the vector);
the package does.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.Argument
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

/-- `FiniteEntryIdentity` is monotone in its line guard: it only quantifies over `g` with `ιL g ≠ 0`. -/
theorem finiteEntryIdentity_mono_guard {n : ℕ} {D : InducingData n} {ι ιL ιL' : AdelicGL → ℂ}
    {F : BinaryAdelicGL → ℂ → ℂ} {r : ℂ} (h : FiniteEntryIdentity D ι ιL F r)
    (hsupp : ∀ g, ιL' g ≠ 0 → ιL g ≠ 0) : FiniteEntryIdentity D ι ιL' F r :=
  fun g hg => h g (hsupp g hg)

/-- **The bad-plane entry only involves the good-line orbit.**  The bad-plane identity holds for every line guard
supported inside the good-line orbit; nothing is asserted (or needed by the paper) at the other line orbit. -/
theorem badPlaneEntryIdentity_of_support {n : ℕ} {D : InducingData n} (S : SphericalEntryData D)
    (ιL : AdelicGL → ℂ) (hsupp : ∀ g, ιL g ≠ 0 → goodLineWeight g ≠ 0) :
    FiniteEntryIdentity D badPlaneWeight ιL S.F S.rBad :=
  finiteEntryIdentity_mono_guard (badPlaneEntryIdentity S) hsupp

/-- The entry data of `FiniteEntryIdentity` together with the lowest-weight Eichler input whose vector it uses. -/
structure SphericalEntryPackage {n : ℕ} (D : InducingData n) where
  /-- The finite-entry data. -/
  S : SphericalEntryData D
  /-- The Eichler input (spherical holomorphic lowest-weight vector). -/
  I : EichlerInput D.cusp n
  vector_eq : I.vector = S.vector
  halfWeight_eq : I.halfWeight = S.halfWeight
  /-- The form of `S` is a nonzero multiple of the classical form of the vector. -/
  scalar : ℂ
  scalar_ne : scalar ≠ 0
  form_eq : (S.form : UpperHalfPlane → ℂ) =
    scalar • cuspScalarWeightedLinear D.cusp S.halfWeight 1 S.vector

namespace SphericalEntryPackage

variable {n : ℕ} {D : InducingData n} (P : SphericalEntryPackage D)

/-- **Holomorphy of the datum.** `S.F x` is holomorphic on the upper half plane for every adelic base point. -/
theorem holomorphic (x : BinaryAdelicGL) :
    DifferentiableOn ℂ (P.S.F x) {z : ℂ | 0 < z.im} := by
  have h := cuspScalarWeightedRealization_holomorphic D.cusp P.I.halfWeight P.I.vector
    P.I.vector_spherical P.I.rotation P.I.holomorphic x
  rw [P.vector_eq, P.halfWeight_eq] at h
  exact h

/-- **Decay of the datum.** -/
theorem decay (x : BinaryAdelicGL) :
    ∃ M : ℝ, ∀ z : ℂ, 0 < z.im → ‖P.S.F x z‖ ^ 2 * z.im ^ (n + 3) ≤ M :=
  decay_of_weight D.cusp P.S.halfWeight P.S.weight P.S.vector x

end SphericalEntryPackage

/-- **Existence of the entry data for the actual datum.**  For an inducing datum with trivial character and a
spherical cuspidal constituent in odd degree `n` (the hypotheses of the per-datum detection), there is a
`SphericalEntryPackage D`: in particular `SphericalEntryData D`, with `3 < n` (indeed `9 ≤ n`), the character trivial on
the integral units, and a nonzero spherical prime Hecke eigenvector of lowest weight whose scalar function is `S.F`. -/
theorem exists_sphericalEntryPackage {n : ℕ} (D : InducingData n) (hodd : Odd n)
    (hχ : D.chi = trivialCharacter) (hsph : SphericalCusp D.cusp) :
    Nonempty (SphericalEntryPackage D) := by
  obtain ⟨I, form, eigenvalues, form_ne, form_eq, relations⟩ :=
    exists_eichlerInput_eigenform D.cusp hsph hodd D.cohomological
  have weight12 := levelOneCuspForm_weight_ge_twelve form form_ne
  have hw := I.weight
  obtain ⟨normalized, initial, normalized_relations, normalized_eq⟩ :=
    levelOneCuspForm_hecke_normalize form form_ne eigenvalues relations
  have hn : 3 < n := by omega
  have hχ1 : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1 := by
    intro u
    rw [hχ]
    rfl
  have normalized1 : fourierCoeff normalized 1 = 1 := by
    have := congrFun (fourierCoeff_eq normalized) 1
    simpa only [initial] using this
  have period : (1 : ℝ) ∈ (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictPeriods := by
    simpa only [Subgroup.strictWidthInfty_SL2Z] using
      (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictWidthInfty_mem_strictPeriods
  have c_ne := cuspForm_hecke_first_coefficient_ne_zero form period form_ne eigenvalues relations
  let S : SphericalEntryData D :=
    { hχ := hχ1
      large := hn
      halfWeight := I.halfWeight
      weight := I.weight
      form := normalized
      normalized := normalized1
      eigenvalues := eigenvalues
      relations := normalized_relations
      vector := I.vector
      nonzero := I.vector_ne
      spherical := I.vector_spherical
      eigen := fun prime => by
        have scalar_holomorphic := cuspScalarWeightedRealization_holomorphic D.cusp I.halfWeight I.vector
          I.vector_spherical I.rotation I.holomorphic 1
        have classical : I.vector ∈ cuspClassicalVectors D.cusp I.halfWeight :=
          cuspClassicalVectors_mem_of_holomorphic D.cusp I.halfWeight I.vector I.vector_spherical I.rotation
            scalar_holomorphic
        exact cuspClassicalVector_hecke_eigen D.cusp I.central_positive I.halfWeight I.vector classical eigenvalues
          (by rw [← form_eq]; exact relations) prime }
  refine ⟨{ S := S, I := I, vector_eq := rfl, halfWeight_eq := rfl,
            scalar := ((UpperHalfPlane.qExpansion 1 form).coeff 1)⁻¹,
            scalar_ne := inv_ne_zero c_ne, form_eq := ?_ }⟩
  show (normalized : UpperHalfPlane → ℂ) = _
  rw [normalized_eq]
  change ((UpperHalfPlane.qExpansion 1 form).coeff 1)⁻¹ • (form : UpperHalfPlane → ℂ) = _
  rw [form_eq]

/-- **The datum of a nonzero bad-plane class.**  For an inducing datum with trivial character (the paper's
`CohomologicalCuspData`) carrying a nonzero plane class with a bad-plane representative, the support is spherical
(`bad_plane_support_sphericity`), `n` is odd (`level_one_cohomological_parity`), and the entry package exists. -/
theorem exists_sphericalEntryPackage_of_badPlane {n : ℕ} (hn : 0 < n) (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (ξ : boundarySummand D .plane) (hξ : ξ ≠ 0)
    (hrep : BadPlaneRepresentative D ξ) : Nonempty (SphericalEntryPackage D) := by
  have hsph : SphericalCusp D.cusp :=
    TernaryPeriodPolynomials.BadPlaneSupportSphericity.bad_plane_support_sphericity n hn D hχ ξ hξ hrep
  have hodd : Odd n :=
    TernaryPeriodPolynomials.LevelOneCohomologicalParity.level_one_cohomological_parity n hn D hχ hsph
  exact exists_sphericalEntryPackage D hodd hχ hsph

/-- The same for a spherical constituent, `n` being odd by `level_one_cohomological_parity`. -/
theorem exists_sphericalEntryPackage_of_spherical {n : ℕ} (hn : 0 < n) (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hsph : SphericalCusp D.cusp) : Nonempty (SphericalEntryPackage D) :=
  exists_sphericalEntryPackage D
    (TernaryPeriodPolynomials.LevelOneCohomologicalParity.level_one_cohomological_parity n hn D hχ hsph)
    hχ hsph

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
