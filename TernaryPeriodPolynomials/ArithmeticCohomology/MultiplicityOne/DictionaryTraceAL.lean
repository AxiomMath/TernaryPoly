module

public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.DictionaryTrace

@[expose] public section


/-!
# The trace of the Atkin–Lehner translate of a level-three vector

Let `W = [[0,-1],[3,0]]`. For a classical level-three vector `v`, the translate
`cuspFiniteRationalSlash σ W v` is again fixed by `borelThree`: for `b` upper triangular modulo
three the matrix `κ = [[b₁₁, -b₁₀/3], [-3 b₀₁, b₀₀]]` is integral, upper triangular modulo
three, and
`κ W = W b`.  Hence the trace of this translate is spherical and its scalar function is
`3^(halfWeight + 1)` times the classical trace of `f ∣ W`.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.LevelThree
open TernaryPeriodPolynomials.LevelThree.LevelThreePeterssonDomain (rep)

namespace TernaryPeriodPolynomials.MultiplicityOne

/-- The Atkin–Lehner matrix `[[0,-1],[3,0]]` in `GL₂(ℚ)`. -/
def atkinLehnerQ : GeneralLinearGroup (Fin 2) ℚ :=
  ⟨!![0, -1; 3, 0], !![0, 1 / 3; -1, 0], by
    ext row column
    fin_cases row <;> fin_cases column <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two], by
    ext row column
    fin_cases row <;> fin_cases column <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]⟩

/-- The same matrix over `ℤ̂`. -/
def atkinLehnerZ : Matrix (Fin 2) (Fin 2) IntegralAdeles := !![0, -1; 3, 0]

theorem atkinLehnerQ_real_det :
    (GeneralLinearGroup.map (algebraMap ℚ ℝ) atkinLehnerQ).val.det = 3 := by
  norm_num [Matrix.det_fin_two, atkinLehnerQ, GeneralLinearGroup.map_apply]

theorem atkinLehnerZ_map :
    integralEmbedding.mapMatrix atkinLehnerZ =
      (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) atkinLehnerQ).val := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [atkinLehnerZ, atkinLehnerQ, GeneralLinearGroup.map_apply, map_ofNat]

theorem integralReduction_eq_primeReduction (x : IntegralAdeles) :
    integralReduction x = integralPrimeReduction primeThree x := rfl

/-- Conjugation by the Atkin–Lehner matrix preserves `borelThree`. -/
theorem atkinLehner_conj (b : GeneralLinearGroup (Fin 2) IntegralAdeles) (hb : b ∈ borelThree) :
    ∃ κ ∈ borelThree, GeneralLinearGroup.map integralEmbedding κ *
        GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) atkinLehnerQ =
      GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) atkinLehnerQ *
        GeneralLinearGroup.map integralEmbedding b := by
  have lower : integralPrimeReduction primeThree (b.val 1 0) = 0 := by
    rw [← integralReduction_eq_primeReduction]
    exact hb
  obtain ⟨g', hg'⟩ := (integralPrimeReduction_zero_iff_dvd primeThree (b.val 1 0)).mp lower
  have h3 : ((primeThree.val : ℕ) : IntegralAdeles) = 3 := by simp [primeThree]
  rw [h3] at hg'
  let K : Matrix (Fin 2) (Fin 2) IntegralAdeles := !![b.val 1 1, -g'; -(3 * b.val 0 1), b.val 0 0]
  have detK : K.det = b.val.det := by
    show (!![b.val 1 1, -g'; -(3 * b.val 0 1), b.val 0 0] :
      Matrix (Fin 2) (Fin 2) IntegralAdeles).det = _
    rw [Matrix.det_fin_two_of, Matrix.det_fin_two, hg']
    ring
  have unit : IsUnit K := by
    rw [Matrix.isUnit_iff_isUnit_det, detK]
    exact (Matrix.isUnit_iff_isUnit_det b.val).mp b.isUnit
  obtain ⟨κ, hκval⟩ := unit
  have hid : K * atkinLehnerZ = atkinLehnerZ * b.val := by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [K, atkinLehnerZ, Matrix.mul_apply, Fin.sum_univ_two, hg'] <;>
      first | done | ring_nf
  refine ⟨κ, ?_, ?_⟩
  · have r3 : integralReduction (3 : IntegralAdeles) = 0 := by
      rw [map_ofNat]
      decide
    change integralReduction (κ.val 1 0) = 0
    rw [hκval]
    show integralReduction (-(3 * b.val 0 1)) = 0
    rw [map_neg, map_mul, r3, zero_mul]
    rfl
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul, ← atkinLehnerZ_map]
    have e1 : (GeneralLinearGroup.map integralEmbedding κ).val = integralEmbedding.mapMatrix K := by
      rw [← hκval]
      rfl
    have e2 : (GeneralLinearGroup.map integralEmbedding b).val =
        integralEmbedding.mapMatrix b.val := rfl
    rw [e1, e2, ← map_mul, ← map_mul, hid]

theorem conj_aux {G : Type*} [Group G] (A x y : G) (h : y * A = A * x) : x * A⁻¹ = A⁻¹ * y := by
  calc x * A⁻¹ = A⁻¹ * (A * x) * A⁻¹ := by group
    _ = A⁻¹ * (y * A) * A⁻¹ := by rw [h]
    _ = A⁻¹ * y := by group

/-- The Atkin–Lehner translate of a level-three vector is fixed by `borelThree`. -/
theorem slashW_borel_fixed (σ : CuspidalRepresentation) (halfWeight : ℤ) (v : σ.smooth)
    (hv : v.val ∈ levelThreeValues σ)
    (rotation : ∀ angle : Circle, σ.π (atInfinity (binaryRotations angle)) v.val =
      (angle : ℂ) ^ (2 * halfWeight) • v.val)
    (b : GeneralLinearGroup (Fin 2) IntegralAdeles) (hb : b ∈ borelThree) :
    σ.π (atFinite (GeneralLinearGroup.map integralEmbedding b))
        (cuspFiniteRationalSlash σ atkinLehnerQ v).val =
      (cuspFiniteRationalSlash σ atkinLehnerQ v).val := by
  obtain ⟨κ, hκ, hfin⟩ := atkinLehner_conj b hb
  have conj := conj_aux _ _ _ hfin
  have action : (cuspFiniteRationalSlash σ atkinLehnerQ v).val =
      σ.π (atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) atkinLehnerQ)⁻¹) v.val := by
    change σ.π (atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) atkinLehnerQ⁻¹))
      v.val = _
    rw [map_inv]
  rw [action, ← Module.End.mul_apply, ← map_mul, ← atFinite_mul, conj, atFinite_mul, map_mul,
    Module.End.mul_apply, levelThree_fixed_of_borel σ halfWeight v hv rotation κ hκ]

/-- **The trace of the Atkin–Lehner translate of a level-three vector is spherical.** -/
theorem traceVector_atkinLehner_spherical (σ : CuspidalRepresentation) (halfWeight : ℤ)
    (v : σ.smooth) (hv : v.val ∈ levelThreeValues σ)
    (rotation : ∀ angle : Circle, σ.π (atInfinity (binaryRotations angle)) v.val =
      (angle : ℂ) ^ (2 * halfWeight) • v.val) :
    (traceVector σ (cuspFiniteRationalSlash σ atkinLehnerQ v)).val ∈ cuspSphericalValues σ := by
  intro k
  rw [traceVector_val]
  exact traceSum_fixed σ _
    (fun b hb => slashW_borel_fixed σ halfWeight v hv rotation b hb) k

/-- **The scalar function of the trace of the Atkin–Lehner translate**: `3^(halfWeight + 1)` times
the classical trace of `f ∣ W`. -/
theorem traceVector_atkinLehner_scalar (σ : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → σ.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (v : σ.smooth)
    (rotation : ∀ angle : Circle, σ.π (atInfinity (binaryRotations angle)) v.val =
      (angle : ℂ) ^ (2 * halfWeight) • v.val) :
    cuspScalarWeightedLinear σ halfWeight 1
        (traceVector σ (cuspFiniteRationalSlash σ atkinLehnerQ v)) =
      (3 : ℂ) ^ (halfWeight + 1) • ∑ i : Option (Fin 3),
        SlashAction.map (-2 * halfWeight) (rep i)
          (SlashAction.map (-2 * halfWeight) (GeneralLinearGroup.map (algebraMap ℚ ℝ) atkinLehnerQ)
            (cuspScalarWeightedLinear σ halfWeight 1 v)) := by
  have positive : 0 < (GeneralLinearGroup.map (algebraMap ℚ ℝ) atkinLehnerQ).val.det := by
    rw [atkinLehnerQ_real_det]
    norm_num
  have rot' := cuspFiniteRationalSlash_rotation σ atkinLehnerQ (2 * halfWeight) v rotation
  rw [traceVector_scalar σ halfWeight _ rot',
    cuspFiniteRationalSlash_eq_slash σ central_positive halfWeight v rotation atkinLehnerQ
      positive, atkinLehnerQ_real_det]
  simp only [ModularForm.SL_smul_slash, Finset.smul_sum, Complex.ofReal_ofNat]

/-- A non-spherical representation has zero trace of the Atkin–Lehner translate. -/
theorem traceVector_atkinLehner_eq_zero_of_not_spherical (σ : CuspidalRepresentation)
    (halfWeight : ℤ) (v : σ.smooth) (hv : v.val ∈ levelThreeValues σ)
    (rotation : ∀ angle : Circle, σ.π (atInfinity (binaryRotations angle)) v.val =
      (angle : ℂ) ^ (2 * halfWeight) • v.val) (not_spherical : ¬SphericalCusp σ) :
    traceVector σ (cuspFiniteRationalSlash σ atkinLehnerQ v) = 0 := by
  by_contra nonzero
  exact not_spherical ⟨_, nonzero,
    traceVector_atkinLehner_spherical σ halfWeight v hv rotation⟩

end TernaryPeriodPolynomials.MultiplicityOne
