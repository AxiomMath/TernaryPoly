module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Eichler.Primitive

@[expose] public section


/-!
# Scalar realization of the Eichler cocycle

The Hilbert-level Eichler cocycle `A ↦ P(A · i)` has smooth, finite-level-fixed components. Its
realization `eichlerCocycle` is a polynomial-valued cocycle in the format of
`GeneralEisenstein.Cohomological`, vanishing on the orthogonal group.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

/-! ### Orthogonal matrices fix `i` -/

theorem orthogonal_entries (k : Matrix (Fin 2) (Fin 2) ℝ) (hk : k.transpose * k = 1) :
    k 0 0 * k 0 0 + k 1 0 * k 1 0 = 1 ∧ k 0 1 * k 0 1 + k 1 1 * k 1 1 = 1 ∧
      k 0 0 * k 0 1 + k 1 0 * k 1 1 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hk 0) 0
  · simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hk 1) 1
  · simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hk 0) 1

theorem orthogonal_smul_I_of_pos (k : BinaryRealGL) (hk : k.val.transpose * k.val = 1)
    (positive : 0 < (GeneralLinearGroup.det k).val) : k • UpperHalfPlane.I = UpperHalfPlane.I := by
  obtain ⟨h1, h2, h3⟩ := orthogonal_entries k.val hk
  have det_sq : k.val.det * k.val.det = 1 := by
    have := congrArg Matrix.det hk
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
  have det_pos : 0 < k.val.det := positive
  have det_one : k.val.det = 1 := by
    have factor : (k.val.det - 1) * (k.val.det + 1) = 0 := by linear_combination det_sq
    rcases mul_eq_zero.mp factor with h | h
    · linarith
    · linarith
  rw [Matrix.det_fin_two] at det_one
  rw [UpperHalfPlane.gl_smul_I_eq_I_iff_of_pos positive]
  have e1 : k.val 0 0 * (k.val 1 1 - k.val 0 0) - k.val 1 0 * (k.val 0 1 + k.val 1 0) = 0 := by
    linear_combination det_one - h1
  have e2 : k.val 0 0 * (k.val 0 1 + k.val 1 0) + k.val 1 0 * (k.val 1 1 - k.val 0 0) = 0 := by
    linear_combination h3
  have u : k.val 1 1 - k.val 0 0 = 0 := by
    have : (k.val 0 0 * k.val 0 0 + k.val 1 0 * k.val 1 0) * (k.val 1 1 - k.val 0 0) = 0 := by
      linear_combination k.val 0 0 * e1 + k.val 1 0 * e2
    rw [h1, one_mul] at this
    exact this
  have v : k.val 0 1 + k.val 1 0 = 0 := by
    have : (k.val 0 0 * k.val 0 0 + k.val 1 0 * k.val 1 0) * (k.val 0 1 + k.val 1 0) = 0 := by
      linear_combination (-k.val 1 0) * e1 + k.val 0 0 * e2
    rw [h1, one_mul] at this
    exact this
  exact ⟨by linarith, by linarith⟩

theorem orthogonal_smul_I (k : BinaryRealGL) (hk : k.val.transpose * k.val = 1) :
    k • UpperHalfPlane.I = UpperHalfPlane.I := by
  rcases lt_or_gt_of_ne (GeneralLinearGroup.det k).ne_zero with negative | positive
  · have hJ : (UpperHalfPlane.J : BinaryRealGL).val.transpose * (UpperHalfPlane.J : BinaryRealGL).val
        = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [UpperHalfPlane.val_J, Matrix.mul_apply, Fin.sum_univ_two]
    have orthogonal : (k * UpperHalfPlane.J).val.transpose * (k * UpperHalfPlane.J).val = 1 := by
      have expand : (k * UpperHalfPlane.J).val.transpose * (k * UpperHalfPlane.J).val =
          (UpperHalfPlane.J : BinaryRealGL).val.transpose * (k.val.transpose * k.val) *
            (UpperHalfPlane.J : BinaryRealGL).val := by
        simp only [Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
      rw [expand, hk, Matrix.mul_one, hJ]
    have product_positive : 0 < (GeneralLinearGroup.det (k * UpperHalfPlane.J)).val := by
      simpa only [map_mul, Units.val_mul, UpperHalfPlane.det_J, Units.val_neg, Units.val_one,
        mul_neg_one, neg_pos] using negative
    have fixed := orthogonal_smul_I_of_pos (k * UpperHalfPlane.J) orthogonal product_positive
    rwa [mul_smul, binaryReflection_smul_I] at fixed
  · exact orthogonal_smul_I_of_pos k hk positive

theorem mem_spherical_iff (σ : CuspidalRepresentation) (v : σ.H) :
    v ∈ cuspSphericalValues σ ↔ ∀ k : GeneralLinearGroup (Fin 2) IntegralAdeles,
      σ.π (atFinite (GeneralLinearGroup.map integralEmbedding k)) v = v := Iff.rfl

namespace EichlerInput

variable {σ : CuspidalRepresentation} {n : ℕ} (D : EichlerInput σ n)

theorem fixedLevel : D.vector.val ∈ BinaryLevel.fixedSubspace σ BinaryLevel.finiteCongruence := by
  rintro ⟨element, compact, _, rfl⟩
  exact D.vector_spherical compact

/-- Every value of the Eichler form is a spherical vector. -/
theorem form_mem_spherical (w : ℂ) (position : Fin (n + 2)) :
    binaryEndpointHolomorphicForm σ n D.halfWeight D.vector.val w position ∈
      cuspSphericalValues σ := by
  have orbit : cuspAffineOrbitVector σ D.vector.val w ∈ cuspSphericalValues σ := by
    refine (mem_spherical_iff σ _).mpr fun k => ?_
    unfold cuspAffineOrbitVector
    change (σ.π (atFinite (GeneralLinearGroup.map integralEmbedding k)) *
      σ.π (atInfinity (invertibleMatrix (binaryUpperSectionMatrix w)))) D.vector.val = _
    rw [← map_mul, (atInfinity_commute_atFinite _ _).symm.eq, map_mul, Module.End.mul_apply]
    exact congrArg _ (D.vector_spherical k)
  unfold binaryEndpointHolomorphicForm cuspWeightedAffineOrbit
  rw [real_smul_eq_coe (w.im ^ D.halfWeight)]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ orbit)

theorem period_fixed (k : GeneralLinearGroup (Fin 2) IntegralAdeles) (z : ℂ) (hz : 0 < z.im)
    (position : Fin (n + 2)) :
    σ.π (atFinite (GeneralLinearGroup.map integralEmbedding k))
        (binaryEndpointPeriod σ n D.halfWeight D.vector.val z position) =
      binaryEndpointPeriod σ n D.halfWeight D.vector.val z position := by
  let T := binaryHilbertTranslation (index := Fin (n + 2)) σ
    (atFinite (GeneralLinearGroup.map integralEmbedding k))
  have integrand_fixed : ∀ t : ℝ,
      T ((z - Complex.I) • binaryEndpointHolomorphicForm σ n D.halfWeight D.vector.val
        (Complex.I + t • (z - Complex.I))) =
      (z - Complex.I) • binaryEndpointHolomorphicForm σ n D.halfWeight D.vector.val
        (Complex.I + t • (z - Complex.I)) := by
    intro t
    funext pos
    simp only [T, binaryHilbertTranslation_apply, Pi.smul_apply, map_smul]
    rw [(mem_spherical_iff σ _).mp (D.form_mem_spherical _ pos) k]
  have transported : T (binaryEndpointPeriod σ n D.halfWeight D.vector.val z) =
      binaryEndpointPeriod σ n D.halfWeight D.vector.val z := by
    unfold binaryEndpointPeriod
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm T
      (binaryEndpointPeriod_integrable σ n D.halfWeight D.vector.val z hz)]
    simp only [integrand_fixed]
  exact congrFun transported position

theorem cocycle_smooth (stages : AnalyticScalar.ContinuousStages σ) (A : BinaryRealGL)
    (position : Fin (n + 2)) : D.cocycle A position ∈ σ.smooth := by
  have positive := basePoint_im_pos A
  have reflected_positive : 0 < (binaryComplexReflection (basePoint A)).im := by
    rw [binaryComplexReflection_im]
    exact positive
  have first_smooth := binaryEndpointPeriod_smooth (n := n) σ stages D.halfWeight D.vector
    D.fixedLevel (basePoint A) positive
  have second_smooth := binaryEndpointPeriod_smooth (n := n) σ stages D.halfWeight D.vector
    D.fixedLevel (binaryComplexReflection (basePoint A)) reflected_positive
  have third_smooth := binaryHilbertOperator_smooth σ UpperHalfPlane.J _ second_smooth
  unfold cocycle potential
  exact σ.smooth.smul_mem _ (σ.smooth.add_mem (first_smooth position) (third_smooth position))

theorem cocycle_fixed (k : GeneralLinearGroup (Fin 2) IntegralAdeles) (A : BinaryRealGL)
    (position : Fin (n + 2)) :
    σ.π (atFinite (GeneralLinearGroup.map integralEmbedding k)) (D.cocycle A position) =
      D.cocycle A position := by
  have positive := basePoint_im_pos A
  have reflected_positive : 0 < (binaryComplexReflection (basePoint A)).im := by
    rw [binaryComplexReflection_im]
    exact positive
  have second := binaryHilbertOperator_preserves_finiteLevel σ (binaryWeightBasis (n + 1))
    UpperHalfPlane.J (GeneralLinearGroup.map integralEmbedding k)
    (binaryEndpointPeriod σ n D.halfWeight D.vector.val (binaryComplexReflection (basePoint A)))
    (D.period_fixed k _ reflected_positive) position
  have first := D.period_fixed k (basePoint A) positive position
  unfold cocycle potential
  simp only [Pi.smul_apply, Pi.add_apply]
  rw [map_smul, map_add, first, second]

/-- The scalar-valued Eichler cocycle: the realization of the Hilbert-level cocycle. -/
def eichlerCocycle (A : BinaryRealGL) : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1) :=
  hilbertLift σ n (D.cocycle A)

theorem hilbertLift_zero' : hilbertLift σ n (0 : Fin (n + 2) → σ.H) = 0 := by
  have zero_realize : ∀ x, smoothRealize σ (0 : σ.H) x = 0 := fun x => by
    have := smoothRealize_of_mem σ (0 : σ.smooth)
    simpa using congrFun this x
  funext x
  simp [hilbertLift, zero_realize]

/-- **The cocycle identity for the scalar Eichler cocycle.** -/
theorem eichlerCocycle_mul (stages : AnalyticScalar.ContinuousStages σ) (g h : BinaryRealGL)
    (x : BinaryAdelicGL) :
    D.eichlerCocycle (g * h) x = D.eichlerCocycle g x +
      binaryCohomologicalAction n g (D.eichlerCocycle h) x := by
  have smooth_g := D.cocycle_smooth stages g
  have smooth_h := D.cocycle_smooth stages h
  have transported := binaryHilbertOperator_smooth σ g (D.cocycle h) smooth_h
  unfold eichlerCocycle
  rw [D.cocycle_mul, hilbertLift_add σ _ _ smooth_g transported,
    hilbertLift_binaryHilbertOperator σ g _ smooth_h]
  rfl

theorem eichlerCocycle_eq_zero_of_smul_I (A : BinaryRealGL)
    (h : A • UpperHalfPlane.I = UpperHalfPlane.I) (x : BinaryAdelicGL) :
    D.eichlerCocycle A x = 0 := by
  unfold eichlerCocycle
  rw [D.cocycle_eq_zero_of_smul_I A h]
  exact congrFun (hilbertLift_zero' (σ := σ) (n := n)) x

/-- **The scalar Eichler cocycle vanishes on every orthogonal matrix.** -/
theorem eichlerCocycle_orthogonal (k : BinaryRealGL) (hk : k.val.transpose * k.val = 1)
    (x : BinaryAdelicGL) : D.eichlerCocycle k x = 0 :=
  D.eichlerCocycle_eq_zero_of_smul_I k (orthogonal_smul_I k hk) x

/-- **Finite level**: the scalar Eichler cocycle is right invariant under `GL₂(Ẑ)`. -/
theorem eichlerCocycle_finiteLevel (stages : AnalyticScalar.ContinuousStages σ)
    (k : GeneralLinearGroup (Fin 2) IntegralAdeles) (g : BinaryRealGL) (x : BinaryAdelicGL) :
    D.eichlerCocycle g (x * atFinite (GeneralLinearGroup.map integralEmbedding k)) =
      D.eichlerCocycle g x := by
  have step : ∀ position : Fin (n + 2),
      smoothRealize σ (D.cocycle g position)
        (x * atFinite (GeneralLinearGroup.map integralEmbedding k)) =
      smoothRealize σ (D.cocycle g position) x := by
    intro position
    rw [smoothRealize_of_mem σ ⟨_, D.cocycle_smooth stages g position⟩]
    have equivariant := σ.equivariant (atFinite (GeneralLinearGroup.map integralEmbedding k))
      ⟨D.cocycle g position, D.cocycle_smooth stages g position⟩ x
    have same : (⟨σ.π (atFinite (GeneralLinearGroup.map integralEmbedding k))
        (D.cocycle g position), σ.smooth_stable _ _ (D.cocycle_smooth stages g position)⟩ :
          σ.smooth) = ⟨D.cocycle g position, D.cocycle_smooth stages g position⟩ :=
      Subtype.ext (D.cocycle_fixed k g position)
    rw [← equivariant]
    exact congrArg (fun v : σ.smooth => σ.realize v x) same
  unfold eichlerCocycle hilbertLift
  exact Finset.sum_congr rfl fun position _ => by rw [step position]

end EichlerInput

end TernaryPeriodPolynomials.SourceConstruction

end
