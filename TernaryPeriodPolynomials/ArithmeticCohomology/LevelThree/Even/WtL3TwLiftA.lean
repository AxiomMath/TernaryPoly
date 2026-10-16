module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.L3EichlerLift
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtL3TwB
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtRealizeA
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtRealizeB

@[expose] public section


/-!
# The weight-generic level-three sign-twisted Eichler cocycle: scalar realization, first half

Formalized by Claude Sonnet 5.5 (AxiomCode).

Twins of the first half of `L3EichlerLift` for `L3InputWt` (an integer rotation weight
`wt = -(n + 3)`): the Hilbert-level cocycle has smooth components fixed by the level-three Levi
level, and its realization `L3InputWt.alpha` is a polynomial-valued function on the adelic group
satisfying the sign-twisted cocycle identity, vanishing on the orthogonal group and right invariant
under the level-three Levi level.
-/

noncomputable section

namespace TernaryPeriodPolynomials.EvenLevelThree

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.TwistedSource
open TernaryPeriodPolynomials.Separation (PlaneLeviLevel)
open TernaryPeriodPolynomials.MultiplicityOne (levelThreeValues mem_levelThreeValues)
open TernaryPeriodPolynomials.SourceConstruction
  (levelThreeValues_fixedLevel orthogonal_smul_I real_smul_eq_coe)
open scoped Matrix.Norms.Elementwise

/-- The scalar-valued twisted Eichler cocycle of a vector, for an integer rotation weight: the
realization of the Hilbert-level cocycle. -/
def l3AlphaWt (σ : CuspidalRepresentation) (n : ℕ) (wt : ℤ) (v : σ.H) (A : BinaryRealGL) :
    BinaryAdelicGL → Binary.HomogeneousPoly (n + 1) :=
  hilbertLift σ n (l3CocycleWt σ n wt v A)

namespace L3InputWt

variable {σ : CuspidalRepresentation} {n : ℕ} (D : L3InputWt σ n)

theorem fixedLevel : D.vector.val ∈ BinaryLevel.fixedSubspace σ BinaryLevel.finiteCongruence :=
  levelThreeValues_fixedLevel D.vector_level

/-- Every value of the Eichler form is a level-three vector. -/
theorem form_mem_level (w : ℂ) (position : Fin (n + 2)) :
    binaryEndpointHolomorphicFormWt σ n D.wt D.vector.val w position ∈
      levelThreeValues σ := by
  have orbit : cuspAffineOrbitVector σ D.vector.val w ∈ levelThreeValues σ := by
    unfold cuspAffineOrbitVector
    exact MultiplicityOne.levelThreeValues_real_stable σ _ D.vector.val D.vector_level
  unfold binaryEndpointHolomorphicFormWt cuspWeightedAffineOrbitWt
  rw [real_smul_eq_coe (wtFactor D.wt w.im)]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ orbit)

theorem period_fixed (k : GeneralLinearGroup (Fin 2) IntegralAdeles) (hk : PlaneLeviLevel k)
    (z : ℂ) (hz : 0 < z.im) (position : Fin (n + 2)) :
    σ.π (atFinite (GeneralLinearGroup.map integralEmbedding k))
        (binaryEndpointPeriodWt σ n D.wt D.vector.val z position) =
      binaryEndpointPeriodWt σ n D.wt D.vector.val z position := by
  let T := binaryHilbertTranslation (index := Fin (n + 2)) σ
    (atFinite (GeneralLinearGroup.map integralEmbedding k))
  have integrand_fixed : ∀ t : ℝ,
      T ((z - Complex.I) • binaryEndpointHolomorphicFormWt σ n D.wt D.vector.val
        (Complex.I + t • (z - Complex.I))) =
      (z - Complex.I) • binaryEndpointHolomorphicFormWt σ n D.wt D.vector.val
        (Complex.I + t • (z - Complex.I)) := by
    intro t
    funext pos
    simp only [T, binaryHilbertTranslation_apply, Pi.smul_apply, map_smul]
    rw [mem_levelThreeValues.mp (D.form_mem_level _ pos) k hk]
  have transported : T (binaryEndpointPeriodWt σ n D.wt D.vector.val z) =
      binaryEndpointPeriodWt σ n D.wt D.vector.val z := by
    unfold binaryEndpointPeriodWt
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm T
      (binaryEndpointPeriod_integrableWt σ n D.wt D.vector.val z hz)]
    simp only [integrand_fixed]
  exact congrFun transported position

theorem cocycle_smooth (stages : AnalyticScalar.ContinuousStages σ) (A : BinaryRealGL)
    (position : Fin (n + 2)) : D.cocycle A position ∈ σ.smooth := by
  have positive := basePoint_im_pos A
  have reflected_positive : 0 < (binaryComplexReflection (basePoint A)).im := by
    rw [binaryComplexReflection_im]
    exact positive
  have first_smooth := binaryEndpointPeriod_smoothWt (n := n) σ stages D.wt D.vector
    D.fixedLevel (basePoint A) positive
  have second_smooth := binaryEndpointPeriod_smoothWt (n := n) σ stages D.wt D.vector
    D.fixedLevel (binaryComplexReflection (basePoint A)) reflected_positive
  have third_smooth := binaryHilbertOperator_smooth σ UpperHalfPlane.J _ second_smooth
  unfold L3InputWt.cocycle L3InputWt.potential l3PotentialWt
  exact σ.smooth.smul_mem _ (σ.smooth.sub_mem (first_smooth position) (third_smooth position))

theorem cocycle_fixed (k : GeneralLinearGroup (Fin 2) IntegralAdeles) (hk : PlaneLeviLevel k)
    (A : BinaryRealGL) (position : Fin (n + 2)) :
    σ.π (atFinite (GeneralLinearGroup.map integralEmbedding k)) (D.cocycle A position) =
      D.cocycle A position := by
  have positive := basePoint_im_pos A
  have reflected_positive : 0 < (binaryComplexReflection (basePoint A)).im := by
    rw [binaryComplexReflection_im]
    exact positive
  have second := binaryHilbertOperator_preserves_finiteLevel σ (binaryWeightBasis (n + 1))
    UpperHalfPlane.J (GeneralLinearGroup.map integralEmbedding k)
    (binaryEndpointPeriodWt σ n D.wt D.vector.val (binaryComplexReflection (basePoint A)))
    (D.period_fixed k hk _ reflected_positive) position
  have first := D.period_fixed k hk (basePoint A) positive position
  unfold L3InputWt.cocycle L3InputWt.potential l3PotentialWt
  simp only [Pi.smul_apply, Pi.sub_apply]
  rw [map_smul, map_sub, first, second]

/-- The scalar-valued twisted Eichler cocycle: the realization of the Hilbert-level cocycle. -/
def alpha (A : BinaryRealGL) : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1) :=
  hilbertLift σ n (D.cocycle A)

theorem alpha_eq (A : BinaryRealGL) :
    D.alpha A = l3AlphaWt σ n D.wt D.vector.val A := rfl

/-- **The twisted cocycle identity for the scalar Eichler cocycle.** -/
theorem alpha_mul (stages : AnalyticScalar.ContinuousStages σ) (g h : BinaryRealGL)
    (x : BinaryAdelicGL) :
    D.alpha (g * h) x = D.alpha g x +
      signDet g • binaryCohomologicalAction n g (D.alpha h) x := by
  have smooth_g := D.cocycle_smooth stages g
  have smooth_h := D.cocycle_smooth stages h
  have transported := binaryHilbertOperator_smooth σ g (D.cocycle h) smooth_h
  have scaled : ∀ position, (signDet g • binaryHilbertOperator σ (binaryWeightBasis (n + 1)) g
      (D.cocycle h)) position ∈ σ.smooth :=
    fun position => σ.smooth.smul_mem _ (transported position)
  unfold L3InputWt.alpha
  rw [D.cocycle_mul, hilbertLift_add σ _ _ smooth_g scaled, hilbertLift_smul σ _ _ transported,
    hilbertLift_binaryHilbertOperator σ g _ smooth_h]
  rfl

theorem alpha_eq_zero_of_smul_I (A : BinaryRealGL)
    (h : A • UpperHalfPlane.I = UpperHalfPlane.I) (x : BinaryAdelicGL) :
    D.alpha A x = 0 := by
  unfold L3InputWt.alpha
  rw [D.cocycle_eq_zero_of_smul_I A h]
  exact congrFun
    (SourceConstruction.EichlerInput.hilbertLift_zero' (σ := σ) (n := n)) x

/-- **The twisted scalar Eichler cocycle vanishes on every orthogonal matrix.** -/
theorem alpha_orthogonal (k : BinaryRealGL) (hk : k.val.transpose * k.val = 1)
    (x : BinaryAdelicGL) : D.alpha k x = 0 :=
  D.alpha_eq_zero_of_smul_I k (orthogonal_smul_I k hk) x

/-- **Finite level**: the twisted scalar Eichler cocycle is right invariant under the
level-three Levi level. -/
theorem alpha_finiteLevel (stages : AnalyticScalar.ContinuousStages σ)
    (k : GeneralLinearGroup (Fin 2) IntegralAdeles) (hk : PlaneLeviLevel k) (g : BinaryRealGL)
    (x : BinaryAdelicGL) :
    D.alpha g (x * atFinite (GeneralLinearGroup.map integralEmbedding k)) = D.alpha g x := by
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
      Subtype.ext (D.cocycle_fixed k hk g position)
    rw [← equivariant]
    exact congrArg (fun v : σ.smooth => σ.realize v x) same
  unfold L3InputWt.alpha hilbertLift
  exact Finset.sum_congr rfl fun position _ => by rw [step position]

/-- **Finite level, bad-line form**: right invariance under every `k ∈ GL₂(ℤ̂)` with `diag(1, k)`
in the finite level. -/
theorem alpha_finiteLevel_badLine (stages : AnalyticScalar.ContinuousStages σ)
    (k : GeneralLinearGroup (Fin 2) IntegralAdeles)
    (hk : GeneralLinearGroup.map integralEmbedding (lineLevi 1 k) ∈ finiteLevel)
    (g : BinaryRealGL) (x : BinaryAdelicGL) :
    D.alpha g (x * atFinite (GeneralLinearGroup.map integralEmbedding k)) = D.alpha g x :=
  D.alpha_finiteLevel stages k
    ((LevelThreeSource.planeLeviLevel_iff_lineLevi_mem k).mpr hk) g x

end L3InputWt

end TernaryPeriodPolynomials.EvenLevelThree

end
