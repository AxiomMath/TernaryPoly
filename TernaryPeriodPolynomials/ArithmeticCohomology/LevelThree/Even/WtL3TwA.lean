module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.L3EichlerPrimitive
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtEndpoint

@[expose] public section


/-!
# Weight-generic level-three Eichler input, first half

Formalized by Claude Sonnet 5.5 (AxiomCode).

Twins of the `halfWeight`-dependent declarations of `L3EichlerRho` and `L3EichlerPrimitive` for an
integer rotation weight `wt = -(n + 3)`, so that the odd weights of even degree `n` are covered:
the twisted endpoint differential, the input structure `L3InputWt`, the potential and cocycle
functions, and the Eichler period as a primitive of the holomorphic form.
-/

noncomputable section

namespace TernaryPeriodPolynomials.EvenLevelThree

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.TwistedSource
open TernaryPeriodPolynomials.MultiplicityOne (LevelThreeCusp levelThreeValues)
open TernaryPeriodPolynomials.SourceConstruction (l3_affineOrbit_reflection)

/-- Both complex types of the sign-twisted plane differential, with all height powers canceled. -/
theorem l3_endpointDifferentialTw_holomorphicFormWt (σ : CuspidalRepresentation)
    (hσ : LevelThreeCusp σ) (degree : ℕ) (wt : ℤ)
    (weight : wt = -((degree : ℤ) + 3))
    (vector : σ.H) (point : ℂ) (positive : 0 < point.im) (direction : ℂ) :
    binaryEndpointDifferentialTw σ (binaryWeightBasis (degree + 1)) (Pi.single 0 vector) point
        direction =
      (2 : ℂ)⁻¹ • (direction • binaryEndpointHolomorphicFormWt σ degree wt vector point +
        (starRingEnd ℂ direction) • binaryHilbertOperator σ (binaryWeightBasis (degree + 1))
          UpperHalfPlane.J
          (binaryEndpointHolomorphicFormWt σ degree wt vector
            (binaryComplexReflection point))) := by
  have reflected_positive : 0 < (binaryComplexReflection point).im := by
    rw [binaryComplexReflection_im]
    exact positive
  have reflected_weighted : point.im⁻¹ •
      binaryAffineOrbitVector σ (binaryWeightBasis (degree + 1))
        (binaryHilbertOperator σ (binaryWeightBasis (degree + 1)) UpperHalfPlane.J
          (Pi.single 0 vector)) point =
      binaryHilbertOperator σ (binaryWeightBasis (degree + 1)) UpperHalfPlane.J
        (binaryEndpointHolomorphicFormWt σ degree wt vector
          (binaryComplexReflection point)) := by
    rw [l3_affineOrbit_reflection σ hσ _ _ point positive,
      ← ContinuousLinearMap.map_smul_of_tower]
    congr 1
    rw [← binaryComplexReflection_im point]
    exact binaryEndpointHolomorphicForm_eqWt σ degree wt weight vector _ reflected_positive
  change point.im⁻¹ • binaryHilbertOperator σ (binaryWeightBasis (degree + 1))
    (invertibleMatrix (binaryUpperSectionMatrix point))
    ((2 : ℂ)⁻¹ • (direction • (Pi.single 0 vector : Fin (degree + 2) → σ.H) +
      (starRingEnd ℂ direction) •
        binaryHilbertOperator σ (binaryWeightBasis (degree + 1)) UpperHalfPlane.J
          (Pi.single 0 vector))) = _
  rw [map_smul, map_add, map_smul, map_smul, smul_comm point.im⁻¹, smul_add,
    smul_comm point.im⁻¹ direction, smul_comm point.im⁻¹ (starRingEnd ℂ direction)]
  change (2 : ℂ)⁻¹ • (direction •
    (point.im⁻¹ • binaryAffineOrbitVector σ (binaryWeightBasis (degree + 1))
      (Pi.single 0 vector) point) +
      (starRingEnd ℂ direction) • (point.im⁻¹ • binaryAffineOrbitVector σ
        (binaryWeightBasis (degree + 1))
        (binaryHilbertOperator σ (binaryWeightBasis (degree + 1)) UpperHalfPlane.J
          (Pi.single 0 vector)) point)) = _
  rw [binaryEndpointHolomorphicForm_eqWt σ degree wt weight vector point positive,
    reflected_weighted]

/-- The input of the weight-generic level-three Eichler construction: a smooth holomorphic
lowest-weight vector of rotation weight `wt = -(n + 3)` fixed by the level-three Levi level, in a
cuspidal representation whose central character is trivial on the positive reals. -/
structure L3InputWt (σ : CuspidalRepresentation) (n : ℕ) where
  central_positive : ∀ unit : ℝˣ, 0 < unit.val → σ.centralCharacter (realAdeleUnit unit) = 1
  cusp3 : LevelThreeCusp σ
  wt : ℤ
  weight : wt = -((n : ℤ) + 3)
  vector : σ.smooth
  vector_level : vector.val ∈ levelThreeValues σ
  rotation : ∀ angle : Circle, σ.π (atInfinity (binaryRotations angle)) vector.val =
    (angle : ℂ) ^ wt • vector.val
  holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbitWt σ wt vector.val)
    UpperHalfPlane.upperHalfPlaneSet

/-- The reflection-antisymmetrised Eichler potential `½ (Per z - J Per(-conj z))` of a vector. -/
def l3PotentialWt (σ : CuspidalRepresentation) (n : ℕ) (wt : ℤ) (v : σ.H) (z : ℂ) :
    Fin (n + 2) → σ.H :=
  (2 : ℂ)⁻¹ • (binaryEndpointPeriodWt σ n wt v z -
    binaryHilbertOperator σ (binaryWeightBasis (n + 1)) UpperHalfPlane.J
      (binaryEndpointPeriodWt σ n wt v (binaryComplexReflection z)))

/-- The twisted Hilbert-level Eichler cocycle `A ↦ P⁻(A · i)` of a vector. -/
def l3CocycleWt (σ : CuspidalRepresentation) (n : ℕ) (wt : ℤ) (v : σ.H)
    (A : BinaryRealGL) : Fin (n + 2) → σ.H :=
  l3PotentialWt σ n wt v (basePoint A)

namespace L3InputWt

variable {σ : CuspidalRepresentation} {n : ℕ} (D : L3InputWt σ n)

/-- The lowest-weight tuple. -/
def lower : Fin (n + 2) → σ.H := Pi.single 0 D.vector.val

theorem lower_rotation (θ : Circle) :
    binaryHilbertOperator σ (binaryWeightBasis (n + 1)) (binaryRotations θ) D.lower =
      ((θ : ℂ) ^ 2)⁻¹ • D.lower := by
  have hw := D.weight
  have coordinates : ∀ (position : Fin (n + 2)) (angle : Circle),
      σ.π (atInfinity (binaryRotations angle)) (D.lower position) =
        (angle : ℂ) ^ binaryUnitaryWeight n (-2) position • D.lower position := by
    intro position angle
    by_cases h : position = 0
    · subst h
      have weight_eq : binaryUnitaryWeight n (-2) 0 = D.wt := by
        simp [binaryUnitaryWeight]
        omega
      rw [weight_eq]
      simp only [lower, Pi.single_eq_same]
      exact D.rotation angle
    · simp only [lower, Pi.single_eq_of_ne h, map_zero, smul_zero]
  rw [binaryWeightBasis_eigenvector_of_coordinates σ n (-2) D.lower coordinates θ, _root_.zpow_neg]
  norm_num

theorem form_differentiableOn :
    DifferentiableOn ℂ (binaryEndpointHolomorphicFormWt σ n D.wt D.vector.val)
      UpperHalfPlane.upperHalfPlaneSet :=
  binaryEndpointHolomorphicForm_holomorphicWt σ n D.wt D.vector.val D.holomorphic

/-- **The Eichler period is a primitive of the holomorphic form.** -/
theorem period_hasDerivAt (z : ℂ) (hz : 0 < z.im) :
    HasDerivAt (binaryEndpointPeriodWt σ n D.wt D.vector.val)
      (binaryEndpointHolomorphicFormWt σ n D.wt D.vector.val z) z := by
  have convex : Convex ℝ UpperHalfPlane.upperHalfPlaneSet :=
    (convex_Ioi (0 : ℝ)).linear_preimage Complex.imLm
  obtain ⟨F, hF⟩ := convex.exists_forall_hasDerivWithinAt D.form_differentiableOn
  have hFat : ∀ a ∈ UpperHalfPlane.upperHalfPlaneSet,
      HasDerivAt F (binaryEndpointHolomorphicFormWt σ n D.wt D.vector.val a) a :=
    fun a ha => (hF a ha).hasDerivAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds ha)
  have period : ∀ x : ℂ, 0 < x.im →
      binaryEndpointPeriodWt σ n D.wt D.vector.val x = F x - F Complex.I := by
    intro x hx
    have path_derivative : ∀ t : ℝ,
        HasDerivAt (fun t : ℝ => Complex.I + t • (x - Complex.I)) (x - Complex.I) t := by
      intro t
      simpa only [one_smul, id_eq] using
        ((hasDerivAt_id t).smul_const (x - Complex.I)).const_add Complex.I
    have derivative : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => F (Complex.I + t • (x - Complex.I)))
          ((x - Complex.I) • binaryEndpointHolomorphicFormWt σ n D.wt D.vector.val
            (Complex.I + t • (x - Complex.I))) t := by
      intro t ht
      have belongs : t ∈ Set.Icc (0 : ℝ) 1 := by simpa only [Set.uIcc_of_le zero_le_one] using ht
      exact (hFat _ (upperHalfPlane_straightPath ⟨x, hx⟩ belongs)).scomp t (path_derivative t)
    have integral := intervalIntegral.integral_eq_sub_of_hasDerivAt derivative
      (binaryEndpointPeriod_integrableWt σ n D.wt D.vector.val x hx)
    unfold binaryEndpointPeriodWt
    rw [integral]
    simp only [one_smul, zero_smul, add_zero, add_sub_cancel]
  have h1 : HasDerivAt (fun x => F x - F Complex.I)
      (binaryEndpointHolomorphicFormWt σ n D.wt D.vector.val z) z :=
    (hFat z (show z ∈ UpperHalfPlane.upperHalfPlaneSet from hz)).sub_const (F Complex.I)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds
    (show z ∈ UpperHalfPlane.upperHalfPlaneSet from hz)] with x hx
  exact period x hx

end L3InputWt

end TernaryPeriodPolynomials.EvenLevelThree

end
