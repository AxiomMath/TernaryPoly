module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Smooth.Bounds
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.MaximalCompact

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel

local instance residueTopology (modulus : ℕ) : TopologicalSpace (ZMod modulus) := ⊥

local instance residueDiscrete (modulus : ℕ) : DiscreteTopology (ZMod modulus) := ⟨rfl⟩

abbrev IntegralBinaryGL := GeneralLinearGroup (Fin 2) IntegralAdeles

noncomputable def integralCongruence : Subgroup IntegralBinaryGL :=
  (GeneralLinearGroup.map integralReduction).ker

noncomputable def finiteCongruence : Subgroup BinaryFiniteGL :=
  integralCongruence.map (GeneralLinearGroup.map integralEmbedding)

theorem padicReduction_continuous {prime : ℕ} [Fact prime.Prime] :
    Continuous (PadicInt.toZMod (p := prime)) := by
  have kernel (value : ℤ_[prime]) : PadicInt.toZMod value = 0 ↔ ‖value‖ < 1 := by
    change value ∈ RingHom.ker PadicInt.toZMod ↔ _
    rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton,
      ← PadicInt.norm_lt_one_iff_dvd]
  apply continuous_discrete_rng.mpr
  intro residue
  have fiber : PadicInt.toZMod ⁻¹' {residue} =
      {value : ℤ_[prime] | ‖value - (residue.val : ℤ_[prime])‖ < 1} := by
    ext value
    change PadicInt.toZMod value = residue ↔ ‖value - (residue.val : ℤ_[prime])‖ < 1
    rw [← kernel]
    simp only [map_sub, map_natCast, ZMod.natCast_zmod_val, sub_eq_zero]
  rw [fiber]
  exact isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const

theorem inverseRingEquiv_continuous {Scalars First Second : Type*}
    [CommSemiring Scalars] [Semiring First] [TopologicalSpace First]
    [Semiring Second] [TopologicalSpace Second] [Algebra Scalars First] [Algebra Scalars Second]
    (equivalence : First ≃A[Scalars] Second) :
    Continuous equivalence.toAlgEquiv.toRingEquiv.symm := equivalence.continuous_invFun

theorem threeIntegralEquiv_continuous : Continuous threeIntegralEquiv :=
  @inverseRingEquiv_continuous _ _ _ _ _ _ _ _ _ (Ring.toIntAlgebra _)
    (PadicInt.adicCompletionIntegersEquiv ℤ primeThree)

theorem integralThree_continuous : Continuous integralThree :=
  threeIntegralEquiv_continuous.comp (continuous_apply placeThree)

theorem integralReduction_continuous : Continuous integralReduction :=
  padicReduction_continuous.comp integralThree_continuous

theorem integralMap_continuous {size : ℕ} :
    Continuous (GeneralLinearGroup.map integralEmbedding (n := Fin size)) := by
  apply Units.continuous_map
  exact continuous_pi (fun row => continuous_pi (fun column =>
    integralEmbedding_isOpenEmbedding.continuous.comp
      ((continuous_apply column).comp (continuous_apply row))))

theorem integralMap_isOpenMap {size : ℕ} :
    IsOpenMap (GeneralLinearGroup.map integralEmbedding (n := Fin size)) := by
  apply Units.isOpenMap_map
  · exact Matrix.map_injective integralEmbedding_injective
  · exact (Topology.IsOpenEmbedding.piMap (fun _ : Fin size =>
      Topology.IsOpenEmbedding.piMap (fun _ : Fin size => integralEmbedding_isOpenEmbedding))).isOpenMap

theorem reductionMap_continuous {size : ℕ} :
    Continuous (GeneralLinearGroup.map integralReduction (n := Fin size)) := by
  apply Units.continuous_map
  exact continuous_pi (fun row => continuous_pi (fun column => integralReduction_continuous.comp
    ((continuous_apply column).comp (continuous_apply row))))

theorem integralCongruence_isOpen : IsOpen (integralCongruence : Set IntegralBinaryGL) := by
  exact (isOpen_discrete ({1} : Set (GeneralLinearGroup (Fin 2) (ZMod 3)))).preimage
    reductionMap_continuous

theorem integralCongruence_isClosed : IsClosed (integralCongruence : Set IntegralBinaryGL) :=
  isClosed_eq reductionMap_continuous continuous_const

theorem finiteCongruence_isOpen : IsOpen (finiteCongruence : Set BinaryFiniteGL) :=
  integralMap_isOpenMap _ integralCongruence_isOpen

theorem finiteCongruence_isCompact : IsCompact (finiteCongruence : Set BinaryFiniteGL) := by
  let : CompactSpace (Matrix (Fin 2) (Fin 2) IntegralAdeles) :=
    inferInstanceAs (CompactSpace (Fin 2 → Fin 2 → IntegralAdeles))
  exact integralCongruence_isClosed.isCompact.image integralMap_continuous

theorem map_planeLevi {Coefficient Target : Type*} [CommRing Coefficient] [CommRing Target]
    (hom : Coefficient →+* Target) (matrix : GeneralLinearGroup (Fin 2) Coefficient)
    (scalar : Coefficientˣ) :
    GeneralLinearGroup.map hom (planeLevi matrix scalar) =
      planeLevi (GeneralLinearGroup.map hom matrix) (Units.map hom.toMonoidHom scalar) := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [planeLevi, planeBlock, GeneralLinearGroup.map_apply]

theorem planeLevi_atFinite (matrix : BinaryFiniteGL) :
    planeLevi (atFinite matrix) 1 = atFinite (planeLevi matrix 1) := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [planeLevi, planeBlock, atFinite, combineGL, pairMatrix] <;> rfl

theorem cuspVector_integralCongruence_fixed {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (binaryMatrix : IntegralBinaryGL) (congruence : binaryMatrix ∈ integralCongruence)
    (realMatrix : RealGL3) (finiteMatrix : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL) :
    data.cusp.π (atFinite (GeneralLinearGroup.map integralEmbedding binaryMatrix))
        (planeCuspVector inducedSection
          (atInfinity realMatrix * atFinite (GeneralLinearGroup.map integralEmbedding finiteMatrix))).val =
      (planeCuspVector inducedSection
        (atInfinity realMatrix * atFinite (GeneralLinearGroup.map integralEmbedding finiteMatrix))).val := by
  let binaryAdele := atFinite (GeneralLinearGroup.map integralEmbedding binaryMatrix)
  let basePoint := atInfinity realMatrix * atFinite (GeneralLinearGroup.map integralEmbedding finiteMatrix)
  have blockReduction : GeneralLinearGroup.map integralReduction (planeLevi binaryMatrix 1) = 1 := by
    rw [map_planeLevi, map_one]
    rw [show GeneralLinearGroup.map integralReduction binaryMatrix = 1 from congruence]
    exact (planeLeviHom (ZMod 3)).map_one
  have sameReduction : GeneralLinearGroup.map integralReduction (planeLevi binaryMatrix 1 * finiteMatrix) =
      GeneralLinearGroup.map integralReduction finiteMatrix := by
    rw [map_mul, blockReduction, one_mul]
  have invariance : planeCuspVector inducedSection (planeLevi binaryAdele 1 * basePoint) =
      planeCuspVector inducedSection basePoint := by
    dsimp only [binaryAdele, basePoint]
    rw [planeLevi_atFinite, ← mul_assoc, TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.atFinite_atInfinity_commute,
      mul_assoc, ← TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.atFinite_mul]
    have blockMap : planeLevi (GeneralLinearGroup.map integralEmbedding binaryMatrix) 1 =
        GeneralLinearGroup.map integralEmbedding (planeLevi binaryMatrix 1) := by
      rw [map_planeLevi]
      rfl
    rw [blockMap, ← map_mul]
    exact TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.planeCuspVector_same_integralReduction inducedSection
      (atInfinity realMatrix) (planeLevi binaryMatrix 1 * finiteMatrix) finiteMatrix sameReduction
  have determinantNorm : normPower (GeneralLinearGroup.det binaryAdele)
      (binaryInductionExponent degree .plane parameter) = 1 := by
    simp only [normPower, binaryAdele, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adeleNorm_det_integral, NNReal.coe_one,
      Real.log_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have formula := planeCuspVector_binaryLevi inducedSection binaryAdele basePoint
  rw [determinantNorm, one_smul] at formula
  exact congrArg Subtype.val (formula.symm.trans invariance)

theorem cuspVector_finiteCongruence_fixed {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (compactElement : AdelicGL) (compactness : inMaximalCompact compactElement)
    (finiteElement : finiteCongruence) :
    data.cusp.π (atFinite finiteElement.val) (planeCuspVector inducedSection compactElement).val =
      (planeCuspVector inducedSection compactElement).val := by
  obtain ⟨binaryMatrix, congruence, equality⟩ := finiteElement.property
  obtain ⟨finiteMatrix, finiteEquality⟩ := compactness.2
  have fixed := cuspVector_integralCongruence_fixed inducedSection binaryMatrix congruence
    (realGroup compactElement) finiteMatrix
  rw [equality, finiteEquality, ← TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adelicGL_eq_mul] at fixed
  exact fixed

noncomputable def unitaryOperator (data : CuspidalRepresentation) (matrix : BinaryAdelicGL) :
    data.H →L[ℂ] data.H :=
  (data.π matrix).mkContinuous 1 (fun vector => by rw [data.unitary, one_mul])

theorem cuspDerivative_integralCongruence_fixed {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (binaryMatrix : IntegralBinaryGL) (congruence : binaryMatrix ∈ integralCongruence)
    (finiteMatrix : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL)
    (order : ℕ) (realMatrix : RealGL3)
    (directions : Fin order → Fin 1 → Matrix (Fin 3) (Fin 3) ℝ) :
    data.cusp.π (atFinite (GeneralLinearGroup.map integralEmbedding binaryMatrix))
        (TernaryPeriodPolynomials.PlaneEisensteinContinuation.SmoothBounds.cuspDerivative inducedSection
          (atFinite (GeneralLinearGroup.map integralEmbedding finiteMatrix)) order realMatrix directions) =
      TernaryPeriodPolynomials.PlaneEisensteinContinuation.SmoothBounds.cuspDerivative inducedSection
        (atFinite (GeneralLinearGroup.map integralEmbedding finiteMatrix)) order realMatrix directions := by
  apply TernaryPeriodPolynomials.PlaneEisensteinContinuation.SmoothBounds.matrixDerivative_fixed
    (planeCuspVector_smooth inducedSection _) ((unitaryOperator data.cusp
      (atFinite (GeneralLinearGroup.map integralEmbedding binaryMatrix))).restrictScalars ℝ)
  intro matrices
  change data.cusp.π (atFinite (GeneralLinearGroup.map integralEmbedding binaryMatrix))
      (planeCuspVector inducedSection
        (atFinite (GeneralLinearGroup.map integralEmbedding finiteMatrix) * atInfinity (matrices 0))).val = _
  rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.atFinite_atInfinity_commute]
  exact cuspVector_integralCongruence_fixed inducedSection binaryMatrix congruence (matrices 0) finiteMatrix

def fixedSubspace (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL) : Submodule ℂ data.H where
  carrier := {vector | ∀ element : level, data.π (atFinite element.val) vector = vector}
  zero_mem' := fun _ => map_zero _
  add_mem' {first second} firstFixed secondFixed element := by
    rw [map_add, firstFixed element, secondFixed element]
  smul_mem' scalar vector vectorFixed element := by
    rw [map_smul, vectorFixed element]

theorem fixedSubspace_isClosed (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL) :
    IsClosed (fixedSubspace data level : Set data.H) := by
  change IsClosed {vector | ∀ element : level, data.π (atFinite element.val) vector = vector}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter (fun element =>
    isClosed_eq (unitaryOperator data (atFinite element.val)).continuous continuous_id)

theorem fixedSubspace_real_stable (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (matrix : BinaryRealGL) (vector : data.H) (fixed : vector ∈ fixedSubspace data level) :
    data.π (atInfinity matrix) vector ∈ fixedSubspace data level := by
  intro element
  have commutation := congrArg (fun value : BinaryAdelicGL => data.π value vector)
    (TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.atFinite_atInfinity_commute element.val matrix)
  simp only [map_mul, Module.End.mul_apply] at commutation
  rw [commutation, fixed element]

theorem cuspVector_mem_fixedSubspace {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (compactElement : AdelicGL) (compactness : inMaximalCompact compactElement) :
    (planeCuspVector inducedSection compactElement).val ∈ fixedSubspace data.cusp finiteCongruence :=
  cuspVector_finiteCongruence_fixed inducedSection compactElement compactness

theorem cuspDerivative_mem_fixedSubspace {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (compactElement : AdelicGL) (compactness : inMaximalCompact compactElement)
    (order : ℕ) (directions : Fin order → Fin 1 → Matrix (Fin 3) (Fin 3) ℝ) :
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.SmoothBounds.cuspDerivative inducedSection (atFinite (finiteGroup compactElement))
      order (realGroup compactElement) directions ∈ fixedSubspace data.cusp finiteCongruence := by
  intro element
  obtain ⟨binaryMatrix, congruence, equality⟩ := element.property
  obtain ⟨finiteMatrix, finiteEquality⟩ := compactness.2
  rw [← equality, ← finiteEquality]
  exact cuspDerivative_integralCongruence_fixed inducedSection binaryMatrix congruence finiteMatrix
    order (realGroup compactElement) directions

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel
