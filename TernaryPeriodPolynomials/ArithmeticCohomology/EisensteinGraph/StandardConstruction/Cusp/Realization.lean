module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Cusp.LiftCovariance
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Analysis.LocallyConvex.WithSeminorms

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix Topology MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CuspRealization

def binaryReal : BinaryAdelicGL →* BinaryRealGL :=
  GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles)

def binaryFinite : BinaryAdelicGL →* BinaryFiniteGL :=
  GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles)

theorem binaryReal_continuous : Continuous binaryReal :=
  TopologicalMatrices.generalLinearMap_continuous _ continuous_fst

theorem binaryFinite_continuous : Continuous binaryFinite :=
  TopologicalMatrices.generalLinearMap_continuous _ continuous_snd

theorem binaryReal_atInfinity (element : BinaryRealGL) : binaryReal (atInfinity element) = element := by
  apply GeneralLinearGroup.ext
  intro row column
  rfl

theorem binaryReal_atFinite (element : BinaryFiniteGL) : binaryReal (atFinite element) = 1 := by
  apply GeneralLinearGroup.ext
  intro row column
  rfl

theorem binaryFinite_atInfinity (element : BinaryRealGL) : binaryFinite (atInfinity element) = 1 := by
  apply GeneralLinearGroup.ext
  intro row column
  rfl

theorem binaryFinite_atFinite (element : BinaryFiniteGL) : binaryFinite (atFinite element) = element := by
  apply GeneralLinearGroup.ext
  intro row column
  rfl

theorem binary_ext {first second : BinaryAdelicGL}
    (real : binaryReal first = binaryReal second) (finite : binaryFinite first = binaryFinite second) :
    first = second := by
  apply GeneralLinearGroup.ext
  intro row column
  exact Prod.ext (congrArg (fun matrix => matrix.val row column) real)
    (congrArg (fun matrix => matrix.val row column) finite)

theorem binary_split (element : BinaryAdelicGL) (reference : BinaryFiniteGL) :
    element = atFinite reference * atInfinity (binaryReal element) *
      atFinite (reference⁻¹ * binaryFinite element) := by
  apply binary_ext
  · simp only [map_mul, binaryReal_atFinite, binaryReal_atInfinity, one_mul, mul_one]
  · simp only [map_mul, binaryFinite_atFinite, binaryFinite_atInfinity, mul_one, mul_inv_cancel_left]

def smoothAction (data : CuspidalRepresentation) : Representation ℂ BinaryAdelicGL data.smooth :=
  data.π.subrepresentation data.smooth data.smooth_stable

theorem realize_equivariant (data : CuspidalRepresentation) (element : BinaryAdelicGL)
    (vector : data.smooth) (argument : BinaryAdelicGL) :
    data.realize (smoothAction data element vector) argument = data.realize vector (argument * element) :=
  data.equivariant element vector argument

theorem finite_invariant (data : CuspidalRepresentation) (vector : data.smooth) :
    ∃ subgroup : Subgroup BinaryFiniteGL, IsOpen (subgroup : Set BinaryFiniteGL) ∧
      IsCompact (subgroup : Set BinaryFiniteGL) ∧
      ∀ element : subgroup, ∀ argument,
        data.realize vector (argument * atFinite element.val) = data.realize vector argument := by
  obtain ⟨subgroup, isOpen, compact, invariant⟩ := ((data.smooth_exact vector.val).mp vector.property).2
  refine ⟨subgroup, isOpen, compact, ?_⟩
  intro element argument
  rw [← realize_equivariant]
  have fixes : smoothAction data (atFinite element.val) vector = vector := Subtype.ext (invariant element)
  rw [fixes]

theorem real_continuous (data : CuspidalRepresentation) (vector : data.smooth)
    (argument : BinaryAdelicGL) :
    Continuous (fun real : BinaryRealGL => data.realize vector (argument * atInfinity real)) :=
  (SmoothContinuity.smooth_continuous _ (data.scalarSmooth vector argument)).comp
    (continuous_pi (fun _ : Fin 1 => continuous_id))

theorem scalar_continuous (data : CuspidalRepresentation) (vector : data.smooth) :
    Continuous (data.realize vector) := by
  obtain ⟨subgroup, isOpen, _, invariant⟩ := finite_invariant data vector
  apply continuous_iff_continuousAt.mpr
  intro element
  have localContinuous : Continuous (fun argument : BinaryAdelicGL =>
      data.realize vector (atFinite (binaryFinite element) * atInfinity (binaryReal argument))) :=
    (real_continuous data vector (atFinite (binaryFinite element))).comp binaryReal_continuous
  have near : ∀ᶠ argument : BinaryAdelicGL in 𝓝 element,
      (binaryFinite element)⁻¹ * binaryFinite argument ∈ subgroup :=
    (isOpen.preimage (continuous_const.mul binaryFinite_continuous)).mem_nhds (by simp)
  apply localContinuous.continuousAt.congr_of_eventuallyEq
  filter_upwards [near] with argument membership
  calc
    data.realize vector argument = data.realize vector
        (atFinite (binaryFinite element) * atInfinity (binaryReal argument) *
          atFinite ((binaryFinite element)⁻¹ * binaryFinite argument)) :=
      congrArg (data.realize vector) (binary_split argument (binaryFinite element))
    _ = _ := invariant ⟨_, membership⟩ _

theorem cuspFunctions_constantTerm (data : CuspidalRepresentation)
    (function : BinaryAdelicGL → ℂ) (membership : function ∈ cuspFunctions data)
    (argument : BinaryAdelicGL) :
    MeasureTheory.IntegrableOn
        (fun value => function (binaryUnipotent value * argument))
        additiveDomain adeleMeasure ∧
      (∫ value in additiveDomain,
        function (binaryUnipotent value * argument) ∂adeleMeasure) = 0 := by
  change function ∈ LinearMap.range data.realize at membership
  obtain ⟨vector, equality⟩ := LinearMap.mem_range.mp membership
  rw [← equality]
  exact data.cuspidal vector argument

theorem planeInduced_constantTerm {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function) (argument : AdelicGL) :
    IntegrableOn (fun value : Adeles =>
      function (binaryLevi .plane (binaryUnipotent value) * argument))
        additiveDomain adeleMeasure ∧
      (∫ value in additiveDomain,
        function (binaryLevi .plane (binaryUnipotent value) * argument) ∂adeleMeasure) = 0 := by
  let normalized : BinaryAdelicGL → ℂ := fun binary =>
    normPower (GeneralLinearGroup.det binary)
      (-binaryInductionExponent degree .plane parameter) *
      function (binaryLevi .plane binary * argument)
  have normalized_mem : normalized ∈ cuspFunctions data.cusp := by
    simpa only [normalized, binaryLevi, binaryInductionExponent] using
      induced.2.2.2.2.2 argument
  obtain ⟨integrable, constantTermZero⟩ :=
    cuspFunctions_constantTerm data.cusp normalized normalized_mem 1
  have determinant (value : Adeles) :
      GeneralLinearGroup.det (binaryUnipotent value) = 1 := by
    apply Units.ext
    simp [GeneralLinearGroup.det, binaryUnipotent, Matrix.det_fin_two]
  have pointwise : (fun value : Adeles =>
      normalized (binaryUnipotent value * 1)) =
      (fun value => function (binaryLevi .plane (binaryUnipotent value) * argument)) := by
    funext value
    simp [normalized, binaryLevi, determinant, ParabolicInvariance.normPower_one]
  constructor
  · simpa only [pointwise] using integrable
  · simpa only [pointwise] using constantTermZero

theorem conjugates_unipotent_fixed_eq_zero (data : CuspidalRepresentation)
    (vector : data.smooth)
    (fixed : ∀ conjugator : BinaryAdelicGL, ∀ value : Adeles,
      data.π (conjugator⁻¹ * binaryUnipotent value * conjugator) vector.val = vector.val) :
    vector = 0 := by
  apply data.injective
  funext argument
  have constant_integrand : ∀ value : Adeles,
      data.realize vector (binaryUnipotent value * argument) = data.realize vector argument := by
    intro value
    let element := argument⁻¹ * binaryUnipotent value * argument
    have fixedElement : smoothAction data element vector = vector :=
      Subtype.ext (fixed argument value)
    have equivariance := realize_equivariant data element vector argument
    rw [fixedElement] at equivariance
    calc
      data.realize vector (binaryUnipotent value * argument) =
          data.realize vector (argument * element) :=
        congrArg (data.realize vector) (by dsimp [element]; group)
      _ = data.realize vector argument := equivariance.symm
  have integralZero := (data.cuspidal vector argument).2
  have integralValue :
      (∫ value in additiveDomain, data.realize vector argument ∂adeleMeasure) = 0 := by
    simpa only [constant_integrand] using integralZero
  have constantIntegral :
      (∫ value in additiveDomain, data.realize vector argument ∂adeleMeasure) =
        data.realize vector argument := by
    simp only [integral_const, Measure.real, Measure.restrict_apply_univ,
      Norms.additiveDomain_measure, ENNReal.toReal_one, one_smul]
  have valueZero : data.realize vector argument = 0 := by
    calc
      data.realize vector argument =
          ∫ value in additiveDomain, data.realize vector argument ∂adeleMeasure :=
        constantIntegral.symm
      _ = 0 := integralValue
  simpa only [map_zero, Pi.zero_apply] using valueZero

theorem binaryValues_constantTerm {degree : ℕ} (data : CuspidalRepresentation)
    (values : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1))
    (membership : BinaryValues data degree values) (monomial : Fin 2 →₀ ℕ)
    (argument : BinaryAdelicGL) :
    MeasureTheory.IntegrableOn
        (fun value => (values (binaryUnipotent value * argument)).val.coeff monomial)
        additiveDomain adeleMeasure ∧
      (∫ value in additiveDomain,
        (values (binaryUnipotent value * argument)).val.coeff monomial ∂adeleMeasure) = 0 :=
  cuspFunctions_constantTerm data _ (membership monomial) argument

def boundedRealization (data : CuspidalRepresentation) :
    data.smooth →ₗ[ℂ] BoundedContinuousFunction BinaryAdelicGL ℂ where
  toFun vector := BoundedContinuousFunction.ofNormedAddCommGroup (data.realize vector)
    (scalar_continuous data vector) (Classical.choose (data.bounded vector))
    (Classical.choose_spec (data.bounded vector))
  map_add' first second := by
    ext argument
    exact congrFun (map_add data.realize first second) argument
  map_smul' scalar vector := by
    ext argument
    exact congrFun (map_smul data.realize scalar vector) argument

theorem boundedRealization_apply (data : CuspidalRepresentation) (vector : data.smooth)
    (argument : BinaryAdelicGL) : boundedRealization data vector argument = data.realize vector argument := rfl

theorem boundedRealization_injective (data : CuspidalRepresentation) :
    Function.Injective (boundedRealization data) := by
  intro first second equality
  apply data.injective
  exact congrArg DFunLike.coe equality

theorem realization_norm_invariant (data : CuspidalRepresentation) (element : BinaryAdelicGL)
    (vector : data.smooth) :
    ‖boundedRealization data (smoothAction data element vector)‖ = ‖boundedRealization data vector‖ := by
  apply le_antisymm
  · apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
    intro argument
    change ‖data.realize (smoothAction data element vector) argument‖ ≤ _
    rw [realize_equivariant]
    exact BoundedContinuousFunction.norm_coe_le_norm (boundedRealization data vector) _
  · apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
    intro argument
    have bound := BoundedContinuousFunction.norm_coe_le_norm
      (boundedRealization data (smoothAction data element vector)) (argument * element⁻¹)
    simpa only [boundedRealization_apply, realize_equivariant, mul_assoc, inv_mul_cancel,
      mul_one] using bound

def realizationSeminorm (data : CuspidalRepresentation) : Seminorm ℂ data.smooth :=
  (normSeminorm ℂ (BoundedContinuousFunction BinaryAdelicGL ℂ)).comp (boundedRealization data)

theorem realizationSeminorm_apply (data : CuspidalRepresentation) (vector : data.smooth) :
    realizationSeminorm data vector = ‖boundedRealization data vector‖ := rfl

theorem realizationSeminorm_zero_iff (data : CuspidalRepresentation) (vector : data.smooth) :
    realizationSeminorm data vector = 0 ↔ vector = 0 := by
  rw [realizationSeminorm_apply, norm_eq_zero, ← map_zero (boundedRealization data)]
  exact (boundedRealization_injective data).eq_iff

theorem realizationSeminorm_invariant (data : CuspidalRepresentation) (element : BinaryAdelicGL)
    (vector : data.smooth) :
    realizationSeminorm data (smoothAction data element vector) = realizationSeminorm data vector :=
  realization_norm_invariant data element vector

theorem realizationSeminorm_smul (data : CuspidalRepresentation) (scalar : ℂ)
    (vector : data.smooth) :
    realizationSeminorm data (scalar • vector) =
      ‖scalar‖ * realizationSeminorm data vector := by
  simp only [realizationSeminorm_apply, map_smul, norm_smul]

theorem realizationSeminorm_cuspLift_planeBinary {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function) (binary : BinaryAdelicGL)
    (argument : AdelicGL) :
    realizationSeminorm data.cusp
        (CuspLift.vector data .plane parameter function induced
          (planeLevi binary 1 * argument)) =
      (adeleNorm (GeneralLinearGroup.det binary) : ℝ) ^
          (binaryInductionExponent degree .plane parameter).re *
        realizationSeminorm data.cusp
          (CuspLift.vector data .plane parameter function induced argument) := by
  have vectorEquality : CuspLift.vector data .plane parameter function induced
      (planeLevi binary 1 * argument) =
      normPower (GeneralLinearGroup.det binary)
        (binaryInductionExponent degree .plane parameter) •
        smoothAction data.cusp binary
          (CuspLift.vector data .plane parameter function induced argument) := by
    apply Subtype.ext
    exact CuspLiftCovariance.vector_binary data .plane parameter function induced binary argument
  rw [realizationSeminorm_apply, vectorEquality, map_smul, norm_smul,
    NormPower.normPower_norm, ← realizationSeminorm_apply,
    realizationSeminorm_invariant]

theorem realizationSeminorm_cuspLift_planeRankOne_cohomological {degree : ℕ}
    (data : InducingData degree) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane cohomologicalPoint function) (unit : Adelesˣ)
    (argument : AdelicGL) :
    realizationSeminorm data.cusp
        (CuspLift.vector data .plane cohomologicalPoint function induced
          (planeLevi 1 unit * argument)) =
      realizationSeminorm data.cusp
        (CuspLift.vector data .plane cohomologicalPoint function induced argument) := by
  rw [CuspLiftCovariance.vector_plane_rankOne, realizationSeminorm_smul]
  have exponent : -2 * inductionExponent .plane cohomologicalPoint = 0 := by
    norm_num [inductionExponent, cohomologicalPoint]
  rw [exponent, ParabolicInvariance.normPower_zero]
  simp [data.chi.unitary]

theorem scalar_bound (data : CuspidalRepresentation) (vector : data.smooth) (argument : BinaryAdelicGL) :
    ‖data.realize vector argument‖ ≤ realizationSeminorm data vector :=
  BoundedContinuousFunction.norm_coe_le_norm (boundedRealization data vector) argument

theorem flat_vector_realizationSeminorm {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (compact : AdelicGL) (membership : inMaximalCompact compact) :
    realizationSeminorm data.cusp
        (CuspLift.vector data .plane parameter (extension parameter)
          (flat.1 parameter) compact) =
      realizationSeminorm data.cusp
        (CuspLift.vector data .plane cohomologicalPoint (extension cohomologicalPoint)
          (flat.1 cohomologicalPoint) compact) := by
  rw [CuspLift.flat_vector data extension flat parameter compact membership]

theorem flat_vector_uniform_binary_bound {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (bound : ℝ)
    (seminormBound : ∀ compact, inMaximalCompact compact →
      realizationSeminorm data.cusp
        (CuspLift.vector data .plane cohomologicalPoint (extension cohomologicalPoint)
          (flat.1 cohomologicalPoint) compact) ≤ bound) :
    ∀ parameter compact, inMaximalCompact compact → ∀ binary,
      ‖data.cusp.realize
        (CuspLift.vector data .plane parameter (extension parameter) (flat.1 parameter)
          compact) binary‖ ≤ bound := by
  intro parameter compact membership binary
  calc
    ‖data.cusp.realize
        (CuspLift.vector data .plane parameter (extension parameter) (flat.1 parameter)
          compact) binary‖ ≤
      realizationSeminorm data.cusp
        (CuspLift.vector data .plane parameter (extension parameter) (flat.1 parameter)
          compact) := scalar_bound data.cusp _ _
    _ = realizationSeminorm data.cusp
        (CuspLift.vector data .plane cohomologicalPoint (extension cohomologicalPoint)
          (flat.1 cohomologicalPoint) compact) :=
      flat_vector_realizationSeminorm data extension flat parameter compact membership
    _ ≤ bound := seminormBound compact membership

theorem seminorm_le_iff (data : CuspidalRepresentation) (vector : data.smooth) (bound : ℝ)
    (nonnegative : 0 ≤ bound) :
    realizationSeminorm data vector ≤ bound ↔ ∀ argument, ‖data.realize vector argument‖ ≤ bound :=
  BoundedContinuousFunction.norm_le nonnegative

theorem seminorm_lowerSemicontinuous {X : Type} [TopologicalSpace X]
    (data : CuspidalRepresentation) (family : X → data.smooth)
    (continuous : ∀ argument, Continuous (fun index => data.realize (family index) argument)) :
    LowerSemicontinuous (fun index => realizationSeminorm data (family index)) := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro bound
  change IsClosed {index | realizationSeminorm data (family index) ≤ bound}
  by_cases nonnegative : 0 ≤ bound
  · have equality : {index | realizationSeminorm data (family index) ≤ bound} =
        ⋂ argument, {index | ‖data.realize (family index) argument‖ ≤ bound} := by
      ext index
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      exact seminorm_le_iff data (family index) bound nonnegative
    rw [equality]
    exact isClosed_iInter (fun argument => isClosed_le (continuous argument).norm continuous_const)
  · have empty : {index | realizationSeminorm data (family index) ≤ bound} = ∅ := by
      ext index
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact not_le.mpr (lt_of_lt_of_le (lt_of_not_ge nonnegative)
        (norm_nonneg (boundedRealization data (family index))))
    rw [empty]
    exact isClosed_empty

theorem lowerSemicontinuous_subadditive_bddOnCompact
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [BaireSpace G]
    (seminorm : G → ℝ) (lowerSemicontinuous : LowerSemicontinuous seminorm)
    (nonnegative : ∀ element, 0 ≤ seminorm element)
    (subadditive : ∀ first second, seminorm (first * second) ≤
      seminorm first + seminorm second)
    (compactSet : Set G) (compact : IsCompact compactSet) :
    ∃ bound : ℝ, ∀ element ∈ compactSet, seminorm element ≤ bound := by
  let level : ℕ → Set G := fun number => {element | seminorm element ≤ number}
  have level_closed (number : ℕ) : IsClosed (level number) := by
    change IsClosed (seminorm ⁻¹' Set.Iic (number : ℝ))
    exact lowerSemicontinuous.isClosed_preimage _
  have level_cover : (⋃ number, level number) = Set.univ := by
    ext element
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨number, bound⟩ := exists_nat_gt (seminorm element)
    exact ⟨number, le_of_lt bound⟩
  have some_interior : ∃ number, (interior (level number)).Nonempty := by
    by_contra no_interior
    have no_interior' : ∀ number, ¬ (interior (level number)).Nonempty := by
      intro number nonempty
      exact no_interior ⟨number, nonempty⟩
    have dense_complement : ∀ number, Dense (level number)ᶜ := by
      intro number
      rw [dense_iff_inter_open]
      intro openSet openSet_open openSet_nonempty
      by_contra empty_intersection
      have subset : openSet ⊆ level number := by
        intro element membership
        by_contra not_membership
        exact empty_intersection ⟨element, membership, not_membership⟩
      obtain ⟨element, element_mem⟩ := openSet_nonempty
      exact no_interior' number ⟨element, interior_maximal subset openSet_open element_mem⟩
    have dense : Dense (⋂ number, (level number)ᶜ) :=
      BaireSpace.baire_property (fun number => (level number)ᶜ)
        (fun number => isOpen_compl_iff.mpr (level_closed number)) dense_complement
    obtain ⟨element, _, in_complement⟩ :=
      (dense_iff_inter_open.mp dense) Set.univ isOpen_univ ⟨1, Set.mem_univ _⟩
    have in_level : element ∈ ⋃ number, level number := by
      rw [level_cover]
      exact Set.mem_univ element
    obtain ⟨number, in_level⟩ := Set.mem_iUnion.mp in_level
    exact (Set.mem_iInter.mp in_complement number) in_level
  obtain ⟨number, ⟨base, base_mem⟩⟩ := some_interior
  let neighborhood : Set G := {element | base * element ∈ interior (level number)}
  have neighborhood_open : IsOpen neighborhood := by
    change IsOpen ((fun element => base * element) ⁻¹' interior (level number))
    exact (continuous_const.mul continuous_id).isOpen_preimage _ isOpen_interior
  have one_mem_neighborhood : (1 : G) ∈ neighborhood := by
    change base * 1 ∈ interior (level number)
    simpa using base_mem
  have neighborhood_bound : ∀ element ∈ neighborhood,
      seminorm element ≤ seminorm base⁻¹ + number := by
    intro element membership
    have translated_mem : base * element ∈ level number := interior_subset membership
    change seminorm (base * element) ≤ number at translated_mem
    calc
      seminorm element = seminorm (base⁻¹ * (base * element)) := by simp
      _ ≤ seminorm base⁻¹ + seminorm (base * element) := subadditive _ _
      _ ≤ seminorm base⁻¹ + number := by linarith
  let translatedNeighborhood : G → Set G := fun basePoint =>
    (fun element => basePoint⁻¹ * element) ⁻¹' neighborhood
  have translatedNeighborhood_open (basePoint : G) : IsOpen (translatedNeighborhood basePoint) :=
    (continuous_const.mul continuous_id).isOpen_preimage _ neighborhood_open
  have translatedNeighborhood_cover : compactSet ⊆ ⋃ basePoint, translatedNeighborhood basePoint := by
    intro element _
    refine Set.mem_iUnion.mpr ⟨element, ?_⟩
    change element⁻¹ * element ∈ neighborhood
    simpa using one_mem_neighborhood
  obtain ⟨finiteCover, finiteCover_spec⟩ := compact.elim_finite_subcover
    translatedNeighborhood translatedNeighborhood_open translatedNeighborhood_cover
  let bound : ℝ := ∑ basePoint ∈ finiteCover,
    (seminorm basePoint + seminorm basePoint⁻¹ + (seminorm base⁻¹ + number))
  have summand_nonnegative (basePoint : G) (_ : basePoint ∈ finiteCover) :
      0 ≤ seminorm basePoint + seminorm basePoint⁻¹ + (seminorm base⁻¹ + number) := by
    exact add_nonneg (add_nonneg (nonnegative _) (nonnegative _))
      (add_nonneg (nonnegative _) (Nat.cast_nonneg _))
  refine ⟨bound, ?_⟩
  intro element membership
  obtain ⟨basePoint, basePoint_mem, translated_mem⟩ :=
    Set.mem_iUnion₂.mp (finiteCover_spec membership)
  have neighborhood_mem : basePoint⁻¹ * element ∈ neighborhood := translated_mem
  have element_eq : element = basePoint * (basePoint⁻¹ * element) := by
    simp
  have local_bound : seminorm element ≤ seminorm basePoint + (seminorm base⁻¹ + number) := by
    rw [element_eq]
    nlinarith [subadditive basePoint (basePoint⁻¹ * element),
      neighborhood_bound (basePoint⁻¹ * element) neighborhood_mem]
  have summand_bound :
      seminorm basePoint + (seminorm base⁻¹ + number) ≤
        seminorm basePoint + seminorm basePoint⁻¹ + (seminorm base⁻¹ + number) := by
    nlinarith [nonnegative basePoint⁻¹]
  have total_bound :
      seminorm basePoint + seminorm basePoint⁻¹ + (seminorm base⁻¹ + number) ≤ bound := by
    dsimp [bound]
    exact Finset.single_le_sum summand_nonnegative basePoint_mem
  exact local_bound.trans (summand_bound.trans total_bound)

theorem invariantCocycle_seminorm_bddOnCompact
    {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [BaireSpace G]
    [HAdd V V V]
    (seminorm : V → ℝ) (nonnegative : ∀ vector, 0 ≤ seminorm vector)
    (subadditive : ∀ first second, seminorm (first + second) ≤
      seminorm first + seminorm second)
    (action : G → V → V)
    (invariant : ∀ element vector, seminorm (action element vector) = seminorm vector)
    (cocycle : G → V)
    (cocycle_law : ∀ first second,
      cocycle (first * second) = cocycle first + action first (cocycle second))
    (lowerSemicontinuous : LowerSemicontinuous (fun element => seminorm (cocycle element)))
    (compactSet : Set G) (compact : IsCompact compactSet) :
    ∃ bound : ℝ, ∀ element ∈ compactSet, seminorm (cocycle element) ≤ bound := by
  have cocycle_seminorm_subadditive (first second : G) :
      seminorm (cocycle (first * second)) ≤
        seminorm (cocycle first) + seminorm (cocycle second) := by
    rw [cocycle_law]
    calc
      seminorm (cocycle first + action first (cocycle second)) ≤
          seminorm (cocycle first) + seminorm (action first (cocycle second)) :=
        subadditive _ _
      _ = seminorm (cocycle first) + seminorm (cocycle second) := by
        rw [invariant]
  exact lowerSemicontinuous_subadditive_bddOnCompact
    (fun element => seminorm (cocycle element)) lowerSemicontinuous
    (fun element => nonnegative (cocycle element)) cocycle_seminorm_subadditive
    compactSet compact

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CuspRealization
