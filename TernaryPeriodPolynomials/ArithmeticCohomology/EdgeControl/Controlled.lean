module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Iwasawa.PrismContinuity
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneOpenProjection
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Real.CompactReduction
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Adelic.Norm

@[expose] public section


/-!
# Sup-norm controlled families of cuspidal tensor values

A family `F : X → cuspidalTensorValues cusp V` over a topological space is *controlled* if every
scalar test of every real translate of it has a sup-norm realization depending continuously on the
parameter and the translating element of `GL₂(ℝ)`. Controlled families are stable under sums,
continuous scalar multiples, continuous families of linear maps of the coefficients, real
translations along continuous paths and the real plane group action along continuous paths.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

namespace TernaryPeriodPolynomials.EdgeControl

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses

section Realization

variable (cusp : CuspidalRepresentation) {V W : Type} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

/-- The sup-norm realization of a scalar test of a real translate. -/
def testRealization (functional : V →ₗ[ℂ] ℂ) (g : BinaryRealGL) :
    cuspidalTensorValues cusp V →ₗ[ℂ] lp (fun _ : BinaryAdelicGL => ℂ) ⊤ :=
  (CuspSupNorm.boundedRealization cusp).comp
    ((cuspidalTensorFunctional cusp functional).comp (cuspidalTensorTranslation cusp (atInfinity
        g)))

theorem testRealization_apply (functional : V →ₗ[ℂ] ℂ) (g : BinaryRealGL)
    (values : cuspidalTensorValues cusp V) (argument : BinaryAdelicGL) :
    ⇑(testRealization cusp functional g values) argument =
      functional (values.val (argument * atInfinity g)) :=
  cuspidalTensorFunctional_realize cusp functional _ argument

theorem lp_ext_iff {first second : lp (fun _ : BinaryAdelicGL => ℂ) ⊤} :
    first = second ↔ ∀ argument, ⇑first argument = ⇑second argument :=
  ⟨fun h _ => by rw [h], fun h => lp.ext (funext h)⟩

theorem translation_translation (g h : BinaryRealGL) (values : cuspidalTensorValues cusp V) :
    cuspidalTensorTranslation cusp (atInfinity g) (cuspidalTensorTranslation cusp (atInfinity h)
        values) =
      cuspidalTensorTranslation cusp (atInfinity (g * h)) values := by
  apply Subtype.ext
  funext argument
  change values.val (argument * atInfinity g * atInfinity h) = values.val (argument * atInfinity (g
      * h))
  rw [Height.atInfinity_mul, mul_assoc]

theorem testRealization_translation (functional : V →ₗ[ℂ] ℂ) (g h : BinaryRealGL)
    (values : cuspidalTensorValues cusp V) :
    testRealization cusp functional g (cuspidalTensorTranslation cusp (atInfinity h) values) =
      testRealization cusp functional (g * h) values := by
  unfold testRealization
  simp only [LinearMap.comp_apply]
  rw [translation_translation]

theorem testRealization_map (functional : W →ₗ[ℂ] ℂ) (g : BinaryRealGL) (linear : V →ₗ[ℂ] W)
    (values : cuspidalTensorValues cusp V) :
    testRealization cusp functional g (cuspidalTensorMap cusp linear values) =
      testRealization cusp (functional.comp linear) g values := by
  rw [lp_ext_iff]
  intro argument
  rw [testRealization_apply, testRealization_apply]
  rfl

theorem testRealization_one (functional : V →ₗ[ℂ] ℂ) (values : cuspidalTensorValues cusp V) :
    testRealization cusp functional 1 values =
      CuspSupNorm.boundedRealization cusp (cuspidalTensorFunctional cusp functional values) := by
  rw [lp_ext_iff]
  intro argument
  rw [testRealization_apply]
  change _ = cusp.realize _ argument
  rw [cuspidalTensorFunctional_realize, AveragingSmooth.atInfinity_one, mul_one]

theorem testRealization_sum_functional {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (functionals : ι → V →ₗ[ℂ] ℂ) (g : BinaryRealGL) (values : cuspidalTensorValues cusp V) :
    testRealization cusp (∑ i ∈ s, c i • functionals i) g values =
      ∑ i ∈ s, c i • testRealization cusp (functionals i) g values := by
  rw [lp_ext_iff]
  intro argument
  rw [testRealization_apply]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, testRealization_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]

end Realization

section Controlled

variable {cusp : CuspidalRepresentation} {V W : Type} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **Controlled families**: every scalar test of every real translate has a sup-norm realization
depending continuously on the parameter and the translating element. -/
def Controlled (cusp : CuspidalRepresentation) (family : X → cuspidalTensorValues cusp V) : Prop :=
  ∀ functional : V →ₗ[ℂ] ℂ, Continuous (fun point : X × BinaryRealGL =>
    testRealization cusp functional point.2 (family point.1))

theorem Controlled.continuous_one {family : X → cuspidalTensorValues cusp V}
    (controlled : Controlled cusp family) (functional : V →ₗ[ℂ] ℂ) :
    Continuous (fun x => CuspSupNorm.boundedRealization cusp
      (cuspidalTensorFunctional cusp functional (family x))) := by
  have composite := Continuous.comp (controlled functional)
    (continuous_id.prodMk continuous_const : Continuous fun x : X => (x, (1 : BinaryRealGL)))
  refine composite.congr (fun x => ?_)
  exact testRealization_one cusp functional (family x)

theorem Controlled.comp {family : X → cuspidalTensorValues cusp V}
    (controlled : Controlled cusp family) {f : Y → X} (hf : Continuous f) :
    Controlled cusp (fun y => family (f y)) := fun functional =>
  Continuous.comp (g := fun point : X × BinaryRealGL =>
      testRealization cusp functional point.2 (family point.1))
    (f := fun point : Y × BinaryRealGL => (f point.1, point.2)) (controlled functional)
    ((hf.comp continuous_fst).prodMk continuous_snd)

theorem controlled_const (values : cuspidalTensorValues cusp V)
    (continuity : ∀ functional : V →ₗ[ℂ] ℂ,
      Continuous (fun g : BinaryRealGL => testRealization cusp functional g values)) :
    Controlled cusp (fun _ : X => values) := fun functional =>
  (continuity functional).comp continuous_snd

theorem controlled_zero : Controlled cusp (fun _ : X => (0 : cuspidalTensorValues cusp V)) :=
  fun functional => by simpa only [map_zero] using continuous_const

theorem Controlled.add {first second : X → cuspidalTensorValues cusp V}
    (hfirst : Controlled cusp first) (hsecond : Controlled cusp second) :
    Controlled cusp (fun x => first x + second x) := fun functional => by
  simp only [map_add]
  exact (hfirst functional).add (hsecond functional)

theorem Controlled.sub {first second : X → cuspidalTensorValues cusp V}
    (hfirst : Controlled cusp first) (hsecond : Controlled cusp second) :
    Controlled cusp (fun x => first x - second x) := fun functional => by
  simp only [map_sub]
  exact (hfirst functional).sub (hsecond functional)

theorem Controlled.neg {family : X → cuspidalTensorValues cusp V}
    (controlled : Controlled cusp family) :
    Controlled cusp (fun x => -family x) := fun functional => by
  simp only [map_neg]
  exact (controlled functional).neg

theorem Controlled.smul {family : X → cuspidalTensorValues cusp V}
    (controlled : Controlled cusp family) {scalar : X → ℂ} (hscalar : Continuous scalar) :
    Controlled cusp (fun x => scalar x • family x) := fun functional => by
  simp only [map_smul]
  exact (hscalar.comp continuous_fst).smul (controlled functional)

theorem Controlled.const_smul {family : X → cuspidalTensorValues cusp V}
    (controlled : Controlled cusp family) (scalar : ℂ) :
    Controlled cusp (fun x => scalar • family x) :=
  controlled.smul continuous_const

theorem controlled_sum {ι : Type} (s : Finset ι) {family : ι → X → cuspidalTensorValues cusp V}
    (controlled : ∀ i ∈ s, Controlled cusp (family i)) :
    Controlled cusp (fun x => ∑ i ∈ s, family i x) := fun functional => by
  simp only [map_sum]
  exact continuous_finsetSum s (fun i hi => controlled i hi functional)

/-- Translation along a continuous path. -/
theorem Controlled.translate {family : X → cuspidalTensorValues cusp V}
    (controlled : Controlled cusp family) {B : X → BinaryRealGL} (hB : Continuous B) :
    Controlled cusp (fun x => cuspidalTensorTranslation cusp (atInfinity (B x)) (family x)) :=
  fun functional => by
    have equality : (fun point : X × BinaryRealGL => testRealization cusp functional point.2
        (cuspidalTensorTranslation cusp (atInfinity (B point.1)) (family point.1))) =
        (fun point : X × BinaryRealGL => testRealization cusp functional point.2 (family point.1)) ∘
          (fun point : X × BinaryRealGL => (point.1, point.2 * B point.1)) := by
      funext point
      exact testRealization_translation cusp functional _ _ _
    rw [equality]
    exact (controlled functional).comp (continuous_fst.prodMk
      (continuous_snd.mul (hB.comp continuous_fst)))

/-- A continuous family of linear maps out of a finite-dimensional coefficient space. -/
theorem Controlled.map {ι : Type} [Fintype ι] (basis : Module.Basis ι ℂ V)
    {family : X → cuspidalTensorValues cusp V} (controlled : Controlled cusp family)
    {linear : X → V →ₗ[ℂ] W}
    (hlinear : ∀ (vector : V) (functional : W →ₗ[ℂ] ℂ),
      Continuous (fun x => functional (linear x vector))) :
    Controlled cusp (fun x => cuspidalTensorMap cusp (linear x) (family x)) := fun functional => by
  classical
  have decomposition (x : X) : functional.comp (linear x) =
      ∑ i, functional (linear x (basis i)) • basis.coord i := by
    apply basis.ext
    intro j
    simp [Module.Basis.coord_apply, Finsupp.single_apply]
  have equality : (fun point : X × BinaryRealGL => testRealization cusp functional point.2
      (cuspidalTensorMap cusp (linear point.1) (family point.1))) =
      fun point => ∑ i, functional (linear point.1 (basis i)) •
        testRealization cusp (basis.coord i) point.2 (family point.1) := by
    funext point
    rw [testRealization_map, decomposition, testRealization_sum_functional]
  rw [equality]
  exact continuous_finsetSum _ (fun i _ =>
    ((hlinear (basis i) functional).comp continuous_fst).smul (controlled (basis.coord i)))

theorem Controlled.map_const {ι : Type} [Fintype ι] (basis : Module.Basis ι ℂ V)
    {family : X → cuspidalTensorValues cusp V} (controlled : Controlled cusp family)
    (linear : V →ₗ[ℂ] W) :
    Controlled cusp (fun x => cuspidalTensorMap cusp linear (family x)) :=
  controlled.map basis (linear := fun _ => linear) (fun _ _ => continuous_const)

end Controlled

section Bases

/-- A basis of the ternary homogeneous polynomials of a given degree. -/
def homogeneousBasis (degree : ℕ) :
    Module.Basis (Fin (Module.finrank ℂ (HomogeneousPoly degree))) ℂ (HomogeneousPoly degree) :=
  let _ : FiniteDimensional ℂ (HomogeneousPoly degree) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 3) ℂ degree)
  Module.finBasis ℂ (HomogeneousPoly degree)

/-- A basis of the binary homogeneous polynomials of a given degree. -/
def binaryHomogeneousBasis (degree : ℕ) :
    Module.Basis (Fin (Module.finrank ℂ (Binary.HomogeneousPoly degree))) ℂ
      (Binary.HomogeneousPoly degree) :=
  let _ : FiniteDimensional ℂ (Binary.HomogeneousPoly degree) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 2) ℂ degree)
  Module.finBasis ℂ (Binary.HomogeneousPoly degree)

end Bases

section Plane

variable {X : Type*} [TopologicalSpace X]

/-- Continuity of a family of points of the real plane group `ℝ² ⋊ GL₂(ℝ)`, in its two
components. -/
def PlaneContinuous (p : X → RealPlaneGroup) : Prop :=
  Continuous (fun x => (p x).left.toAdd) ∧ Continuous (fun x => (p x).right)

theorem planeContinuous_const (element : RealPlaneGroup) : PlaneContinuous (fun _ : X => element) :=
  ⟨continuous_const, continuous_const⟩

theorem PlaneContinuous.comp {Y : Type*} [TopologicalSpace Y] {p : X → RealPlaneGroup}
    (hp : PlaneContinuous p) {f : Y → X} (hf : Continuous f) : PlaneContinuous (fun y => p (f y)) :=
  ⟨hp.1.comp hf, hp.2.comp hf⟩

theorem planeContinuous_inl {v : X → Fin 2 → ℝ} (hv : Continuous v) :
    PlaneContinuous (fun x => (SemidirectProduct.inl (Multiplicative.ofAdd (v x)) :
        RealPlaneGroup)) :=
  ⟨hv, continuous_const⟩

theorem planeContinuous_inr {B : X → BinaryRealGL} (hB : Continuous B) :
    PlaneContinuous (fun x => (SemidirectProduct.inr (B x) : RealPlaneGroup)) :=
  ⟨continuous_const, hB⟩

theorem PlaneContinuous.mul {p q : X → RealPlaneGroup} (hp : PlaneContinuous p)
    (hq : PlaneContinuous q) : PlaneContinuous (fun x => p x * q x) := by
  constructor
  · have equality : (fun x => (p x * q x).left.toAdd) =
        fun x => (p x).left.toAdd + (p x).right.val.mulVec (q x).left.toAdd := by
      funext x
      rw [SemidirectProduct.mul_left, toAdd_mul, realPlaneRadicalAction_apply]
    rw [equality]
    exact hp.1.add (Continuous.matrix_mulVec (Units.continuous_val.comp hp.2) hq.1)
  · simp only [SemidirectProduct.mul_right]
    exact hp.2.mul hq.2

theorem PlaneContinuous.inv {p : X → RealPlaneGroup} (hp : PlaneContinuous p) :
    PlaneContinuous (fun x => (p x)⁻¹) := by
  constructor
  · have equality : (fun x => ((p x)⁻¹).left.toAdd) =
        fun x => ((p x).right⁻¹).val.mulVec (-(p x).left.toAdd) := by
      funext x
      rw [SemidirectProduct.inv_left, realPlaneRadicalAction_apply, toAdd_inv]
    rw [equality]
    exact Continuous.matrix_mulVec (Units.continuous_coe_inv.comp hp.2) hp.1.neg
  · simp only [SemidirectProduct.inv_right]
    exact hp.2.inv

theorem PlaneContinuous.matrix_val {p : X → RealPlaneGroup} (hp : PlaneContinuous p) :
    Continuous (fun x => (realPlaneMatrix (p x)).val) := by
  have left (i : Fin 2) : Continuous (fun x => (p x).left.toAdd i) := (continuous_apply i).comp hp.1
  have rightVal : Continuous (fun x => ((p x).right : Matrix (Fin 2) (Fin 2) ℝ)) :=
    Units.continuous_val.comp hp.2
  have right (i j : Fin 2) : Continuous (fun x => ((p x).right : Matrix (Fin 2) (Fin 2) ℝ) i j) :=
    rightVal.matrix_elem i j
  apply continuous_pi
  intro row
  apply continuous_pi
  intro column
  fin_cases row <;> fin_cases column <;>
    simp [realPlaneMatrix_apply, realPlaneRadicalMatrix, planeUnipotent, planeLevi, planeBlock,
      Matrix.mul_apply, Fin.sum_univ_three] <;>
    first
    | exact continuous_const
    | exact right _ _
    | exact left _

theorem PlaneContinuous.matrix {p : X → RealPlaneGroup} (hp : PlaneContinuous p) :
    Continuous (fun x => realPlaneMatrix (p x)) := by
  apply Units.continuous_iff.mpr
  refine ⟨hp.matrix_val, ?_⟩
  have equality : (fun x => ((realPlaneMatrix (p x))⁻¹ : RealGL3).val) =
      fun x => (realPlaneMatrix ((p x)⁻¹)).val := by
    funext x
    rw [map_inv]
  rw [equality]
  exact hp.inv.matrix_val

theorem normPower_det_atInfinity (B : BinaryRealGL) (exponent : ℂ) :
    normPower (GeneralLinearGroup.det (atInfinity B)) exponent =
      Complex.exp (exponent * (Real.log |B.val.det| : ℂ)) := by
  rw [normPower, EisensteinRegularization.Helpers.det_atInfinity_binary,
    EisensteinRegularization.Helpers.adeleNorm_realAdeleUnit]
  rfl

theorem continuous_normPower_det {B : X → BinaryRealGL} (hB : Continuous B) (exponent : ℂ) :
    Continuous (fun x => normPower (GeneralLinearGroup.det (atInfinity (B x))) exponent) := by
  simp only [normPower_det_atInfinity]
  have hdet : Continuous (fun x => (B x).val.det) := (Units.continuous_val.comp hB).matrix_det
  have hlog : Continuous (fun x => Real.log |(B x).val.det|) :=
    hdet.abs.log (fun x => abs_ne_zero.mpr (B x).det_ne_zero)
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hlog))

theorem norm_normPower_det_atInfinity (B : BinaryRealGL) (exponent : ℝ) :
    ‖normPower (GeneralLinearGroup.det (atInfinity B)) exponent‖ = |B.val.det| ^ exponent := by
  rw [normPower_det_atInfinity, Complex.norm_exp]
  rw [Real.rpow_def_of_pos (abs_pos.mpr B.det_ne_zero), mul_comm]
  congr 1
  rw [← Complex.ofReal_mul, Complex.ofReal_re, mul_comm]

/-- The real plane action, written through a translation, a coefficient map and a scalar. -/
theorem realPlaneCuspidalRep_eq (degree : ℕ) (cusp : CuspidalRepresentation)
    (element : RealPlaneGroup) (values : cuspidalTensorValues cusp (HomogeneousPoly degree)) :
    ((realPlaneCuspidalRep degree cusp trivialCharacter).ρ element values :
        cuspidalTensorValues cusp (HomogeneousPoly degree)) =
      normPower (GeneralLinearGroup.det (atInfinity element.right)) (((degree : ℂ) + 3) / 2) •
        cuspidalTensorMap cusp (realCoefficientComponent degree trivialCharacter
          (realPlaneMatrix element))
          (cuspidalTensorTranslation cusp (atInfinity element.right) values) := by
  apply Subtype.ext
  funext argument
  rw [realPlaneCuspidalRep_apply]
  rfl

/-- **The real plane action along a continuous path preserves control.** -/
theorem Controlled.plane {degree : ℕ} {cusp : CuspidalRepresentation}
    {family : X → cuspidalTensorValues cusp (HomogeneousPoly degree)}
    (controlled : Controlled cusp family) {p : X → RealPlaneGroup} (hp : PlaneContinuous p) :
    Controlled cusp (fun x => ((realPlaneCuspidalRep degree cusp trivialCharacter).ρ (p x)
      (family x) : cuspidalTensorValues cusp (HomogeneousPoly degree))) := by
  simp only [realPlaneCuspidalRep_eq]
  apply Controlled.smul _ (continuous_normPower_det hp.2 _)
  apply (controlled.translate hp.2).map (homogeneousBasis degree)
  intro vector functional
  exact realCoefficientComponent_functional_continuous _ hp.matrix vector functional

end Plane

end TernaryPeriodPolynomials.EdgeControl
