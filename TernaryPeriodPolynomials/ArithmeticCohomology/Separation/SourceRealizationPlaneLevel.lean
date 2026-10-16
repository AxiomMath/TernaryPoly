module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.SourceCoordinate
public import TernaryPeriodPolynomials.ArithmeticCohomology.BadPlane.SupportSphericity.Helpers
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.CombineGL

@[expose] public section


/-!
# The Levi level of the plane cusps

The value at the inverse of the reference frame of an induced section is a vector of `D.cusp`
fixed by the Levi level of the cusp.  At the identity plane this level is `GL₂(ℤ̂)`
(`spherical_of_nonzero_at_identity`).  At the good plane `span(e₁, e₃)`, whose frame is the
permutation `e₂ ↔ e₃`, the Levi element `planeLevi B 1` is moved past the inverse frame into the
finite level exactly when the second row of `B` is `(0, 1)` modulo three
(`goodPlane_shift`).  Hence:

* `PlaneLevelVector σ good` : `σ` has a nonzero smooth vector fixed by the Levi level of the
  cusp (`GL₂(ℤ̂)` for the identity plane, `{B : B₁₀ ≡ 0, B₁₁ ≡ 1 (3)}` for the good plane);
* a section nonzero at the cusp frame gives such a vector
  (`planeLevelVector_of_nonzero`), so a plane cusp with a nonzero coordinate forces it
  (`planeLevelVector_of_coordinateImage_ne_bot`);
* a nonzero plane summand forces a `Γ₁'(3)`-type level vector in `D.cusp`
  (`planeLevelVector_true_of_summand_ne_bot`).

This is the necessary condition under which the construction inputs of
`SourceRealizationPlane` can hold; it does not depend on that file.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.BadPlaneSupportSphericity.Helpers
open TernaryPeriodPolynomials.HeckeTranslate.HeckeInvariance (combineGL_mul rationalGroup_eq)
open TernaryPeriodPolynomials.BoundaryFiniteness.IntegralFlags (rational)

namespace TernaryPeriodPolynomials.Separation

variable {n : ℕ}

/-! ## The Levi level -/

/-- The congruence condition at three of the good-plane Levi level: second row `(0, 1)`. -/
def PlaneLeviLevel (k : GeneralLinearGroup (Fin 2) IntegralAdeles) : Prop :=
  (GeneralLinearGroup.map integralReduction k).val 1 0 = 0 ∧
    (GeneralLinearGroup.map integralReduction k).val 1 1 = 1

/-- `σ` has a nonzero smooth vector fixed by the Levi level of the plane cusp `good`: all of
`GL₂(ℤ̂)` at the identity plane (`good = false`), the elements of `GL₂(ℤ̂)` with second row
`(0, 1)` modulo three at the good plane (`good = true`). -/
def PlaneLevelVector (σ : CuspidalRepresentation) (good : Bool) : Prop :=
  ∃ v : σ.smooth, v ≠ 0 ∧ ∀ k : GeneralLinearGroup (Fin 2) IntegralAdeles,
    (good = true → PlaneLeviLevel k) →
      σ.π (atFinite (GeneralLinearGroup.map integralEmbedding k)) v.val = v.val

theorem planeLevelVector_false_iff (σ : CuspidalRepresentation) :
    PlaneLevelVector σ false ↔ SphericalCusp σ := by
  constructor
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, fun k => h k (fun hf => by cases hf)⟩
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, fun k _ => h k⟩

theorem planeLevelVector_true_of_false (σ : CuspidalRepresentation)
    (h : PlaneLevelVector σ false) : PlaneLevelVector σ true := by
  obtain ⟨v, hv, hfix⟩ := h
  exact ⟨v, hv, fun k _ => hfix k (fun hf => by cases hf)⟩

/-! ## The good-plane frame and the shift -/

/-- The good-plane frame `e₂ ↔ e₃` over a commutative ring. -/
def goodPlaneFrameR (R : Type*) [CommRing R] : GeneralLinearGroup (Fin 3) R :=
  GeneralLinearGroup.map (Int.castRingHom R) goodPlaneFrame

theorem goodPlaneFrameR_val (R : Type*) [CommRing R] :
    (goodPlaneFrameR R).val = !![1, 0, 0; 0, 0, 1; 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [goodPlaneFrameR, goodPlaneFrame, GeneralLinearGroup.map_apply]

theorem goodPlaneFrameR_mul_self (R : Type*) [CommRing R] :
    goodPlaneFrameR R * goodPlaneFrameR R = 1 := by
  apply Units.ext
  rw [Units.val_mul, goodPlaneFrameR_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem goodPlaneFrameR_inv (R : Type*) [CommRing R] :
    (goodPlaneFrameR R)⁻¹ = goodPlaneFrameR R :=
  inv_eq_of_mul_eq_one_right (goodPlaneFrameR_mul_self R)

/-- The conjugate of a plane Levi element by the good-plane frame. -/
def goodPlaneConj (R : Type*) [CommRing R] (B : GeneralLinearGroup (Fin 2) R) :
    GeneralLinearGroup (Fin 3) R :=
  goodPlaneFrameR R * planeLevi B 1 * (goodPlaneFrameR R)⁻¹

/-- The last row of the conjugate is `(B₁₀, 0, B₁₁)`. -/
theorem goodPlaneConj_lastRow (R : Type*) [CommRing R] (B : GeneralLinearGroup (Fin 2) R)
    (j : Fin 3) : (goodPlaneConj R B).val 2 j = ![B.val 1 0, 0, B.val 1 1] j := by
  rw [goodPlaneConj, goodPlaneFrameR_inv, Units.val_mul, Units.val_mul, goodPlaneFrameR_val]
  fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, planeLevi, planeBlock]

theorem goodPlaneConj_mem_finiteLevel (B : GeneralLinearGroup (Fin 2) IntegralAdeles)
    (hB : PlaneLeviLevel B) :
    GeneralLinearGroup.map integralEmbedding (goodPlaneConj IntegralAdeles B) ∈ finiteLevel := by
  refine Subgroup.mem_map.mpr ⟨goodPlaneConj IntegralAdeles B, ?_, rfl⟩
  change lastRow ᵥ* (GeneralLinearGroup.map integralReduction
    (goodPlaneConj IntegralAdeles B)).val = lastRow
  rw [lastRow_vecMul]
  funext j
  show integralReduction ((goodPlaneConj IntegralAdeles B).val 2 j) = lastRow j
  rw [goodPlaneConj_lastRow]
  obtain ⟨h10, h11⟩ := hB
  have h10' : integralReduction (B.val 1 0) = 0 := h10
  have h11' : integralReduction (B.val 1 1) = 1 := h11
  fin_cases j
  · simpa [lastRow, Pi.single_apply] using h10'
  · simp [lastRow]
  · simpa [lastRow, Pi.single_apply] using h11'

theorem rationalFinite_goodPlane :
    rationalFinite (rational goodPlaneFrame) =
      GeneralLinearGroup.map integralEmbedding (goodPlaneFrameR IntegralAdeles) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rationalFinite, rational, goodPlaneFrameR, goodPlaneFrame,
      GeneralLinearGroup.map_apply]

/-- Right multiplication by a rational adelic matrix conjugates a finite element. -/
theorem planeAtFinite_mul_rationalGroup (F : FiniteGL) (r : RationalGL3) :
    atFinite F * rationalGroup r =
      rationalGroup r * atFinite ((rationalFinite r)⁻¹ * F * rationalFinite r) := by
  rw [rationalGroup_eq r, atFinite, atFinite, combineGL_mul, combineGL_mul]
  congr 1
  · group
  · simp only [rationalFinite]; group

theorem atFinite_mul_goodPlaneInv (X : FiniteGL) :
    atFinite X * rationalGroup (rational goodPlaneFrame)⁻¹ =
      rationalGroup (rational goodPlaneFrame)⁻¹ *
        atFinite (GeneralLinearGroup.map integralEmbedding (goodPlaneFrameR IntegralAdeles) * X *
          (GeneralLinearGroup.map integralEmbedding (goodPlaneFrameR IntegralAdeles))⁻¹) := by
  rw [planeAtFinite_mul_rationalGroup, map_inv rationalFinite, rationalFinite_goodPlane,
    inv_inv]

/-- **The shift.**  For `B` in the good-plane Levi level, the Levi element of `B` is moved past
the inverse good-plane frame into the finite level. -/
theorem goodPlane_shift (B : GeneralLinearGroup (Fin 2) IntegralAdeles) (hB : PlaneLeviLevel B) :
    ∃ K : finiteLevel,
      planeLevi (atFinite (GeneralLinearGroup.map integralEmbedding B)) 1 *
          rationalGroup (rational goodPlaneFrame)⁻¹ =
        rationalGroup (rational goodPlaneFrame)⁻¹ * atFinite K.val := by
  refine ⟨⟨_, goodPlaneConj_mem_finiteLevel B hB⟩, ?_⟩
  have h1 : planeLevi (atFinite (GeneralLinearGroup.map integralEmbedding B)) 1 =
      atFinite (GeneralLinearGroup.map integralEmbedding (planeLevi B 1)) := by
    rw [map_planeLevi, map_one, atFinite_planeLevi]
  rw [h1, atFinite_mul_goodPlaneInv]
  simp only [goodPlaneConj, map_mul, map_inv]

/-! ## A section nonzero at a plane cusp frame gives a level vector -/

/-- A section of the plane induced representation that is nonzero at the inverse of the
good-plane frame gives a vector of `D.cusp` fixed by the good-plane Levi level. -/
theorem planeLevelVector_of_nonzero_at_goodPlane {degree : ℕ} (data : InducingData degree)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane cohomologicalPoint function)
    (nonzero : function (rationalGroup (rational goodPlaneFrame)⁻¹) ≠ 0) :
    PlaneLevelVector data.cusp true := by
  obtain ⟨vectors, _, lift⟩ := induced.2.2.1 (rationalGroup (rational goodPlaneFrame)⁻¹)
  let vector : data.cusp.smooth := vectors (fun _ => 1)
  have realization (argument : BinaryAdelicGL) :
      data.cusp.realize vector argument =
        normPower (GeneralLinearGroup.det argument)
          (-binaryInductionExponent degree .plane cohomologicalPoint) *
        function (planeLevi argument 1 * rationalGroup (rational goodPlaneFrame)⁻¹) := by
    simpa [vector, binaryLevi, atInfinity_one] using lift (fun _ => 1) argument
  refine ⟨vector, ?_, ?_⟩
  · intro zero
    have at_one := realization 1
    have vector_zero : data.cusp.realize vector = 0 := by rw [zero, map_zero]
    rw [vector_zero] at at_one
    apply nonzero
    have levi_one : planeLevi (1 : BinaryAdelicGL) 1 = 1 := (planeLeviHom Adeles).map_one
    simpa [normPower, levi_one] using at_one.symm
  · intro k hk
    obtain ⟨K, hshift⟩ := goodPlane_shift k (hk rfl)
    obtain ⟨element, helement⟩ : ∃ e : BinaryAdelicGL,
        e = atFinite (GeneralLinearGroup.map integralEmbedding k) := ⟨_, rfl⟩
    rw [← helement] at hshift ⊢
    apply realize_fixed_of_positive_eigenvalue data.cusp vector element
      (Real.exp (-((degree : ℝ) + 3) / 2 *
        Real.log (adeleNorm (GeneralLinearGroup.det element) : ℝ)))
      (Real.exp_pos _)
    intro argument
    rw [realization, realization, map_mul, normPower_mul, ← normPower_plane_real]
    have levi_mul : planeLevi (argument * element) 1 =
        planeLevi argument 1 * planeLevi element 1 := by
      simpa [planeLeviHom] using (planeLeviHom Adeles).map_mul (argument, 1) (element, 1)
    have hmain : function (planeLevi (argument * element) 1 *
        rationalGroup (rational goodPlaneFrame)⁻¹) =
        function (planeLevi argument 1 * rationalGroup (rational goodPlaneFrame)⁻¹) := by
      rw [levi_mul, mul_assoc, hshift, ← mul_assoc]
      exact induced.2.1 K _
    rw [hmain]
    ring

/-- The reference frame of the plane cusp `good`. -/
def planeFrameQ : Bool → RationalGL3
  | true => rational goodPlaneFrame
  | false => 1

theorem planeFrameQ_flag (good : Bool) :
    (QuotientGroup.mk (planeFrameQ good) : Flags .plane) = cuspFlag .plane good := by
  cases good <;> rfl

/-- A section nonzero at the inverse reference frame of a plane cusp gives a level vector. -/
theorem planeLevelVector_of_nonzero {degree : ℕ} (data : InducingData degree) (good : Bool)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane cohomologicalPoint function)
    (nonzero : function (rationalGroup (planeFrameQ good)⁻¹) ≠ 0) :
    PlaneLevelVector data.cusp good := by
  cases good
  · refine (planeLevelVector_false_iff _).mpr
      (spherical_of_nonzero_at_identity data function induced ?_)
    simpa [planeFrameQ] using nonzero
  · exact planeLevelVector_of_nonzero_at_goodPlane data function induced nonzero

/-! ## Necessity for summand classes -/

/-- Without a level vector, every plane summand class has zero coordinate at the cusp. -/
theorem cuspRes_plane_eq_zero_of_no_levelVector (D : InducingData n) (good : Bool)
    (hns : ¬ PlaneLevelVector D.cusp good) {a : StratumH2 n D.chi .plane}
    (ha : a ∈ boundarySummand D .plane) : cuspRes n D.chi .plane good a = 0 := by
  have hle : boundarySummand D .plane ≤ LinearMap.ker (cuspRes n D.chi .plane good) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨c, hc, z, hz, rfl⟩
    refine LinearMap.mem_ker.mpr ?_
    refine cuspRes_classOf_eq_zero_of_vanish D .plane good hz (planeFrameQ good)
      (planeFrameQ_flag good) ?_
    intro x
    by_contra hne
    have hpoly : ((c (fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (x i))
        (rationalGroup (planeFrameQ good)⁻¹)).val) ≠ 0 := fun h => hne (Subtype.ext h)
    obtain ⟨m, hm⟩ : ∃ m, (c (fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (x i))
          (rationalGroup (planeFrameQ good)⁻¹)).val.coeff m ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hpoly (MvPolynomial.ext _ _ (by simpa using hall))
    apply hns
    exact planeLevelVector_of_nonzero D good
      (fun g => (c (fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (x i)) g).val.coeff m)
      (hc.1 _ m) hm
  exact hle ha

/-- A plane cusp with a nonzero coordinate forces a level vector in `D.cusp`. -/
theorem planeLevelVector_of_coordinateImage_ne_bot (D : InducingData n) (good : Bool)
    (h : coordinateImage D .plane good ≠ ⊥) : PlaneLevelVector D.cusp good := by
  by_contra hns
  apply h
  rw [eq_bot_iff]
  rintro _ ⟨a, ha, rfl⟩
  rw [cuspRes_plane_eq_zero_of_no_levelVector D good hns ha]
  exact Submodule.zero_mem _

/-- **A nonzero plane summand forces a `Γ₁'(3)`-level vector in `D.cusp`.** -/
theorem planeLevelVector_true_of_summand_ne_bot (D : InducingData n)
    (h : boundarySummand D .plane ≠ ⊥) : PlaneLevelVector D.cusp true := by
  by_contra hns
  apply h
  rw [eq_bot_iff]
  intro a ha
  rw [Submodule.mem_bot]
  have hns' : ¬ PlaneLevelVector D.cusp false :=
    fun h' => hns (planeLevelVector_true_of_false _ h')
  exact (eq_zero_iff_cuspRes .plane a).mpr
    ⟨cuspRes_plane_eq_zero_of_no_levelVector D true hns ha,
      cuspRes_plane_eq_zero_of_no_levelVector D false hns' ha⟩

end TernaryPeriodPolynomials.Separation
