module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.Coordinate
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.Global
public import TernaryPeriodPolynomials.ArithmeticCohomology.BadPlane.SupportSphericity.Helpers
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.CombineGL

@[expose] public section


/-!
# The spherical bridge at the identity-plane cusp

The cusp statement at the level-one cusps splits, once local multiplicity one is known, into the nonvanishing of the Shapiro coordinate image
`coordinateImage D side good` whenever the local joint generalized eigenspace is nonzero
(`coordinateStatement_of_multiplicityOne`).  This file records exactly what that nonvanishing is:

* **Necessity (proved).**  A source cocycle whose coordinate at the identity plane is nonzero has a
  nonzero value of an induced section at the identity, hence the cuspidal representation has a
  `GL₂(ℤ̂)`-fixed vector (`BadPlaneSupportSphericity.spherical_of_nonzero_at_identity`).
  Consequently `coordinateImage D .plane false = ⊥` as soon as `D.cusp` is not spherical
  (`coordinateImage_plane_false_eq_bot_of_not_spherical`).
* **The two bridge statements.**  `SphericalSourceConstruction` (S1: sphericity produces a summand
  class with nonzero coordinate) and `SphericalForcedByLocal` (S2: a nonzero local joint
  eigenspace of the pair character forces sphericity).  The second is *necessary* for the
  coordinate statement (`sphericalForcedByLocal_of_coordinateStatement`), and the pair gives the
  coordinate statement (`coordinateStatement_of_sphericalBridge`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SpectralSeparation
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.BadPlaneSupportSphericity.Helpers
open TernaryPeriodPolynomials.HeckeTranslate.HeckeInvariance
  (combineGL_mul rationalGroup_eq atFinite_mul)
open TernaryPeriodPolynomials.GoodApartmentFunctional.FrameOrbit (referenceIntegral)
open TernaryPeriodPolynomials.BoundaryFiniteness.IntegralFlags (rational)

namespace TernaryPeriodPolynomials.Separation

variable {n : ℕ}

/-! ## Necessity: nonzero coordinate at the identity plane forces sphericity -/

/-- If `D.cusp` has no `GL₂(ℤ̂)`-fixed vector, every summand class has zero coordinate at the
identity-plane cusp. -/
theorem cuspRes_plane_false_eq_zero_of_not_spherical (D : InducingData n)
    (hns : ¬ SphericalCusp D.cusp) {a : StratumH2 n D.chi .plane}
    (ha : a ∈ boundarySummand D .plane) : cuspRes n D.chi .plane false a = 0 := by
  have hle : boundarySummand D .plane ≤ LinearMap.ker (cuspRes n D.chi .plane false) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨c, hc, z, hz, rfl⟩
    refine cuspRes_classOf_eq_zero_of_vanish D .plane false hz 1 rfl ?_
    intro x
    by_contra hne
    have hpoly : ((c (fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (x i))
        (rationalGroup (1 : RationalGL3)⁻¹)).val) ≠ 0 := fun h => hne (Subtype.ext h)
    obtain ⟨m, hm⟩ : ∃ m, (c (fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (x i))
          (rationalGroup (1 : RationalGL3)⁻¹)).val.coeff m ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hpoly (MvPolynomial.ext _ _ (by simpa using hall))
    apply hns
    refine spherical_of_nonzero_at_identity D
      (fun g => (c (fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (x i)) g).val.coeff m)
      (hc.1 _ m) ?_
    simpa using hm
  exact hle ha

theorem coordinateImage_plane_false_eq_bot_of_not_spherical (D : InducingData n)
    (hns : ¬ SphericalCusp D.cusp) : coordinateImage D .plane false = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨a, ha, rfl⟩
  rw [cuspRes_plane_false_eq_zero_of_not_spherical D hns ha]
  exact Submodule.zero_mem _

/-- A nonzero Shapiro coordinate of a summand class at the identity plane forces sphericity. -/
theorem sphericalCusp_of_coordinateImage_ne_bot (D : InducingData n)
    (h : coordinateImage D .plane false ≠ ⊥) : SphericalCusp D.cusp := by
  by_contra hns
  exact h (coordinateImage_plane_false_eq_bot_of_not_spherical D hns)

/-- A nonzero summand has a nonzero coordinate at one of the two cusps of its side: if the other
cusp sees nothing, this one does. -/
theorem coordinateImage_ne_bot_of_other_eq_bot (D : InducingData n) (side : Side) (good : Bool)
    (hne : boundarySummand D side ≠ ⊥) (hother : coordinateImage D side (!good) = ⊥) :
    coordinateImage D side good ≠ ⊥ := by
  intro hbot
  apply hne
  rw [eq_bot_iff]
  intro a ha
  rw [Submodule.mem_bot]
  have h1 : cuspRes n D.chi side good a = 0 := by
    have hmem : cuspRes n D.chi side good a ∈ coordinateImage D side good := ⟨a, ha, rfl⟩
    rwa [hbot, Submodule.mem_bot] at hmem
  have h2 : cuspRes n D.chi side (!good) a = 0 := by
    have hmem : cuspRes n D.chi side (!good) a ∈ coordinateImage D side (!good) := ⟨a, ha, rfl⟩
    rwa [hother, Submodule.mem_bot] at hmem
  refine (eq_zero_iff_cuspRes side a).mpr ?_
  cases good
  · exact ⟨h2, h1⟩
  · exact ⟨h1, h2⟩

/-! ## The two bridge statements at the identity plane -/

/-- **(S1) Source construction at the identity plane.**  If the cuspidal representation of `D` has
a `GL₂(ℤ̂)`-fixed vector, some summand class has nonzero Shapiro coordinate at the identity-plane
cusp. -/
def SphericalSourceConstruction (D : InducingData n) : Prop :=
  SphericalCusp D.cusp → coordinateImage D .plane false ≠ ⊥

/-- **(S2) The prime-three input (strong multiplicity one).**  If the local joint generalized
eigenspace of the pair character at the identity-plane cusp is nonzero (so `D.cusp` has, away from
three, the Hecke eigenvalues of a level-one eigenform), then `D.cusp` has a `GL₂(ℤ̂)`-fixed
vector. -/
def SphericalForcedByLocal (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) : Prop :=
  localJoint n D.chi (pairCharacter D hecke hhecke) .plane false ≠ ⊥ → SphericalCusp D.cusp

/-- (S2) is necessary: it follows from the coordinate statement at the identity plane. -/
theorem sphericalForcedByLocal_of_coordinateStatement (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (h : CoordinateStatement D hecke hhecke .plane false) : SphericalForcedByLocal D hecke hhecke := by
  intro hne
  apply sphericalCusp_of_coordinateImage_ne_bot D
  intro hbot
  apply hne
  rw [eq_bot_iff]
  exact (h.trans hbot.le)

/-- **The coordinate statement at the identity plane** from local multiplicity one,
the source construction (S1) and the prime-three input (S2). -/
theorem coordinateStatement_of_sphericalBridge (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hloc : LocalMultiplicityOne n D.chi (pairCharacter D hecke hhecke) .plane false)
    (hS1 : SphericalSourceConstruction D) (hS2 : SphericalForcedByLocal D hecke hhecke) :
    CoordinateStatement D hecke hhecke .plane false :=
  coordinateStatement_of_multiplicityOne D hecke hhecke .plane false hloc
    fun hne => hS1 (hS2 hne)

/-- Given local multiplicity one, the coordinate statement at the identity plane is equivalent to
the nonvanishing of the coordinate image whenever the local joint eigenspace is nonzero. -/
theorem coordinateStatement_iff_of_multiplicityOne (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hloc : LocalMultiplicityOne n D.chi (pairCharacter D hecke hhecke) .plane false) :
    CoordinateStatement D hecke hhecke .plane false ↔
      (localJoint n D.chi (pairCharacter D hecke hhecke) .plane false ≠ ⊥ →
        coordinateImage D .plane false ≠ ⊥) := by
  refine ⟨fun h hne hbot => hne ?_, fun h => coordinateStatement_of_multiplicityOne D hecke hhecke
    .plane false hloc h⟩
  rw [eq_bot_iff]
  exact h.trans hbot.le

/-! ## The good line cusp

At the good line `cuspFlag .line true` (the reference integral frame `r`), the value of an induced
section at `r⁻¹` is a vector of the cuspidal representation fixed by all of `GL₂(ℤ̂)`: the Levi
element `diag(1, B)` is moved past `r⁻¹` by a line unipotent and an element of the level group. -/

/-- A line Levi element normalizes the line radical. -/
theorem lineLevi_mul_lineUnipotent {R : Type*} [CommRing R] (A : GeneralLinearGroup (Fin 2) R)
    (B : Matrix (Fin 2) (Fin 2) R) (hB : B * A.val = 1) (s t : R) :
    lineLevi 1 A * lineUnipotent s t =
      lineUnipotent (s * B 0 0 + t * B 1 0) (s * B 0 1 + t * B 1 1) * lineLevi 1 A := by
  have h00 : B 0 0 * A.val 0 0 + B 0 1 * A.val 1 0 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrArg (fun M => M 0 0) hB
  have h01 : B 0 0 * A.val 0 1 + B 0 1 * A.val 1 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrArg (fun M => M 0 1) hB
  have h10 : B 1 0 * A.val 0 0 + B 1 1 * A.val 1 0 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrArg (fun M => M 1 0) hB
  have h11 : B 1 0 * A.val 0 1 + B 1 1 * A.val 1 1 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrArg (fun M => M 1 1) hB
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, lineLevi_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lineUnipotent, upperUnipotent, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals first
    | linear_combination s * h00 + t * h10
    | linear_combination -(s * h00 + t * h10)
    | linear_combination s * h01 + t * h11
    | linear_combination -(s * h01 + t * h11)

theorem map_lineUnipotent {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (s t : R) :
    GeneralLinearGroup.map φ (lineUnipotent s t) = lineUnipotent (φ s) (φ t) := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [GeneralLinearGroup.map_apply, lineUnipotent, upperUnipotent]

theorem map_lineLevi_one {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (A : GeneralLinearGroup (Fin 2) R) :
    GeneralLinearGroup.map φ (lineLevi 1 A) = lineLevi 1 (GeneralLinearGroup.map φ A) := by
  apply Units.ext
  change (lineLevi 1 A).val.map φ = _
  rw [lineLevi_val, lineLevi_val]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [GeneralLinearGroup.map_apply]

theorem atFinite_lineUnipotent_eq (a b : FiniteAdeles) :
    atFinite (lineUnipotent a b) = lineUnipotent ((0 : ℝ), a) ((0 : ℝ), b) := by
  apply Units.ext
  refine Matrix.ext fun i j => Prod.ext ?_ ?_ <;>
    fin_cases i <;> fin_cases j <;>
    simp [atFinite, combineGL, pairMatrix, lineUnipotent, upperUnipotent]

theorem atFinite_lineLevi_one (m : BinaryFiniteGL) :
    atFinite (lineLevi 1 m) = lineLevi 1 (atFinite m) := by
  apply Units.ext
  refine Matrix.ext fun i j => Prod.ext ?_ ?_
  · change (1 : Matrix (Fin 3) (Fin 3) ℝ) i j = ((lineLevi 1 (atFinite m)).val i j).1
    rw [lineLevi_val]
    fin_cases i <;> fin_cases j <;> simp [atFinite, combineGL, pairMatrix]
  · change (lineLevi 1 m).val i j = ((lineLevi 1 (atFinite m)).val i j).2
    rw [lineLevi_val, lineLevi_val]
    fin_cases i <;> fin_cases j <;> simp [atFinite, combineGL, pairMatrix]

theorem atFinite_mul_rationalGroup_general (F : FiniteGL) (r : RationalGL3) :
    atFinite F * rationalGroup r =
      rationalGroup r * atFinite ((rationalFinite r)⁻¹ * F * rationalFinite r) := by
  rw [rationalGroup_eq r, atFinite, atFinite, combineGL_mul, combineGL_mul]
  congr 1
  · group
  · simp only [rationalFinite]; group

/-- The reference integral frame of the good line over a commutative ring. -/
def goodLineFrame (R : Type*) [CommRing R] : GL3 R :=
  GeneralLinearGroup.map (Int.castRingHom R) referenceIntegral

theorem goodLineFrame_val (R : Type*) [CommRing R] :
    (goodLineFrame R).val = !![1, 0, 0; 0, 1, 0; 1, 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [goodLineFrame, GeneralLinearGroup.map_apply, referenceIntegral]

theorem goodLineFrame_inv_val (R : Type*) [CommRing R] :
    ((goodLineFrame R)⁻¹).val = !![1, 0, 0; 0, 1, 0; -1, -1, 1] := by
  have hinv : (referenceIntegral⁻¹ : IntegralGL3).val = !![1, 0, 0; 0, 1, 0; -1, -1, 1] := rfl
  have h : (goodLineFrame R)⁻¹ = GeneralLinearGroup.map (Int.castRingHom R) (referenceIntegral⁻¹) :=
    (map_inv (GeneralLinearGroup.map (Int.castRingHom R)) referenceIntegral).symm
  rw [h]
  ext i j
  rw [GeneralLinearGroup.map_apply, hinv]
  fin_cases i <;> fin_cases j <;> simp

/-- The last row of the conjugate of the line Levi by the reference frame, after the line unipotent
correction, is the last row of the identity. -/
theorem goodLine_lastRow {R : Type*} [CommRing R] (B : GeneralLinearGroup (Fin 2) R) (s t : R)
    (hs : (1 - s) * B.val 0 0 + (1 - t) * B.val 1 0 = 1)
    (ht : (1 - s) * B.val 0 1 + (1 - t) * B.val 1 1 = 1) (j : Fin 3) :
    (goodLineFrame R * (lineUnipotent s t)⁻¹ * lineLevi 1 B * (goodLineFrame R)⁻¹).val 2 j =
      (Pi.single 2 1 : Fin 3 → R) j := by
  have hu : ((lineUnipotent s t)⁻¹).val = !![1, -s, -t; 0, 1, 0; 0, 0, 1] := rfl
  rw [Units.val_mul, Units.val_mul, Units.val_mul, goodLineFrame_val, goodLineFrame_inv_val,
    lineLevi_val, hu]
  fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  all_goals first
    | linear_combination -ht
    | linear_combination hs - ht
    | linear_combination ht

theorem goodLine_mem_finiteLevel (B : GeneralLinearGroup (Fin 2) IntegralAdeles)
    (s t : IntegralAdeles) (hs : (1 - s) * B.val 0 0 + (1 - t) * B.val 1 0 = 1)
    (ht : (1 - s) * B.val 0 1 + (1 - t) * B.val 1 1 = 1) :
    GeneralLinearGroup.map integralEmbedding
        (goodLineFrame IntegralAdeles * (lineUnipotent s t)⁻¹ * lineLevi 1 B *
          (goodLineFrame IntegralAdeles)⁻¹) ∈ finiteLevel := by
  refine Subgroup.mem_map.mpr ⟨goodLineFrame IntegralAdeles * (lineUnipotent s t)⁻¹ *
    lineLevi 1 B * (goodLineFrame IntegralAdeles)⁻¹, ?_, rfl⟩
  change lastRow ᵥ* (GeneralLinearGroup.map integralReduction
    (goodLineFrame IntegralAdeles * (lineUnipotent s t)⁻¹ * lineLevi 1 B *
      (goodLineFrame IntegralAdeles)⁻¹)).val = lastRow
  rw [lastRow_vecMul]
  funext j
  rw [GeneralLinearGroup.map_apply, goodLine_lastRow B s t hs ht j]
  fin_cases j <;> simp [lastRow]

theorem rationalFinite_goodLine :
    rationalFinite (rational referenceIntegral) =
      GeneralLinearGroup.map integralEmbedding (goodLineFrame IntegralAdeles) := by
  apply Units.ext
  ext i j
  simp [rationalFinite, rational, goodLineFrame, GeneralLinearGroup.map_apply]

/-- **The shift.** The line Levi of an integral element, moved past the inverse of the reference
good-line frame, becomes a line unipotent times the frame times an element of the level group. -/
theorem goodLine_shift (B : GeneralLinearGroup (Fin 2) IntegralAdeles) :
    ∃ (s t : IntegralAdeles) (K : finiteLevel),
      atFinite (GeneralLinearGroup.map integralEmbedding (lineLevi 1 B)) *
          rationalGroup (rational referenceIntegral)⁻¹ =
        lineUnipotent ((0 : ℝ), integralEmbedding s) ((0 : ℝ), integralEmbedding t) *
          rationalGroup (rational referenceIntegral)⁻¹ * atFinite K.val := by
  have h00 : B.inv 0 0 * B.val 0 0 + B.inv 0 1 * B.val 1 0 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrArg (fun M => M 0 0) B.inv_val
  have h01 : B.inv 0 0 * B.val 0 1 + B.inv 0 1 * B.val 1 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrArg (fun M => M 0 1) B.inv_val
  have h10 : B.inv 1 0 * B.val 0 0 + B.inv 1 1 * B.val 1 0 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrArg (fun M => M 1 0) B.inv_val
  have h11 : B.inv 1 0 * B.val 0 1 + B.inv 1 1 * B.val 1 1 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrArg (fun M => M 1 1) B.inv_val
  obtain ⟨s, hs_def⟩ : ∃ s : IntegralAdeles, s = 1 - (B.inv 0 0 + B.inv 1 0) := ⟨_, rfl⟩
  obtain ⟨t, ht_def⟩ : ∃ t : IntegralAdeles, t = 1 - (B.inv 0 1 + B.inv 1 1) := ⟨_, rfl⟩
  have hs : (1 - s) * B.val 0 0 + (1 - t) * B.val 1 0 = 1 := by
    rw [hs_def, ht_def]; linear_combination h00 + h10
  have ht : (1 - s) * B.val 0 1 + (1 - t) * B.val 1 1 = 1 := by
    rw [hs_def, ht_def]; linear_combination h01 + h11
  have hK := goodLine_mem_finiteLevel B s t hs ht
  refine ⟨s, t, ⟨_, hK⟩, ?_⟩
  have key : ∀ F : FiniteGL, atFinite F * rationalGroup (rational referenceIntegral)⁻¹ =
      rationalGroup (rational referenceIntegral)⁻¹ *
        atFinite (GeneralLinearGroup.map integralEmbedding (goodLineFrame IntegralAdeles) * F *
          (GeneralLinearGroup.map integralEmbedding (goodLineFrame IntegralAdeles))⁻¹) := by
    intro F
    rw [atFinite_mul_rationalGroup_general, map_inv rationalFinite, rationalFinite_goodLine, inv_inv]
  have hu : lineUnipotent ((0 : ℝ), integralEmbedding s) ((0 : ℝ), integralEmbedding t) =
      atFinite (GeneralLinearGroup.map integralEmbedding (lineUnipotent s t)) := by
    rw [map_lineUnipotent, atFinite_lineUnipotent_eq]
  have hconj :
      GeneralLinearGroup.map integralEmbedding (goodLineFrame IntegralAdeles) *
          GeneralLinearGroup.map integralEmbedding (lineLevi 1 B) *
          (GeneralLinearGroup.map integralEmbedding (goodLineFrame IntegralAdeles))⁻¹ =
        GeneralLinearGroup.map integralEmbedding (goodLineFrame IntegralAdeles) *
          GeneralLinearGroup.map integralEmbedding (lineUnipotent s t) *
          (GeneralLinearGroup.map integralEmbedding (goodLineFrame IntegralAdeles))⁻¹ *
        GeneralLinearGroup.map integralEmbedding
          (goodLineFrame IntegralAdeles * (lineUnipotent s t)⁻¹ * lineLevi 1 B *
            (goodLineFrame IntegralAdeles)⁻¹) := by
    simp only [map_mul, map_inv]
    group
  rw [hu, key, key, mul_assoc (rationalGroup (rational referenceIntegral)⁻¹), atFinite_mul]
  exact congrArg (fun x => rationalGroup (rational referenceIntegral)⁻¹ * atFinite x) hconj

theorem lineInductionExponent (degree : ℕ) :
    binaryInductionExponent degree .line cohomologicalPoint = (((degree : ℝ) + 1) / 2 : ℝ) := by
  unfold binaryInductionExponent inductionExponent cohomologicalPoint
  push_cast
  ring

theorem normPower_line_real (degree : ℕ) (unit : Adelesˣ) :
    normPower unit (-binaryInductionExponent degree .line cohomologicalPoint) =
      (Real.exp (-((degree : ℝ) + 1) / 2 * Real.log (adeleNorm unit : ℝ)) : ℂ) := by
  rw [lineInductionExponent]
  unfold normPower
  rw [← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_exp]
  congr 2
  ring

/-- A section of the line induced representation that is nonzero at the inverse of the reference
good-line frame gives a `GL₂(ℤ̂)`-fixed vector of the cuspidal representation. -/
theorem spherical_of_nonzero_at_goodLine {degree : ℕ} (data : InducingData degree)
    (function : AdelicGL → ℂ) (induced : IsInduced data .line cohomologicalPoint function)
    (nonzero : function (rationalGroup (rational referenceIntegral)⁻¹) ≠ 0) :
    SphericalCusp data.cusp := by
  obtain ⟨vectors, _, lift⟩ := induced.2.2.1 (rationalGroup (rational referenceIntegral)⁻¹)
  let vector : data.cusp.smooth := vectors (fun _ => 1)
  have realization (argument : BinaryAdelicGL) :
      data.cusp.realize vector argument =
        normPower (GeneralLinearGroup.det argument)
          (-binaryInductionExponent degree .line cohomologicalPoint) *
        function (lineLevi 1 argument * rationalGroup (rational referenceIntegral)⁻¹) := by
    simpa [vector, binaryLevi, atInfinity_one] using lift (fun _ => 1) argument
  refine ⟨vector, ?_, ?_⟩
  · intro zero
    have at_one := realization 1
    have vector_zero : data.cusp.realize vector = 0 := by rw [zero, map_zero]
    rw [vector_zero] at at_one
    apply nonzero
    have levi_one : lineLevi 1 (1 : BinaryAdelicGL) = 1 := (lineLeviHom Adeles).map_one
    simpa [normPower, levi_one] using at_one.symm
  · intro integral
    obtain ⟨_, _, K, hshift⟩ := goodLine_shift integral
    apply realize_fixed_of_positive_eigenvalue data.cusp vector
      (atFinite (GeneralLinearGroup.map integralEmbedding integral))
      (Real.exp (-((degree : ℝ) + 1) / 2 * Real.log (adeleNorm (GeneralLinearGroup.det
        (atFinite (GeneralLinearGroup.map integralEmbedding integral))) : ℝ)))
      (Real.exp_pos _)
    intro argument
    rw [realization, realization, map_mul, normPower_mul, ← normPower_line_real]
    have levi_mul : lineLevi 1 (argument * atFinite (GeneralLinearGroup.map integralEmbedding
        integral)) = lineLevi 1 argument * lineLevi 1 (atFinite (GeneralLinearGroup.map
          integralEmbedding integral)) := by
      simpa [lineLeviHom] using (lineLeviHom Adeles).map_mul (1, argument)
        (1, atFinite (GeneralLinearGroup.map integralEmbedding integral))
    have hel : lineLevi 1 (atFinite (GeneralLinearGroup.map integralEmbedding integral)) =
        atFinite (GeneralLinearGroup.map integralEmbedding (lineLevi 1 integral)) := by
      rw [map_lineLevi_one, atFinite_lineLevi_one]
    have hmain : function (lineLevi 1 (argument * atFinite (GeneralLinearGroup.map
        integralEmbedding integral)) * rationalGroup (rational referenceIntegral)⁻¹) =
        function (lineLevi 1 argument * rationalGroup (rational referenceIntegral)⁻¹) := by
      rw [levi_mul, hel, mul_assoc, hshift, ← mul_assoc, ← mul_assoc,
        lineLevi_mul_lineUnipotent argument argument.inv argument.inv_val,
        induced.2.1 K, mul_assoc]
      exact induced.2.2.2.1 _ _ _
    rw [hmain]
    ring

/-- If `D.cusp` has no `GL₂(ℤ̂)`-fixed vector, every line summand class has zero coordinate at the
good-line cusp. -/
theorem cuspRes_line_true_eq_zero_of_not_spherical (D : InducingData n)
    (hns : ¬ SphericalCusp D.cusp) {a : StratumH2 n D.chi .line}
    (ha : a ∈ boundarySummand D .line) : cuspRes n D.chi .line true a = 0 := by
  have hle : boundarySummand D .line ≤ LinearMap.ker (cuspRes n D.chi .line true) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨c, hc, z, hz, rfl⟩
    refine cuspRes_classOf_eq_zero_of_vanish D .line true hz (rational referenceIntegral) rfl ?_
    intro x
    by_contra hne
    have hpoly : ((c (fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (x i))
        (rationalGroup (rational referenceIntegral)⁻¹)).val) ≠ 0 := fun h => hne (Subtype.ext h)
    obtain ⟨m, hm⟩ : ∃ m, (c (fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (x i))
          (rationalGroup (rational referenceIntegral)⁻¹)).val.coeff m ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hpoly (MvPolynomial.ext _ _ (by simpa using hall))
    apply hns
    refine spherical_of_nonzero_at_goodLine D
      (fun g => (c (fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (x i)) g).val.coeff m)
      (hc.1 _ m) ?_
    simpa using hm
  exact hle ha

theorem coordinateImage_line_true_eq_bot_of_not_spherical (D : InducingData n)
    (hns : ¬ SphericalCusp D.cusp) : coordinateImage D .line true = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨a, ha, rfl⟩
  rw [cuspRes_line_true_eq_zero_of_not_spherical D hns ha]
  exact Submodule.zero_mem _

/-- A nonzero Shapiro coordinate of a line summand class at the good line forces sphericity. -/
theorem sphericalCusp_of_coordinateImage_line_ne_bot (D : InducingData n)
    (h : coordinateImage D .line true ≠ ⊥) : SphericalCusp D.cusp := by
  by_contra hns
  exact h (coordinateImage_line_true_eq_bot_of_not_spherical D hns)

/-- **(S1) at the good line.** -/
def SphericalSourceConstructionLine (D : InducingData n) : Prop :=
  SphericalCusp D.cusp → coordinateImage D .line true ≠ ⊥

/-- **(S2) at the good line.** -/
def SphericalForcedByLocalLine (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) : Prop :=
  localJoint n D.chi (pairCharacter D hecke hhecke) .line true ≠ ⊥ → SphericalCusp D.cusp

theorem sphericalForcedByLocalLine_of_coordinateStatement (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (h : CoordinateStatement D hecke hhecke .line true) :
    SphericalForcedByLocalLine D hecke hhecke := by
  intro hne
  apply sphericalCusp_of_coordinateImage_line_ne_bot D
  intro hbot
  apply hne
  rw [eq_bot_iff]
  exact h.trans hbot.le

/-- **The coordinate statement at the good line** from local multiplicity one, the
source construction and the prime-three input. -/
theorem coordinateStatement_of_sphericalBridge_line (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hloc : LocalMultiplicityOne n D.chi (pairCharacter D hecke hhecke) .line true)
    (hS1 : SphericalSourceConstructionLine D) (hS2 : SphericalForcedByLocalLine D hecke hhecke) :
    CoordinateStatement D hecke hhecke .line true :=
  coordinateStatement_of_multiplicityOne D hecke hhecke .line true hloc
    fun hne => hS1 (hS2 hne)


end TernaryPeriodPolynomials.Separation
