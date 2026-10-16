module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Source.PlaneTwCore
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Source.EichlerTwLift
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceFinal
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Good.LineUniformDecay

@[expose] public section


/-!
# The sign-twisted plane source is a source cocycle

For the odd quadratic character `χ` of conductor three, the twisted plane source
`planeSourceTw D E` built from a sign-twisted Levi cocycle `E` (`PlaneTwCore`) is a smooth
homogeneous two-cocycle whose coefficients are normalized plane-induced sections:
`IsSourceCocycle D .plane (planeSourceTw D E)`.  The proof follows `PlaneSourceLaws`,
`PlaneSourceVector`, `PlaneSourceInduced` and `PlaneSourceFinal`; the new points
are the corner sign `epsP` in the torus law and the analyticity of the matrix coefficients of the
coefficient representation twisted by the sign of the determinant (`coefficientAnalyticTw`), which
are `|det| · (polynomial in the entries)`.  A sign-twisted Eichler cocycle is packaged as such a
Levi cocycle (`exists_leviCocycleDataTw`), which gives `exists_planeSourceTw`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm (finiteAdeleUnit)
open TernaryPeriodPolynomials.SphericalDetection.Helpers (invertibleMatrix_val)
open TernaryPeriodPolynomials.HeckeTranslate.SmoothClosure (smooth_finset_sum smooth_congr)
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.Spectral.LevelOneNontrivial (ConductorThree)

namespace TernaryPeriodPolynomials.TwistedSource

/-! ## Analyticity of the matrix coefficients for an odd character -/

section Analytic

theorem componentCharacter_inv_mul_det (χ : RankOneCharacter)
    (hodd : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (g : RealGL3) :
    componentCharacter χ g⁻¹ * algebraMap ℝ ℂ g.val.det = algebraMap ℝ ℂ |g.val.det| := by
  have h1 : componentCharacter χ g⁻¹ =
      if 0 < (GeneralLinearGroup.det g).val then (1 : ℂ) else -1 :=
    (chi_real_sign χ hodd _).trans (sign_det_inv g)
  have h2 : (GeneralLinearGroup.det g).val = g.val.det := GeneralLinearGroup.val_det_apply g
  have hne : g.val.det ≠ 0 := by
    rw [← h2]
    exact Units.ne_zero _
  rw [h1, h2]
  by_cases hp : 0 < g.val.det
  · rw [ite_eq_left hp, abs_of_pos hp, one_mul]
  · have hn : g.val.det < 0 := lt_of_le_of_ne (not_lt.mp hp) hne
    rw [ite_eq_right hp, abs_of_neg hn, map_neg, neg_one_mul]

/-- **Analyticity of the matrix coefficients of the coefficient representation** for an odd
character: they are `|det|` times a polynomial in the entries. -/
theorem coefficientAnalyticTw (χ : RankOneCharacter)
    (hodd : χ.toMonoidHom (realAdeleUnit (-1)) = -1) : CoefficientAnalytic χ := by
  intro κ μ
  unfold Smooth
  have hdet : ContDiff ℝ ⊤ (fun A : Fin 1 → Matrix (Fin 3) (Fin 3) ℝ => (A 0).det) := by
    have h : ContDiff ℝ ⊤ (fun M : Matrix (Fin 3) (Fin 3) ℝ => M.det) := by
      simp only [Matrix.det_fin_three]
      fun_prop
    exact h.comp (contDiff_apply ℝ (Matrix (Fin 3) (Fin 3) ℝ) (0 : Fin 1))
  have hT : ContDiff ℝ ⊤ (fun A : Fin 1 → Matrix (Fin 3) (Fin 3) ℝ =>
      (substitute ((A 0).map (algebraMap ℝ ℂ)) (MvPolynomial.monomial κ (1 : ℂ))).coeff μ) :=
    contDiff_coeff_substitute
      (fun A : Fin 1 → Matrix (Fin 3) (Fin 3) ℝ => (A 0).map (algebraMap ℝ ℂ))
      (fun i j => (contDiff_mapEntry i j).comp
        (contDiff_apply ℝ (Matrix (Fin 3) (Fin 3) ℝ) (0 : Fin 1)))
      (MvPolynomial.monomial κ (1 : ℂ)) μ
  have habs : ContDiffOn ℝ ⊤
      (fun A : Fin 1 → Matrix (Fin 3) (Fin 3) ℝ => Real.sqrt ((A 0).det ^ 2))
      {A | ∀ i, (A i).det ≠ 0} := by
    intro A hA
    exact ((hdet.pow 2).contDiffWithinAt).sqrt (pow_ne_zero 2 (hA 0))
  have hS : ContDiffOn ℝ ⊤ (fun A : Fin 1 → Matrix (Fin 3) (Fin 3) ℝ =>
      algebraMap ℝ ℂ (Real.sqrt ((A 0).det ^ 2)) *
        (substitute ((A 0).map (algebraMap ℝ ℂ)) (MvPolynomial.monomial κ (1 : ℂ))).coeff μ)
      {A | ∀ i, (A i).det ≠ 0} :=
    (contDiff_algebraMap_real.comp_contDiffOn habs).mul hT.contDiffOn
  refine hS.congr (fun A hA => ?_)
  have hA0 : (A 0).det ≠ 0 := hA 0
  show (fullCoefficientComponent χ (invertibleMatrix (A 0))⁻¹
      (MvPolynomial.monomial κ (1 : ℂ))).coeff μ =
    algebraMap ℝ ℂ (Real.sqrt ((A 0).det ^ 2)) * _
  rw [fullCoefficientComponent_inv_apply, componentCharacter_inv_mul_det χ hodd,
    MvPolynomial.coeff_smul, smul_eq_mul, invertibleMatrix_val (A 0) hA0, Real.sqrt_sq_eq_abs]

end Analytic

/-! ## The corner sign of the generators -/

section Corner

theorem epsP_planeLevi_one (A : BinaryRealGL) (h : planeLevi A 1 ∈ planeParabolic ℝ) :
    epsP ⟨planeLevi A 1, h⟩ = 1 :=
  ite_eq_left (show (0 : ℝ) < (planeLevi A 1).val 2 2 from zero_lt_one)

theorem epsP_planeUnipotent (s t : ℝ) (h : planeUnipotent s t ∈ planeParabolic ℝ) :
    epsP ⟨planeUnipotent s t, h⟩ = 1 :=
  ite_eq_left (show (0 : ℝ) < (planeUnipotent s t).val 2 2 from zero_lt_one)

theorem epsP_planeLevi_torus (χ : RankOneCharacter)
    (hodd : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (d : ℝˣ)
    (h : planeLevi 1 d ∈ planeParabolic ℝ) :
    epsP ⟨planeLevi 1 d, h⟩ = χ.toMonoidHom (realAdeleUnit d) :=
  (chi_real_sign χ hodd d).symm

end Corner

/-! ## The induced-section laws of the twisted plane source -/

section Laws

variable {n : ℕ} (D : InducingData n) (E : LeviCocycleDataTw D.cusp n)
  (h3 : ConductorThree D.chi)

include h3

/-- **Right invariance under the finite level.** -/
theorem planeSourceAtTw_level (g : AdelicGL) (k : finiteLevel) (y : Fin 3 → RealGL3)
    (x : BinaryAdelicGL) :
    planeSourceAtTw D E y (g * atFinite k.val) x = planeSourceAtTw D E y g x := by
  have hcb : ∀ h : BinaryRealGL, cFC D (g * atFinite k.val) • E.α h (x * bFC (g * atFinite k.val)) =
      cFC D g • E.α h (x * bFC g) := by
    intro h
    have := twist_level_cell D E h3 (finiteGroup g) k h x
    rw [← finiteGroup_mul_atFinite g k.val] at this
    exact this
  unfold planeSourceAtTw
  rw [realGroup_mul_atFinite]
  simp only [smul_sub]
  rw [hcb, hcb]

variable (hodd : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1)

include hodd

/-- **Unipotent invariance.** -/
theorem planeSourceAtTw_unipotent (a b : Adeles) (g : AdelicGL) (y : Fin 3 → RealGL3)
    (x : BinaryAdelicGL) :
    planeSourceAtTw D E y (planeUnipotent a b * g) x = planeSourceAtTw D E y g x := by
  have hr : realGroup (planeUnipotent a b * g) =
      planeUnipotent ((RingHom.fst ℝ FiniteAdeles) a) ((RingHom.fst ℝ FiniteAdeles) b) *
        realGroup g := by
    rw [map_mul, realGroup_planeUnipotent]
  have hfin : finiteGroup (planeUnipotent a b * g) =
      planeUnipotent ((RingHom.snd ℝ FiniteAdeles) a) ((RingHom.snd ℝ FiniteAdeles) b) *
        finiteGroup g := by
    rw [map_mul, finiteGroup_planeUnipotent]
  have h := planeSourceAtTw_translate D E h3 hodd g (planeUnipotent a b * g)
    ⟨planeUnipotent ((RingHom.fst ℝ FiniteAdeles) a) ((RingHom.fst ℝ FiniteAdeles) b),
      planeUnipotent_mem' _ _⟩
    (planeUnipotent ((RingHom.snd ℝ FiniteAdeles) a) ((RingHom.snd ℝ FiniteAdeles) b))
    (planeUnipotent_mem' _ _) hr hfin y x
  rw [h, epsP_planeUnipotent, leviBlock_planeUnipotent, planeBlockGL_planeUnipotent,
    finitePlaneFactor_planeUnipotent]
  simp [ps_atFinite_one, ps_normPower_one]

/-- **The rank-one Levi character.** -/
theorem planeSourceAtTw_torus (t : Adelesˣ) (g : AdelicGL) (y : Fin 3 → RealGL3)
    (x : BinaryAdelicGL) :
    planeSourceAtTw D E y (planeLevi 1 t * g) x =
      D.chi.toMonoidHom t • planeSourceAtTw D E y g x := by
  have hr : realGroup (planeLevi 1 t * g) = planeLevi 1 (realUnitPart t) * realGroup g := by
    rw [map_mul, realGroup_planeLevi, realPart_one']
  have hfin : finiteGroup (planeLevi 1 t * g) = planeLevi 1 (finiteUnitPart t) * finiteGroup g := by
    rw [map_mul, finiteGroup_planeLevi, finitePart_one']
  have h := planeSourceAtTw_translate D E h3 hodd g (planeLevi 1 t * g)
    ⟨planeLevi 1 (realUnitPart t), planeLevi_mem _ _⟩ (planeLevi 1 (finiteUnitPart t))
    (planeLevi_mem _ _) hr hfin y x
  rw [character_split D.chi t]
  rw [h, epsP_planeLevi_torus D.chi hodd, leviBlock_planeLevi, planeBlockGL_planeLevi',
    finitePlaneFactor_planeLevi]
  simp [ps_atFinite_one, ps_normPower_one, ps_normPower_zero,
    ps_finiteAdeleUnit_one]

/-- **The `GL₂` Levi law.** -/
theorem planeSourceAtTw_levi (A : BinaryAdelicGL) (g : AdelicGL) (y : Fin 3 → RealGL3)
    (x : BinaryAdelicGL) :
    planeSourceAtTw D E y (planeLevi A 1 * g) x =
      normPower (GeneralLinearGroup.det A) (((n : ℂ) + 3) / 2) •
        planeSourceAtTw D E y g (x * A) := by
  have hr : realGroup (planeLevi A 1 * g) = planeLevi (realPart A) 1 * realGroup g := by
    rw [map_mul, realGroup_planeLevi, realUnitPart_one']
  have hfin : finiteGroup (planeLevi A 1 * g) = planeLevi (finitePart A) 1 * finiteGroup g := by
    rw [map_mul, finiteGroup_planeLevi, finiteUnitPart_one']
  have h := planeSourceAtTw_translate D E h3 hodd g (planeLevi A 1 * g)
    ⟨planeLevi (realPart A) 1, planeLevi_mem _ _⟩ (planeLevi (finitePart A) 1)
    (planeLevi_mem _ _) hr hfin y x
  have hA : atFinite (finitePart A) * atInfinity (realPart A) = A := by
    rw [atFinite_mul_atInfinity_comm, ← adelic_split]
  rw [h, epsP_planeLevi_one, leviBlock_planeLevi, planeBlockGL_planeLevi',
    finitePlaneFactor_planeLevi, ps_finiteAdeleUnit_one, map_one D.chi.toMonoidHom,
    ps_normPower_zero, hA]
  simp only [one_mul, mul_one]
  rw [← normPower_det_split]

end Laws

/-! ## The coefficients of the twisted plane source -/

section Vector

variable {n : ℕ}

/-- **The coefficients of the twisted plane source.** -/
theorem coeff_planeSourceAtTw (D : InducingData n) (E : LeviCocycleDataTw D.cusp n)
    (y : Fin 3 → RealGL3) (g : AdelicGL) (x : BinaryAdelicGL) (μ : Fin 3 →₀ ℕ) :
    (planeSourceAtTw D E y g x).val.coeff μ =
      ∑ ν ∈ binaryMonomials (n + 1), radKernel D μ ν y (realGroup g) *
        (cFC D g * ((E.α (iwA (realGroup g * y 1)) (x * bFC g)).val.coeff ν -
          (E.α (iwA (realGroup g * y 0)) (x * bFC g)).val.coeff ν)) := by
  have h := binary_coeff_apply_eq_sum
    ((realCoefficientComponent n D.chi (realGroup g)⁻¹).comp
      (planeRadical n D.chi (iwP (realGroup g * y 2)) -
        planeRadical n D.chi (iwP (realGroup g * y 1))))
    (cFC D g • (E.α (iwA (realGroup g * y 1)) (x * bFC g) -
      E.α (iwA (realGroup g * y 0)) (x * bFC g))) μ
  simp only [LinearMap.comp_apply] at h
  unfold planeSourceAtTw
  rw [h]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  simp only [radKernel, Submodule.coe_smul, MvPolynomial.coeff_smul, Submodule.coe_sub,
    MvPolynomial.coeff_sub, smul_eq_mul]
  ring

/-- The smooth vector whose realization is the `μ`-coefficient of the twisted plane source. -/
def sourceVecTw (D : InducingData n) (E : LeviCocycleDataTw D.cusp n) (μ : Fin 3 →₀ ℕ) (c : ℂ)
    (b : BinaryAdelicGL) (y : Fin 3 → RealGL3) (w : RealGL3) : D.cusp.smooth :=
  ∑ ν ∈ binaryMonomials (n + 1), (radKernel D μ ν y w * c) •
    (piSmooth D.cusp b (E.lift ν (iwA (w * y 1))) - piSmooth D.cusp b (E.lift ν (iwA (w * y 0))))

theorem sourceVecTw_val (D : InducingData n) (E : LeviCocycleDataTw D.cusp n) (μ : Fin 3 →₀ ℕ)
    (c : ℂ) (b : BinaryAdelicGL) (y : Fin 3 → RealGL3) (w : RealGL3) :
    (sourceVecTw D E μ c b y w).val =
      ∑ ν ∈ binaryMonomials (n + 1), (radKernel D μ ν y w * c) •
        (D.cusp.π b (E.lift ν (iwA (w * y 1))).val - D.cusp.π b (E.lift ν (iwA (w * y 0))).val) := by
  unfold sourceVecTw
  rw [Submodule.coe_sum]
  exact Finset.sum_congr rfl (fun ν _ => rfl)

theorem realize_sourceVecTw (D : InducingData n) (E : LeviCocycleDataTw D.cusp n)
    (μ : Fin 3 →₀ ℕ) (c : ℂ) (b : BinaryAdelicGL) (y : Fin 3 → RealGL3) (w : RealGL3)
    (A : BinaryAdelicGL) :
    D.cusp.realize (sourceVecTw D E μ c b y w) A =
      ∑ ν ∈ binaryMonomials (n + 1), (radKernel D μ ν y w * c) *
        ((E.α (iwA (w * y 1)) (A * b)).val.coeff ν -
          (E.α (iwA (w * y 0)) (A * b)).val.coeff ν) := by
  unfold sourceVecTw
  rw [_root_.map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  rw [map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, realize_piSmooth,
    realize_piSmooth, E.lift_realize, E.lift_realize]

theorem coeff_planeSourceAtTw_eq_realize (D : InducingData n) (E : LeviCocycleDataTw D.cusp n)
    (μ : Fin 3 →₀ ℕ) (y : Fin 3 → RealGL3) (g : AdelicGL) (A : BinaryAdelicGL) :
    (planeSourceAtTw D E y g A).val.coeff μ =
      D.cusp.realize (sourceVecTw D E μ (cFC D g) (bFC g) y (realGroup g)) A := by
  rw [coeff_planeSourceAtTw, realize_sourceVecTw]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  ring

theorem sourceVecTw_smooth (D : InducingData n) (E : LeviCocycleDataTw D.cusp n)
    (hR : RadicalAnalytic n D.chi) (hC : CoefficientAnalytic D.chi) (μ : Fin 3 →₀ ℕ) (c : ℂ)
    (b : BinaryAdelicGL) {k : ℕ} {U : (Fin k → RealGL3) → Fin 3 → RealGL3}
    {W : (Fin k → RealGL3) → RealGL3} (hW : MatSmooth W) (hU : ∀ i, MatSmooth (fun x => U x i)) :
    Smooth (fun x => (sourceVecTw D E μ c b (U x) (W x)).val) := by
  have hv : ∀ (ν : Fin 2 →₀ ℕ) (i : Fin 3), Smooth (fun x : Fin k → RealGL3 =>
      D.cusp.π b (E.lift ν (iwA (W x * U x i))).val) := by
    intro ν i
    have hM : MatSmooth (fun x => iwA (W x * U x i)) :=
      matSmooth_block (matSmooth_iwasawaB (matSmooth_mul hW (hU i)))
        (fun x i' j' => iwA_val _ i' j')
    exact smooth_clm_comp' (psPiCLM D.cusp b)
      (smooth_comp_matSmooth (fun h : BinaryRealGL => (E.lift ν h).val) (E.lift_smooth ν) hM)
  refine smooth_congr (f := fun x => ∑ ν ∈ binaryMonomials (n + 1),
      (radKernel D μ ν (U x) (W x) * c) •
        (D.cusp.π b (E.lift ν (iwA (W x * U x 1))).val -
          D.cusp.π b (E.lift ν (iwA (W x * U x 0))).val))
    (smooth_finset_sum _ _ (fun ν _ => ?_)) (fun x => sourceVecTw_val D E μ c b (U x) (W x))
  exact smooth_smul_vec (smooth_mul_complex (radKernel_smooth D hR hC μ ν hW hU)
    (smooth_const_complex c)) (smooth_sub' (hv ν 1) (hv ν 0))

end Vector

/-! ## The twisted plane source is a source cocycle -/

section Induced

variable {n : ℕ}

theorem coeff_planeSourceAtTw_mul_atInfinity (D : InducingData n)
    (E : LeviCocycleDataTw D.cusp n) (y : Fin 3 → RealGL3) (g : AdelicGL) (z : RealGL3)
    (A : BinaryAdelicGL) (μ : Fin 3 →₀ ℕ) :
    (planeSourceAtTw D E y (g * atInfinity z) A).val.coeff μ =
      ∑ ν ∈ binaryMonomials (n + 1), radKernel D μ ν y (realGroup g * z) *
        (cFC D g * ((E.α (iwA (realGroup g * z * y 1)) (A * bFC g)).val.coeff ν -
          (E.α (iwA (realGroup g * z * y 0)) (A * bFC g)).val.coeff ν)) := by
  rw [coeff_planeSourceAtTw, realGroup_mul_atInfinity, cFC_mul_atInfinity, bFC_mul_atInfinity]

theorem planeCoeffFunTw_smooth (D : InducingData n) (E : LeviCocycleDataTw D.cusp n)
    (hR : RadicalAnalytic n D.chi) (hC : CoefficientAnalytic D.chi) (μ : Fin 3 →₀ ℕ)
    (A : BinaryAdelicGL) (c : ℂ) {k : ℕ} {U : (Fin k → RealGL3) → Fin 3 → RealGL3}
    {W : (Fin k → RealGL3) → RealGL3} (hW : MatSmooth W) (hU : ∀ i, MatSmooth (fun x => U x i)) :
    Smooth (fun x : Fin k → RealGL3 => ∑ ν ∈ binaryMonomials (n + 1),
      radKernel D μ ν (U x) (W x) *
        (c * ((E.α (iwA (W x * U x 1)) A).val.coeff ν -
          (E.α (iwA (W x * U x 0)) A).val.coeff ν))) := by
  refine smooth_finset_sum _ _ (fun ν _ => ?_)
  have hs : ∀ i, Smooth (fun x : Fin k → RealGL3 => (E.α (iwA (W x * U x i)) A).val.coeff ν) := by
    intro i
    exact smooth_comp_matSmooth (fun h : BinaryRealGL => (E.α h A).val.coeff ν)
      (E.scalar_smooth ν A)
      (matSmooth_block (matSmooth_iwasawaB (matSmooth_mul hW (hU i)))
        (fun x i' j' => iwA_val _ i' j'))
  exact smooth_mul_complex (radKernel_smooth D hR hC μ ν hW hU)
    (smooth_mul_complex (smooth_const_complex c) (smooth_sub' (hs 1) (hs 0)))

theorem hsc_realizeTw (D : InducingData n) (E : LeviCocycleDataTw D.cusp n)
    (h3 : ConductorThree D.chi) (hodd : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1)
    (μ : Fin 3 →₀ ℕ) (y : Fin 3 → RealGL3) (a : AdelicGL) (z : RealGL3) (A : BinaryAdelicGL) :
    D.cusp.realize (sourceVecTw D E μ (cFC D a) (bFC a) y (realGroup a * z)) A =
      normPower (GeneralLinearGroup.det A)
          (-binaryInductionExponent n .plane cohomologicalPoint) *
        (planeSourceTw D E y (binaryLevi .plane A * (a * atInfinity z))).val.coeff μ := by
  have e := coeff_planeSourceAtTw_eq_realize D E μ y (a * atInfinity z) A
  rw [cFC_mul_atInfinity, bFC_mul_atInfinity, realGroup_mul_atInfinity] at e
  rw [← e]
  show _ = normPower (GeneralLinearGroup.det A)
      (-binaryInductionExponent n .plane cohomologicalPoint) *
    (planeSourceAtTw D E y (planeLevi A 1 * (a * atInfinity z)) 1).val.coeff μ
  rw [planeSourceAtTw_levi D E h3 hodd A _ y 1, one_mul, Submodule.coe_smul,
    MvPolynomial.coeff_smul, smul_eq_mul, plane_binExp, ← mul_assoc, ps_normPower_neg_mul,
    one_mul]

/-- **The coefficients of the twisted plane source are normalized plane-induced sections.** -/
theorem planeSourceTw_isInduced (D : InducingData n) (E : LeviCocycleDataTw D.cusp n)
    (h3 : ConductorThree D.chi) (hodd : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1)
    (hR : RadicalAnalytic n D.chi) (hC : CoefficientAnalytic D.chi) (y : Fin 3 → RealGL3)
    (μ : Fin 3 →₀ ℕ) :
    IsInduced D .plane cohomologicalPoint (fun g => (planeSourceTw D E y g).val.coeff μ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g
    refine smooth_congr
      (f := fun z : Fin 1 → RealGL3 => ∑ ν ∈ binaryMonomials (n + 1),
        radKernel D μ ν y (realGroup g * z 0) *
          (cFC D g * ((E.α (iwA (realGroup g * z 0 * y 1)) (1 * bFC g)).val.coeff ν -
            (E.α (iwA (realGroup g * z 0 * y 0)) (1 * bFC g)).val.coeff ν)))
      (planeCoeffFunTw_smooth D E hR hC μ (1 * bFC g) (cFC D g) (U := fun _ => y)
        (W := fun z => realGroup g * z 0)
        (matSmooth_mul (matSmooth_const _) (matSmooth_coord 0)) (fun i => matSmooth_const (y i)))
      (fun z => ?_)
    exact coeff_planeSourceAtTw_mul_atInfinity D E y g (z 0) 1 μ
  · intro k g
    show (planeSourceAtTw D E y (g * atFinite k.val) 1).val.coeff μ =
      (planeSourceAtTw D E y g 1).val.coeff μ
    rw [planeSourceAtTw_level D E h3 g k y 1]
  · intro a
    refine ⟨fun x => sourceVecTw D E μ (cFC D a) (bFC a) y (realGroup a * x (Fin.last 0)), ?_, ?_⟩
    · exact sourceVecTw_smooth D E hR hC μ (cFC D a) (bFC a) (U := fun _ => y)
        (W := fun x => realGroup a * x (Fin.last 0))
        (matSmooth_mul (matSmooth_const _) (matSmooth_coord _)) (fun i => matSmooth_const (y i))
    · intro x A
      exact hsc_realizeTw D E h3 hodd μ y a (x (Fin.last 0)) A
  · refine ⟨?_, ?_, ?_⟩
    · intro a b g
      show (planeSourceAtTw D E y (planeUnipotent a b * g) 1).val.coeff μ =
        (planeSourceAtTw D E y g 1).val.coeff μ
      rw [planeSourceAtTw_unipotent D E h3 hodd a b g y 1]
    · intro t g
      show (planeSourceAtTw D E y (planeLevi 1 t * g) 1).val.coeff μ =
        D.chi.toMonoidHom t * normPower t (-2 * inductionExponent .plane cohomologicalPoint) *
          (planeSourceAtTw D E y g 1).val.coeff μ
      rw [planeSourceAtTw_torus D E h3 hodd t g y 1, ind_exp_plane, mul_zero, ps_normPower_zero,
        mul_one, Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]
    · intro g
      unfold cuspFunctions
      refine LinearMap.mem_range.mpr ⟨sourceVecTw D E μ (cFC D g) (bFC g) y (realGroup g), ?_⟩
      funext A
      show D.cusp.realize (sourceVecTw D E μ (cFC D g) (bFC g) y (realGroup g)) A =
        normPower (GeneralLinearGroup.det A)
            (-(((n : ℂ) + 3) / 2 + inductionExponent .plane cohomologicalPoint)) *
          (planeSourceAtTw D E y (planeLevi A 1 * g) 1).val.coeff μ
      rw [← coeff_planeSourceAtTw_eq_realize, planeSourceAtTw_levi D E h3 hodd A g y 1, one_mul,
        Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul, ind_exp_plane, add_zero,
        ← mul_assoc, ps_normPower_neg_mul, one_mul]

/-- **The smooth cusp lift of the twisted plane source in all four real variables.** -/
theorem planeSourceTw_hasSmoothCuspLift (D : InducingData n) (E : LeviCocycleDataTw D.cusp n)
    (h3 : ConductorThree D.chi) (hodd : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1)
    (hR : RadicalAnalytic n D.chi) (hC : CoefficientAnalytic D.chi) (μ : Fin 3 →₀ ℕ) :
    HasSmoothCuspLift D .plane cohomologicalPoint
      (fun x g => (planeSourceTw D E x g).val.coeff μ) := by
  intro a
  refine ⟨fun x => sourceVecTw D E μ (cFC D a) (bFC a) (fun i => x (Fin.castSucc i))
    (realGroup a * x (Fin.last 3)), ?_, ?_⟩
  · exact sourceVecTw_smooth D E hR hC μ (cFC D a) (bFC a)
      (U := fun x i => x (Fin.castSucc i)) (W := fun x => realGroup a * x (Fin.last 3))
      (matSmooth_mul (matSmooth_const _) (matSmooth_coord _)) (fun i => matSmooth_coord _)
  · intro x A
    exact hsc_realizeTw D E h3 hodd μ (fun i => x (Fin.castSucc i)) a (x (Fin.last 3)) A

/-- **Assembly: the twisted plane source is a source cocycle**, given the two analytic inputs. -/
theorem planeSourceTw_isSourceCocycle_of_analytic (D : InducingData n)
    (E : LeviCocycleDataTw D.cusp n) (h3 : ConductorThree D.chi)
    (hodd : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1) (hR : RadicalAnalytic n D.chi)
    (hC : CoefficientAnalytic D.chi) : IsSourceCocycle D .plane (planeSourceTw D E) := by
  refine ⟨fun y μ => planeSourceTw_isInduced D E h3 hodd hR hC y μ,
    fun μ => planeSourceTw_hasSmoothCuspLift D E h3 hodd hR hC μ, ?_, ?_⟩
  · intro h y g
    exact planeSourceAtTw_equivariant D E h y g 1
  · intro x g
    exact planeSourceAtTw_cocycle D E x g 1

/-- **The twisted plane source cocycle.** For the odd character of conductor three and a
sign-twisted analytic Levi cocycle `E`, `planeSourceTw D E` is a smooth homogeneous two-cocycle with
plane-induced coefficients. -/
theorem planeSourceTw_isSourceCocycle (D : InducingData n) (E : LeviCocycleDataTw D.cusp n)
    (h3 : ConductorThree D.chi) (hodd : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1) :
    IsSourceCocycle D .plane (planeSourceTw D E) :=
  planeSourceTw_isSourceCocycle_of_analytic D E h3 hodd (radicalAnalytic n D.chi)
    (coefficientAnalyticTw D.chi hodd)

end Induced

/-! ## Gluing the sign-twisted Eichler cocycle -/

section Glue

/-- A sign-twisted Eichler cocycle, packaged as sign-twisted Levi cocycle data. -/
def LeviCocycleDataTw.ofEichlerTw {σ : CuspidalRepresentation} {n : ℕ}
    {α : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    (h : IsEichlerCocycleTw σ n α) : LeviCocycleDataTw σ n where
  α := α
  cocycle := h.1
  orth := h.2.1
  lift μ g := Classical.choose (h.2.2.2.1 μ) g
  lift_realize μ g A := (Classical.choose_spec (h.2.2.2.1 μ)).2.1 g A
  lift_smooth μ := (Classical.choose_spec (h.2.2.2.1 μ)).1
  scalar_smooth μ A := h.2.2.2.2.1 A μ
  spherical μ g := (Classical.choose_spec (h.2.2.2.1 μ)).2.2 g

/-- **Every sign-twisted Eichler cocycle is the cocycle of some sign-twisted Levi cocycle datum.** -/
theorem exists_leviCocycleDataTw {σ : CuspidalRepresentation} {n : ℕ}
    {α : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    (h : IsEichlerCocycleTw σ n α) : ∃ E : LeviCocycleDataTw σ n, E.α = α :=
  ⟨LeviCocycleDataTw.ofEichlerTw h, rfl⟩

/-- **A twisted plane source cocycle exists** for every spherical cuspidal datum of odd
cohomological degree whose character is the odd character of conductor three. -/
theorem exists_planeSourceTw {n : ℕ} (D : InducingData n) (h3 : ConductorThree D.chi)
    (hodd : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1) (hsph : SphericalCusp D.cusp)
    (hn : Odd n) :
    ∃ E : LeviCocycleDataTw D.cusp n, IsSourceCocycle D .plane (planeSourceTw D E) := by
  obtain ⟨α, hα⟩ := exists_eichlerCocycleTw_of_cohomological D.cusp hsph hn D.cohomological
    (TernaryPeriodPolynomials.AnalyticClasses.continuousStages D)
  obtain ⟨E, -⟩ := exists_leviCocycleDataTw hα
  exact ⟨E, planeSourceTw_isSourceCocycle D E h3 hodd⟩

end Glue

end TernaryPeriodPolynomials.TwistedSource
