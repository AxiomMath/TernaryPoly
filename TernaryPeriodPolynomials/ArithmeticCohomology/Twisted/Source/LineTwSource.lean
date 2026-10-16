module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Source.LineTwCore
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Source.PlaneTwSource
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.RadicalAnalytic
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.Section
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceBridge

@[expose] public section


/-!
# The line source for the odd character is a source cocycle

For the odd quadratic character `χ` of conductor three, the line source `lineSourceTw D E` built
from an *untwisted* analytic Levi cocycle `E` (`LineTwCore`) is a smooth homogeneous two-cocycle whose
coefficients are normalized line-induced sections: `IsSourceCocycle D .line (lineSourceTw D E)`.  The
proof follows the plane case `PlaneTwSource`: the laws of the line source under the line parabolic
(level, unipotent, torus and Levi) are consequences of the general translation law
`lineSourceAtTw_translate`; the coefficients of the source are finite combinations of the
coefficients of `E` with kernels `radKernelTwL` that are real analytic in the real arguments, which
gives the smooth cusp lift; and the exponents of the line induction at the cohomological point are
`2` for the corner and `(n+1)/2` for the block.  The matrix coefficients of the coefficient
representation are analytic by `coefficientAnalyticTw`, and the line radical is analytic along the
Iwasawa factor by `LineRadicalAnalytic`.  The untwisted Eichler cocycle packaged as Levi cocycle data
gives `exists_lineSourceTw`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm (finiteAdeleUnit)
open TernaryPeriodPolynomials.HeckeTranslate.PolyExpansion (degreeMonomials linear_apply_eq_sum)
open TernaryPeriodPolynomials.HeckeTranslate.SmoothClosure (smooth_finset_sum smooth_congr)
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.Spectral.LevelOneNontrivial (ConductorThree)

namespace TernaryPeriodPolynomials.TwistedSource

/-! ## Analyticity of the line radical and the block of the Iwasawa factor -/

section Analytic

/-- Coefficientwise real analyticity of the line radical along the Iwasawa parabolic factor. -/
def RadicalAnalyticTwL (n : ℕ) (χ : RankOneCharacter) : Prop :=
  ∀ (Q : Binary.HomogeneousPoly (n + 1)) (μ : Fin 3 →₀ ℕ),
    Smooth (fun x : Fin 1 → RealGL3 => (lineRadical n χ (iwL (x 0)) Q).val.coeff μ)

theorem radicalAnalyticTwL (n : ℕ) (χ : RankOneCharacter) : RadicalAnalyticTwL n χ := by
  intro Q μ
  unfold Smooth
  have hmaps : Set.MapsTo (fun A : Fin 1 → Matrix (Fin 3) (Fin 3) ℝ => A 0)
      {A : Fin 1 → Matrix (Fin 3) (Fin 3) ℝ | ∀ i, (A i).det ≠ 0}
      {B : Matrix (Fin 3) (Fin 3) ℝ | B.det ≠ 0} := fun A hA => hA 0
  exact (lineRadical_iwasawaB_contDiffOn n χ Q μ).comp
    (contDiff_apply ℝ (Matrix (Fin 3) (Fin 3) ℝ) (0 : Fin 1)).contDiffOn hmaps

/-- The lower right block of the Iwasawa factor, entrywise. -/
theorem iwAL_val_succ (y : RealGL3) (i j : Fin 2) :
    (iwAL y).val i j = (iwasawaB y).val i.succ j.succ := by
  fin_cases i <;> fin_cases j <;> rfl

/-- Smoothness of a `GL₂`-valued function that is the lower right block of a smooth `GL₃`-valued
function. -/
theorem matSmooth_lowerBlockTwL {k : ℕ} {P : (Fin k → RealGL3) → RealGL3}
    {N : (Fin k → RealGL3) → GeneralLinearGroup (Fin 2) ℝ} (hP : MatSmooth P)
    (hN : ∀ x i j, (N x).val i j = (P x).val i.succ j.succ) : MatSmooth N := by
  unfold MatSmooth at hP ⊢
  refine contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => ?_
  have h := contDiffOn_pi.mp (contDiffOn_pi.mp hP i.succ) j.succ
  exact h.congr (fun A _ => hN _ i j)

end Analytic

/-! ## The corner sign and the block of the generators -/

section Corner

theorem normPower_realAdeleUnit_oneTw (z : ℂ) : normPower (realAdeleUnit 1) z = 1 := by
  rw [TernaryPeriodPolynomials.EisensteinRegularization.Helpers.normPower_realAdeleUnit]
  simp

theorem epsL_leviTw (d : ℝˣ) (A : BinaryRealGL) :
    epsL ⟨lineLevi d A, lineLevi_mem d A⟩ = if 0 < d.val then 1 else -1 := by
  have h : ((⟨lineLevi d A, lineLevi_mem d A⟩ : lineParabolic ℝ).1.val 0 0 : ℝ) = d.val :=
    lr_corner_levi d A
  unfold epsL
  rw [h]

theorem epsL_levi_oneTw (A : BinaryRealGL) : epsL ⟨lineLevi 1 A, lineLevi_mem 1 A⟩ = 1 := by
  rw [epsL_leviTw]
  exact ite_eq_left (by rw [Units.val_one]; exact zero_lt_one)

theorem epsL_levi_torusTw (χ : RankOneCharacter)
    (hodd : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (d : ℝˣ) (A : BinaryRealGL) :
    epsL ⟨lineLevi d A, lineLevi_mem d A⟩ = χ.toMonoidHom (realAdeleUnit d) := by
  rw [epsL_leviTw]
  exact (chi_real_signL χ hodd d).symm

theorem epsL_unipotentTw (s t : ℝ) :
    epsL ⟨lineUnipotent s t, lineUnipotent_mem s t⟩ = 1 :=
  ite_eq_left (show (0 : ℝ) < (lineUnipotent s t).val 0 0 from zero_lt_one)

theorem lineCornerUnit_leviTw (d : ℝˣ) (A : BinaryRealGL) :
    lineCornerUnit (⟨lineLevi d A, lineLevi_mem d A⟩ : lineParabolic ℝ).1
      (⟨lineLevi d A, lineLevi_mem d A⟩ : lineParabolic ℝ).2 = d :=
  lineCornerUnit_lineLevi d A _

theorem lineCornerUnit_unipotentTw (s t : ℝ) :
    lineCornerUnit (⟨lineUnipotent s t, lineUnipotent_mem s t⟩ : lineParabolic ℝ).1
      (⟨lineUnipotent s t, lineUnipotent_mem s t⟩ : lineParabolic ℝ).2 = 1 :=
  lineCornerUnit_lineUnipotent s t _

theorem lineLeviBlock_unipotentTw (s t : ℝ) :
    lineLeviBlock ⟨lineUnipotent s t, lineUnipotent_mem s t⟩ = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end Corner

/-! ## The laws of the line source -/

section Laws

variable {n : ℕ} (D : InducingData n) (E : LeviCocycleData D.cusp n)
  (h3 : ConductorThree D.chi)

include h3

/-- **Right invariance under the finite level.** -/
theorem lineSourceAtTw_level (g : AdelicGL) (k : finiteLevel) (y : Fin 3 → RealGL3)
    (x : BinaryAdelicGL) :
    lineSourceAtTw D E y (g * atFinite k.val) x = lineSourceAtTw D E y g x := by
  have hcb : ∀ h : BinaryRealGL, cFL D (g * atFinite k.val) • E.α h (x * bFL (g * atFinite k.val)) =
      cFL D g • E.α h (x * bFL g) := by
    intro h
    have := twist_level_cellL D E h3 (finiteGroup g) k h x
    rw [← finiteGroup_mul_atFinite g k.val] at this
    exact this
  unfold lineSourceAtTw
  rw [realGroup_mul_atFinite]
  simp only [smul_sub]
  rw [hcb, hcb]

variable (hodd : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1)

include hodd

/-- **Unipotent invariance.** -/
theorem lineSourceAtTw_unipotent (a b : Adeles) (g : AdelicGL) (y : Fin 3 → RealGL3)
    (x : BinaryAdelicGL) :
    lineSourceAtTw D E y (lineUnipotent a b * g) x = lineSourceAtTw D E y g x := by
  have hr : realGroup (lineUnipotent a b * g) =
      lineUnipotent ((RingHom.fst ℝ FiniteAdeles) a) ((RingHom.fst ℝ FiniteAdeles) b) *
        realGroup g := by
    rw [map_mul, realGroup_lineUnipotent]
  have hfin : finiteGroup (lineUnipotent a b * g) =
      lineUnipotent ((RingHom.snd ℝ FiniteAdeles) a) ((RingHom.snd ℝ FiniteAdeles) b) *
        finiteGroup g := by
    rw [map_mul, finiteGroup_lineUnipotent]
  have h := lineSourceAtTw_translate D E h3 hodd g (lineUnipotent a b * g)
    ⟨lineUnipotent ((RingHom.fst ℝ FiniteAdeles) a) ((RingHom.fst ℝ FiniteAdeles) b),
      lineUnipotent_mem _ _⟩
    (lineUnipotent ((RingHom.snd ℝ FiniteAdeles) a) ((RingHom.snd ℝ FiniteAdeles) b))
    (lineUnipotent_mem _ _) hr hfin y x
  rw [h, epsL_unipotentTw, lineCornerUnit_unipotentTw, lineLeviBlock_unipotentTw,
    lineBlockGL_lineUnipotent, finiteLineFactor_lineUnipotent]
  simp [ps_atFinite_one, ps_normPower_one, normPower_realAdeleUnit_oneTw]

/-- **The rank-one Levi character** `χ(t) |t|²`. -/
theorem lineSourceAtTw_torus (t : Adelesˣ) (g : AdelicGL) (y : Fin 3 → RealGL3)
    (x : BinaryAdelicGL) :
    lineSourceAtTw D E y (lineLevi t 1 * g) x =
      (D.chi.toMonoidHom t * normPower t 2) • lineSourceAtTw D E y g x := by
  have hr : realGroup (lineLevi t 1 * g) = lineLevi (realUnitPart t) 1 * realGroup g := by
    rw [map_mul, realGroup_lineLevi, realPart_one']
  have hfin : finiteGroup (lineLevi t 1 * g) = lineLevi (finiteUnitPart t) 1 * finiteGroup g := by
    rw [map_mul, finiteGroup_lineLevi, finitePart_one']
  have h := lineSourceAtTw_translate D E h3 hodd g (lineLevi t 1 * g)
    ⟨lineLevi (realUnitPart t) 1, lineLevi_mem _ _⟩ (lineLevi (finiteUnitPart t) 1)
    (lineLevi_mem _ _) hr hfin y x
  rw [h, epsL_levi_torusTw D.chi hodd, lineCornerUnit_leviTw, lineLeviBlock_levi,
    lineBlockGL_lineLevi, finiteLineFactor_lineLevi, character_split D.chi t,
    normPower_split t 2]
  simp only [map_one, ps_atInfinity_one, ps_atFinite_one, ps_normPower_one,
    ps_finiteAdeleUnit_one, mul_one]
  congr 1
  ring

/-- **The `GL₂` Levi law.** -/
theorem lineSourceAtTw_levi (A : BinaryAdelicGL) (g : AdelicGL) (y : Fin 3 → RealGL3)
    (x : BinaryAdelicGL) :
    lineSourceAtTw D E y (lineLevi 1 A * g) x =
      normPower (GeneralLinearGroup.det A) (((n : ℂ) + 1) / 2) •
        lineSourceAtTw D E y g (x * A) := by
  have hr : realGroup (lineLevi 1 A * g) = lineLevi 1 (realPart A) * realGroup g := by
    rw [map_mul, realGroup_lineLevi, realUnitPart_one']
  have hfin : finiteGroup (lineLevi 1 A * g) = lineLevi 1 (finitePart A) * finiteGroup g := by
    rw [map_mul, finiteGroup_lineLevi, finiteUnitPart_one']
  have h := lineSourceAtTw_translate D E h3 hodd g (lineLevi 1 A * g)
    ⟨lineLevi 1 (realPart A), lineLevi_mem _ _⟩ (lineLevi 1 (finitePart A))
    (lineLevi_mem _ _) hr hfin y x
  have hA : atFinite (finitePart A) * atInfinity (realPart A) = A := by
    rw [atFinite_mul_atInfinity_comm, ← adelic_split]
  rw [h, epsL_levi_oneTw, lineCornerUnit_leviTw, normPower_realAdeleUnit_oneTw,
    lineLeviBlock_levi, lineBlockGL_lineLevi, finiteLineFactor_lineLevi,
    ps_finiteAdeleUnit_one, map_one D.chi.toMonoidHom, hA]
  simp only [ps_normPower_one, one_mul, mul_one]
  rw [← normPower_det_split]

end Laws

/-! ## The coefficients of the line source -/

section Vector

variable {n : ℕ}

/-- The matrix coefficient of the line source: the `μ`-coefficient of the image of the monomial
`ν` under `ρ(w⁻¹) ∘ (l(w y₂) - l(w y₁))`. -/
def radKernelTwL (D : InducingData n) (μ : Fin 3 →₀ ℕ) (ν : Fin 2 →₀ ℕ) (y : Fin 3 → RealGL3)
    (w : RealGL3) : ℂ :=
  (realCoefficientComponent n D.chi w⁻¹
    ((lineRadical n D.chi (iwL (w * y 2)) - lineRadical n D.chi (iwL (w * y 1)))
      (binaryMono (n + 1) ν))).val.coeff μ

theorem radKernelTwL_eq (D : InducingData n) (μ : Fin 3 →₀ ℕ) (ν : Fin 2 →₀ ℕ)
    (y : Fin 3 → RealGL3) (w : RealGL3) :
    radKernelTwL D μ ν y w =
      ∑ κ ∈ degreeMonomials n,
        ((lineRadical n D.chi (iwL (w * y 2)) (binaryMono (n + 1) ν)).val.coeff κ -
            (lineRadical n D.chi (iwL (w * y 1)) (binaryMono (n + 1) ν)).val.coeff κ) *
          (fullCoefficientComponent D.chi w⁻¹ (MvPolynomial.monomial κ (1 : ℂ))).coeff μ := by
  unfold radKernelTwL
  have h := linear_apply_eq_sum
    ((MvPolynomial.lcoeff ℂ μ).comp (fullCoefficientComponent D.chi w⁻¹))
    ((lineRadical n D.chi (iwL (w * y 2)) - lineRadical n D.chi (iwL (w * y 1)))
      (binaryMono (n + 1) ν))
  simp only [LinearMap.comp_apply, MvPolynomial.lcoeff_apply] at h
  rw [coe_realCoefficientComponent, h]
  refine Finset.sum_congr rfl (fun κ _ => ?_)
  simp only [LinearMap.sub_apply, Submodule.coe_sub, MvPolynomial.coeff_sub]

theorem radKernelTwL_smooth (D : InducingData n) (hR : RadicalAnalyticTwL n D.chi)
    (hC : CoefficientAnalytic D.chi) (μ : Fin 3 →₀ ℕ) (ν : Fin 2 →₀ ℕ) {k : ℕ}
    {U : (Fin k → RealGL3) → Fin 3 → RealGL3} {W : (Fin k → RealGL3) → RealGL3}
    (hW : MatSmooth W) (hU : ∀ i, MatSmooth (fun x => U x i)) :
    Smooth (fun x => radKernelTwL D μ ν (U x) (W x)) := by
  refine smooth_congr (f := fun x => ∑ κ ∈ degreeMonomials n,
    ((lineRadical n D.chi (iwL (W x * U x 2)) (binaryMono (n + 1) ν)).val.coeff κ -
        (lineRadical n D.chi (iwL (W x * U x 1)) (binaryMono (n + 1) ν)).val.coeff κ) *
      (fullCoefficientComponent D.chi (W x)⁻¹ (MvPolynomial.monomial κ (1 : ℂ))).coeff μ)
    (smooth_finset_sum _ _ (fun κ _ => ?_)) (fun x => radKernelTwL_eq D μ ν (U x) (W x))
  refine smooth_mul_complex (smooth_sub' ?_ ?_) ?_
  · exact smooth_comp_matSmooth
      (fun q : RealGL3 => (lineRadical n D.chi (iwL q) (binaryMono (n + 1) ν)).val.coeff κ)
      (hR _ κ) (matSmooth_mul hW (hU 2))
  · exact smooth_comp_matSmooth
      (fun q : RealGL3 => (lineRadical n D.chi (iwL q) (binaryMono (n + 1) ν)).val.coeff κ)
      (hR _ κ) (matSmooth_mul hW (hU 1))
  · exact smooth_comp_matSmooth
      (fun q : RealGL3 =>
        (fullCoefficientComponent D.chi q⁻¹ (MvPolynomial.monomial κ (1 : ℂ))).coeff μ)
      (hC κ μ) hW

/-- **The coefficients of the line source.** -/
theorem coeff_lineSourceAtTw (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (y : Fin 3 → RealGL3) (g : AdelicGL) (x : BinaryAdelicGL) (μ : Fin 3 →₀ ℕ) :
    (lineSourceAtTw D E y g x).val.coeff μ =
      ∑ ν ∈ binaryMonomials (n + 1), radKernelTwL D μ ν y (realGroup g) *
        (cFL D g * ((E.α (iwAL (realGroup g * y 1)) (x * bFL g)).val.coeff ν -
          (E.α (iwAL (realGroup g * y 0)) (x * bFL g)).val.coeff ν)) := by
  have h := binary_coeff_apply_eq_sum
    ((realCoefficientComponent n D.chi (realGroup g)⁻¹).comp
      (lineRadical n D.chi (iwL (realGroup g * y 2)) -
        lineRadical n D.chi (iwL (realGroup g * y 1))))
    (cFL D g • (E.α (iwAL (realGroup g * y 1)) (x * bFL g) -
      E.α (iwAL (realGroup g * y 0)) (x * bFL g))) μ
  simp only [LinearMap.comp_apply] at h
  unfold lineSourceAtTw
  rw [h]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  simp only [radKernelTwL, Submodule.coe_smul, MvPolynomial.coeff_smul, Submodule.coe_sub,
    MvPolynomial.coeff_sub, smul_eq_mul]
  ring

/-- The smooth vector whose realization is the `μ`-coefficient of the line source. -/
def sourceVecTwL (D : InducingData n) (E : LeviCocycleData D.cusp n) (μ : Fin 3 →₀ ℕ) (c : ℂ)
    (b : BinaryAdelicGL) (y : Fin 3 → RealGL3) (w : RealGL3) : D.cusp.smooth :=
  ∑ ν ∈ binaryMonomials (n + 1), (radKernelTwL D μ ν y w * c) •
    (piSmooth D.cusp b (E.lift ν (iwAL (w * y 1))) - piSmooth D.cusp b (E.lift ν (iwAL (w * y 0))))

theorem sourceVecTwL_val (D : InducingData n) (E : LeviCocycleData D.cusp n) (μ : Fin 3 →₀ ℕ)
    (c : ℂ) (b : BinaryAdelicGL) (y : Fin 3 → RealGL3) (w : RealGL3) :
    (sourceVecTwL D E μ c b y w).val =
      ∑ ν ∈ binaryMonomials (n + 1), (radKernelTwL D μ ν y w * c) •
        (D.cusp.π b (E.lift ν (iwAL (w * y 1))).val -
          D.cusp.π b (E.lift ν (iwAL (w * y 0))).val) := by
  unfold sourceVecTwL
  rw [Submodule.coe_sum]
  exact Finset.sum_congr rfl (fun ν _ => rfl)

theorem realize_sourceVecTwL (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (μ : Fin 3 →₀ ℕ) (c : ℂ) (b : BinaryAdelicGL) (y : Fin 3 → RealGL3) (w : RealGL3)
    (A : BinaryAdelicGL) :
    D.cusp.realize (sourceVecTwL D E μ c b y w) A =
      ∑ ν ∈ binaryMonomials (n + 1), (radKernelTwL D μ ν y w * c) *
        ((E.α (iwAL (w * y 1)) (A * b)).val.coeff ν -
          (E.α (iwAL (w * y 0)) (A * b)).val.coeff ν) := by
  unfold sourceVecTwL
  rw [_root_.map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  rw [map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, realize_piSmooth,
    realize_piSmooth, E.lift_realize, E.lift_realize]

theorem coeff_lineSourceAtTw_eq_realize (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (μ : Fin 3 →₀ ℕ) (y : Fin 3 → RealGL3) (g : AdelicGL) (A : BinaryAdelicGL) :
    (lineSourceAtTw D E y g A).val.coeff μ =
      D.cusp.realize (sourceVecTwL D E μ (cFL D g) (bFL g) y (realGroup g)) A := by
  rw [coeff_lineSourceAtTw, realize_sourceVecTwL]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  ring

theorem sourceVecTwL_smooth (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (hR : RadicalAnalyticTwL n D.chi) (hC : CoefficientAnalytic D.chi) (μ : Fin 3 →₀ ℕ) (c : ℂ)
    (b : BinaryAdelicGL) {k : ℕ} {U : (Fin k → RealGL3) → Fin 3 → RealGL3}
    {W : (Fin k → RealGL3) → RealGL3} (hW : MatSmooth W) (hU : ∀ i, MatSmooth (fun x => U x i)) :
    Smooth (fun x => (sourceVecTwL D E μ c b (U x) (W x)).val) := by
  have hv : ∀ (ν : Fin 2 →₀ ℕ) (i : Fin 3), Smooth (fun x : Fin k → RealGL3 =>
      D.cusp.π b (E.lift ν (iwAL (W x * U x i))).val) := by
    intro ν i
    have hM : MatSmooth (fun x => iwAL (W x * U x i)) :=
      matSmooth_lowerBlockTwL (matSmooth_iwasawaB (matSmooth_mul hW (hU i)))
        (fun x i' j' => iwAL_val_succ _ i' j')
    exact smooth_clm_comp' (psPiCLM D.cusp b)
      (smooth_comp_matSmooth (fun h : BinaryRealGL => (E.lift ν h).val) (E.lift_smooth ν) hM)
  refine smooth_congr (f := fun x => ∑ ν ∈ binaryMonomials (n + 1),
      (radKernelTwL D μ ν (U x) (W x) * c) •
        (D.cusp.π b (E.lift ν (iwAL (W x * U x 1))).val -
          D.cusp.π b (E.lift ν (iwAL (W x * U x 0))).val))
    (smooth_finset_sum _ _ (fun ν _ => ?_)) (fun x => sourceVecTwL_val D E μ c b (U x) (W x))
  exact smooth_smul_vec (smooth_mul_complex (radKernelTwL_smooth D hR hC μ ν hW hU)
    (smooth_const_complex c)) (smooth_sub' (hv ν 1) (hv ν 0))

end Vector

/-! ## The line source is a source cocycle -/

section Induced

variable {n : ℕ}

theorem coeff_lineSourceAtTw_mul_atInfinity (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (y : Fin 3 → RealGL3) (g : AdelicGL) (z : RealGL3) (A : BinaryAdelicGL) (μ : Fin 3 →₀ ℕ) :
    (lineSourceAtTw D E y (g * atInfinity z) A).val.coeff μ =
      ∑ ν ∈ binaryMonomials (n + 1), radKernelTwL D μ ν y (realGroup g * z) *
        (cFL D g * ((E.α (iwAL (realGroup g * z * y 1)) (A * bFL g)).val.coeff ν -
          (E.α (iwAL (realGroup g * z * y 0)) (A * bFL g)).val.coeff ν)) := by
  rw [coeff_lineSourceAtTw, realGroup_mul_atInfinity, cFL_mul_atInfinity, bFL_mul_atInfinity]

theorem lineCoeffFunTw_smooth (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (hR : RadicalAnalyticTwL n D.chi) (hC : CoefficientAnalytic D.chi) (μ : Fin 3 →₀ ℕ)
    (A : BinaryAdelicGL) (c : ℂ) {k : ℕ} {U : (Fin k → RealGL3) → Fin 3 → RealGL3}
    {W : (Fin k → RealGL3) → RealGL3} (hW : MatSmooth W) (hU : ∀ i, MatSmooth (fun x => U x i)) :
    Smooth (fun x : Fin k → RealGL3 => ∑ ν ∈ binaryMonomials (n + 1),
      radKernelTwL D μ ν (U x) (W x) *
        (c * ((E.α (iwAL (W x * U x 1)) A).val.coeff ν -
          (E.α (iwAL (W x * U x 0)) A).val.coeff ν))) := by
  refine smooth_finset_sum _ _ (fun ν _ => ?_)
  have hs : ∀ i, Smooth (fun x : Fin k → RealGL3 => (E.α (iwAL (W x * U x i)) A).val.coeff ν) := by
    intro i
    exact smooth_comp_matSmooth (fun h : BinaryRealGL => (E.α h A).val.coeff ν)
      (E.scalar_smooth ν A)
      (matSmooth_lowerBlockTwL (matSmooth_iwasawaB (matSmooth_mul hW (hU i)))
        (fun x i' j' => iwAL_val_succ _ i' j'))
  exact smooth_mul_complex (radKernelTwL_smooth D hR hC μ ν hW hU)
    (smooth_mul_complex (smooth_const_complex c) (smooth_sub' (hs 1) (hs 0)))

theorem hsc_realizeTwL (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (h3 : ConductorThree D.chi) (hodd : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1)
    (μ : Fin 3 →₀ ℕ) (y : Fin 3 → RealGL3) (a : AdelicGL) (z : RealGL3) (A : BinaryAdelicGL) :
    D.cusp.realize (sourceVecTwL D E μ (cFL D a) (bFL a) y (realGroup a * z)) A =
      normPower (GeneralLinearGroup.det A)
          (-binaryInductionExponent n .line cohomologicalPoint) *
        (lineSourceTw D E y (binaryLevi .line A * (a * atInfinity z))).val.coeff μ := by
  have e := coeff_lineSourceAtTw_eq_realize D E μ y (a * atInfinity z) A
  rw [cFL_mul_atInfinity, bFL_mul_atInfinity, realGroup_mul_atInfinity] at e
  rw [← e]
  show _ = normPower (GeneralLinearGroup.det A)
      (-binaryInductionExponent n .line cohomologicalPoint) *
    (lineSourceAtTw D E y (lineLevi 1 A * (a * atInfinity z)) 1).val.coeff μ
  rw [lineSourceAtTw_levi D E h3 hodd A _ y 1, one_mul, Submodule.coe_smul,
    MvPolynomial.coeff_smul, smul_eq_mul, line_binaryExponent_eq, lineBeta, ← mul_assoc,
    ps_normPower_neg_mul, one_mul]

/-- **The coefficients of the line source are normalized line-induced sections.** -/
theorem lineSourceTw_isInduced (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (h3 : ConductorThree D.chi) (hodd : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1)
    (hR : RadicalAnalyticTwL n D.chi) (hC : CoefficientAnalytic D.chi) (y : Fin 3 → RealGL3)
    (μ : Fin 3 →₀ ℕ) :
    IsInduced D .line cohomologicalPoint (fun g => (lineSourceTw D E y g).val.coeff μ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g
    refine smooth_congr
      (f := fun z : Fin 1 → RealGL3 => ∑ ν ∈ binaryMonomials (n + 1),
        radKernelTwL D μ ν y (realGroup g * z 0) *
          (cFL D g * ((E.α (iwAL (realGroup g * z 0 * y 1)) (1 * bFL g)).val.coeff ν -
            (E.α (iwAL (realGroup g * z 0 * y 0)) (1 * bFL g)).val.coeff ν)))
      (lineCoeffFunTw_smooth D E hR hC μ (1 * bFL g) (cFL D g) (U := fun _ => y)
        (W := fun z => realGroup g * z 0)
        (matSmooth_mul (matSmooth_const _) (matSmooth_coord 0)) (fun i => matSmooth_const (y i)))
      (fun z => ?_)
    exact coeff_lineSourceAtTw_mul_atInfinity D E y g (z 0) 1 μ
  · intro k g
    show (lineSourceAtTw D E y (g * atFinite k.val) 1).val.coeff μ =
      (lineSourceAtTw D E y g 1).val.coeff μ
    rw [lineSourceAtTw_level D E h3 g k y 1]
  · intro a
    refine ⟨fun x => sourceVecTwL D E μ (cFL D a) (bFL a) y (realGroup a * x (Fin.last 0)), ?_, ?_⟩
    · exact sourceVecTwL_smooth D E hR hC μ (cFL D a) (bFL a) (U := fun _ => y)
        (W := fun x => realGroup a * x (Fin.last 0))
        (matSmooth_mul (matSmooth_const _) (matSmooth_coord _)) (fun i => matSmooth_const (y i))
    · intro x A
      exact hsc_realizeTwL D E h3 hodd μ y a (x (Fin.last 0)) A
  · refine ⟨?_, ?_, ?_⟩
    · intro a b g
      show (lineSourceAtTw D E y (lineUnipotent a b * g) 1).val.coeff μ =
        (lineSourceAtTw D E y g 1).val.coeff μ
      rw [lineSourceAtTw_unipotent D E h3 hodd a b g y 1]
    · intro t g
      show (lineSourceAtTw D E y (lineLevi t 1 * g) 1).val.coeff μ =
        D.chi.toMonoidHom t * normPower t (2 * inductionExponent .line cohomologicalPoint) *
          (lineSourceAtTw D E y g 1).val.coeff μ
      rw [lineSourceAtTw_torus D E h3 hodd t g y 1, line_corner_exponent_eq,
        Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]
    · intro g
      unfold cuspFunctions
      refine LinearMap.mem_range.mpr ⟨sourceVecTwL D E μ (cFL D g) (bFL g) y (realGroup g), ?_⟩
      funext A
      show D.cusp.realize (sourceVecTwL D E μ (cFL D g) (bFL g) y (realGroup g)) A =
        normPower (GeneralLinearGroup.det A)
            (-(((n : ℂ) + 3) / 2 - inductionExponent .line cohomologicalPoint)) *
          (lineSourceAtTw D E y (lineLevi 1 A * g) 1).val.coeff μ
      rw [← coeff_lineSourceAtTw_eq_realize, lineSourceAtTw_levi D E h3 hodd A g y 1, one_mul,
        Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul, line_exponent_eq, lineBeta,
        ← mul_assoc, ps_normPower_neg_mul, one_mul]

/-- **The smooth cusp lift of the line source in all four real variables.** -/
theorem lineSourceTw_hasSmoothCuspLift (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (h3 : ConductorThree D.chi) (hodd : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1)
    (hR : RadicalAnalyticTwL n D.chi) (hC : CoefficientAnalytic D.chi) (μ : Fin 3 →₀ ℕ) :
    HasSmoothCuspLift D .line cohomologicalPoint
      (fun x g => (lineSourceTw D E x g).val.coeff μ) := by
  intro a
  refine ⟨fun x => sourceVecTwL D E μ (cFL D a) (bFL a) (fun i => x (Fin.castSucc i))
    (realGroup a * x (Fin.last 3)), ?_, ?_⟩
  · exact sourceVecTwL_smooth D E hR hC μ (cFL D a) (bFL a)
      (U := fun x i => x (Fin.castSucc i)) (W := fun x => realGroup a * x (Fin.last 3))
      (matSmooth_mul (matSmooth_const _) (matSmooth_coord _)) (fun i => matSmooth_coord _)
  · intro x A
    exact hsc_realizeTwL D E h3 hodd μ (fun i => x (Fin.castSucc i)) a (x (Fin.last 3)) A

/-- **Assembly: the line source is a source cocycle**, given the two analytic inputs. -/
theorem lineSourceTw_isSourceCocycle_of_analytic (D : InducingData n)
    (E : LeviCocycleData D.cusp n) (h3 : ConductorThree D.chi)
    (hodd : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1) (hR : RadicalAnalyticTwL n D.chi)
    (hC : CoefficientAnalytic D.chi) : IsSourceCocycle D .line (lineSourceTw D E) := by
  refine ⟨fun y μ => lineSourceTw_isInduced D E h3 hodd hR hC y μ,
    fun μ => lineSourceTw_hasSmoothCuspLift D E h3 hodd hR hC μ, ?_, ?_⟩
  · intro h y g
    exact lineSourceAtTw_equivariant D E h y g 1
  · intro x g
    exact lineSourceAtTw_cocycle D E x g 1

/-- **The line source cocycle for the odd character.** For the odd character of conductor three and
an untwisted analytic Levi cocycle `E`, `lineSourceTw D E` is a smooth homogeneous two-cocycle with
line-induced coefficients. -/
theorem lineSourceTw_isSourceCocycle (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (h3 : ConductorThree D.chi) (hodd : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1) :
    IsSourceCocycle D .line (lineSourceTw D E) :=
  lineSourceTw_isSourceCocycle_of_analytic D E h3 hodd (radicalAnalyticTwL n D.chi)
    (coefficientAnalyticTw D.chi hodd)

end Induced

/-! ## Existence -/

section Glue

/-- **A line source cocycle for the odd character exists** for every spherical cuspidal datum of odd
cohomological degree whose character is the odd character of conductor three. -/
theorem exists_lineSourceTw {n : ℕ} (D : InducingData n) (h3 : ConductorThree D.chi)
    (hodd : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1) (hsph : SphericalCusp D.cusp)
    (hn : Odd n) :
    ∃ E : LeviCocycleData D.cusp n, IsSourceCocycle D .line (lineSourceTw D E) := by
  obtain ⟨α, hα⟩ := exists_eichlerCocycle_of_cohomological D.cusp hsph hn D.cohomological
    (TernaryPeriodPolynomials.AnalyticClasses.continuousStages D)
  exact ⟨LeviCocycleData.ofEichler hα, lineSourceTw_isSourceCocycle D _ h3 hodd⟩

end Glue

end TernaryPeriodPolynomials.TwistedSource
