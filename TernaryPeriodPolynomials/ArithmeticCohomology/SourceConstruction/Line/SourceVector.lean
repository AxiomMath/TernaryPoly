module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.SourceLaws
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceVector

@[expose] public section


/-!
# The smooth-vector form of the line source

Every coefficient of the line source is a finite combination of coefficients of the Levi cocycle with
coefficients `radKernelLine` that are real analytic in the real arguments (given the analytic inputs
on the radical and the coefficient representation).  Hence it is the realization of an explicit
vector `sourceVecLine` of smooth vectors, and `sourceVecLine` depends smoothly on the real arguments.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise
open TernaryPeriodPolynomials.HeckeTranslate.PolyExpansion (degreeMonomials linear_apply_eq_sum)
open TernaryPeriodPolynomials.HeckeTranslate.SmoothClosure (smooth_finset_sum smooth_congr)

namespace TernaryPeriodPolynomials.SourceConstruction

/-! ## Smoothness of the block -/

theorem matSmooth_blockLine {k : ℕ} {P : (Fin k → RealGL3) → RealGL3}
    {N : (Fin k → RealGL3) → GeneralLinearGroup (Fin 2) ℝ} (hP : MatSmooth P)
    (hN : ∀ x i j, (N x).val i j = (P x).val i.succ j.succ) : MatSmooth N := by
  unfold MatSmooth at hP ⊢
  refine contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => ?_
  have h := contDiffOn_pi.mp (contDiffOn_pi.mp hP i.succ) j.succ
  exact h.congr (fun A _ => hN _ i j)

/-! ## The kernel -/

section Kernel

variable {n : ℕ}

/-- The matrix coefficient of the line source: the `μ`-coefficient of the image of the monomial
`ν` under `ρ(w⁻¹) ∘ (l(w y₂) - l(w y₁))`. -/
def radKernelLine (D : InducingData n) (μ : Fin 3 →₀ ℕ) (ν : Fin 2 →₀ ℕ) (y : Fin 3 → RealGL3)
    (w : RealGL3) : ℂ :=
  (realCoefficientComponent n D.chi w⁻¹
    ((lineRadical n D.chi (iwPLine (w * y 2)) - lineRadical n D.chi (iwPLine (w * y 1)))
      (binaryMono (n + 1) ν))).val.coeff μ

theorem radKernelLine_eq (D : InducingData n) (μ : Fin 3 →₀ ℕ) (ν : Fin 2 →₀ ℕ)
    (y : Fin 3 → RealGL3) (w : RealGL3) :
    radKernelLine D μ ν y w =
      ∑ κ ∈ degreeMonomials n,
        ((lineRadical n D.chi (iwPLine (w * y 2)) (binaryMono (n + 1) ν)).val.coeff κ -
            (lineRadical n D.chi (iwPLine (w * y 1)) (binaryMono (n + 1) ν)).val.coeff κ) *
          (fullCoefficientComponent D.chi w⁻¹ (MvPolynomial.monomial κ (1 : ℂ))).coeff μ := by
  unfold radKernelLine
  have h := linear_apply_eq_sum
    ((MvPolynomial.lcoeff ℂ μ).comp (fullCoefficientComponent D.chi w⁻¹))
    ((lineRadical n D.chi (iwPLine (w * y 2)) - lineRadical n D.chi (iwPLine (w * y 1)))
      (binaryMono (n + 1) ν))
  simp only [LinearMap.comp_apply, MvPolynomial.lcoeff_apply] at h
  rw [coe_realCoefficientComponent, h]
  refine Finset.sum_congr rfl (fun κ _ => ?_)
  simp only [LinearMap.sub_apply, Submodule.coe_sub, MvPolynomial.coeff_sub]

theorem radKernelLine_smooth (D : InducingData n) (hR : RadicalAnalyticLine n D.chi)
    (hC : CoefficientAnalytic D.chi) (μ : Fin 3 →₀ ℕ) (ν : Fin 2 →₀ ℕ) {k : ℕ}
    {U : (Fin k → RealGL3) → Fin 3 → RealGL3} {W : (Fin k → RealGL3) → RealGL3}
    (hW : MatSmooth W) (hU : ∀ i, MatSmooth (fun x => U x i)) :
    Smooth (fun x => radKernelLine D μ ν (U x) (W x)) := by
  refine smooth_congr (f := fun x => ∑ κ ∈ degreeMonomials n,
    ((lineRadical n D.chi (iwPLine (W x * U x 2)) (binaryMono (n + 1) ν)).val.coeff κ -
        (lineRadical n D.chi (iwPLine (W x * U x 1)) (binaryMono (n + 1) ν)).val.coeff κ) *
      (fullCoefficientComponent D.chi (W x)⁻¹ (MvPolynomial.monomial κ (1 : ℂ))).coeff μ)
    (smooth_finset_sum _ _ (fun κ _ => ?_)) (fun x => radKernelLine_eq D μ ν (U x) (W x))
  refine smooth_mul_complex (smooth_sub' ?_ ?_) ?_
  · exact smooth_comp_matSmooth
      (fun q : RealGL3 => (lineRadical n D.chi (iwPLine q) (binaryMono (n + 1) ν)).val.coeff κ)
      (hR _ κ) (matSmooth_mul hW (hU 2))
  · exact smooth_comp_matSmooth
      (fun q : RealGL3 => (lineRadical n D.chi (iwPLine q) (binaryMono (n + 1) ν)).val.coeff κ)
      (hR _ κ) (matSmooth_mul hW (hU 1))
  · exact smooth_comp_matSmooth
      (fun q : RealGL3 =>
        (fullCoefficientComponent D.chi q⁻¹ (MvPolynomial.monomial κ (1 : ℂ))).coeff μ)
      (hC κ μ) hW

/-- **The coefficients of the line source.** -/
theorem coeff_lineSourceAt (D : InducingData n) (E : LineLeviCocycleData D.cusp n)
    (y : Fin 3 → RealGL3) (g : AdelicGL) (x : BinaryAdelicGL) (μ : Fin 3 →₀ ℕ) :
    (lineSourceAt D E y g x).val.coeff μ =
      ∑ ν ∈ binaryMonomials (n + 1), radKernelLine D μ ν y (realGroup g) *
        (cFLine D g * ((E.α (iwALine (realGroup g * y 1)) (x * bFLine g)).val.coeff ν -
          (E.α (iwALine (realGroup g * y 0)) (x * bFLine g)).val.coeff ν)) := by
  have h := binary_coeff_apply_eq_sum
    ((realCoefficientComponent n D.chi (realGroup g)⁻¹).comp
      (lineRadical n D.chi (iwPLine (realGroup g * y 2)) -
        lineRadical n D.chi (iwPLine (realGroup g * y 1))))
    (cFLine D g • (E.α (iwALine (realGroup g * y 1)) (x * bFLine g) -
      E.α (iwALine (realGroup g * y 0)) (x * bFLine g))) μ
  simp only [LinearMap.comp_apply] at h
  unfold lineSourceAt
  rw [h]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  simp only [radKernelLine, Submodule.coe_smul, MvPolynomial.coeff_smul, Submodule.coe_sub,
    MvPolynomial.coeff_sub, smul_eq_mul]
  ring

end Kernel

/-! ## The vector -/

section Vector

variable {n : ℕ}

/-- The smooth vector whose realization is the `μ`-coefficient of the line source. -/
def sourceVecLine (D : InducingData n) (E : LineLeviCocycleData D.cusp n) (μ : Fin 3 →₀ ℕ)
    (c : ℂ) (b : BinaryAdelicGL) (y : Fin 3 → RealGL3) (w : RealGL3) : D.cusp.smooth :=
  ∑ ν ∈ binaryMonomials (n + 1), (radKernelLine D μ ν y w * c) •
    (piSmooth D.cusp b (E.lift ν (iwALine (w * y 1))) -
      piSmooth D.cusp b (E.lift ν (iwALine (w * y 0))))

theorem sourceVecLine_val (D : InducingData n) (E : LineLeviCocycleData D.cusp n)
    (μ : Fin 3 →₀ ℕ) (c : ℂ) (b : BinaryAdelicGL) (y : Fin 3 → RealGL3) (w : RealGL3) :
    (sourceVecLine D E μ c b y w).val =
      ∑ ν ∈ binaryMonomials (n + 1), (radKernelLine D μ ν y w * c) •
        (D.cusp.π b (E.lift ν (iwALine (w * y 1))).val -
          D.cusp.π b (E.lift ν (iwALine (w * y 0))).val) := by
  unfold sourceVecLine
  rw [Submodule.coe_sum]
  exact Finset.sum_congr rfl (fun ν _ => rfl)

theorem realize_sourceVecLine (D : InducingData n) (E : LineLeviCocycleData D.cusp n)
    (μ : Fin 3 →₀ ℕ) (c : ℂ) (b : BinaryAdelicGL) (y : Fin 3 → RealGL3) (w : RealGL3)
    (A : BinaryAdelicGL) :
    D.cusp.realize (sourceVecLine D E μ c b y w) A =
      ∑ ν ∈ binaryMonomials (n + 1), (radKernelLine D μ ν y w * c) *
        ((E.α (iwALine (w * y 1)) (A * b)).val.coeff ν -
          (E.α (iwALine (w * y 0)) (A * b)).val.coeff ν) := by
  unfold sourceVecLine
  rw [_root_.map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  rw [map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, realize_piSmooth,
    realize_piSmooth, E.lift_realize, E.lift_realize]

theorem coeff_lineSourceAt_eq_realize (D : InducingData n) (E : LineLeviCocycleData D.cusp n)
    (μ : Fin 3 →₀ ℕ) (y : Fin 3 → RealGL3) (g : AdelicGL) (A : BinaryAdelicGL) :
    (lineSourceAt D E y g A).val.coeff μ =
      D.cusp.realize (sourceVecLine D E μ (cFLine D g) (bFLine g) y (realGroup g)) A := by
  rw [coeff_lineSourceAt, realize_sourceVecLine]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  ring

theorem sourceVecLine_smooth (D : InducingData n) (E : LineLeviCocycleData D.cusp n)
    (hR : RadicalAnalyticLine n D.chi) (hC : CoefficientAnalytic D.chi) (μ : Fin 3 →₀ ℕ) (c : ℂ)
    (b : BinaryAdelicGL) {k : ℕ} {U : (Fin k → RealGL3) → Fin 3 → RealGL3}
    {W : (Fin k → RealGL3) → RealGL3} (hW : MatSmooth W) (hU : ∀ i, MatSmooth (fun x => U x i)) :
    Smooth (fun x => (sourceVecLine D E μ c b (U x) (W x)).val) := by
  have hv : ∀ (ν : Fin 2 →₀ ℕ) (i : Fin 3), Smooth (fun x : Fin k → RealGL3 =>
      D.cusp.π b (E.lift ν (iwALine (W x * U x i))).val) := by
    intro ν i
    have hM : MatSmooth (fun x => iwALine (W x * U x i)) :=
      matSmooth_blockLine (matSmooth_iwasawaB (matSmooth_mul hW (hU i)))
        (fun x i' j' => iwALine_val _ i' j')
    exact smooth_clm_comp' (psPiCLM D.cusp b)
      (smooth_comp_matSmooth (fun h : BinaryRealGL => (E.lift ν h).val) (E.lift_smooth ν) hM)
  refine smooth_congr
    (f := fun x => ∑ ν ∈ binaryMonomials (n + 1), (radKernelLine D μ ν (U x) (W x) * c) •
      (D.cusp.π b (E.lift ν (iwALine (W x * U x 1))).val -
        D.cusp.π b (E.lift ν (iwALine (W x * U x 0))).val))
    (smooth_finset_sum _ _ (fun ν _ => ?_)) (fun x => sourceVecLine_val D E μ c b (U x) (W x))
  exact smooth_smul_vec (smooth_mul_complex (radKernelLine_smooth D hR hC μ ν hW hU)
    (smooth_const_complex c)) (smooth_sub' (hv ν 1) (hv ν 0))

end Vector

end TernaryPeriodPolynomials.SourceConstruction

end
