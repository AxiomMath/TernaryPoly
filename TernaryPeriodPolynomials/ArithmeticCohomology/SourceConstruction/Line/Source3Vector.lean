module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.Source3Laws

@[expose] public section


/-!
# The smooth-vector form of the level-three line source

Every coefficient of the level-three line source is a finite combination of coefficients of the
Levi cocycle with the real analytic kernels `radKernelLine` of the line source (they do not involve
the Levi data and are reused).  Hence it is the realization of an explicit vector `sourceVecLine3`
of smooth vectors, and `sourceVecLine3` depends smoothly on the real arguments.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise
open TernaryPeriodPolynomials.HeckeTranslate.SmoothClosure (smooth_finset_sum smooth_congr)

namespace TernaryPeriodPolynomials.SourceConstruction

section Kernel3

variable {n : ℕ}

/-- **The coefficients of the level-three line source.** -/
theorem coeff_lineSourceAt3 (D : InducingData n) (E : LineLeviCocycleData3 D.cusp n)
    (y : Fin 3 → RealGL3) (g : AdelicGL) (x : BinaryAdelicGL) (μ : Fin 3 →₀ ℕ) :
    (lineSourceAt3 D E y g x).val.coeff μ =
      ∑ ν ∈ binaryMonomials (n + 1), radKernelLine D μ ν y (realGroup g) *
        (cFLine3 D g * ((E.α (iwALine (realGroup g * y 1)) (x * bFLine3 g)).val.coeff ν -
          (E.α (iwALine (realGroup g * y 0)) (x * bFLine3 g)).val.coeff ν)) := by
  have h := binary_coeff_apply_eq_sum
    ((realCoefficientComponent n D.chi (realGroup g)⁻¹).comp
      (lineRadical n D.chi (iwPLine (realGroup g * y 2)) -
        lineRadical n D.chi (iwPLine (realGroup g * y 1))))
    (cFLine3 D g • (E.α (iwALine (realGroup g * y 1)) (x * bFLine3 g) -
      E.α (iwALine (realGroup g * y 0)) (x * bFLine3 g))) μ
  simp only [LinearMap.comp_apply] at h
  unfold lineSourceAt3
  rw [h]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  simp only [radKernelLine, Submodule.coe_smul, MvPolynomial.coeff_smul, Submodule.coe_sub,
    MvPolynomial.coeff_sub, smul_eq_mul]
  ring

end Kernel3

/-! ## The vector -/

section Vector3

variable {n : ℕ}

/-- The smooth vector whose realization is the `μ`-coefficient of the level-three line source. -/
def sourceVecLine3 (D : InducingData n) (E : LineLeviCocycleData3 D.cusp n) (μ : Fin 3 →₀ ℕ)
    (c : ℂ) (b : BinaryAdelicGL) (y : Fin 3 → RealGL3) (w : RealGL3) : D.cusp.smooth :=
  ∑ ν ∈ binaryMonomials (n + 1), (radKernelLine D μ ν y w * c) •
    (piSmooth D.cusp b (E.lift ν (iwALine (w * y 1))) -
      piSmooth D.cusp b (E.lift ν (iwALine (w * y 0))))

theorem sourceVecLine3_val (D : InducingData n) (E : LineLeviCocycleData3 D.cusp n)
    (μ : Fin 3 →₀ ℕ) (c : ℂ) (b : BinaryAdelicGL) (y : Fin 3 → RealGL3) (w : RealGL3) :
    (sourceVecLine3 D E μ c b y w).val =
      ∑ ν ∈ binaryMonomials (n + 1), (radKernelLine D μ ν y w * c) •
        (D.cusp.π b (E.lift ν (iwALine (w * y 1))).val -
          D.cusp.π b (E.lift ν (iwALine (w * y 0))).val) := by
  unfold sourceVecLine3
  rw [Submodule.coe_sum]
  exact Finset.sum_congr rfl (fun ν _ => rfl)

theorem realize_sourceVecLine3 (D : InducingData n) (E : LineLeviCocycleData3 D.cusp n)
    (μ : Fin 3 →₀ ℕ) (c : ℂ) (b : BinaryAdelicGL) (y : Fin 3 → RealGL3) (w : RealGL3)
    (A : BinaryAdelicGL) :
    D.cusp.realize (sourceVecLine3 D E μ c b y w) A =
      ∑ ν ∈ binaryMonomials (n + 1), (radKernelLine D μ ν y w * c) *
        ((E.α (iwALine (w * y 1)) (A * b)).val.coeff ν -
          (E.α (iwALine (w * y 0)) (A * b)).val.coeff ν) := by
  unfold sourceVecLine3
  rw [_root_.map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  rw [map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, realize_piSmooth,
    realize_piSmooth, E.lift_realize, E.lift_realize]

theorem coeff_lineSourceAt3_eq_realize (D : InducingData n) (E : LineLeviCocycleData3 D.cusp n)
    (μ : Fin 3 →₀ ℕ) (y : Fin 3 → RealGL3) (g : AdelicGL) (A : BinaryAdelicGL) :
    (lineSourceAt3 D E y g A).val.coeff μ =
      D.cusp.realize (sourceVecLine3 D E μ (cFLine3 D g) (bFLine3 g) y (realGroup g)) A := by
  rw [coeff_lineSourceAt3, realize_sourceVecLine3]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  ring

theorem sourceVecLine3_smooth (D : InducingData n) (E : LineLeviCocycleData3 D.cusp n)
    (hR : RadicalAnalyticLine n D.chi) (hC : CoefficientAnalytic D.chi) (μ : Fin 3 →₀ ℕ) (c : ℂ)
    (b : BinaryAdelicGL) {k : ℕ} {U : (Fin k → RealGL3) → Fin 3 → RealGL3}
    {W : (Fin k → RealGL3) → RealGL3} (hW : MatSmooth W) (hU : ∀ i, MatSmooth (fun x => U x i)) :
    Smooth (fun x => (sourceVecLine3 D E μ c b (U x) (W x)).val) := by
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
    (smooth_finset_sum _ _ (fun ν _ => ?_)) (fun x => sourceVecLine3_val D E μ c b (U x) (W x))
  exact smooth_smul_vec (smooth_mul_complex (radKernelLine_smooth D hR hC μ ν hW hU)
    (smooth_const_complex c)) (smooth_sub' (hv ν 1) (hv ν 0))

end Vector3

end TernaryPeriodPolynomials.SourceConstruction

end
