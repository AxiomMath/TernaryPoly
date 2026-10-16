module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceLaws

@[expose] public section


/-!
# The smooth-vector form of the plane source

Every coefficient of the plane source is a finite combination of coefficients of the Levi cocycle with
coefficients `radKernel` that are real analytic in the real arguments (given the analytic inputs on
the radical and the coefficient representation). Hence it is the realization of an explicit vector
`sourceVec` of smooth vectors, and `sourceVec` depends smoothly on the real arguments.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise
open TernaryPeriodPolynomials.HeckeTranslate.PolyExpansion (degreeMonomials linear_apply_eq_sum)
open TernaryPeriodPolynomials.HeckeTranslate.SmoothClosure (smooth_finset_sum smooth_congr)

namespace TernaryPeriodPolynomials.SourceConstruction

/-! ## The kernel -/

section Kernel

variable {n : ℕ}

/-- The matrix coefficient of the plane source: the `μ`-coefficient of the image of the monomial
`ν` under `ρ(w⁻¹) ∘ (l(w y₂) - l(w y₁))`. -/
def radKernel (D : InducingData n) (μ : Fin 3 →₀ ℕ) (ν : Fin 2 →₀ ℕ) (y : Fin 3 → RealGL3)
    (w : RealGL3) : ℂ :=
  (realCoefficientComponent n D.chi w⁻¹
    ((planeRadical n D.chi (iwP (w * y 2)) - planeRadical n D.chi (iwP (w * y 1)))
      (binaryMono (n + 1) ν))).val.coeff μ

theorem radKernel_eq (D : InducingData n) (μ : Fin 3 →₀ ℕ) (ν : Fin 2 →₀ ℕ) (y : Fin 3 → RealGL3)
    (w : RealGL3) :
    radKernel D μ ν y w =
      ∑ κ ∈ degreeMonomials n,
        ((planeRadical n D.chi (iwP (w * y 2)) (binaryMono (n + 1) ν)).val.coeff κ -
            (planeRadical n D.chi (iwP (w * y 1)) (binaryMono (n + 1) ν)).val.coeff κ) *
          (fullCoefficientComponent D.chi w⁻¹ (MvPolynomial.monomial κ (1 : ℂ))).coeff μ := by
  unfold radKernel
  have h := linear_apply_eq_sum
    ((MvPolynomial.lcoeff ℂ μ).comp (fullCoefficientComponent D.chi w⁻¹))
    ((planeRadical n D.chi (iwP (w * y 2)) - planeRadical n D.chi (iwP (w * y 1)))
      (binaryMono (n + 1) ν))
  simp only [LinearMap.comp_apply, MvPolynomial.lcoeff_apply] at h
  rw [coe_realCoefficientComponent, h]
  refine Finset.sum_congr rfl (fun κ _ => ?_)
  simp only [LinearMap.sub_apply, Submodule.coe_sub, MvPolynomial.coeff_sub]

theorem radKernel_smooth (D : InducingData n) (hR : RadicalAnalytic n D.chi)
    (hC : CoefficientAnalytic D.chi) (μ : Fin 3 →₀ ℕ) (ν : Fin 2 →₀ ℕ) {k : ℕ}
    {U : (Fin k → RealGL3) → Fin 3 → RealGL3} {W : (Fin k → RealGL3) → RealGL3}
    (hW : MatSmooth W) (hU : ∀ i, MatSmooth (fun x => U x i)) :
    Smooth (fun x => radKernel D μ ν (U x) (W x)) := by
  refine smooth_congr (f := fun x => ∑ κ ∈ degreeMonomials n,
    ((planeRadical n D.chi (iwP (W x * U x 2)) (binaryMono (n + 1) ν)).val.coeff κ -
        (planeRadical n D.chi (iwP (W x * U x 1)) (binaryMono (n + 1) ν)).val.coeff κ) *
      (fullCoefficientComponent D.chi (W x)⁻¹ (MvPolynomial.monomial κ (1 : ℂ))).coeff μ)
    (smooth_finset_sum _ _ (fun κ _ => ?_)) (fun x => radKernel_eq D μ ν (U x) (W x))
  refine smooth_mul_complex (smooth_sub' ?_ ?_) ?_
  · exact smooth_comp_matSmooth
      (fun q : RealGL3 => (planeRadical n D.chi (iwP q) (binaryMono (n + 1) ν)).val.coeff κ)
      (hR _ κ) (matSmooth_mul hW (hU 2))
  · exact smooth_comp_matSmooth
      (fun q : RealGL3 => (planeRadical n D.chi (iwP q) (binaryMono (n + 1) ν)).val.coeff κ)
      (hR _ κ) (matSmooth_mul hW (hU 1))
  · exact smooth_comp_matSmooth
      (fun q : RealGL3 =>
        (fullCoefficientComponent D.chi q⁻¹ (MvPolynomial.monomial κ (1 : ℂ))).coeff μ)
      (hC κ μ) hW

/-- **The coefficients of the plane source.** -/
theorem coeff_planeSourceAt (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (y : Fin 3 → RealGL3) (g : AdelicGL) (x : BinaryAdelicGL) (μ : Fin 3 →₀ ℕ) :
    (planeSourceAt D E y g x).val.coeff μ =
      ∑ ν ∈ binaryMonomials (n + 1), radKernel D μ ν y (realGroup g) *
        (cF D g * ((E.α (iwA (realGroup g * y 1)) (x * bF g)).val.coeff ν -
          (E.α (iwA (realGroup g * y 0)) (x * bF g)).val.coeff ν)) := by
  have h := binary_coeff_apply_eq_sum
    ((realCoefficientComponent n D.chi (realGroup g)⁻¹).comp
      (planeRadical n D.chi (iwP (realGroup g * y 2)) -
        planeRadical n D.chi (iwP (realGroup g * y 1))))
    (cF D g • (E.α (iwA (realGroup g * y 1)) (x * bF g) -
      E.α (iwA (realGroup g * y 0)) (x * bF g))) μ
  simp only [LinearMap.comp_apply] at h
  unfold planeSourceAt
  rw [h]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  simp only [radKernel, Submodule.coe_smul, MvPolynomial.coeff_smul, Submodule.coe_sub,
    MvPolynomial.coeff_sub, smul_eq_mul]
  ring

end Kernel

/-! ## The vector -/

section Vector

variable {n : ℕ}

/-- The continuous real-linear unitary operator of the cuspidal representation. -/
def psPiCLM (σ : CuspidalRepresentation) (g : BinaryAdelicGL) : σ.H →L[ℝ] σ.H :=
  ((σ.π g).mkContinuous 1 (fun v => le_of_eq (by rw [σ.unitary, one_mul]))).restrictScalars ℝ

theorem psPiCLM_apply (σ : CuspidalRepresentation) (g : BinaryAdelicGL) (v : σ.H) :
    psPiCLM σ g v = σ.π g v := rfl

theorem smooth_clm_comp' {k : ℕ} {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] (T : E →L[ℝ] E') {F : (Fin k → RealGL3) → E}
    (hF : Smooth F) : Smooth (fun x => T (F x)) := by
  unfold Smooth at hF ⊢
  exact T.contDiff.comp_contDiffOn hF

/-- The unitary operator of the cuspidal representation, on smooth vectors. -/
def piSmooth (σ : CuspidalRepresentation) (b : BinaryAdelicGL) (v : σ.smooth) : σ.smooth :=
  ⟨σ.π b v.val, σ.smooth_stable b v.val v.property⟩

theorem realize_piSmooth (σ : CuspidalRepresentation) (b : BinaryAdelicGL) (v : σ.smooth)
    (A : BinaryAdelicGL) : σ.realize (piSmooth σ b v) A = σ.realize v (A * b) :=
  σ.equivariant b v A

/-- The smooth vector whose realization is the `μ`-coefficient of the plane source. -/
def sourceVec (D : InducingData n) (E : LeviCocycleData D.cusp n) (μ : Fin 3 →₀ ℕ) (c : ℂ)
    (b : BinaryAdelicGL) (y : Fin 3 → RealGL3) (w : RealGL3) : D.cusp.smooth :=
  ∑ ν ∈ binaryMonomials (n + 1), (radKernel D μ ν y w * c) •
    (piSmooth D.cusp b (E.lift ν (iwA (w * y 1))) - piSmooth D.cusp b (E.lift ν (iwA (w * y 0))))

theorem sourceVec_val (D : InducingData n) (E : LeviCocycleData D.cusp n) (μ : Fin 3 →₀ ℕ)
    (c : ℂ) (b : BinaryAdelicGL) (y : Fin 3 → RealGL3) (w : RealGL3) :
    (sourceVec D E μ c b y w).val =
      ∑ ν ∈ binaryMonomials (n + 1), (radKernel D μ ν y w * c) •
        (D.cusp.π b (E.lift ν (iwA (w * y 1))).val - D.cusp.π b (E.lift ν (iwA (w * y 0))).val) := by
  unfold sourceVec
  rw [Submodule.coe_sum]
  exact Finset.sum_congr rfl (fun ν _ => rfl)

theorem realize_sourceVec (D : InducingData n) (E : LeviCocycleData D.cusp n) (μ : Fin 3 →₀ ℕ)
    (c : ℂ) (b : BinaryAdelicGL) (y : Fin 3 → RealGL3) (w : RealGL3) (A : BinaryAdelicGL) :
    D.cusp.realize (sourceVec D E μ c b y w) A =
      ∑ ν ∈ binaryMonomials (n + 1), (radKernel D μ ν y w * c) *
        ((E.α (iwA (w * y 1)) (A * b)).val.coeff ν -
          (E.α (iwA (w * y 0)) (A * b)).val.coeff ν) := by
  unfold sourceVec
  rw [_root_.map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  rw [map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, realize_piSmooth,
    realize_piSmooth, E.lift_realize, E.lift_realize]

theorem coeff_planeSourceAt_eq_realize (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (μ : Fin 3 →₀ ℕ) (y : Fin 3 → RealGL3) (g : AdelicGL) (A : BinaryAdelicGL) :
    (planeSourceAt D E y g A).val.coeff μ =
      D.cusp.realize (sourceVec D E μ (cF D g) (bF g) y (realGroup g)) A := by
  rw [coeff_planeSourceAt, realize_sourceVec]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  ring

theorem sourceVec_smooth (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (hR : RadicalAnalytic n D.chi) (hC : CoefficientAnalytic D.chi) (μ : Fin 3 →₀ ℕ) (c : ℂ)
    (b : BinaryAdelicGL) {k : ℕ} {U : (Fin k → RealGL3) → Fin 3 → RealGL3}
    {W : (Fin k → RealGL3) → RealGL3} (hW : MatSmooth W) (hU : ∀ i, MatSmooth (fun x => U x i)) :
    Smooth (fun x => (sourceVec D E μ c b (U x) (W x)).val) := by
  have hv : ∀ (ν : Fin 2 →₀ ℕ) (i : Fin 3), Smooth (fun x : Fin k → RealGL3 =>
      D.cusp.π b (E.lift ν (iwA (W x * U x i))).val) := by
    intro ν i
    have hM : MatSmooth (fun x => iwA (W x * U x i)) :=
      matSmooth_block (matSmooth_iwasawaB (matSmooth_mul hW (hU i)))
        (fun x i' j' => iwA_val _ i' j')
    exact smooth_clm_comp' (psPiCLM D.cusp b)
      (smooth_comp_matSmooth (fun h : BinaryRealGL => (E.lift ν h).val) (E.lift_smooth ν) hM)
  refine smooth_congr (f := fun x => ∑ ν ∈ binaryMonomials (n + 1), (radKernel D μ ν (U x) (W x) * c) •
      (D.cusp.π b (E.lift ν (iwA (W x * U x 1))).val -
        D.cusp.π b (E.lift ν (iwA (W x * U x 0))).val))
    (smooth_finset_sum _ _ (fun ν _ => ?_)) (fun x => sourceVec_val D E μ c b (U x) (W x))
  exact smooth_smul_vec (smooth_mul_complex (radKernel_smooth D hR hC μ ν hW hU)
    (smooth_const_complex c)) (smooth_sub' (hv ν 1) (hv ν 0))

end Vector

end TernaryPeriodPolynomials.SourceConstruction
