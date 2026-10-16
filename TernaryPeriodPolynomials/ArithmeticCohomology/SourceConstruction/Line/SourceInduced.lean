module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.SourceVector

@[expose] public section


/-!
# The line source is a source cocycle

For a character `χ` trivial on the integral units, the analytic inputs `RadicalAnalyticLine` and
`CoefficientAnalytic`, and a sign-twisted analytic Levi cocycle `E`, the cochain `lineSource D E` is a
smooth homogeneous two-cocycle whose coefficients are normalized line-induced sections:
`IsSourceCocycle D .line (lineSource D E)`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise
open TernaryPeriodPolynomials.HeckeTranslate.SmoothClosure (smooth_finset_sum smooth_congr)

namespace TernaryPeriodPolynomials.SourceConstruction

section Induced

variable {n : ℕ}

theorem coeff_lineSourceAt_mul_atInfinity (D : InducingData n) (E : LineLeviCocycleData D.cusp n)
    (y : Fin 3 → RealGL3) (g : AdelicGL) (z : RealGL3) (A : BinaryAdelicGL) (μ : Fin 3 →₀ ℕ) :
    (lineSourceAt D E y (g * atInfinity z) A).val.coeff μ =
      ∑ ν ∈ binaryMonomials (n + 1), radKernelLine D μ ν y (realGroup g * z) *
        (cFLine D g * ((E.α (iwALine (realGroup g * z * y 1)) (A * bFLine g)).val.coeff ν -
          (E.α (iwALine (realGroup g * z * y 0)) (A * bFLine g)).val.coeff ν)) := by
  rw [coeff_lineSourceAt, realGroup_mul_atInfinity, cFLine_mul_atInfinity,
    bFLine_mul_atInfinity]

theorem lineCoeffFun_smooth (D : InducingData n) (E : LineLeviCocycleData D.cusp n)
    (hR : RadicalAnalyticLine n D.chi) (hC : CoefficientAnalytic D.chi) (μ : Fin 3 →₀ ℕ)
    (A : BinaryAdelicGL) (c : ℂ) {k : ℕ} {U : (Fin k → RealGL3) → Fin 3 → RealGL3}
    {W : (Fin k → RealGL3) → RealGL3} (hW : MatSmooth W) (hU : ∀ i, MatSmooth (fun x => U x i)) :
    Smooth (fun x : Fin k → RealGL3 => ∑ ν ∈ binaryMonomials (n + 1),
      radKernelLine D μ ν (U x) (W x) *
        (c * ((E.α (iwALine (W x * U x 1)) A).val.coeff ν -
          (E.α (iwALine (W x * U x 0)) A).val.coeff ν))) := by
  refine smooth_finset_sum _ _ (fun ν _ => ?_)
  have hs : ∀ i, Smooth (fun x : Fin k → RealGL3 => (E.α (iwALine (W x * U x i)) A).val.coeff ν) := by
    intro i
    exact smooth_comp_matSmooth (fun h : BinaryRealGL => (E.α h A).val.coeff ν)
      (E.scalar_smooth ν A)
      (matSmooth_blockLine (matSmooth_iwasawaB (matSmooth_mul hW (hU i)))
        (fun x i' j' => iwALine_val _ i' j'))
  exact smooth_mul_complex (radKernelLine_smooth D hR hC μ ν hW hU)
    (smooth_mul_complex (smooth_const_complex c) (smooth_sub' (hs 1) (hs 0)))

theorem hscLine_realize (D : InducingData n) (E : LineLeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (μ : Fin 3 →₀ ℕ) (y : Fin 3 → RealGL3) (a : AdelicGL) (z : RealGL3) (A : BinaryAdelicGL) :
    D.cusp.realize (sourceVecLine D E μ (cFLine D a) (bFLine a) y (realGroup a * z)) A =
      normPower (GeneralLinearGroup.det A) (-binaryInductionExponent n .line cohomologicalPoint) *
        (lineSource D E y (binaryLevi .line A * (a * atInfinity z))).val.coeff μ := by
  have e := coeff_lineSourceAt_eq_realize D E μ y (a * atInfinity z) A
  rw [cFLine_mul_atInfinity, bFLine_mul_atInfinity, realGroup_mul_atInfinity] at e
  rw [← e]
  show _ = normPower (GeneralLinearGroup.det A)
      (-binaryInductionExponent n .line cohomologicalPoint) *
    (lineSourceAt D E y (lineLevi 1 A * (a * atInfinity z)) 1).val.coeff μ
  rw [lineSourceAt_levi D E hχ A _ y 1, one_mul, Submodule.coe_smul, MvPolynomial.coeff_smul,
    smul_eq_mul, line_binaryExponent_eq, ← mul_assoc, normPower_neg_mul, one_mul]

/-- **The coefficients of the line source are normalized line-induced sections.** -/
theorem lineSource_isInduced (D : InducingData n) (E : LineLeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (hR : RadicalAnalyticLine n D.chi) (hC : CoefficientAnalytic D.chi) (y : Fin 3 → RealGL3)
    (μ : Fin 3 →₀ ℕ) :
    IsInduced D .line cohomologicalPoint (fun g => (lineSource D E y g).val.coeff μ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g
    refine smooth_congr
      (f := fun z : Fin 1 → RealGL3 => ∑ ν ∈ binaryMonomials (n + 1),
        radKernelLine D μ ν y (realGroup g * z 0) *
          (cFLine D g * ((E.α (iwALine (realGroup g * z 0 * y 1)) (1 * bFLine g)).val.coeff ν -
            (E.α (iwALine (realGroup g * z 0 * y 0)) (1 * bFLine g)).val.coeff ν)))
      (lineCoeffFun_smooth D E hR hC μ (1 * bFLine g) (cFLine D g) (U := fun _ => y)
        (W := fun z => realGroup g * z 0)
        (matSmooth_mul (matSmooth_const _) (matSmooth_coord 0)) (fun i => matSmooth_const (y i)))
      (fun z => ?_)
    exact coeff_lineSourceAt_mul_atInfinity D E y g (z 0) 1 μ
  · intro k g
    show (lineSourceAt D E y (g * atFinite k.val) 1).val.coeff μ =
      (lineSourceAt D E y g 1).val.coeff μ
    rw [lineSourceAt_level D E hχ g k y 1]
  · intro a
    refine ⟨fun x => sourceVecLine D E μ (cFLine D a) (bFLine a) y (realGroup a * x (Fin.last 0)),
      ?_, ?_⟩
    · exact sourceVecLine_smooth D E hR hC μ (cFLine D a) (bFLine a) (U := fun _ => y)
        (W := fun x => realGroup a * x (Fin.last 0))
        (matSmooth_mul (matSmooth_const _) (matSmooth_coord _)) (fun i => matSmooth_const (y i))
    · intro x A
      exact hscLine_realize D E hχ μ y a (x (Fin.last 0)) A
  · refine ⟨?_, ?_, ?_⟩
    · intro a b g
      show (lineSourceAt D E y (lineUnipotent a b * g) 1).val.coeff μ =
        (lineSourceAt D E y g 1).val.coeff μ
      rw [lineSourceAt_unipotent D E hχ a b g y 1]
    · intro t g
      show (lineSourceAt D E y (lineLevi t 1 * g) 1).val.coeff μ =
        D.chi.toMonoidHom t * normPower t (2 * inductionExponent .line cohomologicalPoint) *
          (lineSourceAt D E y g 1).val.coeff μ
      rw [lineSourceAt_torus D E hχ t g y 1, line_corner_exponent_eq, Submodule.coe_smul,
        MvPolynomial.coeff_smul, smul_eq_mul]
    · intro g
      unfold cuspFunctions
      refine LinearMap.mem_range.mpr ⟨sourceVecLine D E μ (cFLine D g) (bFLine g) y (realGroup g), ?_⟩
      funext A
      show D.cusp.realize (sourceVecLine D E μ (cFLine D g) (bFLine g) y (realGroup g)) A =
        normPower (GeneralLinearGroup.det A)
            (-(((n : ℂ) + 3) / 2 - inductionExponent .line cohomologicalPoint)) *
          (lineSourceAt D E y (lineLevi 1 A * g) 1).val.coeff μ
      rw [← coeff_lineSourceAt_eq_realize, lineSourceAt_levi D E hχ A g y 1, one_mul,
        Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul, line_exponent_eq,
        ← mul_assoc, normPower_neg_mul, one_mul]

/-- **The smooth cusp lift of the line source in all four real variables.** -/
theorem lineSource_hasSmoothCuspLift (D : InducingData n) (E : LineLeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (hR : RadicalAnalyticLine n D.chi) (hC : CoefficientAnalytic D.chi) (μ : Fin 3 →₀ ℕ) :
    HasSmoothCuspLift D .line cohomologicalPoint
      (fun x g => (lineSource D E x g).val.coeff μ) := by
  intro a
  refine ⟨fun x => sourceVecLine D E μ (cFLine D a) (bFLine a) (fun i => x (Fin.castSucc i))
    (realGroup a * x (Fin.last 3)), ?_, ?_⟩
  · exact sourceVecLine_smooth D E hR hC μ (cFLine D a) (bFLine a)
      (U := fun x i => x (Fin.castSucc i)) (W := fun x => realGroup a * x (Fin.last 3))
      (matSmooth_mul (matSmooth_const _) (matSmooth_coord _)) (fun i => matSmooth_coord _)
  · intro x A
    exact hscLine_realize D E hχ μ (fun i => x (Fin.castSucc i)) a (x (Fin.last 3)) A

/-- **Assembly: the line source is a source cocycle.** -/
theorem lineSource_isSourceCocycle_of_analytic (D : InducingData n)
    (E : LineLeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (hR : RadicalAnalyticLine n D.chi) (hC : CoefficientAnalytic D.chi) :
    IsSourceCocycle D .line (lineSource D E) := by
  refine ⟨fun y μ => lineSource_isInduced D E hχ hR hC y μ,
    fun μ => lineSource_hasSmoothCuspLift D E hχ hR hC μ, ?_, ?_⟩
  · intro h y g
    exact lineSourceAt_equivariant D E h y g 1
  · intro x g
    exact lineSourceAt_cocycle D E x g 1

end Induced

end TernaryPeriodPolynomials.SourceConstruction

end
