module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceVector

@[expose] public section


/-!
# The plane source is a source cocycle

For a character `χ` trivial on the integral units, the analytic inputs `RadicalAnalytic` and
`CoefficientAnalytic`, and an `O(2)`-normalized analytic Levi cocycle `E`, the cochain
`planeSource D E` is a smooth homogeneous two-cocycle whose coefficients are normalized
plane-induced sections: `IsSourceCocycle D .plane (planeSource D E)`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise
open TernaryPeriodPolynomials.HeckeTranslate.SmoothClosure (smooth_finset_sum smooth_congr)

namespace TernaryPeriodPolynomials.SourceConstruction

section Exponents

theorem ind_exp_plane : inductionExponent .plane cohomologicalPoint = 0 := by
  unfold inductionExponent cohomologicalPoint
  ring

theorem plane_binExp (n : ℕ) :
    binaryInductionExponent n .plane cohomologicalPoint = ((n : ℂ) + 3) / 2 := by
  unfold binaryInductionExponent
  rw [ind_exp_plane, add_zero]

theorem ps_normPower_neg_mul (t : Adelesˣ) (z : ℂ) : normPower t (-z) * normPower t z = 1 := by
  unfold normPower
  rw [← Complex.exp_add]
  simp

end Exponents

section Induced

variable {n : ℕ}

theorem cF_mul_atInfinity (D : InducingData n) (g : AdelicGL) (z : RealGL3) :
    cF D (g * atInfinity z) = cF D g := by
  unfold cF
  rw [finiteGroup_mul_atInfinity]

theorem bF_mul_atInfinity (g : AdelicGL) (z : RealGL3) : bF (g * atInfinity z) = bF g := by
  unfold bF
  rw [finiteGroup_mul_atInfinity]

theorem coeff_planeSourceAt_mul_atInfinity (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (y : Fin 3 → RealGL3) (g : AdelicGL) (z : RealGL3) (A : BinaryAdelicGL) (μ : Fin 3 →₀ ℕ) :
    (planeSourceAt D E y (g * atInfinity z) A).val.coeff μ =
      ∑ ν ∈ binaryMonomials (n + 1), radKernel D μ ν y (realGroup g * z) *
        (cF D g * ((E.α (iwA (realGroup g * z * y 1)) (A * bF g)).val.coeff ν -
          (E.α (iwA (realGroup g * z * y 0)) (A * bF g)).val.coeff ν)) := by
  rw [coeff_planeSourceAt, realGroup_mul_atInfinity, cF_mul_atInfinity, bF_mul_atInfinity]

theorem planeCoeffFun_smooth (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (hR : RadicalAnalytic n D.chi) (hC : CoefficientAnalytic D.chi) (μ : Fin 3 →₀ ℕ)
    (A : BinaryAdelicGL) (c : ℂ) {k : ℕ} {U : (Fin k → RealGL3) → Fin 3 → RealGL3}
    {W : (Fin k → RealGL3) → RealGL3} (hW : MatSmooth W) (hU : ∀ i, MatSmooth (fun x => U x i)) :
    Smooth (fun x : Fin k → RealGL3 => ∑ ν ∈ binaryMonomials (n + 1),
      radKernel D μ ν (U x) (W x) *
        (c * ((E.α (iwA (W x * U x 1)) A).val.coeff ν - (E.α (iwA (W x * U x 0)) A).val.coeff ν))) := by
  refine smooth_finset_sum _ _ (fun ν _ => ?_)
  have hs : ∀ i, Smooth (fun x : Fin k → RealGL3 => (E.α (iwA (W x * U x i)) A).val.coeff ν) := by
    intro i
    exact smooth_comp_matSmooth (fun h : BinaryRealGL => (E.α h A).val.coeff ν)
      (E.scalar_smooth ν A)
      (matSmooth_block (matSmooth_iwasawaB (matSmooth_mul hW (hU i)))
        (fun x i' j' => iwA_val _ i' j'))
  exact smooth_mul_complex (radKernel_smooth D hR hC μ ν hW hU)
    (smooth_mul_complex (smooth_const_complex c) (smooth_sub' (hs 1) (hs 0)))

theorem hsc_realize (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (μ : Fin 3 →₀ ℕ) (y : Fin 3 → RealGL3) (a : AdelicGL) (z : RealGL3) (A : BinaryAdelicGL) :
    D.cusp.realize (sourceVec D E μ (cF D a) (bF a) y (realGroup a * z)) A =
      normPower (GeneralLinearGroup.det A) (-binaryInductionExponent n .plane cohomologicalPoint) *
        (planeSource D E y (binaryLevi .plane A * (a * atInfinity z))).val.coeff μ := by
  have e := coeff_planeSourceAt_eq_realize D E μ y (a * atInfinity z) A
  rw [cF_mul_atInfinity, bF_mul_atInfinity, realGroup_mul_atInfinity] at e
  rw [← e]
  show _ = normPower (GeneralLinearGroup.det A) (-binaryInductionExponent n .plane cohomologicalPoint) *
    (planeSourceAt D E y (planeLevi A 1 * (a * atInfinity z)) 1).val.coeff μ
  rw [planeSourceAt_levi D E hχ A _ y 1, one_mul, Submodule.coe_smul, MvPolynomial.coeff_smul,
    smul_eq_mul, plane_binExp, ← mul_assoc, ps_normPower_neg_mul, one_mul]

/-- **The coefficients of the plane source are normalized plane-induced sections.** -/
theorem planeSource_isInduced (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (hR : RadicalAnalytic n D.chi) (hC : CoefficientAnalytic D.chi) (y : Fin 3 → RealGL3)
    (μ : Fin 3 →₀ ℕ) :
    IsInduced D .plane cohomologicalPoint (fun g => (planeSource D E y g).val.coeff μ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g
    refine smooth_congr
      (f := fun z : Fin 1 → RealGL3 => ∑ ν ∈ binaryMonomials (n + 1),
        radKernel D μ ν y (realGroup g * z 0) *
          (cF D g * ((E.α (iwA (realGroup g * z 0 * y 1)) (1 * bF g)).val.coeff ν -
            (E.α (iwA (realGroup g * z 0 * y 0)) (1 * bF g)).val.coeff ν)))
      (planeCoeffFun_smooth D E hR hC μ (1 * bF g) (cF D g) (U := fun _ => y)
        (W := fun z => realGroup g * z 0)
        (matSmooth_mul (matSmooth_const _) (matSmooth_coord 0)) (fun i => matSmooth_const (y i)))
      (fun z => ?_)
    exact coeff_planeSourceAt_mul_atInfinity D E y g (z 0) 1 μ
  · intro k g
    show (planeSourceAt D E y (g * atFinite k.val) 1).val.coeff μ =
      (planeSourceAt D E y g 1).val.coeff μ
    rw [planeSourceAt_level D E hχ g k y 1]
  · intro a
    refine ⟨fun x => sourceVec D E μ (cF D a) (bF a) y (realGroup a * x (Fin.last 0)), ?_, ?_⟩
    · exact sourceVec_smooth D E hR hC μ (cF D a) (bF a) (U := fun _ => y)
        (W := fun x => realGroup a * x (Fin.last 0))
        (matSmooth_mul (matSmooth_const _) (matSmooth_coord _)) (fun i => matSmooth_const (y i))
    · intro x A
      exact hsc_realize D E hχ μ y a (x (Fin.last 0)) A
  · refine ⟨?_, ?_, ?_⟩
    · intro a b g
      show (planeSourceAt D E y (planeUnipotent a b * g) 1).val.coeff μ =
        (planeSourceAt D E y g 1).val.coeff μ
      rw [planeSourceAt_unipotent D E hχ a b g y 1]
    · intro t g
      show (planeSourceAt D E y (planeLevi 1 t * g) 1).val.coeff μ =
        D.chi.toMonoidHom t * normPower t (-2 * inductionExponent .plane cohomologicalPoint) *
          (planeSourceAt D E y g 1).val.coeff μ
      rw [planeSourceAt_torus D E hχ t g y 1, ind_exp_plane, mul_zero, ps_normPower_zero, mul_one,
        Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]
    · intro g
      unfold cuspFunctions
      refine LinearMap.mem_range.mpr ⟨sourceVec D E μ (cF D g) (bF g) y (realGroup g), ?_⟩
      funext A
      show D.cusp.realize (sourceVec D E μ (cF D g) (bF g) y (realGroup g)) A =
        normPower (GeneralLinearGroup.det A)
            (-(((n : ℂ) + 3) / 2 + inductionExponent .plane cohomologicalPoint)) *
          (planeSourceAt D E y (planeLevi A 1 * g) 1).val.coeff μ
      rw [← coeff_planeSourceAt_eq_realize, planeSourceAt_levi D E hχ A g y 1, one_mul,
        Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul, ind_exp_plane, add_zero,
        ← mul_assoc, ps_normPower_neg_mul, one_mul]

/-- **The smooth cusp lift of the plane source in all four real variables.** -/
theorem planeSource_hasSmoothCuspLift (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (hR : RadicalAnalytic n D.chi) (hC : CoefficientAnalytic D.chi) (μ : Fin 3 →₀ ℕ) :
    HasSmoothCuspLift D .plane cohomologicalPoint
      (fun x g => (planeSource D E x g).val.coeff μ) := by
  intro a
  refine ⟨fun x => sourceVec D E μ (cF D a) (bF a) (fun i => x (Fin.castSucc i))
    (realGroup a * x (Fin.last 3)), ?_, ?_⟩
  · exact sourceVec_smooth D E hR hC μ (cF D a) (bF a)
      (U := fun x i => x (Fin.castSucc i)) (W := fun x => realGroup a * x (Fin.last 3))
      (matSmooth_mul (matSmooth_const _) (matSmooth_coord _)) (fun i => matSmooth_coord _)
  · intro x A
    exact hsc_realize D E hχ μ (fun i => x (Fin.castSucc i)) a (x (Fin.last 3)) A

/-- **Assembly: the plane source is a source cocycle.** -/
theorem planeSource_isSourceCocycle_of_analytic (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (hR : RadicalAnalytic n D.chi) (hC : CoefficientAnalytic D.chi) :
    IsSourceCocycle D .plane (planeSource D E) := by
  refine ⟨fun y μ => planeSource_isInduced D E hχ hR hC y μ,
    fun μ => planeSource_hasSmoothCuspLift D E hχ hR hC μ, ?_, ?_⟩
  · intro h y g
    exact planeSourceAt_equivariant D E h y g 1
  · intro x g
    exact planeSourceAt_cocycle D E x g 1

end Induced

end TernaryPeriodPolynomials.SourceConstruction
