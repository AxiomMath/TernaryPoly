module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.GoodPlaneSourceAlgebra

@[expose] public section


/-!
# The good-plane source is a source cocycle

For a character `χ` trivial on the integral units and a level-three Levi cocycle `E`, the cochain
`goodPlaneSource D E` is a smooth homogeneous two-cocycle whose coefficients are normalized
plane-induced sections: `IsSourceCocycle D .plane (goodPlaneSource D E)`.

Every coefficient of the good-plane source is a finite combination of coefficients of the Levi
cocycle with the real analytic kernels `radKernel` (SC), hence the realization of an explicit vector
`goodSourceVec` of smooth vectors depending smoothly on the real arguments; this ports SC's
`PlaneSourceVector` and `PlaneSourceInduced` with the finite part `gpsF`, `gpsB`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.HeckeTranslate.SmoothClosure (smooth_finset_sum smooth_congr)

namespace TernaryPeriodPolynomials.LevelThreeSource

/-! ## The vector -/

section Vector

variable {n : ℕ}

/-- **The coefficients of the good-plane source.** -/
theorem coeff_goodPlaneSourceAt (D : InducingData n) (E : LevelLeviCocycleData D.cusp n)
    (y : Fin 3 → RealGL3) (g : AdelicGL) (x : BinaryAdelicGL) (μ : Fin 3 →₀ ℕ) :
    (goodPlaneSourceAt D E y g x).val.coeff μ =
      ∑ ν ∈ binaryMonomials (n + 1), radKernel D μ ν y (realGroup g) *
        (gpsF D g * ((E.α (iwA (realGroup g * y 1)) (x * gpsB g)).val.coeff ν -
          (E.α (iwA (realGroup g * y 0)) (x * gpsB g)).val.coeff ν)) := by
  have h := binary_coeff_apply_eq_sum
    ((realCoefficientComponent n D.chi (realGroup g)⁻¹).comp
      (planeRadical n D.chi (iwP (realGroup g * y 2)) -
        planeRadical n D.chi (iwP (realGroup g * y 1))))
    (gpsF D g • (E.α (iwA (realGroup g * y 1)) (x * gpsB g) -
      E.α (iwA (realGroup g * y 0)) (x * gpsB g))) μ
  simp only [LinearMap.comp_apply] at h
  unfold goodPlaneSourceAt
  rw [h]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  simp only [radKernel, Submodule.coe_smul, MvPolynomial.coeff_smul, Submodule.coe_sub,
    MvPolynomial.coeff_sub, smul_eq_mul]
  ring

/-- The smooth vector whose realization is the `μ`-coefficient of the good-plane source. -/
def goodSourceVec (D : InducingData n) (E : LevelLeviCocycleData D.cusp n) (μ : Fin 3 →₀ ℕ)
    (c : ℂ) (b : BinaryAdelicGL) (y : Fin 3 → RealGL3) (w : RealGL3) : D.cusp.smooth :=
  ∑ ν ∈ binaryMonomials (n + 1), (radKernel D μ ν y w * c) •
    (piSmooth D.cusp b (E.lift ν (iwA (w * y 1))) - piSmooth D.cusp b (E.lift ν (iwA (w * y 0))))

theorem goodSourceVec_val (D : InducingData n) (E : LevelLeviCocycleData D.cusp n)
    (μ : Fin 3 →₀ ℕ) (c : ℂ) (b : BinaryAdelicGL) (y : Fin 3 → RealGL3) (w : RealGL3) :
    (goodSourceVec D E μ c b y w).val =
      ∑ ν ∈ binaryMonomials (n + 1), (radKernel D μ ν y w * c) •
        (D.cusp.π b (E.lift ν (iwA (w * y 1))).val -
          D.cusp.π b (E.lift ν (iwA (w * y 0))).val) := by
  unfold goodSourceVec
  rw [Submodule.coe_sum]
  exact Finset.sum_congr rfl (fun ν _ => rfl)

theorem realize_goodSourceVec (D : InducingData n) (E : LevelLeviCocycleData D.cusp n)
    (μ : Fin 3 →₀ ℕ) (c : ℂ) (b : BinaryAdelicGL) (y : Fin 3 → RealGL3) (w : RealGL3)
    (A : BinaryAdelicGL) :
    D.cusp.realize (goodSourceVec D E μ c b y w) A =
      ∑ ν ∈ binaryMonomials (n + 1), (radKernel D μ ν y w * c) *
        ((E.α (iwA (w * y 1)) (A * b)).val.coeff ν -
          (E.α (iwA (w * y 0)) (A * b)).val.coeff ν) := by
  unfold goodSourceVec
  rw [_root_.map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  rw [map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, realize_piSmooth,
    realize_piSmooth, E.lift_realize, E.lift_realize]

theorem coeff_goodPlaneSourceAt_eq_realize (D : InducingData n)
    (E : LevelLeviCocycleData D.cusp n) (μ : Fin 3 →₀ ℕ) (y : Fin 3 → RealGL3) (g : AdelicGL)
    (A : BinaryAdelicGL) :
    (goodPlaneSourceAt D E y g A).val.coeff μ =
      D.cusp.realize (goodSourceVec D E μ (gpsF D g) (gpsB g) y (realGroup g)) A := by
  rw [coeff_goodPlaneSourceAt, realize_goodSourceVec]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  ring

theorem goodSourceVec_smooth (D : InducingData n) (E : LevelLeviCocycleData D.cusp n)
    (hR : RadicalAnalytic n D.chi) (hC : CoefficientAnalytic D.chi) (μ : Fin 3 →₀ ℕ) (c : ℂ)
    (b : BinaryAdelicGL) {k : ℕ} {U : (Fin k → RealGL3) → Fin 3 → RealGL3}
    {W : (Fin k → RealGL3) → RealGL3} (hW : MatSmooth W) (hU : ∀ i, MatSmooth (fun x => U x i)) :
    Smooth (fun x => (goodSourceVec D E μ c b (U x) (W x)).val) := by
  have hv : ∀ (ν : Fin 2 →₀ ℕ) (i : Fin 3), Smooth (fun x : Fin k → RealGL3 =>
      D.cusp.π b (E.lift ν (iwA (W x * U x i))).val) := by
    intro ν i
    have hM : MatSmooth (fun x => iwA (W x * U x i)) :=
      matSmooth_block (matSmooth_iwasawaB (matSmooth_mul hW (hU i)))
        (fun x i' j' => iwA_val _ i' j')
    exact smooth_clm_comp' (psPiCLM D.cusp b)
      (smooth_comp_matSmooth (fun h : BinaryRealGL => (E.lift ν h).val) (E.lift_smooth ν) hM)
  refine smooth_congr
    (f := fun x => ∑ ν ∈ binaryMonomials (n + 1), (radKernel D μ ν (U x) (W x) * c) •
      (D.cusp.π b (E.lift ν (iwA (W x * U x 1))).val -
        D.cusp.π b (E.lift ν (iwA (W x * U x 0))).val))
    (smooth_finset_sum _ _ (fun ν _ => ?_)) (fun x => goodSourceVec_val D E μ c b (U x) (W x))
  exact smooth_smul_vec (smooth_mul_complex (radKernel_smooth D hR hC μ ν hW hU)
    (smooth_const_complex c)) (smooth_sub' (hv ν 1) (hv ν 0))

end Vector

/-! ## The induced-section property -/

section Induced

variable {n : ℕ}

theorem coeff_goodPlaneSourceAt_mul_atInfinity (D : InducingData n)
    (E : LevelLeviCocycleData D.cusp n) (y : Fin 3 → RealGL3) (g : AdelicGL) (z : RealGL3)
    (A : BinaryAdelicGL) (μ : Fin 3 →₀ ℕ) :
    (goodPlaneSourceAt D E y (g * atInfinity z) A).val.coeff μ =
      ∑ ν ∈ binaryMonomials (n + 1), radKernel D μ ν y (realGroup g * z) *
        (gpsF D g * ((E.α (iwA (realGroup g * z * y 1)) (A * gpsB g)).val.coeff ν -
          (E.α (iwA (realGroup g * z * y 0)) (A * gpsB g)).val.coeff ν)) := by
  rw [coeff_goodPlaneSourceAt, realGroup_mul_atInfinity, gpsF_mul_atInfinity, gpsB_mul_atInfinity]

theorem goodPlaneCoeffFun_smooth (D : InducingData n) (E : LevelLeviCocycleData D.cusp n)
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

theorem gp_hsc_realize (D : InducingData n) (E : LevelLeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (μ : Fin 3 →₀ ℕ) (y : Fin 3 → RealGL3) (a : AdelicGL) (z : RealGL3) (A : BinaryAdelicGL) :
    D.cusp.realize (goodSourceVec D E μ (gpsF D a) (gpsB a) y (realGroup a * z)) A =
      normPower (GeneralLinearGroup.det A)
          (-binaryInductionExponent n .plane cohomologicalPoint) *
        (goodPlaneSource D E y (binaryLevi .plane A * (a * atInfinity z))).val.coeff μ := by
  have e := coeff_goodPlaneSourceAt_eq_realize D E μ y (a * atInfinity z) A
  rw [gpsF_mul_atInfinity, gpsB_mul_atInfinity, realGroup_mul_atInfinity] at e
  rw [← e]
  show _ = normPower (GeneralLinearGroup.det A)
      (-binaryInductionExponent n .plane cohomologicalPoint) *
    (goodPlaneSourceAt D E y (planeLevi A 1 * (a * atInfinity z)) 1).val.coeff μ
  rw [goodPlaneSourceAt_levi D E hχ A _ y 1, one_mul, Submodule.coe_smul, MvPolynomial.coeff_smul,
    smul_eq_mul, plane_binExp, ← mul_assoc, ps_normPower_neg_mul, one_mul]

/-- **The coefficients of the good-plane source are normalized plane-induced sections.** -/
theorem goodPlaneSource_isInduced (D : InducingData n) (E : LevelLeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (hR : RadicalAnalytic n D.chi) (hC : CoefficientAnalytic D.chi) (y : Fin 3 → RealGL3)
    (μ : Fin 3 →₀ ℕ) :
    IsInduced D .plane cohomologicalPoint (fun g => (goodPlaneSource D E y g).val.coeff μ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g
    refine smooth_congr
      (f := fun z : Fin 1 → RealGL3 => ∑ ν ∈ binaryMonomials (n + 1),
        radKernel D μ ν y (realGroup g * z 0) *
          (gpsF D g * ((E.α (iwA (realGroup g * z 0 * y 1)) (1 * gpsB g)).val.coeff ν -
            (E.α (iwA (realGroup g * z 0 * y 0)) (1 * gpsB g)).val.coeff ν)))
      (goodPlaneCoeffFun_smooth D E hR hC μ (1 * gpsB g) (gpsF D g) (U := fun _ => y)
        (W := fun z => realGroup g * z 0)
        (matSmooth_mul (matSmooth_const _) (matSmooth_coord 0)) (fun i => matSmooth_const (y i)))
      (fun z => ?_)
    exact coeff_goodPlaneSourceAt_mul_atInfinity D E y g (z 0) 1 μ
  · intro k g
    show (goodPlaneSourceAt D E y (g * atFinite k.val) 1).val.coeff μ =
      (goodPlaneSourceAt D E y g 1).val.coeff μ
    rw [goodPlaneSourceAt_level D E hχ g k y 1]
  · intro a
    refine ⟨fun x => goodSourceVec D E μ (gpsF D a) (gpsB a) y
      (realGroup a * x (Fin.last 0)), ?_, ?_⟩
    · exact goodSourceVec_smooth D E hR hC μ (gpsF D a) (gpsB a) (U := fun _ => y)
        (W := fun x => realGroup a * x (Fin.last 0))
        (matSmooth_mul (matSmooth_const _) (matSmooth_coord _)) (fun i => matSmooth_const (y i))
    · intro x A
      exact gp_hsc_realize D E hχ μ y a (x (Fin.last 0)) A
  · refine ⟨?_, ?_, ?_⟩
    · intro a b g
      show (goodPlaneSourceAt D E y (planeUnipotent a b * g) 1).val.coeff μ =
        (goodPlaneSourceAt D E y g 1).val.coeff μ
      rw [goodPlaneSourceAt_unipotent D E hχ a b g y 1]
    · intro t g
      show (goodPlaneSourceAt D E y (planeLevi 1 t * g) 1).val.coeff μ =
        D.chi.toMonoidHom t * normPower t (-2 * inductionExponent .plane cohomologicalPoint) *
          (goodPlaneSourceAt D E y g 1).val.coeff μ
      rw [goodPlaneSourceAt_torus D E hχ t g y 1, ind_exp_plane, mul_zero, ps_normPower_zero,
        mul_one, Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]
    · intro g
      unfold cuspFunctions
      refine LinearMap.mem_range.mpr ⟨goodSourceVec D E μ (gpsF D g) (gpsB g) y (realGroup g), ?_⟩
      funext A
      show D.cusp.realize (goodSourceVec D E μ (gpsF D g) (gpsB g) y (realGroup g)) A =
        normPower (GeneralLinearGroup.det A)
            (-(((n : ℂ) + 3) / 2 + inductionExponent .plane cohomologicalPoint)) *
          (goodPlaneSourceAt D E y (planeLevi A 1 * g) 1).val.coeff μ
      rw [← coeff_goodPlaneSourceAt_eq_realize, goodPlaneSourceAt_levi D E hχ A g y 1, one_mul,
        Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul, ind_exp_plane, add_zero,
        ← mul_assoc, ps_normPower_neg_mul, one_mul]

/-- **The smooth cusp lift of the good-plane source in all four real variables.** -/
theorem goodPlaneSource_hasSmoothCuspLift (D : InducingData n)
    (E : LevelLeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (hR : RadicalAnalytic n D.chi) (hC : CoefficientAnalytic D.chi) (μ : Fin 3 →₀ ℕ) :
    HasSmoothCuspLift D .plane cohomologicalPoint
      (fun x g => (goodPlaneSource D E x g).val.coeff μ) := by
  intro a
  refine ⟨fun x => goodSourceVec D E μ (gpsF D a) (gpsB a) (fun i => x (Fin.castSucc i))
    (realGroup a * x (Fin.last 3)), ?_, ?_⟩
  · exact goodSourceVec_smooth D E hR hC μ (gpsF D a) (gpsB a)
      (U := fun x i => x (Fin.castSucc i)) (W := fun x => realGroup a * x (Fin.last 3))
      (matSmooth_mul (matSmooth_const _) (matSmooth_coord _)) (fun i => matSmooth_coord _)
  · intro x A
    exact gp_hsc_realize D E hχ μ (fun i => x (Fin.castSucc i)) a (x (Fin.last 3)) A

/-- **Assembly: the good-plane source is a source cocycle** (given the two analytic inputs, which
SC discharges in `radicalAnalytic` and `coefficientAnalytic`). -/
theorem goodPlaneSource_isSourceCocycle_of_analytic (D : InducingData n)
    (E : LevelLeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (hR : RadicalAnalytic n D.chi) (hC : CoefficientAnalytic D.chi) :
    IsSourceCocycle D .plane (goodPlaneSource D E) := by
  refine ⟨fun y μ => goodPlaneSource_isInduced D E hχ hR hC y μ,
    fun μ => goodPlaneSource_hasSmoothCuspLift D E hχ hR hC μ, ?_, ?_⟩
  · intro h y g
    exact goodPlaneSourceAt_equivariant D E h y g 1
  · intro x g
    exact goodPlaneSourceAt_cocycle D E x g 1

/-- **The good-plane source cocycle.** For `χ` trivial on the integral units and a level-three
Levi cocycle `E`, `goodPlaneSource D E` is a smooth homogeneous two-cocycle with plane-induced
coefficients. -/
theorem goodPlaneSource_isSourceCocycle (D : InducingData n)
    (E : LevelLeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1) :
    IsSourceCocycle D .plane (goodPlaneSource D E) :=
  goodPlaneSource_isSourceCocycle_of_analytic D E hχ (radicalAnalytic n D.chi)
    (coefficientAnalytic D.chi hχ)

/-- The same for the trivial character. -/
theorem goodPlaneSource_isSourceCocycle_of_trivial (D : InducingData n)
    (E : LevelLeviCocycleData D.cusp n) (hchi : D.chi = trivialCharacter) :
    IsSourceCocycle D .plane (goodPlaneSource D E) :=
  goodPlaneSource_isSourceCocycle D E (fun u => by rw [hchi]; rfl)

end Induced

end TernaryPeriodPolynomials.LevelThreeSource
