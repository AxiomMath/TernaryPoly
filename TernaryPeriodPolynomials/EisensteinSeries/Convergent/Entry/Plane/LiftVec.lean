module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Plane.LiftAnalytic
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.CochainEntry
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.JvecLift
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceVector

@[expose] public section


/-!
# The smooth vector of the plane integral cochain

`planeHol_stokes`: the holomorphic half of the plane integral cochain (`planeIntG` of `planeHolData`) is
`-(c_F/2)·Bare(F(x b_F))` (Stokes, `Entry/PlaneStokes`).  `OmegaVec`: the smooth vector `-(c/2)(B(M) + π(J_∞) B(εM))`
whose realization at `β` is the coefficient `κ` of the plane integral cochain at the frame `M = g_∞` (holomorphic half at
`M` plus reflected half at `εM`), built from the smooth lifts `JS` of the boundary integrals (`exists_JvecLift`).

Formalized by Claude Sonnet 5.5.
-/

open scoped Matrix.Norms.Elementwise
open MeasureTheory Set MvPolynomial Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

theorem Jpl_eq_JgenInt (n : ℕ) (c : ℂ) (G' : ℂ → ℂ) (μ : Fin 3 →₀ ℕ) (x y : Mat3) :
    Jpl n (fun z => c * G' z) μ x y = c * JgenInt G' n μ x y := by
  unfold Jpl JgenInt
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  simp only [smul_eq_mul]
  ring

/-- **The holomorphic half of the plane integral cochain as boundary integrals.** -/
theorem planeHol_stokes {n : ℕ} (D : InducingData n) (F : BinaryAdelicGL → ℂ → ℂ)
    (hol : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im}) (g : AdelicGL) (x : BinaryAdelicGL)
    (M Γ₀ Γ₁ Γ₂ : Mat3) (hM : M.det ≠ 0) (p₀ : Γ₀.PosDef) (p₁ : Γ₁.PosDef) (p₂ : Γ₂.PosDef)
    (κ : Fin 3 →₀ ℕ) :
    planeIntG n (planeHolData n D F g x) M Γ₀ Γ₁ Γ₂ κ =
      -(cF D g * 2⁻¹) * Bare (G := ℂ) (F (x * bF g)) n κ M Γ₀ Γ₁ Γ₂ := by
  have hcont : ContinuousOn (fun z : ℂ => cF D g * 2⁻¹ * F (x * bF g) z) {z : ℂ | 0 < z.im} :=
    continuousOn_const.mul (hol _).continuousOn
  have h := planeIntG_stokes (eichlerDatum n F hol (x * bF g) (cF D g)) hcont M Γ₀ Γ₁ Γ₂ hM p₀ p₁ p₂ κ
  have e : planeHolData n D F g x = fun z => (-1) ^ n * ((n + 1 : ℕ) : ℂ) * (cF D g * 2⁻¹ * F (x * bF g) z) := rfl
  rw [e, h]
  unfold Bare
  simp only [Jpl_eq_JgenInt, smul_eq_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  ring


/-- The plane integral cochain at a general binary adele `x` (the coefficient `κ`). -/
def cOmegaCoeffAt (n : ℕ) (D : InducingData n) (F : BinaryAdelicGL → ℂ → ℂ) (y : Fin 3 → RealGL3)
    (g : AdelicGL) (x : BinaryAdelicGL) (κ : Fin 3 →₀ ℕ) : ℂ :=
  planeIntG n (planeHolData n D F g x) (realGroup g).val (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) κ +
  planeIntG n (planeHolData n D F g (x * atInfinity UpperHalfPlane.J)) (epsJ.val * (realGroup g).val)
    (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) κ

theorem cOmegaCoeffAt_one (n : ℕ) (D : InducingData n) (F : BinaryAdelicGL → ℂ → ℂ) (y : Fin 3 → RealGL3)
    (g : AdelicGL) (κ : Fin 3 →₀ ℕ) : cOmegaCoeffAt n D F y g 1 κ = cOmegaCoeff n D F y g κ := by
  unfold cOmegaCoeffAt cOmegaCoeff
  rw [one_mul]

section Vec

variable (σ : CuspidalRepresentation) (stages : AnalyticScalar.ContinuousStages σ) (hw : ℤ)
  (v : σ.smooth) (fixed : v.val ∈ BinaryLevel.fixedSubspace σ BinaryLevel.finiteCongruence)

/-- The smooth lift of a boundary integral (chosen). -/
def JS (n : ℕ) (ν : Fin 3 →₀ ℕ) (Γa Γb : Mat3) (ha : Γa.PosDef) (hb : Γb.PosDef) : σ.smooth :=
  (exists_JvecLift σ stages hw v fixed n ν ha hb).choose

theorem JS_val (n : ℕ) (ν : Fin 3 →₀ ℕ) (Γa Γb : Mat3) (ha : Γa.PosDef) (hb : Γb.PosDef) :
    (JS σ stages hw v fixed n ν Γa Γb ha hb).val = JgenInt (cuspWeightedAffineOrbit σ hw v.val) n ν Γa Γb :=
  (exists_JvecLift σ stages hw v fixed n ν ha hb).choose_spec.1

theorem JS_realize (n : ℕ) (ν : Fin 3 →₀ ℕ) (Γa Γb : Mat3) (ha : Γa.PosDef) (hb : Γb.PosDef)
    (β : BinaryAdelicGL) :
    σ.realize (JS σ stages hw v fixed n ν Γa Γb ha hb) β =
      JgenInt (cuspScalarWeightedRealization σ hw v β) n ν Γa Γb :=
  (exists_JvecLift σ stages hw v fixed n ν ha hb).choose_spec.2 β

/-- The smooth vector whose realization is the boundary combination `Bare`. -/
def BareS (n : ℕ) (m : Fin 3 →₀ ℕ) (M Γ₀ Γ₁ Γ₂ : Mat3) (hM : M.det ≠ 0) (p₀ : Γ₀.PosDef)
    (p₁ : Γ₁.PosDef) (p₂ : Γ₂.PosDef) : σ.smooth :=
  ∑ ν ∈ degSet n, (SeedC3.rho M⁻¹ (MvPolynomial.monomial ν 1)).coeff m •
    (JS σ stages hw v fixed n ν _ _ (posDef_congr p₁ hM) (posDef_congr p₂ hM) -
      JS σ stages hw v fixed n ν _ _ (posDef_congr p₀ hM) (posDef_congr p₂ hM) +
      JS σ stages hw v fixed n ν _ _ (posDef_congr p₀ hM) (posDef_congr p₁ hM))

theorem BareS_val (n : ℕ) (m : Fin 3 →₀ ℕ) (M Γ₀ Γ₁ Γ₂ : Mat3) (hM : M.det ≠ 0) (p₀ : Γ₀.PosDef)
    (p₁ : Γ₁.PosDef) (p₂ : Γ₂.PosDef) :
    (BareS σ stages hw v fixed n m M Γ₀ Γ₁ Γ₂ hM p₀ p₁ p₂).val =
      Bare (cuspWeightedAffineOrbit σ hw v.val) n m M Γ₀ Γ₁ Γ₂ := by
  unfold BareS Bare
  rw [Submodule.coe_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Submodule.coe_smul, Submodule.coe_add, Submodule.coe_sub, JS_val, JS_val, JS_val]

theorem BareS_realize (n : ℕ) (m : Fin 3 →₀ ℕ) (M Γ₀ Γ₁ Γ₂ : Mat3) (hM : M.det ≠ 0) (p₀ : Γ₀.PosDef)
    (p₁ : Γ₁.PosDef) (p₂ : Γ₂.PosDef) (β : BinaryAdelicGL) :
    σ.realize (BareS σ stages hw v fixed n m M Γ₀ Γ₁ Γ₂ hM p₀ p₁ p₂) β =
      Bare (G := ℂ) (cuspScalarWeightedRealization σ hw v β) n m M Γ₀ Γ₁ Γ₂ := by
  unfold BareS Bare
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [map_smul, map_add, map_sub]
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul, JS_realize]


theorem det_epsJ_mul_ne_zero {M : Mat3} (hM : M.det ≠ 0) : (epsJ.val * M).det ≠ 0 := by
  rw [Matrix.det_mul]
  exact mul_ne_zero (det_ne_zero_realGL3 epsJ) hM

/-- **The smooth vector of the plane integral cochain** (coefficient `m`, finite scalar `c`): the holomorphic half at
`M` plus the reflected half (`π(J_∞)`-translate) at `ε M`. -/
def OmegaVec (n : ℕ) (m : Fin 3 →₀ ℕ) (c : ℂ) (M Γ₀ Γ₁ Γ₂ : Mat3) (hM : M.det ≠ 0) (p₀ : Γ₀.PosDef)
    (p₁ : Γ₁.PosDef) (p₂ : Γ₂.PosDef) : σ.smooth :=
  (-(c * 2⁻¹)) • (BareS σ stages hw v fixed n m M Γ₀ Γ₁ Γ₂ hM p₀ p₁ p₂ +
    piSmooth σ (atInfinity UpperHalfPlane.J)
      (BareS σ stages hw v fixed n m (epsJ.val * M) Γ₀ Γ₁ Γ₂ (det_epsJ_mul_ne_zero hM) p₀ p₁ p₂))

theorem OmegaVec_val (n : ℕ) (m : Fin 3 →₀ ℕ) (c : ℂ) (M Γ₀ Γ₁ Γ₂ : Mat3) (hM : M.det ≠ 0)
    (p₀ : Γ₀.PosDef) (p₁ : Γ₁.PosDef) (p₂ : Γ₂.PosDef) :
    (OmegaVec σ stages hw v fixed n m c M Γ₀ Γ₁ Γ₂ hM p₀ p₁ p₂).val =
      (-(c * 2⁻¹)) • (Bare (cuspWeightedAffineOrbit σ hw v.val) n m M Γ₀ Γ₁ Γ₂ +
        σ.π (atInfinity UpperHalfPlane.J)
          (Bare (cuspWeightedAffineOrbit σ hw v.val) n m (epsJ.val * M) Γ₀ Γ₁ Γ₂)) := by
  unfold OmegaVec
  rw [Submodule.coe_smul, Submodule.coe_add, BareS_val]
  show _ • (_ + σ.π _ (BareS σ stages hw v fixed n m (epsJ.val * M) Γ₀ Γ₁ Γ₂ _ p₀ p₁ p₂).val) = _
  rw [BareS_val]

theorem OmegaVec_realize (n : ℕ) (m : Fin 3 →₀ ℕ) (c : ℂ) (M Γ₀ Γ₁ Γ₂ : Mat3) (hM : M.det ≠ 0)
    (p₀ : Γ₀.PosDef) (p₁ : Γ₁.PosDef) (p₂ : Γ₂.PosDef) (β : BinaryAdelicGL) :
    σ.realize (OmegaVec σ stages hw v fixed n m c M Γ₀ Γ₁ Γ₂ hM p₀ p₁ p₂) β =
      -(c * 2⁻¹) * (Bare (G := ℂ) (cuspScalarWeightedRealization σ hw v β) n m M Γ₀ Γ₁ Γ₂ +
        Bare (G := ℂ) (cuspScalarWeightedRealization σ hw v (β * atInfinity UpperHalfPlane.J)) n m
          (epsJ.val * M) Γ₀ Γ₁ Γ₂) := by
  unfold OmegaVec
  rw [map_smul, map_add]
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [realize_piSmooth, BareS_realize, BareS_realize]

end Vec

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
