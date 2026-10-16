module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Plane.LiftVec
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Eichler.BridgeAnalytic

@[expose] public section


/-!
# The smooth vector and its analyticity (plane integral cochain)

`analyticAt_OmegaExpl`, `contDiffOn_OmegaExpl`: the Hilbert-space value `OmegaExpl` of the vector of the plane integral
cochain (`π(b)(−(c/2)(B(M) + π(J_∞) B(εM)))`) is real analytic in the frame `M` and the Gram matrices at invertible `M` and
positive definite `Γᵢ`, hence smooth along any real-analytic family of frames (`contDiffOn_OmegaExpl`).  The scalar
analogue is `contDiffOn_OmegaScal`; `cOmegaCoeffAt_eq_scal`, `OmegaScal_eq_realize` identify the coefficient of the plane
integral cochain with `OmegaScal` and with the realization of `OmegaVec`.

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

theorem bF_comm_atInfinityJ (g : AdelicGL) :
    bF g * atInfinity UpperHalfPlane.J = atInfinity UpperHalfPlane.J * bF g :=
  atFinite_mul_atInfinity_comm _ _

section Expl

variable (σ : CuspidalRepresentation)

theorem analyticAt_weightedOrbit (hw : ℤ) (v : σ.smooth) {z : ℂ} (hz : 0 < z.im) :
    AnalyticAt ℝ (cuspWeightedAffineOrbit σ hw v.val) z := by
  have weight : AnalyticAt ℝ (fun argument : ℂ => argument.im ^ hw) z :=
    (Complex.imCLM.analyticAt z).zpow (ne_of_gt hz)
  exact weight.smul (affineOrbit_analyticAt σ v hz)

/-- The explicit Hilbert-space value of the vector of the plane integral cochain. -/
def OmegaExpl (hw : ℤ) (v : σ.smooth) (n : ℕ) (m : Fin 3 →₀ ℕ) (c : ℂ) (b : BinaryAdelicGL)
    (M Γ₀ Γ₁ Γ₂ : Mat3) : σ.H :=
  σ.π b ((-(c * 2⁻¹)) • (Bare (cuspWeightedAffineOrbit σ hw v.val) n m M Γ₀ Γ₁ Γ₂ +
    σ.π (atInfinity UpperHalfPlane.J) (Bare (cuspWeightedAffineOrbit σ hw v.val) n m (epsJ.val * M) Γ₀ Γ₁ Γ₂)))

theorem analyticAt_OmegaExpl (hw : ℤ) (v : σ.smooth) (n : ℕ) (m : Fin 3 →₀ ℕ) (c : ℂ) (b : BinaryAdelicGL)
    {M Γ₀ Γ₁ Γ₂ : Mat3} (hM : M.det ≠ 0) (p₀ : Γ₀.PosDef) (p₁ : Γ₁.PosDef) (p₂ : Γ₂.PosDef) :
    AnalyticAt ℝ (fun x : Mat3 × Mat3 × Mat3 × Mat3 => OmegaExpl σ hw v n m c b x.1 x.2.1 x.2.2.1 x.2.2.2)
      (M, Γ₀, Γ₁, Γ₂) := by
  have hO : ∀ z : ℂ, 0 < z.im → AnalyticAt ℝ (cuspWeightedAffineOrbit σ hw v.val) z :=
    fun z hz => analyticAt_weightedOrbit σ hw v hz
  have h1 := analyticAt_Bare (cuspWeightedAffineOrbit σ hw v.val) hO n m hM p₀ p₁ p₂
  have hε : AnalyticAt ℝ (fun x : Mat3 × Mat3 × Mat3 × Mat3 => (epsJ.val * x.1, x.2.1, x.2.2.1, x.2.2.2))
      (M, Γ₀, Γ₁, Γ₂) := by
    have : ContDiff ℝ ⊤ (fun x : Mat3 × Mat3 × Mat3 × Mat3 => (epsJ.val * x.1, x.2.1, x.2.2.1, x.2.2.2)) := by
      refine ContDiff.prodMk ?_ (by fun_prop)
      exact contDiff_matMul contDiff_const (by fun_prop)
    exact this.contDiffAt.analyticAt
  have h2 := analyticAt_Bare (cuspWeightedAffineOrbit σ hw v.val) hO n m (det_epsJ_mul_ne_zero hM) p₀ p₁ p₂
  have h2' : AnalyticAt ℝ (fun x : Mat3 × Mat3 × Mat3 × Mat3 =>
      Bare (cuspWeightedAffineOrbit σ hw v.val) n m (epsJ.val * x.1) x.2.1 x.2.2.1 x.2.2.2) (M, Γ₀, Γ₁, Γ₂) := by
    have h := AnalyticAt.comp_of_eq
      (g := fun x : Mat3 × Mat3 × Mat3 × Mat3 => Bare (cuspWeightedAffineOrbit σ hw v.val) n m x.1 x.2.1 x.2.2.1 x.2.2.2)
      h2 hε rfl
    exact h
  have hJ := (psPiCLM σ (atInfinity UpperHalfPlane.J)).analyticAt (Bare (cuspWeightedAffineOrbit σ hw v.val) n m
    (epsJ.val * M) Γ₀ Γ₁ Γ₂)
  have h3 := AnalyticAt.comp_of_eq hJ h2' rfl
  have h4 : AnalyticAt ℝ (fun x : Mat3 × Mat3 × Mat3 × Mat3 =>
      (-(c * 2⁻¹)) • (Bare (cuspWeightedAffineOrbit σ hw v.val) n m x.1 x.2.1 x.2.2.1 x.2.2.2 +
        σ.π (atInfinity UpperHalfPlane.J)
          (Bare (cuspWeightedAffineOrbit σ hw v.val) n m (epsJ.val * x.1) x.2.1 x.2.2.1 x.2.2.2)))
      (M, Γ₀, Γ₁, Γ₂) :=
    analyticAt_const.smul (h1.add h3)
  have hb := (psPiCLM σ b).analyticAt ((-(c * 2⁻¹)) • (Bare (cuspWeightedAffineOrbit σ hw v.val) n m M Γ₀ Γ₁ Γ₂ +
    σ.π (atInfinity UpperHalfPlane.J) (Bare (cuspWeightedAffineOrbit σ hw v.val) n m (epsJ.val * M) Γ₀ Γ₁ Γ₂)))
  exact AnalyticAt.comp_of_eq hb h4 rfl


theorem contDiffOn_OmegaExpl (hw : ℤ) (v : σ.smooth) (n : ℕ) (m : Fin 3 →₀ ℕ) (c : ℂ) (b : BinaryAdelicGL)
    {K : ℕ} (fM f0 f1 f2 : (Fin K → Mat3) → Mat3) (hM : ContDiff ℝ ⊤ fM) (h0 : ContDiff ℝ ⊤ f0)
    (h1 : ContDiff ℝ ⊤ f1) (h2 : ContDiff ℝ ⊤ f2)
    (hdet : ∀ A : Fin K → Mat3, (∀ i, (A i).det ≠ 0) → (fM A).det ≠ 0)
    (hp0 : ∀ A : Fin K → Mat3, (∀ i, (A i).det ≠ 0) → (f0 A).PosDef)
    (hp1 : ∀ A : Fin K → Mat3, (∀ i, (A i).det ≠ 0) → (f1 A).PosDef)
    (hp2 : ∀ A : Fin K → Mat3, (∀ i, (A i).det ≠ 0) → (f2 A).PosDef) :
    ContDiffOn ℝ ⊤ (fun A => OmegaExpl σ hw v n m c b (fM A) (f0 A) (f1 A) (f2 A))
      {A : Fin K → Mat3 | ∀ i, (A i).det ≠ 0} := by
  have han : AnalyticOnNhd ℝ (fun A => OmegaExpl σ hw v n m c b (fM A) (f0 A) (f1 A) (f2 A))
      {A : Fin K → Mat3 | ∀ i, (A i).det ≠ 0} := by
    intro A hA
    have hmap : AnalyticAt ℝ (fun A : Fin K → Mat3 => (fM A, f0 A, f1 A, f2 A)) A :=
      (hM.prodMk (h0.prodMk (h1.prodMk h2))).contDiffAt.analyticAt
    have := analyticAt_OmegaExpl σ hw v n m c b (hdet A hA) (hp0 A hA) (hp1 A hA) (hp2 A hA)
    have hc := AnalyticAt.comp_of_eq this hmap rfl
    exact hc.congr (Filter.Eventually.of_forall fun _ => rfl)
  have hopen : IsOpen {A : Fin K → Mat3 | ∀ i, (A i).det ≠ 0} := by
    have e : {A : Fin K → Mat3 | ∀ i, (A i).det ≠ 0} = ⋂ i, {A : Fin K → Mat3 | (A i).det ≠ 0} := by
      ext A; simp
    rw [e]
    exact isOpen_iInter_of_finite fun i => isOpen_ne.preimage
      ((Continuous.matrix_det continuous_id).comp (continuous_apply i))
  exact han.contDiffOn hopen.uniqueDiffOn


end Expl

section Scal

/-- The scalar value of the plane integral cochain coefficient in terms of the datum `F`. -/
def OmegaScal (F : BinaryAdelicGL → ℂ → ℂ) (n : ℕ) (m : Fin 3 →₀ ℕ) (c : ℂ) (β : BinaryAdelicGL)
    (M Γ₀ Γ₁ Γ₂ : Mat3) : ℂ :=
  -(c * 2⁻¹) * (Bare (G := ℂ) (F β) n m M Γ₀ Γ₁ Γ₂ +
    Bare (G := ℂ) (F (β * atInfinity UpperHalfPlane.J)) n m (epsJ.val * M) Γ₀ Γ₁ Γ₂)

theorem cOmegaCoeffAt_eq_scal {n : ℕ} (D : InducingData n) (F : BinaryAdelicGL → ℂ → ℂ)
    (hol : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im}) (y : Fin 3 → RealGL3) (g : AdelicGL)
    (x : BinaryAdelicGL) (κ : Fin 3 →₀ ℕ) :
    cOmegaCoeffAt n D F y g x κ =
      OmegaScal F n κ (cF D g) (x * bF g) (realGroup g).val (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) := by
  have hM := det_ne_zero_realGL3 (realGroup g)
  unfold cOmegaCoeffAt OmegaScal
  rw [planeHol_stokes D F hol g x _ _ _ _ hM (posDef_gramOf _) (posDef_gramOf _) (posDef_gramOf _) κ,
    planeHol_stokes D F hol g (x * atInfinity UpperHalfPlane.J) _ _ _ _ (det_epsJ_mul_ne_zero hM)
      (posDef_gramOf _) (posDef_gramOf _) (posDef_gramOf _) κ]
  have e : x * atInfinity UpperHalfPlane.J * bF g = x * bF g * atInfinity UpperHalfPlane.J := by
    rw [mul_assoc, ← bF_comm_atInfinityJ g, ← mul_assoc]
  rw [e]
  ring

theorem OmegaScal_eq_realize (σ : CuspidalRepresentation) (stages : AnalyticScalar.ContinuousStages σ) (hw : ℤ)
    (v : σ.smooth) (fixed : v.val ∈ BinaryLevel.fixedSubspace σ BinaryLevel.finiteCongruence) (n : ℕ)
    (m : Fin 3 →₀ ℕ) (c : ℂ) (β : BinaryAdelicGL) (M Γ₀ Γ₁ Γ₂ : Mat3) (hM : M.det ≠ 0) (p₀ : Γ₀.PosDef)
    (p₁ : Γ₁.PosDef) (p₂ : Γ₂.PosDef) :
    OmegaScal (cuspScalarWeightedRealization σ hw v) n m c β M Γ₀ Γ₁ Γ₂ =
      σ.realize (OmegaVec σ stages hw v fixed n m c M Γ₀ Γ₁ Γ₂ hM p₀ p₁ p₂) β := by
  rw [OmegaVec_realize]
  rfl

theorem contDiffOn_OmegaScal (F : BinaryAdelicGL → ℂ → ℂ)
    (hF : ∀ h z, 0 < z.im → AnalyticAt ℝ (F h) z) (n : ℕ) (m : Fin 3 →₀ ℕ) (c : ℂ) (β : BinaryAdelicGL)
    {K : ℕ} (fM f0 f1 f2 : (Fin K → Mat3) → Mat3) (hM : ContDiff ℝ ⊤ fM) (h0 : ContDiff ℝ ⊤ f0)
    (h1 : ContDiff ℝ ⊤ f1) (h2 : ContDiff ℝ ⊤ f2)
    (hdet : ∀ A : Fin K → Mat3, (∀ i, (A i).det ≠ 0) → (fM A).det ≠ 0)
    (hp0 : ∀ A : Fin K → Mat3, (∀ i, (A i).det ≠ 0) → (f0 A).PosDef)
    (hp1 : ∀ A : Fin K → Mat3, (∀ i, (A i).det ≠ 0) → (f1 A).PosDef)
    (hp2 : ∀ A : Fin K → Mat3, (∀ i, (A i).det ≠ 0) → (f2 A).PosDef) :
    ContDiffOn ℝ ⊤ (fun A => OmegaScal F n m c β (fM A) (f0 A) (f1 A) (f2 A))
      {A : Fin K → Mat3 | ∀ i, (A i).det ≠ 0} := by
  have han : AnalyticOnNhd ℝ (fun A => OmegaScal F n m c β (fM A) (f0 A) (f1 A) (f2 A))
      {A : Fin K → Mat3 | ∀ i, (A i).det ≠ 0} := by
    intro A hA
    have hmap : AnalyticAt ℝ (fun A : Fin K → Mat3 => (fM A, f0 A, f1 A, f2 A)) A :=
      (hM.prodMk (h0.prodMk (h1.prodMk h2))).contDiffAt.analyticAt
    have hε : AnalyticAt ℝ (fun A : Fin K → Mat3 => (epsJ.val * fM A, f0 A, f1 A, f2 A)) A :=
      ((contDiff_matMul contDiff_const hM).prodMk (h0.prodMk (h1.prodMk h2))).contDiffAt.analyticAt
    have b1 := analyticAt_Bare (F β) (hF β) n m (hdet A hA) (hp0 A hA) (hp1 A hA) (hp2 A hA)
    have b2 := analyticAt_Bare (F (β * atInfinity UpperHalfPlane.J)) (hF _) n m
      (det_epsJ_mul_ne_zero (hdet A hA)) (hp0 A hA) (hp1 A hA) (hp2 A hA)
    have c1 := AnalyticAt.comp_of_eq b1 hmap rfl
    have c2 := AnalyticAt.comp_of_eq b2 hε rfl
    unfold OmegaScal
    exact analyticAt_const.mul (c1.add c2)
  have hopen : IsOpen {A : Fin K → Mat3 | ∀ i, (A i).det ≠ 0} := by
    have e : {A : Fin K → Mat3 | ∀ i, (A i).det ≠ 0} = ⋂ i, {A : Fin K → Mat3 | (A i).det ≠ 0} := by
      ext A; simp
    rw [e]
    exact isOpen_iInter_of_finite fun i => isOpen_ne.preimage
      ((Continuous.matrix_det continuous_id).comp (continuous_apply i))
  exact han.contDiffOn hopen.uniqueDiffOn

end Scal

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
