module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.LimitInduction
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.BaseQ
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.SingleFiniteIntegral
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.Integrand
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.FibreConst
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.LfinScalar

@[expose] public section


/-!
# The line step at a prime `q` for `0 < det g∞` (route (a), positive determinant)

Formalized by Claude Haiku 5.5, with Claude Opus 5.5.

`lineStep_cq_pos`: for a finite place `q ≠ 3`, `T ∌ q` with `T` avoiding `3`, and `y ∈ (WS T)²`,
the integral over `x ∈ K_q²` of the global integrand at `(ι_q x + ι_T y)` equals
`c_q · globalIntegrand(ι_T y)`, with `c_q = globalOuterLocalRatio`.

Proof. Local factorisations are chosen per place from local coordinates (`facLoc`, via
`SingleSplit.plane_factor_all`), so that the factorisation at `w ≠ q` of `ι_q x + ι_T y` equals that
of `ι_T y`. Absorption (`GlobalIntegrand.globalIntegrand_absorb`) at `T` gives `X₀` with
`globalIntegrand(ι_T y) = (∏_T e) · normPower(det Z) · vh(X₀ Z)`. Absorption at `insert q T` and the
single-place shell identity (`ShellBaseQ.pointwise_multi_loc` at `{q}` with base `X₀ Z`) agree
pointwise in `x`. Lemma Q (`ShellBaseQ.lemmaQ_literal`) at the base `X₀ Z` then gives the line step.
The hypothesis `0 < det g∞` is used only in Lemma Q.
-/

open Matrix PadicInt MeasureTheory GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalGL3
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellIntegralLift
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinScalar
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinBlockMulti
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitFibreG
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitBlockG
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitPlane
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitPlaneG
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitGL
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinGlobal
open TernaryPeriodPolynomials.Argument.LatticeCounts.PlaneSection
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinFactor
open TernaryPeriodPolynomials.Argument.LatticeCounts.SingleSplit
open TernaryPeriodPolynomials.Argument.LatticeCounts.SingleFiniteIntegral
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalIntegrand
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitSplit
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitInduction
open TernaryPeriodPolynomials.Argument.LatticeCounts.FibreConst
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellBaseQ
open TernaryPeriodPolynomials.Argument.LatticeCounts.PointwiseMulti
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparison
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparisonNeg
open TernaryPeriodPolynomials.Argument (fourierCoeff IsNormalizedEigenform globalOuterLocalRatio)

open Classical

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.LineStepCq

variable {σ : CuspidalRepresentation} {n : ℕ}

/-- Every finite place carries its prime (the completion is `ℚ_p` for `p = primesEquiv v`). -/
instance factPrimeOf (v : FinitePlace) : Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

theorem psiV_eMeas_cq (v : FinitePlace) (u : v.adicCompletion ℚ) : psiV v (eMeas v u) = u :=
  psiV_adic v u

/-- The local plane factorisation of `L(u₁, u₂)` at a place, from the local coordinates. -/
theorem facLoc (w : FinitePlace) (u₁ u₂ : w.adicCompletion ℚ) :
    ∃ P κ : GeneralLinearGroup (Fin 3) (w.adicCompletion ℚ),
      P.val 2 0 = 0 ∧ P.val 2 1 = 0 ∧ LstR u₁ u₂ = P.val * κ.val ∧ IntGL3 w κ.val := by
  obtain ⟨P, κ, h20, h21, hf, hk⟩ := plane_factor_all w (eMeas w u₁) (eMeas w u₂)
  rw [psiV_eMeas_cq, psiV_eMeas_cq] at hf
  exact ⟨P, κ, h20, h21, hf, hk⟩

/-- The chosen plane factor at a place. -/
noncomputable def facP (w : FinitePlace) (u₁ u₂ : w.adicCompletion ℚ) :
    GeneralLinearGroup (Fin 3) (w.adicCompletion ℚ) :=
  (facLoc w u₁ u₂).choose

/-- The chosen integral factor at a place. -/
noncomputable def facK (w : FinitePlace) (u₁ u₂ : w.adicCompletion ℚ) :
    GeneralLinearGroup (Fin 3) (w.adicCompletion ℚ) :=
  (facLoc w u₁ u₂).choose_spec.choose

theorem facSpec (w : FinitePlace) (u₁ u₂ : w.adicCompletion ℚ) :
    (facP w u₁ u₂).val 2 0 = 0 ∧ (facP w u₁ u₂).val 2 1 = 0 ∧
      LstR u₁ u₂ = (facP w u₁ u₂).val * (facK w u₁ u₂).val ∧ IntGL3 w (facK w u₁ u₂).val :=
  (facLoc w u₁ u₂).choose_spec.choose_spec

theorem facP20 (w : FinitePlace) (u₁ u₂ : w.adicCompletion ℚ) : (facP w u₁ u₂).val 2 0 = 0 :=
  (facSpec w u₁ u₂).1

theorem facP21 (w : FinitePlace) (u₁ u₂ : w.adicCompletion ℚ) : (facP w u₁ u₂).val 2 1 = 0 :=
  (facSpec w u₁ u₂).2.1

theorem facLK (w : FinitePlace) (u₁ u₂ : w.adicCompletion ℚ) :
    LstR u₁ u₂ = (facP w u₁ u₂).val * (facK w u₁ u₂).val :=
  (facSpec w u₁ u₂).2.2.1

theorem facKint (w : FinitePlace) (u₁ u₂ : w.adicCompletion ℚ) :
    IntGL3 w (facK w u₁ u₂).val :=
  (facSpec w u₁ u₂).2.2.2

/-- The local factorisation data of a point, at a place `w`, from its local values. -/
abbrev pzOf (z : FiniteAwayThree × FiniteAwayThree) (w : FinitePlace) :
    GeneralLinearGroup (Fin 3) (w.adicCompletion ℚ) :=
  facP w (finiteEvaluation w (awayVal z.1)) (finiteEvaluation w (awayVal z.2))

/-- The integral-part data of a point, at a place `w`. -/
abbrev kzOf (z : FiniteAwayThree × FiniteAwayThree) (w : FinitePlace) :
    GeneralLinearGroup (Fin 3) (w.adicCompletion ℚ) :=
  facK w (finiteEvaluation w (awayVal z.1)) (finiteEvaluation w (awayVal z.2))

theorem cq_hS (z : FiniteAwayThree × FiniteAwayThree) (w : FinitePlace) :
    evM3 w (LfinGLof (awayVal z.1) (awayVal z.2)).val = (pzOf z w).val * (kzOf z w).val := by
  rw [evM3_LfinGLof]
  exact facLK _ _ _

theorem cq_hP (z : FiniteAwayThree × FiniteAwayThree) (w : FinitePlace) :
    (pzOf z w).val 2 0 = 0 ∧ (pzOf z w).val 2 1 = 0 :=
  ⟨facP20 _ _ _, facP21 _ _ _⟩

theorem cq_hK (z : FiniteAwayThree × FiniteAwayThree) (w : FinitePlace) :
    IntGL3 w (kzOf z w).val :=
  facKint _ _ _

theorem cq_ev_add (w : FinitePlace) (a b : FiniteAwayThree) :
    finiteEvaluation w (awayVal (a + b)) =
      finiteEvaluation w (awayVal a) + finiteEvaluation w (awayVal b) := by
  simp [awayVal]

theorem cq_ev_iota (T : Finset FinitePlace) (hT : ∀ p ∈ T, p ≠ placeThree) (a : WS T)
    (w : FinitePlace) (hw : w ∉ T) : finiteEvaluation w (awayVal (iotaS T hT a)) = 0 :=
  eval_iotaS_of_notMem T hT a w hw

/-- The point `(ι_q x₁ + ι_T y₁, ι_q x₂ + ι_T y₂)` lies in `U_{insert q T}`. -/
theorem cq_zx_mem (T : Finset FinitePlace) (hT : ∀ p ∈ T, p ≠ placeThree) (q : FinitePlace)
    (hq : q ≠ placeThree) (x₁ x₂ : q.adicCompletion ℚ) (y₁ y₂ : WS T) :
    (finiteAwayThreeAtPlace q hq x₁ + iotaS T hT y₁, finiteAwayThreeAtPlace q hq x₂ + iotaS T hT y₂)
      ∈ UregionS (insert q T) := by
  intro w hw
  rw [Finset.mem_insert, not_or] at hw
  obtain ⟨hwq, hwT⟩ := hw
  show finiteEvaluation w (awayVal (finiteAwayThreeAtPlace q hq x₁ + iotaS T hT y₁)) ∈ OS w ∧
    finiteEvaluation w (awayVal (finiteAwayThreeAtPlace q hq x₂ + iotaS T hT y₂)) ∈ OS w
  rw [cq_ev_add, cq_ev_add, eval_atPlace_ne q hq x₁ w hwq, eval_atPlace_ne q hq x₂ w hwq,
    cq_ev_iota T hT y₁ w hwT, cq_ev_iota T hT y₂ w hwT, add_zero]
  exact ⟨(OS w).zero_mem, (OS w).zero_mem⟩

/-- The point `(ι_T y₁, ι_T y₂)` lies in `U_T`. -/
theorem cq_z0_mem (T : Finset FinitePlace) (hT : ∀ p ∈ T, p ≠ placeThree) (y₁ y₂ : WS T) :
    (iotaS T hT y₁, iotaS T hT y₂) ∈ UregionS T := by
  intro w hw
  show finiteEvaluation w (awayVal (iotaS T hT y₁)) ∈ OS w ∧
    finiteEvaluation w (awayVal (iotaS T hT y₂)) ∈ OS w
  rw [cq_ev_iota T hT y₁ w hw, cq_ev_iota T hT y₂ w hw]
  exact ⟨(OS w).zero_mem, (OS w).zero_mem⟩

/-- At `q` the factorisation of `ι_q x + ι_T y` is the one of `x`. -/
theorem cq_pz_q (T : Finset FinitePlace) (hT : ∀ p ∈ T, p ≠ placeThree) (q : FinitePlace)
    (hq : q ≠ placeThree) (hqT : q ∉ T) (x₁ x₂ : q.adicCompletion ℚ) (y₁ y₂ : WS T) :
    pzOf (finiteAwayThreeAtPlace q hq x₁ + iotaS T hT y₁,
        finiteAwayThreeAtPlace q hq x₂ + iotaS T hT y₂) q = facP q x₁ x₂ := by
  show facP q (finiteEvaluation q (awayVal (finiteAwayThreeAtPlace q hq x₁ + iotaS T hT y₁)))
      (finiteEvaluation q (awayVal (finiteAwayThreeAtPlace q hq x₂ + iotaS T hT y₂))) = facP q x₁ x₂
  rw [cq_ev_add, cq_ev_add, eval_atPlace_self, eval_atPlace_self,
    cq_ev_iota T hT y₁ q hqT, cq_ev_iota T hT y₂ q hqT, add_zero, add_zero]

/-- Away from `q` the factorisations of `ι_q x + ι_T y` and of `ι_T y` agree. -/
theorem cq_pz_ne (q : FinitePlace) (hq : q ≠ placeThree) (x₁ x₂ : q.adicCompletion ℚ)
    (T : Finset FinitePlace) (hT : ∀ p ∈ T, p ≠ placeThree) (y₁ y₂ : WS T)
    (w : FinitePlace) (hw : w ≠ q) :
    pzOf (finiteAwayThreeAtPlace q hq x₁ + iotaS T hT y₁,
        finiteAwayThreeAtPlace q hq x₂ + iotaS T hT y₂) w =
      pzOf (iotaS T hT y₁, iotaS T hT y₂) w := by
  show facP w (finiteEvaluation w (awayVal (finiteAwayThreeAtPlace q hq x₁ + iotaS T hT y₁)))
      (finiteEvaluation w (awayVal (finiteAwayThreeAtPlace q hq x₂ + iotaS T hT y₂))) =
    facP w (finiteEvaluation w (awayVal (iotaS T hT y₁)))
      (finiteEvaluation w (awayVal (iotaS T hT y₂)))
  rw [cq_ev_add, cq_ev_add, eval_atPlace_ne q hq x₁ w hw, eval_atPlace_ne q hq x₂ w hw,
    zero_add, zero_add]

/-- The shell integrand, unfolded to the literal `expo I` form. -/
theorem shellIntegrandG_eq (q : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv q).val.Prime]
    (I : EichlerInput σ n) (W : BinaryFiniteGL) (gInf : BinaryRealGL)
    (s t : q.adicCompletion ℚ) :
    shellIntegrandG q I W gInf (eMeas q s, eMeas q t) =
      smoothReal σ (finitePlaneVector σ GeneralEisenstein.trivialCharacter 0 (expo I)
        (ιGL3 q (LstV q (eMeas q s, eMeas q t)) * blkGL W) I.vector.val) (atInfinity gInf) :=
  rfl

/-- **Pointwise line identity.** For `x ∈ K_q²`, the global integrand at `ι_q x + ι_T y` equals the
literal shell integrand at `x` with base `X₀ Z`, where `X₀` is the block base of `ι_T y`. -/
theorem cq_point_eq (I : EichlerInput σ n)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne
      (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (q : FinitePlace) (hq : q ≠ placeThree) (T : Finset FinitePlace) (hT : ∀ p ∈ T, p ≠ placeThree)
    (hqT : q ∉ T) (Z : BinaryFiniteGL)
    (hZ : ∀ w : FinitePlace, IntGL w (GeneralLinearGroup.map (finiteEvaluation w) Z).val)
    (gInf : BinaryRealGL) (y₁ y₂ : WS T)
    (X0 : GeneralLinearGroup (Fin 2) FiniteAdeles)
    (hX0 : ∀ w : FinitePlace, (GeneralLinearGroup.map (finiteEvaluation w) X0).val =
      if w ∈ T then blk2 (pzOf (iotaS T hT y₁, iotaS T hT y₂) w).val else 1)
    (x₁ x₂ : q.adicCompletion ℚ) :
    globalIntegrand I Z gInf (finiteAwayThreeAtPlace q hq x₁ + iotaS T hT y₁,
        finiteAwayThreeAtPlace q hq x₂ + iotaS T hT y₂) =
      shellIntegrandG q I (X0 * Z) gInf (eMeas q x₁, eMeas q x₂) := by
  -- global absorption at `insert q T`
  obtain ⟨Xa, hXa, hga⟩ := globalIntegrand_absorb I h hform (insert q T)
    (pzOf (finiteAwayThreeAtPlace q hq x₁ + iotaS T hT y₁, finiteAwayThreeAtPlace q hq x₂ + iotaS T hT y₂))
    (kzOf (finiteAwayThreeAtPlace q hq x₁ + iotaS T hT y₁, finiteAwayThreeAtPlace q hq x₂ + iotaS T hT y₂))
    (fun w _ => cq_hP _ w)
    (finiteAwayThreeAtPlace q hq x₁ + iotaS T hT y₁, finiteAwayThreeAtPlace q hq x₂ + iotaS T hT y₂)
    (fun w _ => cq_hS _ w) (fun w _ => cq_hK _ w)
    (fun w hw => intGL3_LfinGLof_of_mem (cq_zx_mem T hT q hq x₁ x₂ y₁ y₂) w hw) Z hZ gInf
  -- local shell identity at `{q}` with base `X₀ Z`
  have hPq : ∀ w ∈ ({q} : Finset FinitePlace),
      ((extend1 q (facP q x₁ x₂)) w).val 2 0 = 0 ∧ ((extend1 q (facP q x₁ x₂)) w).val 2 1 = 0 := by
    intro w hw
    rw [Finset.mem_singleton] at hw
    rw [hw, extend1_self]
    exact ⟨facP20 _ _ _, facP21 _ _ _⟩
  have hSq : ∀ w ∈ ({q} : Finset FinitePlace),
      evM3 w (ιGL3 q (LstV q (eMeas q x₁, eMeas q x₂))).val =
        (extend1 q (facP q x₁ x₂) w).val * (extend1 q (facK q x₁ x₂) w).val := by
    intro w hw
    rw [Finset.mem_singleton] at hw
    rw [hw, extend1_self, extend1_self, evM3_ιGL3_self, LstV_val_eq, psiV_eMeas_cq,
      psiV_eMeas_cq]
    exact facLK _ _ _
  have hκq : ∀ w ∈ ({q} : Finset FinitePlace), IntGL3 w (extend1 q (facK q x₁ x₂) w).val := by
    intro w hw
    rw [Finset.mem_singleton] at hw
    rw [hw, extend1_self]
    exact facKint _ _ _
  have hL1q : ∀ w : FinitePlace, w ∉ ({q} : Finset FinitePlace) →
      evM3 w (ιGL3 q (LstV q (eMeas q x₁, eMeas q x₂))).val = 1 := by
    intro w hw
    apply evM3_ιGL3_ne q w
    intro hwq
    exact hw (by rw [Finset.mem_singleton]; exact hwq)
  have hgfq : ∀ w ∈ ({q} : Finset FinitePlace),
      IntGL w (GeneralLinearGroup.map (finiteEvaluation w) (X0 * Z)).val := by
    intro w hw
    rw [Finset.mem_singleton] at hw
    rw [hw, map_mul, Units.val_mul, hX0 q, ite_eq_right hqT, one_mul]
    exact hZ q
  obtain ⟨Xs, hXs, hgs⟩ := pointwise_multi_loc I h hform {q} (extend1 q (facP q x₁ x₂))
    (extend1 q (facK q x₁ x₂)) hPq (ιGL3 q (LstV q (eMeas q x₁, eMeas q x₂))) hSq hκq hL1q
    (X0 * Z) hgfq (expo I) gInf
  rw [Finset.prod_singleton, extend1_self] at hgs
  -- the two bases agree
  have hXeq : Xa = Xs * X0 := by
    apply gl2_ext
    intro w
    rw [hXa w, map_mul, Units.val_mul, hXs w, hX0 w]
    by_cases hwq : w = q
    · rw [hwq, ite_eq_left (Finset.mem_insert_self q T), ite_eq_left (Finset.mem_singleton_self q),
        ite_eq_right hqT, extend1_self, mul_one, cq_pz_q T hT q hq hqT x₁ x₂ y₁ y₂]
    · by_cases hwT : w ∈ T
      · rw [ite_eq_left (Finset.mem_insert_of_mem hwT),
          ite_eq_right (fun h' => hwq (Finset.mem_singleton.1 h')), ite_eq_left hwT, one_mul,
          cq_pz_ne q hq x₁ x₂ T hT y₁ y₂ w hwq]
      · rw [ite_eq_right (show w ∉ insert q T from by simp [hwq, hwT]),
          ite_eq_right (fun h' => hwq (Finset.mem_singleton.1 h')), ite_eq_right hwT, mul_one]
  -- the scalar split at `T`
  have hprod : (∏ w ∈ T, Complex.exp (expo I *
        (Real.log ‖pe w (blk2 (pzOf (finiteAwayThreeAtPlace q hq x₁ + iotaS T hT y₁,
          finiteAwayThreeAtPlace q hq x₂ + iotaS T hT y₂) w).val).det‖ : ℂ))) =
      ∏ w ∈ T, Complex.exp (expo I *
        (Real.log ‖pe w (blk2 (pzOf (iotaS T hT y₁, iotaS T hT y₂) w).val).det‖ : ℂ)) :=
    Finset.prod_congr rfl fun w hw => by
      rw [cq_pz_ne q hq x₁ x₂ T hT y₁ y₂ w (fun h' => hqT (h' ▸ hw))]
  have hnp := normPower_det_mul_split T X0 Z (pzOf (iotaS T hT y₁, iotaS T hT y₂)) hX0 (expo I)
  rw [Finset.prod_insert hqT, cq_pz_q T hT q hq hqT x₁ x₂ y₁ y₂, hprod] at hga
  rw [shellIntegrandG_eq, hgs, hga, hXeq, mul_assoc Xs X0 Z, hnp]
  ring

/-- **Line step at `q` for `0 < det g∞`.** -/
theorem lineStep_cq_pos (I : EichlerInput σ n)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne
      (-2 * I.halfWeight))
    (hh : IsNormalizedEigenform h)
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (hk : 6 < -2 * I.halfWeight)
    (Z : BinaryFiniteGL)
    (hZ : ∀ w : FinitePlace, IntGL w (GeneralLinearGroup.map (finiteEvaluation w) Z).val)
    (gInf : BinaryRealGL) (hg : 0 < (Matrix.GeneralLinearGroup.det gInf).val)
    (q : FinitePlace) (hq : q ≠ placeThree) (p : Nat.Primes)
    (hv : ((Rat.HeightOneSpectrum.primesEquiv q : Nat.Primes) : ℕ) = (p : ℕ)) :
    LineStep I Z gInf q hq (globalOuterLocalRatio (-2 * I.halfWeight) (fourierCoeff h (p : ℕ)) p) := by
  unfold LineStep
  intro T hT hqT y
  obtain ⟨X0, hX0, hg0⟩ := globalIntegrand_absorb I h hform T
    (pzOf (iotaS T hT y.1, iotaS T hT y.2)) (kzOf (iotaS T hT y.1, iotaS T hT y.2))
    (fun w _ => cq_hP _ w) (iotaS T hT y.1, iotaS T hT y.2)
    (fun w _ => cq_hS _ w) (fun w _ => cq_hK _ w)
    (fun w hw => intGL3_LfinGLof_of_mem (cq_z0_mem T hT y.1 y.2) w hw) Z hZ gInf
  have hW : IntGL q (GeneralLinearGroup.map (finiteEvaluation q) (X0 * Z)).val := by
    rw [map_mul, Units.val_mul, hX0 q, ite_eq_right hqT, one_mul]
    exact hZ q
  have hEP : MeasurePreserving
      (MeasurableEquiv.prodCongr (eMeas q) (eMeas q))
      ((finiteCompletionMeasure q).prod (finiteCompletionMeasure q))
      ((finitePadicMeasure q).prod (finitePadicMeasure q)) :=
    (⟨(eMeas q).measurable, rfl⟩ : MeasurePreserving (eMeas q) (finiteCompletionMeasure q)
      (finitePadicMeasure q)).prod ⟨(eMeas q).measurable, rfl⟩
  have hsplit := normPower_det_mul_split T X0 Z (pzOf (iotaS T hT y.1, iotaS T hT y.2)) hX0
    (((-2 * I.halfWeight : ℤ) : ℂ) / 2)
  unfold expo at hg0
  calc ∫ x : q.adicCompletion ℚ × q.adicCompletion ℚ,
        globalIntegrand I Z gInf (finiteAwayThreeAtPlace q hq x.1 + iotaS T hT y.1,
          finiteAwayThreeAtPlace q hq x.2 + iotaS T hT y.2)
          ∂((finiteCompletionMeasure q).prod (finiteCompletionMeasure q))
      = ∫ x : q.adicCompletion ℚ × q.adicCompletion ℚ,
          shellIntegrandG q I (X0 * Z) gInf (eMeas q x.1, eMeas q x.2)
          ∂((finiteCompletionMeasure q).prod (finiteCompletionMeasure q)) :=
        integral_congr_ae (Filter.Eventually.of_forall fun x =>
          cq_point_eq I h hform q hq T hT hqT Z hZ gInf y.1 y.2 X0 hX0 x.1 x.2)
    _ = ∫ s, shellIntegrandG q I (X0 * Z) gInf s
          ∂((finitePadicMeasure q).prod (finitePadicMeasure q)) :=
        hEP.integral_comp' (shellIntegrandG q I (X0 * Z) gInf)
    _ = normPower (TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.finiteAdeleUnit
          (GeneralLinearGroup.det (X0 * Z))) (((-2 * I.halfWeight : ℤ) : ℂ) / 2) *
          vhValueFull (-2 * I.halfWeight) h gInf (X0 * Z) *
          globalOuterLocalRatio (-2 * I.halfWeight) (fourierCoeff h (p : ℕ)) p :=
        lemmaQ_literal I h hh hform hk p q hv gInf hg (X0 * Z) hW
    _ = globalOuterLocalRatio (-2 * I.halfWeight) (fourierCoeff h (p : ℕ)) p *
          globalIntegrand I Z gInf (iotaS T hT y.1, iotaS T hT y.2) := by
        rw [hsplit, hg0]
        ring

end TernaryPeriodPolynomials.Argument.LatticeCounts.LineStepCq

end
