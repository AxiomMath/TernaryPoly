module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.ConstantTerm
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.PolyCalcCoef
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Frozen

@[expose] public section


/-!
# Translations of the boundary model and their coefficient transport

(averaging on
the fiber "with its coefficient transport": the periodic gauge `ρ(u)⁻¹ s(u)` of a flat section on the
unipotent fiber `ℝ²`).

The group `ℝ²` of translations `(u, τ) ↦ (u + v, τ)` of `e(P) = ℝ² × ℍ` is a plane parabolic group
(`trPD`, with `λ = 1`, `w = v`); `trPD_act` identifies its action with the translation, `trL n v` is
the coefficient transport `ρ(t_v)` on `Coef n` (the real matrix `[[1, v], [0, 1]]`), it is additive
in `v` (`trL_add`), and `v ↦ trL n v` is `C^∞` (`contDiff_trL`: the matrix coefficients are
polynomial in `v`).

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial
open scoped ContDiff
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3.Psi

/-- The group `ℝ²` of translations of the boundary model, written multiplicatively. -/
abbrev TransGrp := Multiplicative (Fin 2 → ℝ)

/-- The translation group as a plane parabolic group: `λ = 1`, `w = v`. -/
def trPD : PlaneData TransGrp where
  lam := 1
  w := Multiplicative.toAdd
  det_one g := by simp
  w_mul g h := by simp

theorem trPD_act (s : TransGrp) (x : Face) :
    trPD.act s x = x + ![(Multiplicative.toAdd s) 0, (Multiplicative.toAdd s) 1, 0, 0] := by
  funext i
  fin_cases i <;> simp [PlaneData.act, trPD, mob, faceTau]

theorem trPD_plm (s : TransGrp) :
    trPD.plm s = transMat ((Multiplicative.toAdd s) 0) ((Multiplicative.toAdd s) 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [PlaneData.plm, trPD, parabolicMatrix, transMat]

/-- The coefficient of `ρ(t_v) q` is a smooth (polynomial) function of the translation vector. -/
theorem contDiff_coeff_rho_transMat (q : MvPolynomial (Fin 3) ℂ) (e : Fin 3 →₀ ℕ) :
    ContDiff ℝ ∞ (fun v : Fin 2 → ℝ => (SeedC3.rho (transMat (v 0) (v 1)) q).coeff e) := by
  let f : Fin 3 → MvPolynomial (Fin 3 ⊕ Fin 2) ℂ :=
    ![X (Sum.inl 0) - X (Sum.inr 0) * X (Sum.inl 2), X (Sum.inl 1) - X (Sum.inr 1) * X (Sum.inl 2),
      X (Sum.inl 2)]
  let Q : MvPolynomial (Fin 3 ⊕ Fin 2) ℂ := bind₁ f q
  have hs : ∀ a : Fin 2, ContDiffOn ℝ ∞ (fun v : Fin 2 → ℝ => ((v a : ℝ) : ℂ)) Set.univ :=
    fun a => (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ a)).contDiffOn
  have key := Calc.contDiffOn_coeff_spec Set.univ (fun a (v : Fin 2 → ℝ) => ((v a : ℝ) : ℂ)) hs Q e
  have key' : ContDiff ℝ ∞ (fun v : Fin 2 → ℝ =>
      (Calc.spec (fun a => ((v a : ℝ) : ℂ)) Q).coeff e) := contDiffOn_univ.mp key
  have hfun : (fun v : Fin 2 → ℝ => (SeedC3.rho (transMat (v 0) (v 1)) q).coeff e) =
      (fun v : Fin 2 → ℝ => (Calc.spec (fun a => ((v a : ℝ) : ℂ)) Q).coeff e) := by
    funext v
    rw [← rho_transMat]
    congr 2
    simp only [Q, Calc.spec]
    rw [MvPolynomial.aeval_bind₁]
    show aeval _ q = aeval _ q
    congr 2
    funext i
    fin_cases i <;> simp [f]
  rw [hfun]
  exact key'

/-- The coefficient transport `ρ(t_v)` of the translation by `v`. -/
def trL (n : ℕ) (v : Fin 2 → ℝ) : Coef n →L[ℝ] Coef n :=
  ZigZag.repCLM (trPD.rhoR n) (Multiplicative.ofAdd v)

theorem toPoly_trL (n : ℕ) (v : Fin 2 → ℝ) (q : Coef n) :
    Coef.toPoly (trL n v q) = SeedC3.rho (transMat (v 0) (v 1)) (Coef.toPoly q) := by
  change Coef.toPoly (trPD.rhoCoef n (Multiplicative.ofAdd v) q) = _
  rw [trPD.toPoly_rhoCoef, trPD_plm]
  rfl

theorem trL_add (n : ℕ) (v w : Fin 2 → ℝ) : trL n (v + w) = (trL n v).comp (trL n w) := by
  unfold trL
  rw [ofAdd_add, ZigZag.repCLM_mul]

theorem trL_zero (n : ℕ) : trL n 0 = ContinuousLinearMap.id ℝ (Coef n) := by
  ext q
  apply Coef.toPoly_injective
  rw [toPoly_trL]
  simp only [Pi.zero_apply]
  have : transMat 0 0 = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [transMat]
  rw [this, rho_one]
  rfl

theorem contDiff_trL (n : ℕ) : ContDiff ℝ ∞ (fun v : Fin 2 → ℝ => trL n v) := by
  rw [contDiff_clm_apply_iff]
  intro q
  refine Calc.contDiffOn_of_vec n ?_ |> contDiffOn_univ.mp
  rw [contDiffOn_univ, contDiff_pi]
  intro e
  have := contDiff_coeff_rho_transMat (Coef.toPoly q) (Finsupp.equivFunOnFinite.symm (fun k => (e k : ℕ)))
  change ContDiff ℝ ∞ (fun x : Fin 2 → ℝ =>
    (Coef.toPoly (trL n x q)).coeff (Finsupp.equivFunOnFinite.symm (fun k => (e k : ℕ))))
  simp only [toPoly_trL]
  exact this

end TernaryPeriodPolynomials.Argument.EisensteinClass
