module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Unfold.Sum
public import TernaryPeriodPolynomials.EisensteinSeries.Class.GammaNAverage
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Periodic

@[expose] public section


/-!
# Obligation (b): the torus average of the non-identity part of the series vanishes

Paper: "The binary root
average is zero by cuspidality ... Fubini applies".

`restAverageVanishes` (`3 ≤ N`, `4 ≤ n`, holomorphic seed at the standard cusp): the average
`Av(restFaceForm)` of the grouped non-identity part is zero. The averaged integrand is the sum over the
non-identity cosets of the coefficient of `S(γ n(v))` (`coeff_trL_rest`), whose torus integral vanishes by
`total_zero`.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups ContDiff
open MeasureTheory Set MvPolynomial
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham
open TernaryPeriodPolynomials.Argument.SeedC3.Psi

/-- Two alternating two-forms on the face agreeing on all pairs of coordinate vectors are equal. -/
theorem ext2Face {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : Face [⋀^Fin 2]→L[ℝ] F}
    (h : ∀ i j : Fin 4, f ![Pi.single i 1, Pi.single j 1] = g ![Pi.single i 1, Pi.single j 1]) :
    f = g := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  refine (Pi.basisFun ℝ (Fin 4)).ext_alternating ?_
  intro v _
  have hv : (fun k => (Pi.basisFun ℝ (Fin 4)) (v k)) =
      ![Pi.single (v 0) 1, Pi.single (v 1) 1] := by
    funext k; fin_cases k <;> simp
  rw [hv]
  exact h (v 0) (v 1)

/-- Evaluation of a two-form on a fixed pair of vectors, as a continuous linear map. -/
def evalPairCLM (n : ℕ) (p q : Face) : (Face [⋀^Fin 2]→L[ℝ] Coef n) →L[ℝ] Coef n :=
  LinearMap.mkContinuous
    { toFun := fun w => w ![p, q]
      map_add' := fun w w' => by simp
      map_smul' := fun r w => by simp }
    (‖p‖ * ‖q‖) (fun w => by
      have := w.le_opNorm ![p, q]
      simpa [Fin.prod_univ_two, mul_comm, mul_left_comm] using this)

theorem evalPairCLM_apply (n : ℕ) (p q : Face) (w : Face [⋀^Fin 2]→L[ℝ] Coef n) :
    evalPairCLM n p q w = w ![p, q] := rfl

/-- The `m`-th coefficient as a real-linear continuous functional on `E_n`. -/
def polyCoefCLM (n : ℕ) (m : Fin 3 →₀ ℕ) : Coef n →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => (Coef.toPoly w).coeff m
      map_add' := fun w w' => by simp
      map_smul' := fun r w => by
        change (Coef.toPoly ((r : ℂ) • w)).coeff m = (r : ℂ) * (Coef.toPoly w).coeff m
        rw [Coef.toPoly_smul, MvPolynomial.coeff_C_mul] }

theorem polyCoefCLM_apply (n : ℕ) (m : Fin 3 →₀ ℕ) (w : Coef n) :
    polyCoefCLM n m w = (Coef.toPoly w).coeff m := rfl

theorem ptOf_shVec (x : Face) (v : Fin 2 → ℝ) :
    ptOf (x + shVec v) = ptOf x + ![v 0, v 1, 0, 0, 0] := by
  funext k
  fin_cases k <;> simp [ptOf, shVec]

variable (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n)

/-- **The averaged integrand is the sum over the non-identity cosets**: the `m`-th coefficient of
`ρ(t_{-v}) R(x + v)(e_p, e_q)` is `Σ'_{c ≠ [1]} (S_c(γ_c n(v)))`. -/
theorem coeff_trL_rest {x : Face} (hx : x ∈ faceSet) (v : Fin 2 → ℝ) (p q : Fin 4)
    (m : Fin 3 →₀ ℕ) :
    polyCoefCLM n m (trL n (-v)
      (((restFaceForm N n f hn : Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2)
        (x + shVec v) ![Pi.single p 1, Pi.single q 1])) =
      ∑' c : PlaneCoset (gammaN N), Fc N n f (ptOf x) p.castSucc q.castSucc m c v := by
  classical
  have hy : x + shVec v ∈ faceSet := shVec_mem hx v
  have hΩ := ptOf_mem hx
  set w := (((restFaceForm N n f hn : Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2)
        (x + shVec v) ![Pi.single p 1, Pi.single q 1]) with hw
  have hcoef : ∀ m', (Coef.toPoly w).coeff m' =
      restCoeff (gammaN N) n f p.castSucc q.castSucc m' (ptOf (x + shVec v)) :=
    fun m' => restFaceForm_basis N n f hn hy p q m'
  rw [polyCoefCLM_apply, toPoly_trL]
  have hneg : transMat ((-v) 0) ((-v) 1) = nmat (-v) := rfl
  rw [hneg, coeff_rho_expansion (Coef.toPoly_isHomogeneous w) _ m]
  simp only [hcoef, ptOf_shVec]
  -- the right-hand side
  have hRHS : ∀ c : PlaneCoset (gammaN N),
      Fc N n f (ptOf x) p.castSucc q.castSucc m c v = ∑ m' ∈ monSet n,
        (if c = idCoset (gammaN N) then 0 else
          termFun (gammaN N) n f c p.castSucc q.castSucc m' (ptOf x + ![v 0, v 1, 0, 0, 0])) *
          (rho (nmat (-v)) (monomial m' 1)).coeff m := by
    intro c
    unfold Fc
    by_cases hc : c = idCoset (gammaN N)
    · simp [hc]
    · simp only [ite_eq_right hc]
      exact PhiC_expansion N n f hΩ _ _ m c v
  simp_rw [hRHS]
  have hΩ' : ptOf x + ![v 0, v 1, 0, 0, 0] ∈ Omega := shift_mem_Omega hΩ v
  have hsum : ∀ m' : Fin 3 →₀ ℕ, Summable fun c : PlaneCoset (gammaN N) =>
      (if c = idCoset (gammaN N) then 0 else
        termFun (gammaN N) n f c p.castSucc q.castSucc m' (ptOf x + ![v 0, v 1, 0, 0, 0])) *
        (rho (nmat (-v)) (monomial m' 1)).coeff m := by
    intro m'
    have h0 := summable_termFun_val (gammaN N) (leviGroup N) n f hn hΩ' p.castSucc q.castSucc m'
    have h1 := h0.update (idCoset (gammaN N)) 0
    have h2 : (fun c : PlaneCoset (gammaN N) =>
        if c = idCoset (gammaN N) then 0 else
          termFun (gammaN N) n f c p.castSucc q.castSucc m' (ptOf x + ![v 0, v 1, 0, 0, 0])) =
        Function.update (fun c => termFun (gammaN N) n f c p.castSucc q.castSucc m'
          (ptOf x + ![v 0, v 1, 0, 0, 0])) (idCoset (gammaN N)) 0 := by
      funext c
      by_cases hc : c = idCoset (gammaN N)
      · simp [hc]
      · simp [hc]
    have hs0 : Summable fun c : PlaneCoset (gammaN N) =>
        if c = idCoset (gammaN N) then 0 else
          termFun (gammaN N) n f c p.castSucc q.castSucc m' (ptOf x + ![v 0, v 1, 0, 0, 0]) := by
      rw [h2]; exact h1
    exact hs0.mul_right _
  rw [Summable.tsum_finsetSum (fun m' _ => hsum m')]
  refine Finset.sum_congr rfl fun m' _ => ?_
  unfold restCoeff
  rw [tsum_mul_right]

/-- **Obligation (b), proved for `3 ≤ N`**: the torus average of the non-identity part of the series
vanishes. -/
theorem restAverageVanishes (hN : 3 ≤ N) : RestAverageVanishes N n f hn := by
  unfold RestAverageVanishes
  apply Subtype.ext
  rw [avInv_val]
  show avForm n (N : ℝ) (restFaceForm N n f hn).1 = 0
  apply Form.ext
  intro x hx
  rw [avForm_apply n _ _ hx]
  show avRaw n (N : ℝ) (restFaceForm N n f hn).1 x = 0
  unfold avRaw
  have hcont := continuous_avIntegrand_uncurry n (N : ℝ) (restFaceForm N n f hn).1 hx
  apply ext2Face
  intro p q
  apply Coef.toPoly_injective
  apply MvPolynomial.ext
  intro m
  let Λ : (Face [⋀^Fin 2]→L[ℝ] Coef n) →L[ℝ] ℂ :=
    (polyCoefCLM n m).comp (evalPairCLM n (Pi.single p 1) (Pi.single q 1))
  have h1 := iterIntegral_clm_comm Λ (fun a b => avIntegrand n (N : ℝ) (restFaceForm N n f hn).1
    ((x, a), b)) hcont
  have h2 : Λ (∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..1,
      avIntegrand n (N : ℝ) (restFaceForm N n f hn).1 ((x, a), b)) =
      (Coef.toPoly ((∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..1,
        avIntegrand n (N : ℝ) (restFaceForm N n f hn).1 ((x, a), b))
          ![Pi.single p 1, Pi.single q 1])).coeff m := rfl
  have h3 : ∀ a b : ℝ, Λ (avIntegrand n (N : ℝ) (restFaceForm N n f hn).1 ((x, a), b)) =
      ∑' c : PlaneCoset (gammaN N),
        Fc N n f (ptOf x) p.castSucc q.castSucc m c ((N : ℝ) • ![a, b]) := by
    intro a b
    rw [← coeff_trL_rest N n f hn hx ((N : ℝ) • ![a, b]) p q m]
    show polyCoefCLM n m
      (evalPairCLM n (Pi.single p 1) (Pi.single q 1) (((shiftForm n ((N : ℝ) • ![a, b])
        (restFaceForm N n f hn).1 : Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) x)) = _
    rw [shiftForm_apply n _ _ hx]
    rfl
  have h4 : (Coef.toPoly ((∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..1,
        avIntegrand n (N : ℝ) (restFaceForm N n f hn).1 ((x, a), b))
          ![Pi.single p 1, Pi.single q 1])).coeff m = 0 := by
    rw [← h2, h1]
    simp only [h3]
    exact total_zero N n f hN hn (ptOf_mem hx) _ _ m
  simpa using h4

end TernaryPeriodPolynomials.Argument.EisensteinClass
