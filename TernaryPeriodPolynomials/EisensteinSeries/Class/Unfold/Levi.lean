module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Equivariance

@[expose] public section


/-!
# The seed under an arbitrary parabolic element with a determinant-one Levi block

`summandPoly_parabolic_mul`: for `M = [[A, w], [0, 1]]` with `det A = 1` (not necessarily in the cusp
group of `h`), `S_h(M G) = S_{h|A}(G)`, where `S_h(g) = ρ(g)⁻¹ g^* ω_h` is the summand of the series
and `h|A` is `slashTwisted (n + 3) A h`. This generalizes `summandPoly_stab_mul`, which required
`h|A = h`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open MvPolynomial

theorem formPullback_parabolic_seed (n : ℕ) (h : ℂ → ℂ) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A.det = 1) (w : Fin 2 → ℝ) {p : Fin 5 → ℝ} (hp : 0 < p 3) (i j : Fin 5) :
    formPullback (parabolicMap A w) (seedForm n h) p i j =
      rho (parabolicMatrix A w) (seedForm n (slashTwisted (n + 3) A h) p i j) := by
  unfold parabolicMap
  rw [formPullback_translate, lemma_C3_iii n _ _ 1 (by rw [hA]; exact one_pos) one_pos p hp i j,
    rho_parabolicMatrix _ _ (by rw [hA]; exact one_ne_zero)]

/-- **Left multiplication by a parabolic element changes `h` into `h|A`**:
`S_h(M g) = S_{h|A}(g)` for `M = [[A, w], [0, 1]]`, `det A = 1`. -/
theorem summandPoly_parabolic_mul (n : ℕ) (h : ℂ → ℂ) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A.det = 1) (w : Fin 2 → ℝ) {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : G.det = 1)
    {q : Fin 5 → ℝ} (hq : q ∈ Omega) (i j : Fin 5) :
    summandPoly n h (parabolicMatrix A w * G) q i j =
      summandPoly n (slashTwisted (n + 3) A h) G q i j := by
  set L := parabolicMatrix A w with hLdef
  have hL : L.det = 1 := by rw [hLdef, det_parabolicMatrix, hA]
  have hq' := planeAct_mem hG hq
  have hev : planeAct (L * G) =ᶠ[nhds q] planeAct L ∘ planeAct G :=
    Filter.eventuallyEq_of_mem (isOpen_Omega.mem_nhds hq) fun x hx => planeAct_mul hG hx
  unfold summandPoly
  rw [formPullback_congr _ hev, formPullback_comp _ _ _ q (differentiableAt_planeAct hG hq)
    (differentiableAt_planeAct hL hq') i j]
  have hev2 : planeAct L =ᶠ[nhds (planeAct G q)] parabolicMap A w :=
    Filter.eventuallyEq_of_mem (isOpen_Omega.mem_nhds hq') fun y hy =>
      planeAct_parabolicMatrix A w hA hy
  rw [formPullback_congr_form (Φ := planeAct G)
      (ν' := fun x a b => rho L (seedForm n (slashTwisted (n + 3) A h) x a b)) q
      (fun a b => by
        rw [formPullback_congr _ hev2]
        exact formPullback_parabolic_seed n h A hA w hq'.1 a b) i j, formPullback_rho, rho_mul]
  have hLu : IsUnit L.det := by rw [hL]; exact isUnit_one
  have hinv : (L * G)⁻¹ * L = G⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.nonsing_inv_mul L hLu, Matrix.mul_one]
  rw [hinv]

end TernaryPeriodPolynomials.Argument.EisensteinClass
