module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.CupSeed
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Plane.SourcePackage

@[expose] public section


/-!
# Stokes for the plane seed: the integral cochain as boundary integrals of an orbit-type form

`dual_bridge`: for `a ∈ C²`, `l ∈ C¹` and a bilinear pairing `β`, the antisymmetrised integral of `β(da, dl)` over an
affine triangle is *minus* the boundary combination of the single integrals `J(x,y) = ∫₀¹ β(da_{γ(t)}(y-x), l(γ(t))) dt`
(Stokes for the one-form `β(da, l)`; the dual of `cup_bridge`).  For the plane seed this gives
`plane_stokes` / `planeIntG_stokes`: the Gram-triangle integral cochain is `-∑_ν ρ(M⁻¹)_{κν} (J_ν(Γ₁',Γ₂') - J_ν(Γ₀',Γ₂') +
J_ν(Γ₀',Γ₁'))`, with `J_ν(x,y) = ∫₀¹ F'(τ(γ(t))) K_ν(γ(t), y-x) dt`, `K_ν(G,D) = (∑ⱼ c_j(τ(G)) ℓ_{ν,j}(G)) dτ_G(D)`.
Each `J_ν` is a single orbit-type integral of the datum `F'`, which is what lifts to a Hilbert-space integral of the orbit
of the Eichler vector.

Formalized by Claude Sonnet 5.5.
-/

open scoped Matrix.Norms.Elementwise
open MeasureTheory Set MvPolynomial Matrix
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

section DualBridge

variable {E A B F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup A]
  [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F]

/-- **The dual Stokes bridge.**  For a `C²` function `a` and a `C¹` function `l` on an open set `U` containing the
affine triangle `[y₀, y₁, y₂]`, and a bilinear pairing `β`: the antisymmetrised integral of `β(da, dl)` over the
triangle is minus the boundary integral of the one-form `β(da, l)`:
`∫_Δ (β(da(y₁-y₀), dl(y₂-y₀)) - β(da(y₂-y₀), dl(y₁-y₀))) = -(J(y₁,y₂) - J(y₀,y₂) + J(y₀,y₁))`,
`J(x,y) = ∫₀¹ β(da_{γ(t)}(y-x), l(γ(t))) dt`. -/
theorem dual_bridge (β : A →L[ℝ] B →L[ℝ] F) (a : E → A) (l : E → B) (U : Set E) (hU : IsOpen U)
    (ha : ContDiffOn ℝ 2 a U) (hl : ContDiffOn ℝ 1 l U) (y₀ y₁ y₂ : E)
    (hT : ∀ p ∈ stdTriangle, affTri y₀ y₁ y₂ p ∈ U) :
    ∫ p in stdTriangle,
        (β (fderiv ℝ a (affTri y₀ y₁ y₂ p) (y₁ - y₀)) (fderiv ℝ l (affTri y₀ y₁ y₂ p) (y₂ - y₀)) -
          β (fderiv ℝ a (affTri y₀ y₁ y₂ p) (y₂ - y₀)) (fderiv ℝ l (affTri y₀ y₁ y₂ p) (y₁ - y₀))) =
      -((∫ t in (0 : ℝ)..1, β (fderiv ℝ a (y₁ + t • (y₂ - y₁)) (y₂ - y₁)) (l (y₁ + t • (y₂ - y₁)))) -
        (∫ t in (0 : ℝ)..1, β (fderiv ℝ a (y₀ + t • (y₂ - y₀)) (y₂ - y₀)) (l (y₀ + t • (y₂ - y₀)))) +
        (∫ t in (0 : ℝ)..1, β (fderiv ℝ a (y₀ + t • (y₁ - y₀)) (y₁ - y₀)) (l (y₀ + t • (y₁ - y₀))))) := by
  have hη := contDiffOn_cupForm β.flip l a U hU hl ha
  have hst := stokes_affine_triangle (cupForm β.flip l a) U hU hη y₀ y₁ y₂ hT
  have hint : ∫ p in stdTriangle,
        (β (fderiv ℝ a (affTri y₀ y₁ y₂ p) (y₁ - y₀)) (fderiv ℝ l (affTri y₀ y₁ y₂ p) (y₂ - y₀)) -
          β (fderiv ℝ a (affTri y₀ y₁ y₂ p) (y₂ - y₀)) (fderiv ℝ l (affTri y₀ y₁ y₂ p) (y₁ - y₀))) =
      -∫ p in stdTriangle, (fderiv ℝ (cupForm β.flip l a) (y₀ + p.1 • (y₁ - y₀) + p.2 • (y₂ - y₀)) (y₁ - y₀) (y₂ - y₀) -
          fderiv ℝ (cupForm β.flip l a) (y₀ + p.1 • (y₁ - y₀) + p.2 • (y₂ - y₀)) (y₂ - y₀) (y₁ - y₀)) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_stdTriangle (fun p hp => ?_)
    have hpU : affTri y₀ y₁ y₂ p ∈ U := hT p hp
    have := fderiv_cupForm_antisymm β.flip l a U hU hl ha hpU (y₁ - y₀) (y₂ - y₀)
    simp only [ContinuousLinearMap.flip_apply] at this
    show _ = -(fderiv ℝ (cupForm β.flip l a) (affTri y₀ y₁ y₂ p) (y₁ - y₀) (y₂ - y₀) -
      fderiv ℝ (cupForm β.flip l a) (affTri y₀ y₁ y₂ p) (y₂ - y₀) (y₁ - y₀))
    rw [this]
    abel
  rw [hint, hst]
  congr 1

end DualBridge



section PlaneStokes

/-- The coefficient of the potential in the dual boundary form: `K_μ(G, D) = (∑ⱼ c_j(τ(G)) ℓ_{μ,j}(G)) · dτ_G(D)`. -/
def Kfun (n : ℕ) (μ : Fin 3 →₀ ℕ) (G D : Mat3) : ℂ :=
  (∑ j, pointCoord n (gramPlaneTau G) j * lFun n μ G j) * planeDTau G D

/-- The boundary integral of the dual one-form along the segment `x → y`. -/
def Jpl (n : ℕ) (F' : ℂ → ℂ) (μ : Fin 3 →₀ ℕ) (x y : Mat3) : ℂ :=
  ∫ t in (0 : ℝ)..1, F' (gramPlaneTau (x + t • (y - x))) * Kfun n μ (x + t • (y - x)) (y - x)

theorem isSymm_segment {x y : Mat3} (hx : x.IsSymm) (hy : y.IsSymm) (t : ℝ) : (x + t • (y - x)).IsSymm := by
  unfold Matrix.IsSymm at *
  rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_sub, hx, hy]

theorem Jpl_eq {n : ℕ} {F' : ℂ → ℂ} (P : PotentialDatum n F') (μ : Fin 3 →₀ ℕ) {x y : Mat3}
    (hx : x.IsSymm) (hy : y.IsSymm) (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (y - x) ∈ gramDomain) :
    (∫ t in (0 : ℝ)..1, PotentialDatum.dotPairing (n + 2) (fderiv ℝ P.aFun (x + t • (y - x)) (y - x))
        (lFun n μ (x + t • (y - x)))) = Jpl n F' μ x y := by
  unfold Jpl
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [uIcc_of_le zero_le_one] at ht
  have hsy : (y - x).IsSymm := by
    unfold Matrix.IsSymm at *
    rw [Matrix.transpose_sub, hx, hy]
  simp only [PotentialDatum.dotPairing_apply, P.fderiv_aFun_apply (hseg t ht) (isSymm_segment hx hy t) _ hsy,
    Kfun, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Stokes for the plane seed.**  The integral over a Gram triangle of the coefficient `μ` of the seed form
`ω_h`, `h = (-1)ⁿ (n+1) F'`, is minus the boundary combination of the single integrals `Jpl`. -/
theorem plane_stokes {n : ℕ} {F' : ℂ → ℂ} (P : PotentialDatum n F') (μ : Fin 3 →₀ ℕ) (G₀ G₁ G₂ : Mat3)
    (h₀ : G₀.IsSymm) (h₁ : G₁.IsSymm) (h₂ : G₂.IsSymm)
    (hT : ∀ p ∈ stdTriangle, affTri G₀ G₁ G₂ p ∈ gramDomain) :
    ∫ p in stdTriangle, (formPair
        (seedForm n (fun z => (-1) ^ n * ((n + 1 : ℕ) : ℂ) * F' z)) (affTri G₀ G₁ G₂ p) (G₁ - G₀) (G₂ - G₀)).coeff μ =
      -(Jpl n F' μ G₁ G₂ - Jpl n F' μ G₀ G₂ + Jpl n F' μ G₀ G₁) := by
  have key := dual_bridge (PotentialDatum.dotPairing (n + 2)) P.aFun (lFun n μ) gramDomain isOpen_gramDomain
    (P.contDiffOn_aFun.of_le (by simp)) ((contDiffOn_lFun n μ).of_le (by simp)) G₀ G₁ G₂ hT
  have e12 : ∀ t ∈ Icc (0 : ℝ) 1, G₁ + t • (G₂ - G₁) ∈ gramDomain := by
    intro t ht
    have := hT (1 - t, t) ⟨by linarith [ht.2], ht.1, by linarith⟩
    convert this using 1
    simp only [affTri]
    module
  have e02 : ∀ t ∈ Icc (0 : ℝ) 1, G₀ + t • (G₂ - G₀) ∈ gramDomain := by
    intro t ht
    have := hT (0, t) ⟨le_refl _, ht.1, by linarith [ht.2]⟩
    convert this using 1
    simp [affTri]
  have e01 : ∀ t ∈ Icc (0 : ℝ) 1, G₀ + t • (G₁ - G₀) ∈ gramDomain := by
    intro t ht
    have := hT (t, 0) ⟨ht.1, le_refl _, by linarith [ht.2]⟩
    convert this using 1
    simp [affTri]
  rw [← Jpl_eq P μ h₁ h₂ e12, ← Jpl_eq P μ h₀ h₂ e02, ← Jpl_eq P μ h₀ h₁ e01]
  refine Eq.trans ?_ key
  have hS : ∀ p ∈ stdTriangle, (affTri G₀ G₁ G₂ p).IsSymm := by
    intro p _
    unfold affTri Matrix.IsSymm at *
    simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_sub, h₀, h₁, h₂]
  refine setIntegral_congr_fun measurableSet_stdTriangle fun p hp => ?_
  have := P.cup_form_eq_seed μ (hT p hp) (hS p hp) (G₁ - G₀) (G₂ - G₀)
    (by unfold Matrix.IsSymm at *; simp [Matrix.transpose_sub, h₀, h₁])
    (by unfold Matrix.IsSymm at *; simp [Matrix.transpose_sub, h₀, h₂])
  rw [← this]
  simp only [PotentialDatum.dotPairing_apply, ← Finset.sum_sub_distrib]
  rfl


theorem gramDomain_of_posDef {Γ : Mat3} (h : Γ.PosDef) : Γ ∈ gramDomain :=
  cholDomain_subset_gramDomain (posDef_transpose h) (posDef_mem_cholDomain h)

/-- **The plane integral cochain as a combination of boundary integrals.**  For an invertible `M`, positive
definite `Γ₀, Γ₁, Γ₂` and the seed `h = (-1)ⁿ (n+1) F'` of a potential datum:
`planeIntG h M Γ₀ Γ₁ Γ₂ κ = -∑_ν ρ(M⁻¹)_{κν} (J(Γ₁',Γ₂') - J(Γ₀',Γ₂') + J(Γ₀',Γ₁'))`, `Γᵢ' = M Γᵢ Mᵀ`. -/
theorem planeIntG_stokes {n : ℕ} {F' : ℂ → ℂ} (P : PotentialDatum n F')
    (hF : ContinuousOn F' {z : ℂ | 0 < z.im}) (M Γ₀ Γ₁ Γ₂ : Mat3) (hM : M.det ≠ 0)
    (p₀ : Γ₀.PosDef) (p₁ : Γ₁.PosDef) (p₂ : Γ₂.PosDef) (κ : Fin 3 →₀ ℕ) :
    planeIntG n (fun z => (-1) ^ n * ((n + 1 : ℕ) : ℂ) * F' z) M Γ₀ Γ₁ Γ₂ κ =
      -∑ ν ∈ degSet n, (SeedC3.rho M⁻¹ (MvPolynomial.monomial ν 1)).coeff κ *
        (Jpl n F' ν (M * Γ₁ * Mᵀ) (M * Γ₂ * Mᵀ) - Jpl n F' ν (M * Γ₀ * Mᵀ) (M * Γ₂ * Mᵀ) +
          Jpl n F' ν (M * Γ₀ * Mᵀ) (M * Γ₁ * Mᵀ)) := by
  set hh : ℂ → ℂ := fun z => (-1) ^ n * ((n + 1 : ℕ) : ℂ) * F' z with hhdef
  set G0 : Mat3 := M * Γ₀ * Mᵀ with hG0
  set G1 : Mat3 := M * Γ₁ * Mᵀ with hG1
  set G2 : Mat3 := M * Γ₂ * Mᵀ with hG2
  have q0 : G0.PosDef := posDef_congr p₀ hM
  have q1 : G1.PosDef := posDef_congr p₁ hM
  have q2 : G2.PosDef := posDef_congr p₂ hM
  have hcond := affTri_mem_cholDomain q0 q1 q2
  have hdom : ∀ p ∈ stdTriangle, affTri G0 G1 G2 p ∈ gramDomain := fun p hp =>
    cholDomain_subset_gramDomain (posDef_transpose (posDef_affTri q0 q1 q2 hp)) (hcond p hp)
  have s0 : G0ᵀ = G0 := posDef_transpose q0
  have s1 : G1ᵀ = G1 := posDef_transpose q1
  have s2 : G2ᵀ = G2 := posDef_transpose q2
  have hQ1 : M * (Γ₁ - Γ₀) * Mᵀ = G1 - G0 := by
    simp only [hG0, hG1, Matrix.mul_sub, Matrix.sub_mul]
  have hQ2 : M * (Γ₂ - Γ₀) * Mᵀ = G2 - G0 := by
    simp only [hG0, hG2, Matrix.mul_sub, Matrix.sub_mul]
  have hP : ∀ p, M * affTri Γ₀ Γ₁ Γ₂ p * Mᵀ = affTri G0 G1 G2 p := fun p =>
    (affTri_congr M Γ₀ Γ₁ Γ₂ p).symm
  have hint : planeIntG n hh M Γ₀ Γ₁ Γ₂ κ =
      ∑ ν ∈ degSet n, (∫ p in stdTriangle, (formPair (seedForm n hh)
        (affTri G0 G1 G2 p) (G1 - G0) (G2 - G0)).coeff ν) *
          (SeedC3.rho M⁻¹ (MvPolynomial.monomial ν 1)).coeff κ := by
    unfold planeIntG twPull
    simp_rw [hP, hQ1, hQ2]
    refine integral_coeff_rho _ n _ _ (fun p => isHomogeneous_formPair_seed n hh _ _ _) (fun ν => ?_) κ
    have hc : ContinuousOn (fun p : ℝ × ℝ => (formPair (seedForm n hh)
        (affTri G0 G1 G2 p) (G1 - G0) (G2 - G0)).coeff ν) stdTriangle := by
      have hhc : ContinuousOn hh {z : ℂ | 0 < z.im} := by
        simp only [hhdef]
        exact continuousOn_const.mul hF
      have hQs1 : (G1 - G0)ᵀ = G1 - G0 := by rw [Matrix.transpose_sub, s1, s0]
      have hQs2 : (G2 - G0)ᵀ = G2 - G0 := by rw [Matrix.transpose_sub, s2, s0]
      exact continuousOn_coeff_formPair_comp n hh hhc _ _ _ (continuous_affTri G0 G1 G2).continuousOn
        continuousOn_const continuousOn_const
        (fun p hp => ⟨hdom p hp, posDef_transpose (posDef_affTri q0 q1 q2 hp), hQs1, hQs2⟩) ν
    exact hc.integrableOn_compact isCompact_stdTriangle
  rw [hint, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [plane_stokes P ν G0 G1 G2 s0 s1 s2 hdom]
  ring

end PlaneStokes

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
