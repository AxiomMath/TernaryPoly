module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.ConvergenceC4
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.PlaneRep
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.ZigZagMain

@[expose] public section


/-!
# The group, its action on `Ω ≅ 𝒳` and its coefficient representation (Appendix C.3, C.4)

The form `ℰ_P(ω_h)` is a closed `Γ`-equivariant `E`-valued two-form on
`𝒳 = SL₃(ℝ)/SO(3)`, hence has a class in `H²(X_Γ, E) = H²(Γ, E)`.

For a subgroup `Γ ⊂ SL₃(ℤ)` this file sets up, in the vocabulary of the de Rham zig-zag
`SeedC3.ZigZag`:

* `convex_Omega`, `Omega_nonempty`: `Ω = {p ∈ ℝ⁵ : p₃ > 0, p₄ > 0}` (open by `ConvergenceC4.isOpen_Omega`)
  is convex and nonempty;
* `gammaAct Γ : ZigZag.Action Γ Ω`, `δ ↦ planeAct (realMat δ)` (the action of `SL₃(ℤ)` on the chart);
* `gammaRho Γ n : Representation ℝ Γ (Coef n)`, the real form of `ρ(δ) q(𝐗) = det(δ)⁻¹ q(δ⁻¹𝐗)` on the
  normed model `Coef n` of `E_n`, with `Coef.toPoly (gammaRho Γ n δ q) = SeedC3.rho (realMat δ) q`.

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial GeneralEisenstein
open scoped ContDiff MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3

/-! ### The domain `Ω` -/

theorem convex_Omega : Convex ℝ Omega := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx3, hx4⟩ := hx
  obtain ⟨hy3, hy4⟩ := hy
  have key : ∀ u v : ℝ, 0 < u → 0 < v → 0 < a * u + b * v := by
    intro u v hu hv
    rcases ha.eq_or_lt with rfl | ha'
    · have : b = 1 := by linarith
      subst this; simpa using hv
    · have h1 : 0 < a * u := mul_pos ha' hu
      have h2 : 0 ≤ b * v := mul_nonneg hb hv.le
      linarith
  exact ⟨by simpa using key _ _ hx3 hy3, by simpa using key _ _ hx4 hy4⟩

theorem Omega_nonempty : Omega.Nonempty := ⟨basePt, basePt_mem⟩

/-! ### The action of a subgroup of `SL₃(ℤ)` on `Ω` -/

theorem contDiffOn_planeAct (g : Matrix (Fin 3) (Fin 3) ℝ) (hg : g.det = 1) :
    ContDiffOn ℝ ∞ (planeAct g) Omega := by
  intro p hp
  have h1 := contDiffAt_planeAct_pair hg hp
  have h2 : ContDiffAt ℝ ⊤ (fun y : Fin 5 → ℝ => (matToFun g, y)) p :=
    contDiffAt_const.prodMk contDiffAt_id
  have h3 := h1.comp p h2
  exact (h3.of_le le_top).contDiffWithinAt

/-- The action of `Γ ⊂ SL₃(ℤ)` on the chart `Ω`, `δ ↦ planeAct (realMat δ)`. -/
def gammaAct (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) :
    SeedC3.ZigZag.Action Γ Omega where
  act δ := planeAct (realMat δ.1)
  smooth δ := contDiffOn_planeAct _ (det_realMat δ.1)
  mapsTo δ _ hp := planeAct_mem (det_realMat δ.1) hp
  mul g h p hp := by
    change planeAct (realMat (g.1 * h.1)) p = planeAct (realMat g.1) (planeAct (realMat h.1) p)
    rw [realMat_mul]
    exact planeAct_mul (det_realMat h.1) hp

theorem gammaAct_act (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) (δ : Γ)
    (p : Fin 5 → ℝ) : (gammaAct Γ).act δ p = planeAct (realMat δ.1) p := rfl

/-! ### The coefficient representation -/

/-- The real matrix of an element of `Γ ⊂ SL₃(ℤ)` as an element of `GL₃(ℝ)`. -/
def gammaSigma (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) : Γ →* GL (Fin 3) ℝ :=
  (Matrix.SpecialLinearGroup.mapGL ℝ).comp Γ.subtype

theorem gammaSigma_val (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) (δ : Γ) :
    ((gammaSigma Γ δ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) = realMat δ.1 := by
  rw [show ((gammaSigma Γ δ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) =
    (Matrix.SpecialLinearGroup.mapGL ℝ δ.1 : GL (Fin 3) ℝ) from rfl,
    Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  ext i j
  simp [realMat]

/-- The complex-linear coefficient representation of `Γ` on `E_n = Sym^n ⊗ det⁻¹`. -/
def gammaRhoC (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) (n : ℕ) :
    Representation ℂ Γ (HomogeneousPoly n) :=
  (GeneralEisenstein.realCoefficient n).comp (gammaSigma Γ)

/-- **The coefficient action on polynomials is `SeedC3.rho (realMat δ)`.** -/
theorem gammaRhoC_coe (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) (n : ℕ) (δ : Γ)
    (q : HomogeneousPoly n) :
    ((gammaRhoC Γ n δ q : HomogeneousPoly n) : MvPolynomial (Fin 3) ℂ) =
      rho (realMat δ.1) (q : MvPolynomial (Fin 3) ℂ) := by
  have hdet : (realMat δ.1).det = 1 := det_realMat δ.1
  have hd : ((realMat δ.1).map Complex.ofReal).det = 1 := by
    have := RingHom.map_det Complex.ofRealHom (realMat δ.1)
    rw [hdet, map_one] at this
    exact this.symm
  unfold gammaRhoC
  change ((GeneralEisenstein.action (-1)
    (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) (gammaSigma Γ δ)))
      (q : MvPolynomial (Fin 3) ℂ)) = _
  rw [GeneralEisenstein.action_apply]
  unfold rho GeneralEisenstein.substitute GeneralEisenstein.linearForm
  rw [hdet]
  simp [GeneralEisenstein.determinantCharacter, Matrix.GeneralLinearGroup.map]
  rw [gammaSigma_val, hd, inv_one, one_smul]

/-- The coefficient action on the normed model `Coef n` of `E_n`, complex linear. -/
def gammaRhoCoef (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) (n : ℕ) (δ : Γ) :
    Coef n →ₗ[ℂ] Coef n := gammaRhoC Γ n δ

theorem toPoly_gammaRhoCoef (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) (n : ℕ) (δ : Γ)
    (q : Coef n) :
    Coef.toPoly (gammaRhoCoef Γ n δ q) = rho (realMat δ.1) (Coef.toPoly q) :=
  gammaRhoC_coe Γ n δ q

/-- **The real coefficient representation of `Γ`**: `ρ(δ) q(𝐗) = det(δ)⁻¹ q(δ⁻¹𝐗)` on the normed
model `Coef n` of `E_n` (the complex representation `gammaRhoC`, regarded over `ℝ`). -/
def gammaRho (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) (n : ℕ) :
    Representation ℝ Γ (Coef n) where
  toFun g := (gammaRhoCoef Γ n g).restrictScalars ℝ
  map_one' := by
    ext q
    change gammaRhoC Γ n 1 q = q
    rw [map_one]; rfl
  map_mul' g k := by
    ext q
    change gammaRhoC Γ n (g * k) q = gammaRhoC Γ n g (gammaRhoC Γ n k q)
    rw [map_mul]; rfl

theorem gammaRho_apply (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) (n : ℕ) (δ : Γ)
    (q : Coef n) : gammaRho Γ n δ q = gammaRhoCoef Γ n δ q := rfl

theorem toPoly_gammaRho (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) (n : ℕ) (δ : Γ)
    (q : Coef n) :
    Coef.toPoly (gammaRho Γ n δ q) = rho (realMat δ.1) (Coef.toPoly q) :=
  toPoly_gammaRhoCoef Γ n δ q

end TernaryPeriodPolynomials.Argument.EisensteinClass
