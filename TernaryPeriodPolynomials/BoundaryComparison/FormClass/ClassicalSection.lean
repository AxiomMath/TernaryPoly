module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.KBruhat
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.SLSurjective
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.IntegralReduction

@[expose] public section


/-!
# (A) The classical induced section: values, transform law, congruence-coset indexing

Formalized by Claude Sonnet 5.5.
Paper: `ar:eq:seed-transform`, `ar:eq:Eseries`.

`sectionClR n h g := ρ(g)⁻¹ g^* ω_h` (the `summandPoly`) is the value at `g ∈ SL₃` of the classical induced section of the seed `h`; its values are `E`-valued forms on `Ω`.
* `sectionCl_planeStab_mul` (transform law, positive Levi sign): for `M ∈ P(ℤ)` (bottom row `(0,0,1)`), `Φ_h(Mγ) = Φ_{h|A_M}(γ)`; `sectionCl_neg_mul`: bottom-right entry `-1`.
* `sectionCl_gammaNP_mul`: for `M ∈ Γ_P = Γ(N) ∩ P(ℤ)` and `h = f ∘ ofComplex`, `Φ_h(Mγ) = Φ_h(γ)` (well-definedness on `Γ_P\\SL₃(ℤ)`).
* `sectionCl_mul_right`: `Φ_h(γδ) = ρ(δ)⁻¹ δ^* Φ_h(γ)` (the cocycle law, i.e. right translation in the invariant-frame trivialization).
* `reduction_eq_iff`, `liftSL`: `SL₃(ℤ)/Γ(N) = SL₃(ℤ/N)`; the finite component of `γ` is its class in `SL₃(ℤ/N)`.
* `PhiQ0_eq_sectionClR`: the summands `PhiQ0` of `lineA1K` are exactly the values of this section on the real `k γ_c qMat u`.
-/

open scoped MatrixGroups
open MvPolynomial
noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3S4c
  TernaryPeriodPolynomials.Argument.GammaNFaces
open ComplexConjugate

variable (n : ℕ)

/-- **The classical induced section** at a real matrix `g`: the `E`-valued form `ρ(g)⁻¹ g^* ω_h`. -/
abbrev sectionClR (h : ℂ → ℂ) (g : Matrix (Fin 3) (Fin 3) ℝ) (y : Fin 5 → ℝ) (a b : Fin 5) : MvPolynomial (Fin 3) ℂ :=
  summandPoly n h g y a b

/-- The classical induced section at an element of `SL₃(ℤ)`. -/
abbrev sectionCl (h : ℂ → ℂ) (γ : SL(3, ℤ)) (y : Fin 5 → ℝ) (a b : Fin 5) : MvPolynomial (Fin 3) ℂ :=
  sectionClR n h (realMat γ) y a b

/-- **Transform law (positive sign).** -/
theorem sectionCl_planeStab_mul (h : ℂ → ℂ) {M : SL(3, ℤ)} (hM : M ∈ planeStab) (γ : SL(3, ℤ))
    {y : Fin 5 → ℝ} (hy : y ∈ Omega) (a b : Fin 5) :
    sectionCl n h (M * γ) y a b =
      sectionCl n (slashTwisted (n + 3) (topBlock (realMat M)) h) γ y a b := by
  obtain ⟨h0, h1, h2⟩ := hM
  have e0 : (realMat M) 2 0 = 0 := by simp [realMat_apply, h0]
  have e1 : (realMat M) 2 1 = 0 := by simp [realMat_apply, h1]
  have e2 : 0 < (realMat M) 2 2 := by simp [realMat_apply, h2]
  change summandPoly n h (realMat (M * γ)) y a b = _
  rw [realMat_mul]
  exact summandPoly_bottom_mul n h (det_realMat M) e0 e1 e2 (det_realMat γ) hy a b

/-- **Transform law (negative sign).** -/
theorem sectionCl_neg_mul (h : ℂ → ℂ) {M : SL(3, ℤ)}
    (h0 : (M : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0) (h1 : (M : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = 0)
    (h2 : (M : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = -1) (γ : SL(3, ℤ)) {y : Fin 5 → ℝ} (hy : y ∈ Omega) (a b : Fin 5) :
    sectionCl n h (M * γ) y a b =
      cxP true (sectionCl n (hStar (slashTwisted (n + 3) (topBlock (realMat M * realMat rPrime)) h)) γ y a b) := by
  have e0 : (realMat M) 2 0 = 0 := by simp [realMat_apply, h0]
  have e1 : (realMat M) 2 1 = 0 := by simp [realMat_apply, h1]
  have e2 : (realMat M) 2 2 < 0 := by simp [realMat_apply, h2]
  change summandPoly n h (realMat (M * γ)) y a b = _
  rw [realMat_mul]
  exact summandPoly_bottom_neg_mul n h (det_realMat M) e0 e1 e2 (det_realMat γ) hy a b

/-- **Left invariance under `Γ_P = Γ(N) ∩ P(ℤ)`** for the section of a cusp form of `Γ₂(N)`. -/
theorem sectionCl_gammaNP_mul (N : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) {M : SL(3, ℤ)}
    (hM : M ∈ gammaNP N) (γ : SL(3, ℤ)) {y : Fin 5 → ℝ} (hy : y ∈ Omega) (a b : Fin 5) :
    sectionCl n (hfun f) (M * γ) y a b = sectionCl n (hfun f) γ y a b := by
  change summandPoly n (hfun f) (realMat (M * γ)) y a b = summandPoly n (hfun f) (realMat γ) y a b
  exact summandPoly_stab_mul (leviGroup N) n f M γ hM.2 (leviIn_gammaN N M hM.1 hM.2) hy a b

/-- **Right translation (the cocycle law).** -/
theorem sectionCl_mul_right (h : ℂ → ℂ) (γ δ : SL(3, ℤ)) {y : Fin 5 → ℝ} (hy : y ∈ Omega) (a b : Fin 5) :
    sectionCl n h (γ * δ) y a b =
      rho (realMat δ)⁻¹ (formPullback (planeAct (realMat δ)) (fun y' a' b' => sectionCl n h γ y' a' b') y a b) := by
  change summandPoly n h (realMat (γ * δ)) y a b = _
  rw [realMat_mul]
  exact summandPoly_mul_eq n h (det_realMat γ) (det_realMat δ) hy a b

section Reduction

variable (N : ℕ) [NeZero N]

/-- The finite component of `γ ∈ SL₃(ℤ)`: its class in `SL₃(ℤ/N)`. -/
abbrev finComp (γ : SL(3, ℤ)) : SL(3, ZMod N) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ

/-- A lift of a class of `SL₃(ℤ/N)` (`sl3_map_surjective`). -/
def liftSL (x : SL(3, ZMod N)) : SL(3, ℤ) := (sl3_map_surjective N x).choose

theorem finComp_liftSL (x : SL(3, ZMod N)) : finComp N (liftSL N x) = x := (sl3_map_surjective N x).choose_spec

omit [NeZero N] in
/-- `Γ(N)` is the kernel of the reduction `SL₃(ℤ) → SL₃(ℤ/N)`. -/
theorem mem_gammaN_iff_finComp (δ : SL(3, ℤ)) : δ ∈ gammaN N ↔ finComp N δ = 1 := by
  constructor
  · intro h
    apply Subtype.ext
    ext i j
    have := entry_eq_of_mem_gammaN h i j
    simpa [Matrix.one_apply] using this
  · intro h
    rw [mem_gammaN]
    intro i j
    have := congrArg (fun x : SL(3, ZMod N) => (x : Matrix (Fin 3) (Fin 3) (ZMod N)) i j) h
    simp only [Matrix.SpecialLinearGroup.coe_one] at this
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub]
    have e : ((((δ : Matrix (Fin 3) (Fin 3) ℤ) i j : ℤ)) : ZMod N) = (1 : Matrix (Fin 3) (Fin 3) (ZMod N)) i j := this
    rw [e]
    simp [Matrix.one_apply]

omit [NeZero N] in
/-- **The finite components are the cosets of `Γ(N)`**: equal reductions iff `γ⁻¹ γ' ∈ Γ(N)`. -/
theorem finComp_eq_iff (γ γ' : SL(3, ℤ)) : finComp N γ = finComp N γ' ↔ γ⁻¹ * γ' ∈ gammaN N := by
  rw [mem_gammaN_iff_finComp]
  change _ ↔ Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) (γ⁻¹ * γ') = 1
  rw [map_mul, map_inv, inv_mul_eq_one, eq_comm]

omit [NeZero N] in
/-- **Sections with the same finite component differ by a `Γ(N)`-translation**: `Φ_h(γ δ) = ρ(δ)⁻¹ δ^* Φ_h(γ)`. -/
theorem sectionCl_finComp (h : ℂ → ℂ) {γ γ' : SL(3, ℤ)} (hγ : finComp N γ = finComp N γ') {y : Fin 5 → ℝ}
    (hy : y ∈ Omega) (a b : Fin 5) :
    ∃ δ ∈ gammaN N, sectionCl n h γ' y a b =
      rho (realMat δ)⁻¹ (formPullback (planeAct (realMat δ)) (fun y' a' b' => sectionCl n h γ y' a' b') y a b) := by
  refine ⟨γ⁻¹ * γ', (finComp_eq_iff N γ γ').1 hγ, ?_⟩
  have := sectionCl_mul_right n h γ (γ⁻¹ * γ') hy a b
  rwa [mul_inv_cancel_left] at this

end Reduction

section LineK

variable (N : ℕ) [NeZero N] (k : SL(3, ℤ)) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

omit [NeZero N] in
/-- **The summands of `lineA1K` are values of the classical induced section** at the real matrix `k γ_c qMat w`. -/
theorem PhiQ0_eq_sectionClR (x : Face) (p q : Fin 4) (m : Fin 3 →₀ ℕ) (c : Ck N k) (w : Fin 2 → ℝ) :
    PhiQ0 N k n f x p q m c w =
      (fPull jFace (fun y a b => sectionClR n (hfun f) (realMat k * realMat (Quotient.out c).1 * qMat w) y a b) x p q).coeff m :=
  rfl

end LineK

end TernaryPeriodPolynomials.Argument.FormClassK
