module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.RationalDecomp

@[expose] public section


/-!
# (B), step 3: the adelic section and its invariances

Formalized by Claude Sonnet 5.5.
Paper: `ar:eq:seed-transform`.

`adelicSection N n h gR g_f` is `ρ(π_∞⁻¹ gR)⁻¹ (π_∞⁻¹ gR)^* ω_h` when `g_f = π κ` with `π` a determinant-one rational plane-parabolic element and `κ ∈ K(N)`, and `0` otherwise (the section is supported on `P(ℚ) K(N)`; `N ≥ 3`, so that two decompositions differ by `Γ_P`).
* `adelicSection_of_decomp`: the value does not depend on the decomposition (two decompositions differ by `Γ_P`, which fixes the section of a cusp form of `Γ₂(N)`).
* `adelicSection_mul_ker`: right `K(N)`-invariance; `adelicSection_planeDet_mul`: left `P₁(ℚ)`-invariance.
-/

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.IntegralReduction
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.EisensteinClass
open UpperHalfPlane ModularForm

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

/-- The real matrix of a rational matrix. -/
def ratReal (π : GL3 ℚ) : Matrix (Fin 3) (Fin 3) ℝ := (Rat.castHom ℝ).mapMatrix π.val

theorem ratReal_apply (π : GL3 ℚ) (i j : Fin 3) : ratReal π i j = ((π.val i j : ℚ) : ℝ) := rfl

theorem ratReal_mul (π σ : GL3 ℚ) : ratReal (π * σ) = ratReal π * ratReal σ := by
  simp [ratReal, map_mul]

theorem ratReal_one : ratReal 1 = 1 := by simp [ratReal]

theorem ratReal_inv_mul (π : GL3 ℚ) : ratReal π⁻¹ * ratReal π = 1 := by
  rw [← ratReal_mul, inv_mul_cancel, ratReal_one]

theorem ratReal_det {π : GL3 ℚ} (h : π.val.det = 1) : (ratReal π).det = 1 := by
  rw [ratReal, ← RingHom.map_det, h]; simp

theorem ratReal_mapGL (w : SL(3, ℤ)) :
    ratReal (Matrix.SpecialLinearGroup.mapGL ℚ w) = realMat w := by
  ext i j
  rw [ratReal_apply, realMat_apply, Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  simp

/-- **Left `Γ_P`-invariance of the section at a real matrix**, for a cusp form of `Γ₂(N)`. -/
theorem sectionClR_gammaNP_mulR (n N : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) {M : SL(3, ℤ)}
    (hM : M ∈ gammaNP N) {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : G.det = 1) {q : Fin 5 → ℝ}
    (hq : q ∈ Omega) (i j : Fin 5) :
    summandPoly n (hfun f) (realMat M * G) q i j = summandPoly n (hfun f) G q i j := by
  have hL : (realMat M).det = 1 := det_realMat M
  have hq' := planeAct_mem hG hq
  have hev : planeAct (realMat M * G) =ᶠ[nhds q] planeAct (realMat M) ∘ planeAct G :=
    Filter.eventuallyEq_of_mem (isOpen_Omega.mem_nhds hq) fun x hx => planeAct_mul hG hx
  unfold summandPoly hfun
  rw [formPullback_congr _ hev,
    formPullback_comp _ _ _ q (differentiableAt_planeAct hG hq)
      (differentiableAt_planeAct hL hq') i j]
  rw [formPullback_congr_form (Φ := planeAct G)
      (ν' := fun x a b => SeedC3.rho (realMat M) (seedForm n (fun z => f (ofComplex z)) x a b)) q
      (fun a b => formPullback_stab (leviGroup N) n f M hM.2 (leviIn_gammaN N M hM.1 hM.2) hq' a b) i j,
    ConvergenceC4.formPullback_rho, rho_mul]
  have hLu : IsUnit (realMat M).det := by rw [hL]; exact isUnit_one
  have hinv : (realMat M * G)⁻¹ * realMat M = G⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.nonsing_inv_mul (realMat M) hLu, Matrix.mul_one]
  rw [hinv]

variable (N : ℕ) [NeZero N]

open Classical in
/-- **The adelic induced section** of the seed `h`: supported on `P₁(ℚ) K(N)`, and there equal to
the classical section at `π_∞⁻¹ g_∞` for any decomposition `g_f = π κ`. -/
def adelicSection (n : ℕ) (h : ℂ → ℂ) (gR : Matrix (Fin 3) (Fin 3) ℝ) (gf : FiniteGL)
    (y : Fin 5 → ℝ) (a b : Fin 5) : MvPolynomial (Fin 3) ℂ :=
  if hd : ∃ π κ, IsDecomp N gf π κ then sectionClR n h (ratReal hd.choose⁻¹ * gR) y a b else 0

omit [NeZero N] in
theorem ratReal_inv_det {π : GL3 ℚ} (hπ : PlaneDet π) : (ratReal π⁻¹).det = 1 :=
  ratReal_det hπ.inv.det

/-- **Independence of the decomposition.** -/
theorem adelicSection_of_decomp (hN : 3 ≤ N) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))
    {gR : Matrix (Fin 3) (Fin 3) ℝ} (hg : gR.det = 1) {gf : FiniteGL} {π : GL3 ℚ}
    {κ : GL3 IntegralAdeles} (hd : IsDecomp N gf π κ) {y : Fin 5 → ℝ} (hy : y ∈ Omega) (a b : Fin 5) :
    adelicSection N n (hfun f) gR gf y a b = sectionClR n (hfun f) (ratReal π⁻¹ * gR) y a b := by
  have hex : ∃ π κ, IsDecomp N gf π κ := ⟨π, κ, hd⟩
  unfold adelicSection
  rw [dite_eq_left hex]
  obtain ⟨κ0, hd0⟩ := hex.choose_spec
  obtain ⟨w, hw, hwe⟩ := decomp_ratio N hN hd0 hd
  have e : hex.choose⁻¹ = Matrix.SpecialLinearGroup.mapGL ℚ w⁻¹ * π⁻¹ := by
    have : hex.choose = π * Matrix.SpecialLinearGroup.mapGL ℚ w := by
      rw [← hwe]; group
    rw [this, _root_.mul_inv_rev, map_inv]
  rw [e, ratReal_mul, ratReal_mapGL, Matrix.mul_assoc]
  exact sectionClR_gammaNP_mulR n N f ((gammaNP N).inv_mem hw)
    (by rw [Matrix.det_mul, ratReal_inv_det hd.ppos, hg, one_mul]) hy a b

theorem adelicSection_of_not (n : ℕ) (h : ℂ → ℂ) (gR : Matrix (Fin 3) (Fin 3) ℝ) {gf : FiniteGL}
    (hd : ¬∃ π κ, IsDecomp N gf π κ) (y : Fin 5 → ℝ) (a b : Fin 5) :
    adelicSection N n h gR gf y a b = 0 := by
  unfold adelicSection
  rw [dite_eq_right hd]

theorem IsDecomp.mul_ker {g : FiniteGL} {π : GL3 ℚ} {κ κ' : GL3 IntegralAdeles}
    (hd : IsDecomp N g π κ) (hk : κ' ∈ levelKernel N 3) :
    IsDecomp N (g * GeneralLinearGroup.map integralEmbedding κ') π (κ * κ') :=
  ⟨hd.ppos, (levelKernel N 3).mul_mem hd.ker hk, by rw [hd.eq, map_mul, mul_assoc]⟩

theorem exists_decomp_mul_ker {g : FiniteGL} {κ' : GL3 IntegralAdeles} (hk : κ' ∈ levelKernel N 3) :
    (∃ π κ, IsDecomp N (g * GeneralLinearGroup.map integralEmbedding κ') π κ) ↔
      ∃ π κ, IsDecomp N g π κ := by
  constructor
  · rintro ⟨π, κ, hd⟩
    refine ⟨π, κ * κ'⁻¹, ?_⟩
    have := hd.mul_ker N ((levelKernel N 3).inv_mem hk)
    rwa [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one] at this
  · rintro ⟨π, κ, hd⟩
    exact ⟨π, _, hd.mul_ker N hk⟩

/-- **Right `K(N)`-invariance.** -/
theorem adelicSection_mul_ker (hN : 3 ≤ N) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))
    {gR : Matrix (Fin 3) (Fin 3) ℝ} (hg : gR.det = 1) (gf : FiniteGL) {κ' : GL3 IntegralAdeles}
    (hk : κ' ∈ levelKernel N 3) {y : Fin 5 → ℝ} (hy : y ∈ Omega) (a b : Fin 5) :
    adelicSection N n (hfun f) gR (gf * GeneralLinearGroup.map integralEmbedding κ') y a b =
      adelicSection N n (hfun f) gR gf y a b := by
  by_cases hd : ∃ π κ, IsDecomp N gf π κ
  · obtain ⟨π, κ, hd⟩ := hd
    rw [adelicSection_of_decomp N hN n f hg (hd.mul_ker N hk) hy a b,
      adelicSection_of_decomp N hN n f hg hd hy a b]
  · rw [adelicSection_of_not N n _ gR hd, adelicSection_of_not N n _ gR]
    rwa [exists_decomp_mul_ker N hk]

theorem IsDecomp.planeDet_mul {g : FiniteGL} {π κ} (hd : IsDecomp N g π κ) {p : GL3 ℚ} (hp : PlaneDet p) :
    IsDecomp N (rationalFinite p * g) (p * π) κ :=
  ⟨hp.mul hd.ppos, hd.ker, by rw [hd.eq, map_mul, mul_assoc]⟩

theorem exists_decomp_planeDet_mul (g : FiniteGL) {p : GL3 ℚ} (hp : PlaneDet p) :
    (∃ π κ, IsDecomp N (rationalFinite p * g) π κ) ↔ ∃ π κ, IsDecomp N g π κ := by
  constructor
  · rintro ⟨π, κ, hd⟩
    refine ⟨p⁻¹ * π, κ, ?_⟩
    have := hd.planeDet_mul N hp.inv
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul] at this
  · rintro ⟨π, κ, hd⟩
    exact ⟨p * π, κ, hd.planeDet_mul N hp⟩

/-- **Left `P₁(ℚ)`-invariance** (with the section normalised as `ρ(g)⁻¹ g^* ω_h`). -/
theorem adelicSection_planeDet_mul (hN : 3 ≤ N) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))
    {gR : Matrix (Fin 3) (Fin 3) ℝ} (hg : gR.det = 1) (gf : FiniteGL) {p : GL3 ℚ} (hp : PlaneDet p)
    {y : Fin 5 → ℝ} (hy : y ∈ Omega) (a b : Fin 5) :
    adelicSection N n (hfun f) (ratReal p * gR) (rationalFinite p * gf) y a b =
      adelicSection N n (hfun f) gR gf y a b := by
  have hg' : (ratReal p * gR).det = 1 := by rw [Matrix.det_mul, ratReal_det hp.det, hg, one_mul]
  by_cases hd : ∃ π κ, IsDecomp N gf π κ
  · obtain ⟨π, κ, hd⟩ := hd
    rw [adelicSection_of_decomp N hN n f hg' (hd.planeDet_mul N hp) hy a b,
      adelicSection_of_decomp N hN n f hg hd hy a b]
    have : ratReal (p * π)⁻¹ * (ratReal p * gR) = ratReal π⁻¹ * gR := by
      rw [_root_.mul_inv_rev, ratReal_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (ratReal p⁻¹),
        ratReal_inv_mul, Matrix.one_mul]
    rw [this]
  · rw [adelicSection_of_not N n _ gR hd, adelicSection_of_not N n _ (ratReal p * gR)]
    rwa [exists_decomp_planeDet_mul N gf hp]

omit [NeZero N] in
theorem rationalFinite_mapGL (γ : SL(3, ℤ)) :
    rationalFinite (Matrix.SpecialLinearGroup.mapGL ℚ γ) =
      GeneralLinearGroup.map integralEmbedding (Matrix.SpecialLinearGroup.mapGL IntegralAdeles γ) := by
  apply Units.ext
  ext i j
  simp [rationalFinite, Matrix.GeneralLinearGroup.map_apply, Matrix.SpecialLinearGroup.mapGL_coe_matrix]

theorem mapGL_mem_levelKernel {γ : SL(3, ℤ)} (hγ : γ ∈ gammaN N) :
    Matrix.SpecialLinearGroup.mapGL IntegralAdeles γ ∈ levelKernel N 3 := by
  rw [mapGL_mem_levelKernel_iff]
  have h1 := (mem_gammaN_iff_finComp N γ).1 hγ
  apply Units.ext
  have := congrArg (fun x : SL(3, ZMod N) => (x : Matrix (Fin 3) (Fin 3) (ZMod N))) h1
  simpa [Matrix.SpecialLinearGroup.mapGL_coe_matrix] using this

theorem decomp_rational {π : GL3 ℚ} (hπ : PlaneDet π) {γ : SL(3, ℤ)} (hγ : γ ∈ gammaN N) :
    IsDecomp N (rationalFinite (π * Matrix.SpecialLinearGroup.mapGL ℚ γ)) π
      (Matrix.SpecialLinearGroup.mapGL IntegralAdeles γ) :=
  ⟨hπ, mapGL_mem_levelKernel N hγ, by rw [map_mul, rationalFinite_mapGL]⟩

/-- **The section at the rational points `π γ`, `γ ∈ Γ(N)`, is the classical section at `π_∞⁻¹ g_∞`.** -/
theorem adelicSection_rational (hN : 3 ≤ N) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))
    {gR : Matrix (Fin 3) (Fin 3) ℝ} (hg : gR.det = 1) {π : GL3 ℚ} (hπ : PlaneDet π) {γ : SL(3, ℤ)}
    (hγ : γ ∈ gammaN N) {y : Fin 5 → ℝ} (hy : y ∈ Omega) (a b : Fin 5) :
    adelicSection N n (hfun f) gR (rationalFinite (π * Matrix.SpecialLinearGroup.mapGL ℚ γ)) y a b =
      sectionClR n (hfun f) (ratReal π⁻¹ * gR) y a b :=
  adelicSection_of_decomp N hN n f hg (decomp_rational N hπ hγ) hy a b

end TernaryPeriodPolynomials.Argument.FormClassK
