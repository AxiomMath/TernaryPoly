module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Packaging

@[expose] public section


/-!
# Proposition C.4: seeds of both types

The holomorphic seed `ω_h` and the antiholomorphic seed `ω̄_h` (complex conjugation of the
coefficient polynomial and of the differential) are treated together through a flag `b : Bool`.
The coefficient action `ρ` has real coefficients and `formPullback` has real scalar coefficients,
so both commute with coefficientwise conjugation: the summand of the antiholomorphic seed is the
conjugate of the summand of the holomorphic one (`summandK_eq`), and the cocycle relation
(`summandK_mul_eq`) holds for both. Also: invariance of the summand under a real plane stabilizer
matrix with Levi block in the cusp group (`summandPoly_realstab_mul`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

open scoped ContDiff
open Matrix MvPolynomial

/-- The coefficient conjugation attached to the type of a seed: `false` is the identity
(holomorphic seed), `true` is complex conjugation (antiholomorphic seed). -/
def cx (b : Bool) : ℂ →+* ℂ := if b then starRingEnd ℂ else RingHom.id ℂ

/-- The same map as a real linear isometric equivalence. -/
def cxL (b : Bool) : ℂ ≃ₗᵢ[ℝ] ℂ := if b then Complex.conjLIE else LinearIsometryEquiv.refl ℝ ℂ

theorem cxL_apply (b : Bool) (z : ℂ) : cxL b z = cx b z := by
  cases b <;> simp [cxL, cx]

theorem cx_ofReal (b : Bool) (r : ℝ) : cx b (r : ℂ) = r := by
  cases b <;> simp [cx]

theorem cx_cx (b : Bool) (z : ℂ) : cx b (cx b z) = z := by
  cases b <;> simp [cx]

/-- Coefficientwise application of `cx b` to a polynomial. -/
def cxP (b : Bool) : MvPolynomial (Fin 3) ℂ →+* MvPolynomial (Fin 3) ℂ := MvPolynomial.map (cx b)

theorem coeff_cxP (b : Bool) (q : MvPolynomial (Fin 3) ℂ) (m : Fin 3 →₀ ℕ) :
    (cxP b q).coeff m = cx b (q.coeff m) := MvPolynomial.coeff_map _ _ _

theorem cxP_false (q : MvPolynomial (Fin 3) ℂ) : cxP false q = q := by
  simp [cxP, cx, MvPolynomial.map_id]

theorem isHomogeneous_cxP (b : Bool) {q : MvPolynomial (Fin 3) ℂ} {n : ℕ}
    (hq : q.IsHomogeneous n) : (cxP b q).IsHomogeneous n :=
  hq.map _

theorem rho_cxP (b : Bool) (g : Matrix (Fin 3) (Fin 3) ℝ) (q : MvPolynomial (Fin 3) ℂ) :
    SeedC3.rho g (cxP b q) = cxP b (SeedC3.rho g q) := by
  have hφ : ∀ i : Fin 3, cxP b (∑ j : Fin 3, C (((g⁻¹) i j : ℝ) : ℂ) * (X j : MvPolynomial (Fin 3) ℂ)) =
      ∑ j : Fin 3, C (((g⁻¹) i j : ℝ) : ℂ) * (X j : MvPolynomial (Fin 3) ℂ) := by
    intro i
    simp only [cxP, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, cx_ofReal]
  unfold SeedC3.rho
  conv_rhs => rw [map_mul, show cxP b = MvPolynomial.map (cx b) from rfl, MvPolynomial.map_C,
    MvPolynomial.map_bind₁, cx_ofReal]
  simp only [← show cxP b = MvPolynomial.map (cx b) from rfl, hφ]

theorem formPullback_cxP (b : Bool) (Φ : (Fin 5 → ℝ) → (Fin 5 → ℝ))
    (om : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ) (p : Fin 5 → ℝ) (i j : Fin 5) :
    formPullback Φ (fun y a c => cxP b (om y a c)) p i j = cxP b (formPullback Φ om p i j) := by
  unfold formPullback
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul]
  unfold cxP
  rw [MvPolynomial.map_C, cx_ofReal]

/-! ### The seeds of both types and their summands -/

/-- The seed of type `b`: the holomorphic seed `ω_h` for `b = false`, and for `b = true` the
antiholomorphic seed obtained from it by complex conjugation (of the coefficient polynomial and of
the differential, i.e. of the component functions `ω(∂ᵢ, ∂ⱼ)`). -/
def seedFormK (b : Bool) (n : ℕ) (h : ℂ → ℂ) (p : Fin 5 → ℝ) (i j : Fin 5) :
    MvPolynomial (Fin 3) ℂ :=
  cxP b (seedForm n h p i j)

/-- The summand `ρ(g)⁻¹ g^* ω` of the series for the seed of type `b`. -/
def summandK (b : Bool) (n : ℕ) (h : ℂ → ℂ) (g : Matrix (Fin 3) (Fin 3) ℝ) (q : Fin 5 → ℝ)
    (i j : Fin 5) : MvPolynomial (Fin 3) ℂ :=
  SeedC3.rho g⁻¹ (formPullback (planeAct g) (seedFormK b n h) q i j)

theorem summandK_eq (b : Bool) (n : ℕ) (h : ℂ → ℂ) (g : Matrix (Fin 3) (Fin 3) ℝ)
    (q : Fin 5 → ℝ) (i j : Fin 5) :
    summandK b n h g q i j = cxP b (summandPoly n h g q i j) := by
  unfold summandK summandPoly seedFormK
  rw [formPullback_cxP b (planeAct g) (seedForm n h), rho_cxP]

theorem summandK_false (n : ℕ) (h : ℂ → ℂ) (g : Matrix (Fin 3) (Fin 3) ℝ)
    (q : Fin 5 → ℝ) (i j : Fin 5) : summandK false n h g q i j = summandPoly n h g q i j := by
  rw [summandK_eq, cxP_false]

/-- The cocycle relation for the summands of either type. -/
theorem summandK_mul_eq (b : Bool) (n : ℕ) (h : ℂ → ℂ) {g d : Matrix (Fin 3) (Fin 3) ℝ}
    (hg : g.det = 1) (hd : d.det = 1) {x : Fin 5 → ℝ} (hx : x ∈ Omega) (i j : Fin 5) :
    summandK b n h (g * d) x i j =
      SeedC3.rho d⁻¹ (formPullback (planeAct d) (fun y a c => summandK b n h g y a c) x i j) := by
  simp only [summandK_eq]
  rw [summandPoly_mul_eq n h hg hd hx i j, formPullback_cxP b (planeAct d)
    (fun y a c => summandPoly n h g y a c), rho_cxP]

/-! ### Invariance under a real plane stabilizer element -/

section RealStab

open UpperHalfPlane ModularForm
open scoped UpperHalfPlane

variable {F : Type*} [FunLike F ℍ ℂ] (Λ : Subgroup (GL (Fin 2) ℝ)) [Λ.HasDetOne] (n : ℕ)
  [SlashInvariantFormClass F Λ ((n + 3 : ℕ) : ℤ)] (f : F)

theorem eq_parabolicMatrix_of_row (L : Matrix (Fin 3) (Fin 3) ℝ) (h0 : L 2 0 = 0) (h1 : L 2 1 = 0)
    (h2 : L 2 2 = 1) : L = SeedC3.parabolicMatrix (topBlock L) (sideVec L) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SeedC3.parabolicMatrix, topBlock, sideVec, h0, h1, h2]

theorem det_topBlock_of_row {L : Matrix (Fin 3) (Fin 3) ℝ} (hdet : L.det = 1) (h0 : L 2 0 = 0)
    (h1 : L 2 1 = 0) (h2 : L 2 2 = 1) : (topBlock L).det = 1 := by
  have e := eq_parabolicMatrix_of_row L h0 h1 h2
  rw [e, SeedC3.det_parabolicMatrix] at hdet
  exact hdet

/-- The seed is equivariant for any real matrix with bottom row `(0, 0, 1)` and Levi block in `Λ`. -/
theorem formPullback_stab_real (L : Matrix (Fin 3) (Fin 3) ℝ) (hdet : L.det = 1)
    (h0 : L 2 0 = 0) (h1 : L 2 1 = 0) (h2 : L 2 2 = 1)
    (hΛ : ∃ g ∈ Λ, (g : Matrix (Fin 2) (Fin 2) ℝ) = topBlock L)
    {x : Fin 5 → ℝ} (hx : x ∈ Omega) (a b : Fin 5) :
    formPullback (planeAct L) (seedForm n (fun z => f (ofComplex z))) x a b =
      SeedC3.rho L (seedForm n (fun z => f (ofComplex z)) x a b) := by
  obtain ⟨g, hgΛ, hg⟩ := hΛ
  have e := eq_parabolicMatrix_of_row L h0 h1 h2
  have hev : planeAct L =ᶠ[nhds x] SeedC3.parabolicMap (g : Matrix (Fin 2) (Fin 2) ℝ)
      (sideVec L) := by
    refine Filter.eventuallyEq_of_mem (isOpen_Omega.mem_nhds hx) fun y hy => ?_
    have h1' : planeAct L y =
        SeedC3.parabolicMap (topBlock L) (sideVec L) y := by
      rw [← planeAct_parabolicMatrix _ _ (det_topBlock_of_row hdet h0 h1 h2) hy, ← e]
    rw [h1', ← hg]
  rw [formPullback_congr _ hev]
  have := SeedC3.seed_parabolic_equivariant Λ n f g hgΛ (sideVec L) x hx.1 a b
  rw [this, hg, ← e]

/-- **Invariance of the summand under a real plane stabilizer.** -/
theorem summandPoly_realstab_mul (L G : Matrix (Fin 3) (Fin 3) ℝ) (hL : L.det = 1)
    (hG : G.det = 1) (h0 : L 2 0 = 0) (h1 : L 2 1 = 0) (h2 : L 2 2 = 1)
    (hΛ : ∃ g ∈ Λ, (g : Matrix (Fin 2) (Fin 2) ℝ) = topBlock L)
    {q : Fin 5 → ℝ} (hq : q ∈ Omega) (i j : Fin 5) :
    summandPoly n (fun z => f (ofComplex z)) (L * G) q i j =
      summandPoly n (fun z => f (ofComplex z)) G q i j := by
  have hq' := planeAct_mem hG hq
  have hev : planeAct (L * G) =ᶠ[nhds q] planeAct L ∘ planeAct G :=
    Filter.eventuallyEq_of_mem (isOpen_Omega.mem_nhds hq) fun x hx => planeAct_mul hG hx
  unfold summandPoly
  rw [formPullback_congr _ hev,
    formPullback_comp _ _ _ q (differentiableAt_planeAct hG hq)
      (differentiableAt_planeAct hL hq') i j]
  rw [formPullback_congr_form (Φ := planeAct G)
      (ν' := fun x a b => SeedC3.rho L (seedForm n (fun z => f (ofComplex z)) x a b)) q
      (fun a b => formPullback_stab_real Λ n f L hL h0 h1 h2 hΛ hq' a b) i j, formPullback_rho,
    rho_mul]
  have hLu : IsUnit L.det := by rw [hL]; exact isUnit_one
  have hinv : (L * G)⁻¹ * L = G⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.nonsing_inv_mul L hLu, Matrix.mul_one]
  rw [hinv]

end RealStab

end TernaryPeriodPolynomials.Argument.ConvergenceC4
