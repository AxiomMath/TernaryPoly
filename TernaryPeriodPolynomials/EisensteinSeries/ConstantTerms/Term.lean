module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.ValueBound
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.ParabolicEquivariance

@[expose] public section


/-!
# Invariance of the summand under the plane stabilizer (Appendix C.3, `ar:sec:series`)

The coefficient action `ρ` is linear and satisfies the cocycle law; `SL₃(ℤ)` embeds into real
matrices; the plane stabilizer `Γ_P` consists of the elements with bottom row `(0, 0, 1)`. For
`γ ∈ Γ_P` with Levi block in a group `Λ` of slash-invariance of `h`, the pullback of the seed is
`γ^* ω_h = ρ(γ) ω_h` (`seed_closed_equivariant` through `SeedC3.seed_parabolic_equivariant`), hence the
summand `ρ(g)⁻¹ g^* ω_h` at `γ g` equals that at `g`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

open Matrix MvPolynomial

/-! ### The coefficient action `ρ`: linearity, unit and cocycle -/

theorem rho_one (q : MvPolynomial (Fin 3) ℂ) : SeedC3.rho 1 q = q := by
  unfold SeedC3.rho
  have hσ : (fun i : Fin 3 => ∑ j : Fin 3, C ((((1 : Matrix (Fin 3) (Fin 3) ℝ)⁻¹) i j : ℝ) : ℂ) *
      (X j : MvPolynomial (Fin 3) ℂ)) = X := by
    funext i
    rw [show (1 : Matrix (Fin 3) (Fin 3) ℝ)⁻¹ = 1 from inv_one]
    fin_cases i <;> simp [Matrix.one_apply, Fin.sum_univ_three]
  rw [hσ, Matrix.det_one]
  simp only [inv_one, Complex.ofReal_one, map_one, one_mul]
  rw [bind₁_X_left]
  rfl

theorem rho_C_mul (g : Matrix (Fin 3) (Fin 3) ℝ) (c : ℂ) (P : MvPolynomial (Fin 3) ℂ) :
    SeedC3.rho g (C c * P) = C c * SeedC3.rho g P := by
  unfold SeedC3.rho
  rw [map_mul, bind₁_C_right]
  ring

theorem rho_sum {ι : Type*} (g : Matrix (Fin 3) (Fin 3) ℝ) (s : Finset ι)
    (P : ι → MvPolynomial (Fin 3) ℂ) :
    SeedC3.rho g (∑ i ∈ s, P i) = ∑ i ∈ s, SeedC3.rho g (P i) := by
  unfold SeedC3.rho
  rw [map_sum, Finset.mul_sum]

theorem rho_mul {g h : Matrix (Fin 3) (Fin 3) ℝ} (q : MvPolynomial (Fin 3) ℂ) :
    SeedC3.rho g (SeedC3.rho h q) = SeedC3.rho (g * h) q := by
  unfold SeedC3.rho
  rw [map_mul, bind₁_C_right, ← mul_assoc, ← MvPolynomial.C_mul, bind₁_bind₁]
  have hdet : (g * h).det⁻¹ = g.det⁻¹ * h.det⁻¹ := by
    rw [Matrix.det_mul, mul_inv]
  have hinv : (g * h)⁻¹ = h⁻¹ * g⁻¹ := Matrix.mul_inv_rev g h
  rw [hdet, hinv]
  have hfun : (fun i : Fin 3 => bind₁ (fun i : Fin 3 =>
      ∑ j : Fin 3, C (((g⁻¹) i j : ℝ) : ℂ) * (X j : MvPolynomial (Fin 3) ℂ))
        (∑ j : Fin 3, C (((h⁻¹) i j : ℝ) : ℂ) * (X j : MvPolynomial (Fin 3) ℂ))) =
      fun i : Fin 3 => ∑ j : Fin 3, C ((((h⁻¹ * g⁻¹) i j : ℝ)) : ℂ) * (X j : MvPolynomial (Fin 3) ℂ) := by
    funext i
    simp only [Fin.sum_univ_three, map_add, map_mul, bind₁_X_right, bind₁_C_right,
      Matrix.mul_apply]
    push_cast
    simp only [map_add, map_mul]
    ring
  rw [hfun]
  push_cast
  ring_nf

/-! ### Real matrices from `SL₃(ℤ)` and the plane stabilizer -/

/-- The real matrix of an element of `SL₃(ℤ)`. -/
def realMat (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (Int.castRingHom ℝ).mapMatrix (γ : Matrix (Fin 3) (Fin 3) ℤ)

theorem realMat_apply (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) (i j : Fin 3) :
    realMat γ i j = (((γ : Matrix (Fin 3) (Fin 3) ℤ) i j : ℤ) : ℝ) := by
  simp [realMat]

theorem det_realMat (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : (realMat γ).det = 1 := by
  rw [realMat, ← RingHom.map_det, Matrix.SpecialLinearGroup.det_coe]
  simp

theorem realMat_mul (γ δ : Matrix.SpecialLinearGroup (Fin 3) ℤ) :
    realMat (γ * δ) = realMat γ * realMat δ := by
  simp [realMat, map_mul]

theorem realMat_one : realMat 1 = 1 := by
  simp [realMat]

theorem realMat_inv (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : realMat γ⁻¹ = (realMat γ)⁻¹ := by
  refine (Matrix.inv_eq_right_inv ?_).symm
  rw [← realMat_mul, mul_inv_cancel, realMat_one]

/-- The stabilizer of the plane: `SL₃(ℤ)` elements with bottom row `(0, 0, 1)`. -/
def planeStab : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ) where
  carrier := {γ | (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0 ∧ (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = 0 ∧
    (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = 1}
  mul_mem' := by
    rintro γ δ ⟨h0, h1, h2⟩ ⟨k0, k1, k2⟩
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, h0, h1, h2, k0, k1, k2]
  one_mem' := by simp
  inv_mem' := by
    rintro γ ⟨h0, h1, h2⟩
    have hm : (γ : Matrix (Fin 3) (Fin 3) ℤ) * ((γ⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℤ) :
        Matrix (Fin 3) (Fin 3) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]; rfl
    have key : ∀ j, ((γ⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) 2 j =
        (1 : Matrix (Fin 3) (Fin 3) ℤ) 2 j := by
      intro j
      have := congrFun (congrFun hm 2) j
      simp only [Matrix.mul_apply, Fin.sum_univ_three, h0, h1, h2, zero_mul, one_mul,
        zero_add] at this
      exact this
    refine ⟨?_, ?_, ?_⟩
    · simpa using key 0
    · simpa using key 1
    · simpa using key 2

/-! ### Invariance of the summand under the plane stabilizer -/

theorem formPullback_congr (ω : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ)
    {Φ₁ Φ₂ : (Fin 5 → ℝ) → (Fin 5 → ℝ)} {p : Fin 5 → ℝ} (h : Φ₁ =ᶠ[nhds p] Φ₂) (i j : Fin 5) :
    formPullback Φ₁ ω p i j = formPullback Φ₂ ω p i j := by
  unfold formPullback
  rw [h.fderiv_eq, h.eq_of_nhds]

/-- The upper-left `2 × 2` block of a `3 × 3` matrix. -/
def topBlock (L : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![L 0 0, L 0 1; L 1 0, L 1 1]

/-- The last column's first two entries. -/
def sideVec (L : Matrix (Fin 3) (Fin 3) ℝ) : Fin 2 → ℝ := ![L 0 2, L 1 2]

theorem realMat_stab_eq {γ : Matrix.SpecialLinearGroup (Fin 3) ℤ} (hγ : γ ∈ planeStab) :
    realMat γ = SeedC3.parabolicMatrix (topBlock (realMat γ)) (sideVec (realMat γ)) := by
  obtain ⟨h0, h1, h2⟩ := hγ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realMat, SeedC3.parabolicMatrix, topBlock, sideVec, h0, h1, h2]

theorem det_topBlock {γ : Matrix.SpecialLinearGroup (Fin 3) ℤ} (hγ : γ ∈ planeStab) :
    (topBlock (realMat γ)).det = 1 := by
  have h1 := det_realMat γ
  rw [realMat_stab_eq hγ, SeedC3.det_parabolicMatrix] at h1
  exact h1

theorem parabolicMatrix_eq_mul (A : Matrix (Fin 2) (Fin 2) ℝ) (w : Fin 2 → ℝ) :
    SeedC3.parabolicMatrix A w = transMat (w 0) (w 1) * diagMat A 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SeedC3.parabolicMatrix, transMat, diagMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem planeAct_parabolicMatrix (A : Matrix (Fin 2) (Fin 2) ℝ) (w : Fin 2 → ℝ)
    (hA : A.det = 1) {x : Fin 5 → ℝ} (hx : x ∈ Omega) :
    planeAct (SeedC3.parabolicMatrix A w) x = SeedC3.parabolicMap A w x := by
  have hd : (diagMat A 1).det = 1 := by rw [det_diagMat, hA]; norm_num
  have hApos : 0 < A.det := by rw [hA]; exact one_pos
  have hm : leviMap A 1 x ∈ Omega := by
    rw [← planeAct_diag A 1 hApos one_pos (by rw [hA]; norm_num) hx]; exact planeAct_mem hd hx
  rw [parabolicMatrix_eq_mul, planeAct_mul hd hx, planeAct_diag A 1 hApos one_pos
    (by rw [hA]; norm_num) hx, planeAct_transMat _ _ hm]
  rfl

section Invariance

open UpperHalfPlane ModularForm
open scoped UpperHalfPlane

variable {F : Type*} [FunLike F ℍ ℂ] (Λ : Subgroup (GL (Fin 2) ℝ)) [Λ.HasDetOne] (n : ℕ)
  [SlashInvariantFormClass F Λ ((n + 3 : ℕ) : ℤ)] (f : F)

/-- Equivariance of the seed under a plane-stabilizer element whose Levi block is in `Λ`:
`λ^* ω_h = ρ(λ) ω_h`. -/
theorem formPullback_stab (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) (hγ : γ ∈ planeStab)
    (hΛ : ∃ g ∈ Λ, (g : Matrix (Fin 2) (Fin 2) ℝ) = topBlock (realMat γ))
    {x : Fin 5 → ℝ} (hx : x ∈ Omega) (a b : Fin 5) :
    formPullback (planeAct (realMat γ)) (seedForm n (fun z => f (ofComplex z))) x a b =
      SeedC3.rho (realMat γ) (seedForm n (fun z => f (ofComplex z)) x a b) := by
  obtain ⟨g, hgΛ, hg⟩ := hΛ
  have hev : planeAct (realMat γ) =ᶠ[nhds x] SeedC3.parabolicMap (g : Matrix (Fin 2) (Fin 2) ℝ)
      (sideVec (realMat γ)) := by
    refine Filter.eventuallyEq_of_mem (isOpen_Omega.mem_nhds hx) fun y hy => ?_
    have e := realMat_stab_eq hγ
    have h1 : planeAct (realMat γ) y =
        SeedC3.parabolicMap (topBlock (realMat γ)) (sideVec (realMat γ)) y := by
      rw [← planeAct_parabolicMatrix _ _ (det_topBlock hγ) hy, ← e]
    rw [h1, ← hg]
  rw [formPullback_congr _ hev]
  have := SeedC3.seed_parabolic_equivariant Λ n f g hgΛ (sideVec (realMat γ)) x hx.1 a b
  rw [this, hg, ← realMat_stab_eq hγ]

end Invariance

theorem formPullback_congr_form {Φ : (Fin 5 → ℝ) → (Fin 5 → ℝ)}
    {ν ν' : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ} (p : Fin 5 → ℝ)
    (h : ∀ a b, ν (Φ p) a b = ν' (Φ p) a b) (i j : Fin 5) :
    formPullback Φ ν p i j = formPullback Φ ν' p i j := by
  unfold formPullback
  simp only [h]

theorem formPullback_rho (g : Matrix (Fin 3) (Fin 3) ℝ) (Φ : (Fin 5 → ℝ) → (Fin 5 → ℝ))
    (ω : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ) (p : Fin 5 → ℝ) (i j : Fin 5) :
    formPullback Φ (fun x a b => SeedC3.rho g (ω x a b)) p i j =
      SeedC3.rho g (formPullback Φ ω p i j) := by
  unfold formPullback
  rw [rho_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [rho_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [rho_C_mul]

section Invariance2

open UpperHalfPlane ModularForm
open scoped UpperHalfPlane

variable {F : Type*} [FunLike F ℍ ℂ] (Λ : Subgroup (GL (Fin 2) ℝ)) [Λ.HasDetOne] (n : ℕ)
  [SlashInvariantFormClass F Λ ((n + 3 : ℕ) : ℤ)] (f : F)

/-- **Invariance of the summand.** The summand at `λ γ` equals the summand at `γ` for every `λ` in
the plane stabilizer with Levi block in `Λ`. -/
theorem summandPoly_stab_mul (γ δ : Matrix.SpecialLinearGroup (Fin 3) ℤ) (hγ : γ ∈ planeStab)
    (hΛ : ∃ g ∈ Λ, (g : Matrix (Fin 2) (Fin 2) ℝ) = topBlock (realMat γ))
    {q : Fin 5 → ℝ} (hq : q ∈ Omega) (i j : Fin 5) :
    summandPoly n (fun z => f (ofComplex z)) (realMat (γ * δ)) q i j =
      summandPoly n (fun z => f (ofComplex z)) (realMat δ) q i j := by
  set L := realMat γ with hLdef
  set G := realMat δ with hGdef
  have hL : L.det = 1 := det_realMat γ
  have hG : G.det = 1 := det_realMat δ
  have hq' := planeAct_mem hG hq
  have hev : planeAct (L * G) =ᶠ[nhds q] planeAct L ∘ planeAct G :=
    Filter.eventuallyEq_of_mem (isOpen_Omega.mem_nhds hq) fun x hx => planeAct_mul hG hx
  unfold summandPoly
  rw [realMat_mul, ← hLdef, ← hGdef, formPullback_congr _ hev,
    formPullback_comp _ _ _ q (differentiableAt_planeAct hG hq)
      (differentiableAt_planeAct hL hq') i j]
  rw [formPullback_congr_form (Φ := planeAct G)
      (ν' := fun x a b => SeedC3.rho L (seedForm n (fun z => f (ofComplex z)) x a b)) q
      (fun a b => formPullback_stab Λ n f γ hγ hΛ hq' a b) i j, formPullback_rho, rho_mul]
  have hLu : IsUnit L.det := by rw [hL]; exact isUnit_one
  have hinv : (L * G)⁻¹ * L = G⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.nonsing_inv_mul L hLu, Matrix.mul_one]
  rw [hinv]

end Invariance2

end TernaryPeriodPolynomials.Argument.ConvergenceC4
