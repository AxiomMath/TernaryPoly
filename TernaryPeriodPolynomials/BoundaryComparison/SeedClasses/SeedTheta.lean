module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.SeedTransform
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.PlaneRep

@[expose] public section


/-!
# The primitives `θ_g` of the defect `g^*η - ρ(g)η`

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial
open scoped ContDiff

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3

open Calc Psi

section RhoHomogeneous

variable (A : Matrix (Fin 2) (Fin 2) ℝ) (w : Fin 2 → ℝ)

theorem rho_isHomogeneous (hA : A.det = 1) {m : ℕ} {q : MvPolynomial (Fin 3) ℂ}
    (hq : q.IsHomogeneous m) : (rho (parabolicMatrix A w) q).IsHomogeneous m := by
  rw [rho_eq_bind A w hA]
  have hlin : ∀ i : Fin 3, (∑ j : Fin 3, C ((((parabolicMatrix A w)⁻¹ i j : ℝ)) : ℂ) * X j :
      MvPolynomial (Fin 3) ℂ).IsHomogeneous 1 := fun i =>
    IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X _ _
  have := hq.aeval (fun i : Fin 3 => ∑ j : Fin 3, C ((((parabolicMatrix A w)⁻¹ i j : ℝ)) : ℂ) * X j)
    hlin
  simpa [aeval_eq_bind₁] using this

theorem monoY_isHomogeneous (n j : ℕ) (hj : j ≤ n + 1) : (monoY n j).IsHomogeneous (n + 1) := by
  unfold monoY
  have := ((isHomogeneous_X ℂ (1 : Fin 3)).pow j).mul
    ((isHomogeneous_X ℂ (0 : Fin 3)).pow (n + 1 - j))
  have e : 1 * j + 1 * (n + 1 - j) = n + 1 := by omega
  rwa [e] at this

end RhoHomogeneous

namespace PlaneData

variable {G : Type} [Group G] (D : PlaneData G) (n : ℕ)

/-- The polynomial `R_j(g) = ρ(g)(Y^jX^{n+1-j}) - ρ(g₀)(Y^jX^{n+1-j})`, divisible by `Z`. -/
def thetaR (g : G) (j : ℕ) : MvPolynomial (Fin 3) ℂ :=
  rho (parabolicMatrix (D.lamM g) (D.w g)) (monoY n j) -
    rho (parabolicMatrix (D.lamM g) 0) (monoY n j)

theorem X_two_dvd_thetaR (g : G) (j : ℕ) : (X 2 : MvPolynomial (Fin 3) ℂ) ∣ D.thetaR n g j :=
  X_two_dvd_rho_sub (D.lamM g) (D.w g) (D.lamM_det g) _

theorem thetaR_isHomogeneous (g : G) {j : ℕ} (hj : j ≤ n + 1) :
    (D.thetaR n g j).IsHomogeneous (n + 1) :=
  (rho_isHomogeneous _ _ (D.lamM_det g) (monoY_isHomogeneous n j hj)).sub
    (rho_isHomogeneous _ _ (D.lamM_det g) (monoY_isHomogeneous n j hj))

/-- The coefficient vectors of `Θ_g`: `m_j(g) = coefB_j (n+1)⁻¹ ddiv R_j(g)`. -/
def thetaVec (g : G) (j : ℕ) : Coef n :=
  toCoef n (C (((n : ℂ) + 1)⁻¹ * coefB n j) * ddiv (D.thetaR n g j))

theorem toPoly_thetaVec (g : G) {j : ℕ} (hj : j ≤ n + 1) :
    Coef.toPoly (D.thetaVec n g j) = C (((n : ℂ) + 1)⁻¹ * coefB n j) * ddiv (D.thetaR n g j) := by
  unfold thetaVec
  apply toPoly_toCoef_of_isHomogeneous
  have := (isHomogeneous_C (Fin 3) (((n : ℂ) + 1)⁻¹ * coefB n j)).mul
    (ddiv_isHomogeneous (D.thetaR_isHomogeneous n g hj))
  simpa using this

theorem Cn1_mul_Z_toPoly_thetaVec (g : G) {j : ℕ} (hj : j ≤ n + 1) :
    C ((n : ℂ) + 1) * X 2 * Coef.toPoly (D.thetaVec n g j) = C (coefB n j) * D.thetaR n g j := by
  have hn : ((n : ℂ) + 1) ≠ 0 := by
    have : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
    simpa using this
  rw [D.toPoly_thetaVec n g hj]
  have hZ := X_two_mul_ddiv (D.X_two_dvd_thetaR n g j)
  calc C ((n : ℂ) + 1) * X 2 * (C (((n : ℂ) + 1)⁻¹ * coefB n j) * ddiv (D.thetaR n g j))
      = (C ((n : ℂ) + 1) * C (((n : ℂ) + 1)⁻¹ * coefB n j)) * (X 2 * ddiv (D.thetaR n g j)) := by
        ring
    _ = C (coefB n j) * D.thetaR n g j := by
        rw [hZ, ← map_mul, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]

variable (h : ℂ → ℂ)

/-- `Θ_g'(τ) = Σ_j h(τ)τ^j m_j(g)`, the derivative of the primitive `Θ_g`. -/
def thetaDeriv (g : G) (τ : ℂ) : Coef n :=
  ∑ j ∈ Finset.range (n + 2), (h τ * τ ^ j) • D.thetaVec n g j

theorem toPoly_sum {ι : Type*} (s : Finset ι) (f : ι → Coef n) :
    Coef.toPoly (∑ i ∈ s, f i) = ∑ i ∈ s, Coef.toPoly (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Coef.toPoly_add, ih]

theorem Cn1_mul_Z_toPoly_thetaDeriv (g : G) (τ : ℂ) :
    C ((n : ℂ) + 1) * X 2 * Coef.toPoly (D.thetaDeriv n h g τ) =
      C (h τ) * (rho (parabolicMatrix (D.lamM g) (D.w g)) (Apoly τ ^ (n + 1)) -
        rho (parabolicMatrix (D.lamM g) 0) (Apoly τ ^ (n + 1))) := by
  have hA := D.lamM_det g
  unfold thetaDeriv
  rw [toPoly_sum, Finset.mul_sum]
  have hterm : ∀ j ∈ Finset.range (n + 2),
      C ((n : ℂ) + 1) * X 2 * Coef.toPoly ((h τ * τ ^ j) • D.thetaVec n g j) =
        C (h τ) * (C (coefB n j * τ ^ j) * D.thetaR n g j) := by
    intro j hj
    have hj' : j ≤ n + 1 := by simpa [Nat.lt_succ_iff] using hj
    rw [Coef.toPoly_smul]
    calc C ((n : ℂ) + 1) * X 2 * (C (h τ * τ ^ j) * Coef.toPoly (D.thetaVec n g j))
        = C (h τ * τ ^ j) * (C ((n : ℂ) + 1) * X 2 * Coef.toPoly (D.thetaVec n g j)) := by ring
      _ = C (h τ * τ ^ j) * (C (coefB n j) * D.thetaR n g j) := by
          rw [D.Cn1_mul_Z_toPoly_thetaVec n g hj']
      _ = C (h τ) * (C (coefB n j * τ ^ j) * D.thetaR n g j) := by
          simp only [map_mul]; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  rw [Apoly_pow, rho_sum_poly _ _ hA, rho_sum_poly _ _ hA, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [rho_C_mul_poly _ _ hA, rho_C_mul_poly _ _ hA, thetaR]
  ring

end PlaneData

theorem Apoly_isHomogeneous (τ : ℂ) : (Apoly τ).IsHomogeneous 1 := by
  unfold Apoly
  exact (isHomogeneous_C_mul_X _ _).sub (isHomogeneous_X ℂ _)

variable (h : ℂ → ℂ) (n : ℕ)

omit h in
theorem spec_polC (z : Fin 4 → ℂ) : spec z polC = C (z 0 - z 2 * z 1) := by
  simp [polC, pU1, pU2, pT, spec]

theorem spec_polA_eq (x : Face) :
    spec (fun a => sPar h a x) polA = Apoly (faceTau x) := by
  rw [spec_polA]; rfl

theorem psiSpec_eq (x : Face) :
    psiSpec h n x = C (((n : ℂ) + 1)⁻¹) * C (h (faceTau x)) *
      C ((x 0 : ℂ) - faceTau x * (x 1 : ℂ)) *
        ∑ k ∈ Finset.range (n + 1), seedLinear (ptOf x) ^ k * Apoly (faceTau x) ^ (n - k) := by
  unfold psiSpec psiPoly
  simp only [map_mul, map_sum, map_pow, spec_polB_eq, spec_polA_eq, spec_polC, spec_pH, spec_C]
  simp [sPar]

theorem psiSpec_isHomogeneous (x : Face) : (psiSpec h n x).IsHomogeneous n := by
  rw [psiSpec_eq]
  have hsum : (∑ k ∈ Finset.range (n + 1),
      seedLinear (ptOf x) ^ k * Apoly (faceTau x) ^ (n - k)).IsHomogeneous n := by
    refine IsHomogeneous.sum _ _ _ fun k hk => ?_
    have hk' : k ≤ n := by simpa [Nat.lt_succ_iff] using hk
    have := ((seedLinear_isHomogeneous (ptOf x)).pow k).mul
      ((Apoly_isHomogeneous (faceTau x)).pow (n - k))
    have e : 1 * k + 1 * (n - k) = n := by omega
    rwa [e] at this
  have h1 := (((isHomogeneous_C (Fin 3) (((n : ℂ) + 1)⁻¹)).mul
    (isHomogeneous_C (Fin 3) (h (faceTau x)))).mul
    (isHomogeneous_C (Fin 3) ((x 0 : ℂ) - faceTau x * (x 1 : ℂ)))).mul hsum
  simpa using h1

theorem toPoly_psiVal (x : Face) : Coef.toPoly (psiVal h n x) = psiSpec h n x :=
  toPoly_toCoef_of_isHomogeneous n (psiSpec_isHomogeneous h n x)

namespace PlaneData

variable {G : Type} [Group G] (D : PlaneData G) (h : ℂ → ℂ) (n : ℕ)

/-- The coefficient action on the normed model `Coef n`. -/
def rhoCoef (g : G) : Coef n →ₗ[ℂ] Coef n := D.rhoC n g

theorem toPoly_rhoCoef (g : G) (q : Coef n) :
    Coef.toPoly (D.rhoCoef n g q) = rho (D.plm g) (Coef.toPoly q) :=
  D.rhoC_coe n g q

omit h in
theorem Cn1_Z_ne_zero : (C ((n : ℂ) + 1) * X 2 : MvPolynomial (Fin 3) ℂ) ≠ 0 := by
  have hn : ((n : ℂ) + 1) ≠ 0 := by
    have : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
    simpa using this
  refine mul_ne_zero ?_ (X_ne_zero 2)
  intro h0
  apply hn
  exact C_injective (Fin 3) ℂ (by rw [h0, map_zero])

/-- **The defect of `Ψ` is the derivative of `Θ_g`** (polynomial form). -/
theorem defect_poly (g : G) {x : Face} (hx : x ∈ faceSet)
    (hmod : h (mob (D.lam g) (faceTau x)) =
      dnm (D.lam g) (faceTau x) ^ (n + 3) * h (faceTau x)) :
    C (((dnm (D.lam g) (faceTau x))⁻¹) ^ 2) * psiSpec h n (D.act g x) -
        rho (D.plm g) (psiSpec h n x) = Coef.toPoly (D.thetaDeriv n h g (faceTau x)) := by
  apply mul_left_cancel₀ (Cn1_Z_ne_zero n)
  rw [D.transform_psiSpec h n g hx hmod, D.Cn1_mul_Z_toPoly_thetaDeriv n h g (faceTau x)]
  rfl

/-- **The defect of `Ψ` is the derivative of `Θ_g`** (in `E_n`). -/
theorem defect_coef (g : G) {x : Face} (hx : x ∈ faceSet)
    (hmod : h (mob (D.lam g) (faceTau x)) =
      dnm (D.lam g) (faceTau x) ^ (n + 3) * h (faceTau x)) :
    ((dnm (D.lam g) (faceTau x))⁻¹ ^ 2) • psiVal h n (D.act g x) -
        D.rhoCoef n g (psiVal h n x) = D.thetaDeriv n h g (faceTau x) := by
  apply Coef.toPoly_injective
  rw [Coef.toPoly_sub, Coef.toPoly_smul, toPoly_psiVal, D.toPoly_rhoCoef, toPoly_psiVal]
  exact D.defect_poly h n g hx hmod

end PlaneData

end TernaryPeriodPolynomials.Argument.SeedC3
