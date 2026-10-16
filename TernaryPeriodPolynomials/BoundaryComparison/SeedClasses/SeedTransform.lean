module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.RhoAction
public import Mathlib.Algebra.MvPolynomial.Division
public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.Translation
public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.LeviIdentities
public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.LeviAssembly
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.RadicalPoincare
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.SeedPsi
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.PlaneAction
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.PlaneRep

@[expose] public section


/-!
# Transformation of the seed polynomials under a plane parabolic element

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3

open TernaryPeriodPolynomials.Argument

/-- **Transformation of the linear form `𝓑`:** `ρ([[A,w],[0,1]]) 𝓑(p) = (cτ + d) 𝓑(g·p)`. -/
theorem rho_parabolic_seedLinear (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.det = 1)
    (w : Fin 2 → ℝ) (p : Fin 5 → ℝ) (hp : 0 < p 3) :
    rho (parabolicMatrix A w) (seedLinear p) =
      C ((A 1 0 : ℂ) * seedTau p + A 1 1) *
        seedLinear (leviMap A 1 p + ![w 0, w 1, 0, 0, 0]) := by
  have hdet : A.det ≠ 0 := by rw [hA]; exact one_ne_zero
  have hden := leviDenom_ne_zero A p (by rw [hA]; exact one_pos) hp
  rw [rho_parabolicMatrix A w hdet, leviCoefficientAction]
  have hb := bind_leviCoeffSubst_seedLinear A 1 p hdet hden one_ne_zero
  rw [hA] at hb ⊢
  simp only [Complex.ofReal_one, div_one, mul_one, inv_one, map_one, one_mul,
    Complex.ofReal_neg] at hb ⊢
  rw [hb, map_mul, bind₁_C_right, seedLinear_bind_shift]

section RhoLemmas

variable (A : Matrix (Fin 2) (Fin 2) ℝ) (w : Fin 2 → ℝ)

theorem det_parabolicMatrix' (hA : A.det = 1) : (parabolicMatrix A w).det = 1 := by
  rw [det_parabolicMatrix, hA]

theorem rho_eq_bind (hA : A.det = 1) (q : MvPolynomial (Fin 3) ℂ) :
    rho (parabolicMatrix A w) q =
      bind₁ (fun i : Fin 3 =>
        ∑ j : Fin 3, C ((((parabolicMatrix A w)⁻¹ i j : ℝ)) : ℂ) * X j) q := by
  unfold rho
  rw [det_parabolicMatrix' A w hA]
  simp

theorem rho_mul_poly (hA : A.det = 1) (q r : MvPolynomial (Fin 3) ℂ) :
    rho (parabolicMatrix A w) (q * r) =
      rho (parabolicMatrix A w) q * rho (parabolicMatrix A w) r := by
  rw [rho_eq_bind A w hA, rho_eq_bind A w hA, rho_eq_bind A w hA, map_mul]

theorem rho_pow_poly (hA : A.det = 1) (q : MvPolynomial (Fin 3) ℂ) (k : ℕ) :
    rho (parabolicMatrix A w) (q ^ k) = rho (parabolicMatrix A w) q ^ k := by
  rw [rho_eq_bind A w hA, rho_eq_bind A w hA, map_pow]

theorem rho_add_poly (hA : A.det = 1) (q r : MvPolynomial (Fin 3) ℂ) :
    rho (parabolicMatrix A w) (q + r) =
      rho (parabolicMatrix A w) q + rho (parabolicMatrix A w) r := by
  rw [rho_eq_bind A w hA, rho_eq_bind A w hA, rho_eq_bind A w hA, map_add]

theorem rho_sub_poly (hA : A.det = 1) (q r : MvPolynomial (Fin 3) ℂ) :
    rho (parabolicMatrix A w) (q - r) =
      rho (parabolicMatrix A w) q - rho (parabolicMatrix A w) r := by
  rw [rho_eq_bind A w hA, rho_eq_bind A w hA, rho_eq_bind A w hA, map_sub]

theorem rho_C_mul_poly (hA : A.det = 1) (c : ℂ) (q : MvPolynomial (Fin 3) ℂ) :
    rho (parabolicMatrix A w) (C c * q) = C c * rho (parabolicMatrix A w) q := by
  rw [rho_eq_bind A w hA, rho_eq_bind A w hA, map_mul, bind₁_C_right]

theorem rho_sum_poly (hA : A.det = 1) {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin 3) ℂ) :
    rho (parabolicMatrix A w) (∑ i ∈ s, f i) = ∑ i ∈ s, rho (parabolicMatrix A w) (f i) := by
  rw [rho_eq_bind A w hA, map_sum]
  simp only [rho_eq_bind A w hA]

theorem rho_X_two (hA : A.det = 1) : rho (parabolicMatrix A w) (X 2) = X 2 := by
  have hdet : A.det ≠ 0 := by rw [hA]; exact one_ne_zero
  rw [rho_parabolicMatrix A w hdet, leviCoefficientAction]
  simp [hA]

end RhoLemmas

section Binomial

/-- The linear form `𝔄(τ) = τY - X`. -/
def Apoly (τ : ℂ) : MvPolynomial (Fin 3) ℂ := C τ * X 1 - X 0

/-- The monomial `Y^j X^{n+1-j}`. -/
def monoY (n j : ℕ) : MvPolynomial (Fin 3) ℂ := X 1 ^ j * X 0 ^ (n + 1 - j)

/-- The binomial coefficient `C(n+1, j) (-1)^{n+1-j}`. -/
def coefB (n j : ℕ) : ℂ := ((n + 1).choose j : ℂ) * (-1) ^ (n + 1 - j)

theorem Apoly_pow (τ : ℂ) (n : ℕ) :
    Apoly τ ^ (n + 1) = ∑ j ∈ Finset.range (n + 2), C (coefB n j * τ ^ j) * monoY n j := by
  have h : Apoly τ = C τ * X 1 + (-X 0) := by unfold Apoly; ring
  rw [h, add_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold coefB monoY
  rw [mul_pow, neg_pow, map_mul, map_pow, map_mul, map_pow, map_natCast]
  simp only [map_neg, map_one]
  ring

end Binomial

section Divisibility

variable (A : Matrix (Fin 2) (Fin 2) ℝ) (w : Fin 2 → ℝ)

theorem setZ_bind_shift (w : Fin 2 → ℝ) (r : MvPolynomial (Fin 3) ℂ) :
    setZ (bind₁ (![X 0 - C (w 0 : ℂ) * X 2, X 1 - C (w 1 : ℂ) * X 2, X 2] :
      Fin 3 → MvPolynomial (Fin 3) ℂ) r) = setZ r := by
  have : (setZ.comp (bind₁ (![X 0 - C (w 0 : ℂ) * X 2, X 1 - C (w 1 : ℂ) * X 2, X 2] :
      Fin 3 → MvPolynomial (Fin 3) ℂ))) = setZ := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [setZ]
  exact congrArg (fun f => f r) this

theorem setZ_rho_eq (hA : A.det = 1) (q : MvPolynomial (Fin 3) ℂ) :
    setZ (rho (parabolicMatrix A w) q) = setZ (rho (parabolicMatrix A 0) q) := by
  have hdet : A.det ≠ 0 := by rw [hA]; exact one_ne_zero
  rw [rho_parabolicMatrix A w hdet, rho_parabolicMatrix A 0 hdet, setZ_bind_shift,
    setZ_bind_shift]

theorem X_two_dvd_rho_sub (hA : A.det = 1) (q : MvPolynomial (Fin 3) ℂ) :
    (X 2 : MvPolynomial (Fin 3) ℂ) ∣ rho (parabolicMatrix A w) q - rho (parabolicMatrix A 0) q := by
  apply X_two_dvd_of_setZ_eq_zero
  rw [map_sub, setZ_rho_eq A w hA, sub_self]

/-- Exact division by `Z` (the quotient is meaningful when `Z` divides). -/
def ddiv (q : MvPolynomial (Fin 3) ℂ) : MvPolynomial (Fin 3) ℂ :=
  MvPolynomial.divMonomial q (Finsupp.single 2 1)

theorem X_two_mul_ddiv {q : MvPolynomial (Fin 3) ℂ} (h : (X 2 : MvPolynomial (Fin 3) ℂ) ∣ q) :
    (X 2 : MvPolynomial (Fin 3) ℂ) * ddiv q = q := by
  have h1 := MvPolynomial.divMonomial_add_modMonomial_single q (2 : Fin 3)
  have h2 : MvPolynomial.modMonomial q (Finsupp.single 2 1) = 0 :=
    MvPolynomial.X_dvd_iff_modMonomial_eq_zero.mp h
  rw [h2, add_zero] at h1
  exact h1

theorem ddiv_add (q r : MvPolynomial (Fin 3) ℂ) : ddiv (q + r) = ddiv q + ddiv r := by
  unfold ddiv; exact MvPolynomial.add_divMonomial _ _ _

theorem ddiv_C_mul (c : ℂ) (q : MvPolynomial (Fin 3) ℂ) : ddiv (C c * q) = C c * ddiv q := by
  apply MvPolynomial.ext
  intro d
  unfold ddiv
  simp [MvPolynomial.coeff_divMonomial, coeff_C_mul]

theorem ddiv_isHomogeneous {q : MvPolynomial (Fin 3) ℂ} {m : ℕ} (hq : q.IsHomogeneous (m + 1)) :
    (ddiv q).IsHomogeneous m := by
  intro d hd
  unfold ddiv at hd
  rw [MvPolynomial.coeff_divMonomial] at hd
  have := hq hd
  have h1 : (Finsupp.weight 1) (Finsupp.single (2 : Fin 3) 1) = 1 := by
    simp [Finsupp.weight_apply, Finsupp.sum_single_index]
  rw [map_add, h1] at this
  omega

end Divisibility

section PsiTransform

open Psi

variable (h : ℂ → ℂ) (n : ℕ)

/-- `Ψ(x)` as a polynomial. -/
def psiSpec (x : Face) : MvPolynomial (Fin 3) ℂ := Calc.spec (fun a => sPar h a x) (psiPoly n)

omit h n in
theorem spec_vZ (z : Fin 4 → ℂ) : Calc.spec z vZ = X 2 := by
  simp [vZ, Calc.spec]

theorem psiSpec_mul_Z (x : Face) :
    C ((n : ℂ) + 1) * X 2 * psiSpec h n x =
      C (h (faceTau x)) * (seedLinear (ptOf x) ^ (n + 1) - Apoly (faceTau x) ^ (n + 1)) := by
  have h1 := congrArg (Calc.spec (fun a => sPar h a x)) (psi_mul_Z n)
  simp only [map_mul, map_sub, map_pow, spec_vZ, spec_pH, spec_polB_eq, spec_polA] at h1
  unfold psiSpec
  have hC : (Calc.spec (fun a => sPar h a x)) (C ((n : ℂ) + 1)) = C ((n : ℂ) + 1) := Calc.spec_C _ _
  rw [hC] at h1
  simpa [sPar, Apoly] using h1

end PsiTransform

namespace PlaneData

open Psi

variable {G : Type} [Group G] (D : PlaneData G)

/-- The matrix of `D.lam g` as a real `2 × 2` matrix. -/
abbrev lamM (g : G) : Matrix (Fin 2) (Fin 2) ℝ := (D.lam g : GL (Fin 2) ℝ)

theorem lamM_det (g : G) : (D.lamM g).det = 1 := by
  have := congrArg Units.val (D.det_one g)
  simpa [Matrix.GeneralLinearGroup.det] using this

theorem plm_eq (g : G) : D.plm g = parabolicMatrix (D.lamM g) (D.w g) := rfl

theorem faceTau_act (g : G) (x : Face) : faceTau (D.act g x) = mob (D.lam g) (faceTau x) := by
  simp only [faceTau, D.act_two, D.act_three]
  exact Complex.re_add_im _

theorem ptOf_act (g : G) (x : Face) :
    ptOf (D.act g x) = leviMap (D.lamM g) 1 (ptOf x) + ![D.w g 0, D.w g 1, 0, 0, 0] := by
  ext i
  fin_cases i
  · simp [ptOf, leviMap, D.act_zero, lamM]
  · simp [ptOf, leviMap, D.act_one, lamM]
  · have h1 : (leviMap (D.lamM g) 1 (ptOf x)) 2 = (mob (D.lam g) (faceTau x)).re := by
      have := seedTau_leviMap (D.lamM g) 1 (ptOf x)
      simp only [leviMap, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons]
      rw [seedTau_ptOf]
      simp [mob, lamM]
    have e2 : (ptOf (D.act g x)) 2 = (mob (D.lam g) (faceTau x)).re := by simp [ptOf, D.act_two]
    show ptOf (D.act g x) 2 = (leviMap (D.lamM g) 1 (ptOf x) + ![D.w g 0, D.w g 1, 0, 0, 0]) 2
    rw [Pi.add_apply, e2, h1]
    simp
  · have h1 : (leviMap (D.lamM g) 1 (ptOf x)) 3 = (mob (D.lam g) (faceTau x)).im := by
      simp only [leviMap, Matrix.cons_val_three, Matrix.tail_cons,
        Matrix.head_cons]
      rw [seedTau_ptOf]
      simp [mob, lamM]
    have e2 : (ptOf (D.act g x)) 3 = (mob (D.lam g) (faceTau x)).im := by simp [ptOf, D.act_three]
    show ptOf (D.act g x) 3 = (leviMap (D.lamM g) 1 (ptOf x) + ![D.w g 0, D.w g 1, 0, 0, 0]) 3
    rw [Pi.add_apply, e2, h1]
    simp
  · simp [ptOf, leviMap]

theorem dnm_eq_lamM (g : G) (z : ℂ) :
    dnm (D.lam g) z = ((D.lamM g) 1 0 : ℂ) * z + (D.lamM g) 1 1 := rfl

theorem dnm_ne_zero' (g : G) {x : Face} (hx : x ∈ faceSet) :
    dnm (D.lam g) (faceTau x) ≠ 0 := dnm_ne_zero _ (faceTau_im hx)

theorem seedLinear_act (g : G) {x : Face} (hx : x ∈ faceSet) :
    seedLinear (ptOf (D.act g x)) =
      C ((dnm (D.lam g) (faceTau x))⁻¹) * rho (D.plm g) (seedLinear (ptOf x)) := by
  have hp : 0 < (ptOf x) 3 := by simpa [ptOf, faceSet] using hx
  have h1 := rho_parabolic_seedLinear (D.lamM g) (D.lamM_det g) (D.w g) (ptOf x) hp
  rw [plm_eq, h1, seedTau_ptOf, ← mul_assoc, ← map_mul, ptOf_act]
  have hne := D.dnm_ne_zero' g hx
  have e : ((D.lamM g) 1 0 : ℂ) * faceTau x + (D.lamM g) 1 1 = dnm (D.lam g) (faceTau x) := rfl
  rw [e, inv_mul_cancel₀ hne, map_one, one_mul]

theorem seedLinear_of_u_zero (q : Fin 5 → ℝ) (h0 : q 0 = 0) (h1 : q 1 = 0) :
    seedLinear q = Apoly (seedTau q) := by
  simp [seedLinear, Apoly, h0, h1]

theorem Apoly_act (g : G) {x : Face} (hx : x ∈ faceSet) :
    Apoly (faceTau (D.act g x)) =
      C ((dnm (D.lam g) (faceTau x))⁻¹) *
        rho (parabolicMatrix (D.lamM g) 0) (Apoly (faceTau x)) := by
  set p0 : Fin 5 → ℝ := ![0, 0, x 2, x 3, 1] with hp0
  have hp : 0 < p0 3 := by simpa [hp0, faceSet] using hx
  have h1 := rho_parabolic_seedLinear (D.lamM g) (D.lamM_det g) 0 p0 hp
  have hτ0 : seedTau p0 = faceTau x := by
    simp [hp0, seedTau, faceTau]; ring
  have e0 : seedLinear p0 = Apoly (faceTau x) := by
    rw [seedLinear_of_u_zero p0 (by simp [hp0]) (by simp [hp0]), hτ0]
  have hq0 : (leviMap (D.lamM g) 1 p0 +
      ![(0 : Fin 2 → ℝ) 0, (0 : Fin 2 → ℝ) 1, 0, 0, 0]) 0 = 0 := by
    simp [leviMap, hp0]
  have hq1 : (leviMap (D.lamM g) 1 p0 +
      ![(0 : Fin 2 → ℝ) 0, (0 : Fin 2 → ℝ) 1, 0, 0, 0]) 1 = 0 := by
    simp [leviMap, hp0]
  have hτ' : seedTau (leviMap (D.lamM g) 1 p0 +
      ![(0 : Fin 2 → ℝ) 0, (0 : Fin 2 → ℝ) 1, 0, 0, 0]) = faceTau (D.act g x) := by
    rw [seedTau_add_shift, seedTau_leviMap, hτ0, D.faceTau_act g x]
    rfl
  have e1 := seedLinear_of_u_zero _ hq0 hq1
  rw [hτ'] at e1
  rw [e0, e1, hτ0] at h1
  have hne := D.dnm_ne_zero' g hx
  have e : ((D.lamM g) 1 0 : ℂ) * faceTau x + (D.lamM g) 1 1 = dnm (D.lam g) (faceTau x) := rfl
  rw [e] at h1
  rw [h1, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hne, map_one, one_mul]

variable (h : ℂ → ℂ) (n : ℕ)

/-- **The transformation law of `Ψ`** (multiplied by `(n+1)Z`): the failure of `Ψ` to be
`ρ`-equivariant is the difference of two `ρ`-images of `𝔄^{n+1}`. -/
theorem transform_psiSpec (g : G) {x : Face} (hx : x ∈ faceSet)
    (hmod : h (mob (D.lam g) (faceTau x)) =
      dnm (D.lam g) (faceTau x) ^ (n + 3) * h (faceTau x)) :
    C ((n : ℂ) + 1) * X 2 * (C (((dnm (D.lam g) (faceTau x))⁻¹) ^ 2) * psiSpec h n (D.act g x) -
        rho (D.plm g) (psiSpec h n x)) =
      C (h (faceTau x)) * (rho (D.plm g) (Apoly (faceTau x) ^ (n + 1)) -
        rho (parabolicMatrix (D.lamM g) 0) (Apoly (faceTau x) ^ (n + 1))) := by
  set c := dnm (D.lam g) (faceTau x) with hc
  have hne : c ≠ 0 := D.dnm_ne_zero' g hx
  have hA := D.lamM_det g
  have E1 := psiSpec_mul_Z h n x
  have E2 := psiSpec_mul_Z h n (D.act g x)
  have hB := D.seedLinear_act g hx
  have hAp := D.Apoly_act g hx
  rw [← hc] at hB hAp
  have hτ' : h (faceTau (D.act g x)) = c ^ (n + 3) * h (faceTau x) := by
    rw [D.faceTau_act]; exact hmod
  have hscal : (c⁻¹) ^ 2 * (c ^ (n + 3) * h (faceTau x)) * (c⁻¹) ^ (n + 1) = h (faceTau x) := by
    have e : c ^ (n + 3) = c ^ 2 * c ^ (n + 1) := by ring
    rw [e, inv_pow, inv_pow]
    field_simp
  have hC : (C ((c⁻¹) ^ 2) * C (c ^ (n + 3) * h (faceTau x)) * C c⁻¹ ^ (n + 1) :
      MvPolynomial (Fin 3) ℂ) = C (h (faceTau x)) := by
    rw [← map_pow, ← map_mul, ← map_mul, hscal]
  have hrho : rho (D.plm g) (C ((n : ℂ) + 1) * X 2 * psiSpec h n x) =
      C ((n : ℂ) + 1) * X 2 * rho (D.plm g) (psiSpec h n x) := by
    rw [D.plm_eq, rho_mul_poly _ _ hA, rho_C_mul_poly _ _ hA, rho_X_two _ _ hA]
  have key : C ((c⁻¹) ^ 2) * (C ((n : ℂ) + 1) * X 2 * psiSpec h n (D.act g x)) -
      rho (D.plm g) (C ((n : ℂ) + 1) * X 2 * psiSpec h n x) =
      C (h (faceTau x)) * (rho (D.plm g) (Apoly (faceTau x) ^ (n + 1)) -
        rho (parabolicMatrix (D.lamM g) 0) (Apoly (faceTau x) ^ (n + 1))) := by
    rw [E2, E1, hτ', hB, hAp, mul_pow, mul_pow]
    rw [D.plm_eq, rho_C_mul_poly _ _ hA, rho_sub_poly _ _ hA, rho_pow_poly _ _ hA,
      rho_pow_poly _ _ hA]
    rw [rho_pow_poly _ 0 hA]
    linear_combination (rho (parabolicMatrix (D.lamM g) (D.w g)) (seedLinear (ptOf x)) ^ (n + 1) -
      rho (parabolicMatrix (D.lamM g) 0) (Apoly (faceTau x)) ^ (n + 1)) * hC
  linear_combination key + hrho

end PlaneData

end TernaryPeriodPolynomials.Argument.SeedC3
