module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.GammaNCoordinate
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Seed.Edge
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.PolynomialDerivativeKernel

@[expose] public section


/-!
# Scaling the normal coordinate `Z` (the conjugation by `diag(1, 1, N)` on polynomials)

Paper: Lemma C.3
(`ar:lem:seed`), the plane group `Γ_P = Γ(N) ∩ P(ℤ)` with radical `Nℤ²`.

The conjugating operator `T = ρ(diag(1, 1, N))` of `GammaNCoordinate` acts on polynomials by
`T q = N⁻¹ · q(X, Y, Z/N)` (`tOp_coe`, `rho_dmat`); on the quotient `ddiv q = q / Z` it satisfies
`ddiv (q(X, Y, Z/N)) = N⁻¹ · (ddiv q)(X, Y, Z/N)` (`ddiv_sc`), and it carries the radical shear of
`Nℤ²` on a binary form to that of `ℤ²` (`sc_shift`). Consequently the closed-form seed cocycle of
`Γ_P` is carried to that of `ℤ² ⋊ Γ₂(N)` with the same constant (`tOp_edgePoly`).

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open GeneralEisenstein Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- The substitution `Z ↦ c Z`. -/
def zsc (c : ℂ) : Fin 3 → MvPolynomial (Fin 3) ℂ := ![X 0, X 1, C c * X 2]

/-- Scaling of the variable `Z`. -/
def sc (c : ℂ) (q : MvPolynomial (Fin 3) ℂ) : MvPolynomial (Fin 3) ℂ := bind₁ (zsc c) q

theorem coeff_sc (c : ℂ) (q : MvPolynomial (Fin 3) ℂ) (d : Fin 3 →₀ ℕ) :
    (sc c q).coeff d = c ^ (d 2) * q.coeff d := by
  induction q using MvPolynomial.induction_on' with
  | monomial s a =>
    have h : sc c (monomial s a) = monomial s (c ^ (s 2) * a) := by
      rw [sc, monomial_eq, monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
      simp only [map_mul, bind₁_C_right, map_pow, map_prod, bind₁_X_right]
      rw [Fin.prod_univ_three, Fin.prod_univ_three]
      simp [mul_pow, zsc]
      ring
    rw [h]
    simp only [coeff_monomial]
    by_cases hs : s = d
    · subst hs; simp
    · simp [hs]
  | add p q hp hq =>
    simp only [sc, map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] at hp hq ⊢
    rw [hp, hq, mul_add]


theorem ddiv_sc (c : ℂ) (q : MvPolynomial (Fin 3) ℂ) : ddiv (sc c q) = C c * sc c (ddiv q) := by
  apply MvPolynomial.ext
  intro d
  unfold ddiv
  rw [MvPolynomial.coeff_divMonomial, coeff_C_mul, coeff_sc, coeff_sc,
    MvPolynomial.coeff_divMonomial]
  simp
  ring


variable (N : ℕ) [NeZero N] {n : ℕ}

theorem dmat_inv_val :
    ((dmat N : Matrix (Fin 3) (Fin 3) ℝ))⁻¹ = Matrix.diagonal ![1, 1, ((N : ℝ))⁻¹] := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  refine Matrix.inv_eq_right_inv ?_
  rw [dmat_val, Matrix.diagonal_mul_diagonal]
  have : (fun i => (![1, 1, (N : ℝ)] i * ![1, 1, ((N : ℝ))⁻¹] i)) = fun _ => (1 : ℝ) := by
    funext i; fin_cases i <;> simp [hN]
  rw [this]
  exact Matrix.diagonal_one

theorem dmat_det_val : ((dmat N : Matrix (Fin 3) (Fin 3) ℝ)).det = N := by
  rw [dmat_val, Matrix.det_diagonal]
  simp [Fin.prod_univ_three]

theorem rho_dmat (q : MvPolynomial (Fin 3) ℂ) :
    rho (dmat N : Matrix (Fin 3) (Fin 3) ℝ) q = C ((N : ℂ)⁻¹) * sc ((N : ℂ)⁻¹) q := by
  unfold rho sc
  rw [dmat_inv_val, dmat_det_val]
  have hz : (fun i : Fin 3 => ∑ j : Fin 3, C (((Matrix.diagonal ![1, 1, ((N : ℝ))⁻¹] :
      Matrix (Fin 3) (Fin 3) ℝ) i j : ℝ) : ℂ) * (X j : MvPolynomial (Fin 3) ℂ)) =
        zsc ((N : ℂ)⁻¹) := by
    funext i
    fin_cases i <;> simp [zsc, Matrix.diagonal_apply, Fin.sum_univ_three]
  rw [hz]
  simp



theorem realCoefficient_coe (m : ℕ) (g : GL (Fin 3) ℝ) (q : HomogeneousPoly m) :
    ((GeneralEisenstein.realCoefficient m g q : HomogeneousPoly m) : MvPolynomial (Fin 3) ℂ) =
      rho (g : Matrix (Fin 3) (Fin 3) ℝ) (q : MvPolynomial (Fin 3) ℂ) := by
  change ((GeneralEisenstein.action (-1)
    (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) g)) (q : MvPolynomial (Fin 3) ℂ)) = _
  rw [GeneralEisenstein.action_apply]
  unfold rho GeneralEisenstein.substitute GeneralEisenstein.linearForm
  simp [GeneralEisenstein.determinantCharacter, Matrix.GeneralLinearGroup.map]
  have hd : ((g : Matrix (Fin 3) (Fin 3) ℝ).map Complex.ofReal).det =
      (((g : Matrix (Fin 3) (Fin 3) ℝ).det : ℝ) : ℂ) := by
    have := RingHom.map_det Complex.ofRealHom (g : Matrix (Fin 3) (Fin 3) ℝ)
    exact this.symm
  rw [hd, smul_eq_C_mul]



theorem tOp_coe (m : ℕ) (x : HomogeneousPoly m) :
    ((tOp N m x : HomogeneousPoly m) : MvPolynomial (Fin 3) ℂ) =
      C ((N : ℂ)⁻¹) * sc ((N : ℂ)⁻¹) (x : MvPolynomial (Fin 3) ℂ) := by
  change ((GeneralEisenstein.realCoefficient m (dmat N) x : HomogeneousPoly m) :
    MvPolynomial (Fin 3) ℂ) = _
  rw [realCoefficient_coe, rho_dmat]

theorem sc_rename (c : ℂ) (E : MvPolynomial (Fin 2) ℂ) :
    sc c (rename Fin.castSucc E) = rename Fin.castSucc E := by
  unfold sc
  rw [bind₁_rename]
  have : zsc c ∘ Fin.castSucc = fun i => X (Fin.castSucc i) := by
    funext i
    fin_cases i <;> simp [zsc]
  rw [this, rename_eq_aeval]
  rfl



theorem sc_mul (c : ℂ) (p q : MvPolynomial (Fin 3) ℂ) : sc c (p * q) = sc c p * sc c q := by
  simp [sc]

theorem sc_neg (c : ℂ) (p : MvPolynomial (Fin 3) ℂ) : sc c (-p) = -sc c p := by
  simp [sc]

theorem sc_sub (c : ℂ) (p q : MvPolynomial (Fin 3) ℂ) : sc c (p - q) = sc c p - sc c q := by
  simp [sc]

theorem sc_C (c a : ℂ) : sc c (C a) = C a := by simp [sc]

/-- **The conjugation `T` carries the radical shear of `Nℤ²` to that of `ℤ²`** on a binary form
lifted to `ℂ[X, Y, Z]`. -/
theorem sc_shift (E : Binary.HomogeneousPoly (n + 1)) (r : RadicalLattice) :
    sc ((N : ℂ)⁻¹) (bind₁ (shiftSub
        ![((N : ℝ) * (r.toAdd.1 : ℝ)), ((N : ℝ) * (r.toAdd.2 : ℝ))])
        (binaryPolynomialLift E.val)) =
      bind₁ (shiftSub ![(r.toAdd.1 : ℝ), (r.toAdd.2 : ℝ)]) (binaryPolynomialLift E.val) := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hL : binaryPolynomialLift E.val = rename Fin.castSucc E.val := rfl
  rw [hL, sc, bind₁_rename, bind₁_rename, bind₁_bind₁]
  congr 2
  funext i
  have hc : ((N : MvPolynomial (Fin 3) ℂ)) * C ((N : ℂ)⁻¹) = 1 := by
    rw [← map_natCast C, ← C_mul, mul_inv_cancel₀ hN, C_1]
  fin_cases i <;>
    simp [shiftSub, zsc, mul_comm, ← mul_assoc] <;>
    left <;> linear_combination (X 2 : MvPolynomial (Fin 3) ℂ) * hc



theorem tOp_edgePoly (c : ℂ) (E : Binary.HomogeneousPoly (n + 1)) (r : RadicalLattice) :
    C ((N : ℂ)⁻¹) * sc ((N : ℂ)⁻¹)
        (-(C c * ddiv (bind₁ (shiftSub
          ![((N : ℝ) * (r.toAdd.1 : ℝ)), ((N : ℝ) * (r.toAdd.2 : ℝ))])
            (binaryPolynomialLift E.val) - binaryPolynomialLift E.val))) =
      -(C c * ddiv (bind₁ (shiftSub ![(r.toAdd.1 : ℝ), (r.toAdd.2 : ℝ)])
        (binaryPolynomialLift E.val) - binaryPolynomialLift E.val)) := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  set L := binaryPolynomialLift E.val with hL
  have hsc : sc ((N : ℂ)⁻¹) L = L := sc_rename _ _
  have hΔ : sc ((N : ℂ)⁻¹) (bind₁ (shiftSub
      ![((N : ℝ) * (r.toAdd.1 : ℝ)), ((N : ℝ) * (r.toAdd.2 : ℝ))]) L - L) =
      bind₁ (shiftSub ![(r.toAdd.1 : ℝ), (r.toAdd.2 : ℝ)]) L - L := by
    rw [sc_sub, hsc]
    exact congrArg (· - L) (sc_shift N E r)
  have hdd : ∀ q : MvPolynomial (Fin 3) ℂ,
      sc ((N : ℂ)⁻¹) (ddiv q) = C (N : ℂ) * ddiv (sc ((N : ℂ)⁻¹) q) := by
    intro q
    rw [ddiv_sc, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hN, C_1, one_mul]
  rw [sc_neg, sc_mul, sc_C, hdd, hΔ]
  have hc : C ((N : ℂ)⁻¹) * C (N : ℂ) = (1 : MvPolynomial (Fin 3) ℂ) := by
    rw [← C_mul, inv_mul_cancel₀ hN, C_1]
  linear_combination
    (-(C c * ddiv (bind₁ (shiftSub ![(r.toAdd.1 : ℝ), (r.toAdd.2 : ℝ)]) L - L))) * hc


end TernaryPeriodPolynomials.Argument.SeedC3S4c
