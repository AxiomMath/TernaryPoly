module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Bad.LinePairs
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Good.LineRestriction

@[expose] public section


/-!
# The coefficient of `X₀ⁿ` and the line parabolic

The functional `κ(v) = coeff_{X₀ⁿ}(v)` on `Sym^n` kills the infinitesimal generators of the upper
line radical `U` and is `U`-invariant; more generally, for a rational element `g` of the line
parabolic (first column `(a, 0, 0)ᵗ`), `κ(ρ(g) v) = det(g)⁻¹ a^{-n} κ(v)` (`kappaB_rho`). For
`R(w, a, B)` this is `(a det B)⁻¹ a^{-n} κ(v)` (`kappaB_R`), so `κ ∘ ρ(ℓ_j) = p⁻¹ κ`,
`κ ∘ ρ(τ_d) = (εp)^{-(n+1)} κ` and `κ ∘ ρ(Ux x) = κ` for the bad-line Hecke cosets.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThree.BadLineKappa

open Matrix MvPolynomial GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral
open LineCoordinates IdentityPlaneCosets LevelOneCosets LevelThreeCosets BadLineCoordinates
open BadLineCosets BadLineTransitions IdentityPlaneCoordinate

variable (n : ℕ)

/-- The coefficient of `X₀ⁿ`. -/
def kappaB : HomogeneousPoly n →ₗ[ℂ] ℂ where
  toFun v := v.val.coeff (Finsupp.single 0 n)
  map_add' v w := by simp
  map_smul' a v := by simp

theorem coeff0_X_mul_zero (i : Fin 3) (hi : i ≠ 0) (m : ℕ) (g : Poly) :
    (X i * g).coeff (Finsupp.single 0 m) = 0 := by
  rw [mul_comm, MvPolynomial.coeff_mul_X']
  rw [ite_eq_right]
  simp [Finsupp.mem_support_iff, hi.symm]

theorem coeff0_mul_X (i : Fin 3) (hi : i ≠ 0) (m : ℕ) (g : Poly) :
    (g * X i).coeff (Finsupp.single 0 m) = 0 := by
  rw [mul_comm]
  exact coeff0_X_mul_zero i hi m g

theorem coeff0_mul_X0 (m : ℕ) (g : Poly) :
    (g * X 0).coeff (Finsupp.single 0 (m + 1)) =
      g.coeff (Finsupp.single 0 m) := by
  rw [MvPolynomial.coeff_mul_X']
  rw [ite_eq_left (by simp)]
  congr 1
  ext k
  simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply]
  split_ifs <;> omega

theorem coeff0_zero_mul_X0 (g : Poly) :
    (g * X 0).coeff (Finsupp.single 0 0) = 0 := by
  rw [MvPolynomial.coeff_mul_X', ite_eq_right (by simp)]

/-- **Substitution by a matrix with vanishing first column below the diagonal scales the
coefficient of `X₀ᵐ` by `M₀₀ᵐ`.** -/
theorem coeff_subst_line (M : Matrix (Fin 3) (Fin 3) ℂ) (h10 : M 1 0 = 0) (h20 : M 2 0 = 0)
    (f : Poly) :
    ∀ m : ℕ, (substitute M f).coeff (Finsupp.single 0 m) =
      (M 0 0) ^ m * f.coeff (Finsupp.single 0 m) := by
  have hl : ∀ k : Fin 3, linearForm M k =
      C (M k 0) * X 0 + C (M k 1) * X 1 + C (M k 2) * X 2 := by
    intro k
    simp [linearForm, Fin.sum_univ_three]
  induction f using MvPolynomial.induction_on with
  | C a =>
    intro m
    rw [show substitute M (C a) = C a from MvPolynomial.bind₁_C_right _ _,
      MvPolynomial.coeff_C]
    split_ifs with h
    · have : m = 0 := by
        have := congrArg (fun x : Fin 3 →₀ ℕ => x 0) h
        simpa using this.symm
      subst this
      simp
    · simp
  | add f g hf hg =>
    intro m
    rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hf, hg, mul_add]
  | mul_X f i hf =>
    intro m
    rw [map_mul, substitute_X]
    have c0 : (substitute M f * linearForm M 0).coeff (Finsupp.single 0 m) =
        (M 0 0) ^ m * (f * X 0).coeff (Finsupp.single 0 m) := by
      rw [hl 0, mul_add, mul_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
        ← mul_assoc (substitute M f) (C (M 0 1)) (X 1),
        ← mul_assoc (substitute M f) (C (M 0 2)) (X 2),
        coeff0_mul_X 1 (by decide), coeff0_mul_X 2 (by decide),
        mul_left_comm (substitute M f) (C (M 0 0)) (X 0), MvPolynomial.coeff_C_mul, add_zero,
        add_zero]
      cases m with
      | zero => rw [coeff0_zero_mul_X0, coeff0_zero_mul_X0]; simp
      | succ m => rw [coeff0_mul_X0, coeff0_mul_X0, hf m]; ring
    have c1 : (substitute M f * linearForm M 1).coeff (Finsupp.single 0 m) =
        (M 0 0) ^ m * (f * X 1).coeff (Finsupp.single 0 m) := by
      rw [hl 1, h10, MvPolynomial.C_0, zero_mul, zero_add, mul_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
        ← mul_assoc (substitute M f) (C (M 1 1)) (X 1),
        ← mul_assoc (substitute M f) (C (M 1 2)) (X 2),
        coeff0_mul_X 1 (by decide), coeff0_mul_X 2 (by decide), coeff0_mul_X 1 (by decide)]
      simp
    have c2 : (substitute M f * linearForm M 2).coeff (Finsupp.single 0 m) =
        (M 0 0) ^ m * (f * X 2).coeff (Finsupp.single 0 m) := by
      rw [hl 2, h20, MvPolynomial.C_0, zero_mul, zero_add, mul_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
        ← mul_assoc (substitute M f) (C (M 2 1)) (X 1),
        ← mul_assoc (substitute M f) (C (M 2 2)) (X 2),
        coeff0_mul_X 1 (by decide), coeff0_mul_X 2 (by decide), coeff0_mul_X 2 (by decide)]
      simp
    fin_cases i
    exacts [c0, c1, c2]

/-- **`κ` along a rational element of the line parabolic.** -/
theorem kappaB_rho (g : RationalGL3) (h10 : (g⁻¹ : RationalGL3).val 1 0 = 0)
    (h20 : (g⁻¹ : RationalGL3).val 2 0 = 0) (v : HomogeneousPoly n) :
    kappaB n (ρn n g v) = (algebraMap ℚ ℂ g.val.det)⁻¹ *
      (algebraMap ℚ ℂ ((g⁻¹ : RationalGL3).val 0 0)) ^ n * kappaB n v := by
  change (ρn n g v).val.coeff (Finsupp.single 0 n) = _
  rw [rho_coe, action_apply, MvPolynomial.coeff_smul]
  have hMentry : ∀ i j, (((GeneralLinearGroup.map (algebraMap ℚ ℂ) g)⁻¹ : GL3) :
      Matrix (Fin 3) (Fin 3) ℂ) i j = algebraMap ℚ ℂ ((g⁻¹ : RationalGL3).val i j) := by
    intro i j
    rw [← map_inv]
    rfl
  have hdet : determinantCharacter (-1) (GeneralLinearGroup.map (algebraMap ℚ ℂ) g) =
      (algebraMap ℚ ℂ g.val.det)⁻¹ := by
    change (((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℚ ℂ) g) : ℂˣ) : ℂ)) ^
      (-1 : ℤ) = _
    rw [_root_.zpow_neg_one, GeneralLinearGroup.val_det_apply]
    congr 1
    have h1 : (g.val.map (algebraMap ℚ ℂ)).det = algebraMap ℚ ℂ (g.val.det) :=
      (RingHom.map_det _ _).symm
    exact h1
  have h1 : (((GeneralLinearGroup.map (algebraMap ℚ ℂ) g)⁻¹ : GL3) :
      Matrix (Fin 3) (Fin 3) ℂ) 1 0 = 0 := by
    rw [hMentry, h10, map_zero]
  have h2 : (((GeneralLinearGroup.map (algebraMap ℚ ℂ) g)⁻¹ : GL3) :
      Matrix (Fin 3) (Fin 3) ℂ) 2 0 = 0 := by
    rw [hMentry, h20, map_zero]
  rw [coeff_subst_line _ h1 h2 v.val n, hMentry, hdet, smul_eq_mul]
  change _ = _ * kappaB n v
  rw [show v.val.coeff (Finsupp.single 0 n) = kappaB n v from rfl]
  ring

theorem det_R (w : ℚ × ℚ) (a : ℚˣ) (B : GL (Fin 2) ℚ) :
    (R w a B).val.det = (a : ℚ) * B.val.det := by
  rw [R_val]
  simp [Matrix.det_fin_three, Matrix.det_fin_two]
  ring

theorem kappaB_R (w : ℚ × ℚ) (a : ℚˣ) (B : GL (Fin 2) ℚ) (v : HomogeneousPoly n) :
    kappaB n (ρn n (R w a B) v) =
      (algebraMap ℚ ℂ ((a : ℚ) * B.val.det))⁻¹ * (algebraMap ℚ ℂ ((a⁻¹ : ℚˣ) : ℚ)) ^ n *
        kappaB n v := by
  have h := kappaB_rho n (R w a B) (by rw [R_inv, R_val]; simp) (by rw [R_inv, R_val]; simp) v
  rw [h, det_R, R_inv, R_val]
  simp

theorem kappaB_Ux (x : ℤ × ℤ) (v : HomogeneousPoly n) :
    kappaB n (ρn n ((Ux x : ΛB) : RationalGL3) v) = kappaB n v := by
  rw [Ux, Mel_val, kappaB_R]
  simp

theorem kappaB_sLev (p : Nat.Primes) (j : Option (Fin p.val)) (v : HomogeneousPoly n) :
    kappaB n (ρn n (sLev p j) v) = (p.val : ℂ)⁻¹ * kappaB n v := by
  rw [sLev, kappaB_R]
  have hdet : (BQ p j).val.det = (p.val : ℚ) := by
    rw [BQ_val, show ((Bl p j).map (Int.castRingHom ℚ)).det = (((Bl p j).det : ℤ) : ℚ) from
      (RingHom.map_det (Int.castRingHom ℚ) (Bl p j)).symm, Bl_det]
    simp
  rw [hdet]
  simp

theorem kappaB_sRad (p : Nat.Primes) (d : Fin p.val × Fin p.val) (v : HomogeneousPoly n) :
    kappaB n (ρn n (sRad p d) v) = (((epsP p : ℂ))⁻¹) ^ (n + 1) * kappaB n v := by
  rw [sRad, kappaB_R]
  have h : algebraMap ℚ ℂ (((epsU p)⁻¹ : ℚˣ) : ℚ) = ((epsP p : ℤ) : ℂ)⁻¹ := by
    simp [epsU_val]
  have h2 : algebraMap ℚ ℂ (((epsU p : ℚˣ) : ℚ) * (1 : GL (Fin 2) ℚ).val.det) =
      ((epsP p : ℤ) : ℂ) := by
    simp [epsU_val]
  rw [h, h2]
  ring

end TernaryPeriodPolynomials.LevelThree.BadLineKappa
