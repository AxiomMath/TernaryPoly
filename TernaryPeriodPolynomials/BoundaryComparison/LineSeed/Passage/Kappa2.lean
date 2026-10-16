module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Passage.Kappa
public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Passage.Uniq

@[expose] public section


/-!
# The reflection acts on the line seed cochain by the opposite seed (Passage 9)

`kappa_chain`: for forms `f, g` whose moment primitives are related by `\overline{G^f_j(-\bar z)} = (-1)^{j+1} G^g_j(z)` (the case `g = f^*`, `momentPrim_reflect`), the zig-zag cochain of `f` on the
conjugate pair `(κxκ, κyκ)` is `-ρ(κ)` applied to the coefficientwise conjugate of the cochain of `g` on `(x, y)`.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open GeneralEisenstein Matrix MvPolynomial ComplexConjugate

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.Argument.LineSeed
open TernaryPeriodPolynomials.Argument.SeedC3 hiding toPoly_cuspSeedCochain cuspSeedCochain cuspSeedInv cuspSeedClass
  cuspSeedConjClass cuspSeedConjInv cuspSeedCochain_cocycle cuspSeedConjCochain cuspSeedConjCochain_eq
  cuspSeedConjCochain_cocycle deRhamClass_cuspSeed deRhamClass_cuspSeedConj cuspSeedDatum
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.SeedC3S4c (Lvl1 ambRep fStar)

/-- The real matrix of `κ`. -/
def Kmat : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![-1, 1, -1]

theorem Kmat_mul_self : Kmat * Kmat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Kmat, Matrix.mul_apply, Fin.sum_univ_three]

theorem det_Kmat : Kmat.det = 1 := by simp [Kmat, Matrix.det_diagonal, Fin.prod_univ_three]

theorem Kmat_inv : Kmat⁻¹ = Kmat := Matrix.inv_eq_right_inv Kmat_mul_self

theorem realMat_kapSL : realMat kapSL = Kmat := by
  ext i j
  rw [realMat_apply]
  fin_cases i <;> fin_cases j <;> simp [kapSL, kapSign, Kmat]

theorem realMat_kapConj (x : ↥lineStab) :
    realMat (kapConj x).1 = Kmat * realMat x.1 * Kmat := by
  change realMat (kapSL * x.1 * kapSL) = _
  rw [realMat_mul, realMat_mul, realMat_kapSL]

theorem rho_Kmat_mono (n j : ℕ) :
    rho Kmat (X 2 ^ j * X 1 ^ (n - j) : MvPolynomial (Fin 3) ℂ) = C ((-1 : ℂ) ^ j) * (X 2 ^ j * X 1 ^ (n - j)) := by
  unfold rho
  rw [det_Kmat, Kmat_inv]
  have hσ : (fun i : Fin 3 => ∑ k : Fin 3, C (((Kmat i k : ℝ)) : ℂ) * (X k : MvPolynomial (Fin 3) ℂ)) =
      ![-X 0, X 1, -X 2] := by
    funext i
    fin_cases i <;> simp [Kmat, Fin.sum_univ_three]
  rw [hσ]
  simp only [map_mul, map_pow, bind₁_X_right, inv_one, Complex.ofReal_one, map_one, one_mul]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [neg_pow, map_neg, map_one]
  ring

theorem rho_kap_conj (x : ↥lineStab) (q : MvPolynomial (Fin 3) ℂ) :
    rho (lineStabData.lmat (kapConj x)) q = rho Kmat (rho (lineStabData.lmat x) (rho Kmat q)) := by
  rw [lineStab_lmat, lineStab_lmat, realMat_kapConj, rho_mul, rho_mul]

/-- **The reflection `κ` exchanges the line seed cochains of `f` and of its reflection `g`** (exact identity of closed forms). -/
theorem kappa_chain {n : ℕ} (f g : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ))
    (hfg : ∀ (j : ℕ) (z : ℂ), 0 < z.im →
      conj (momentPrim Lvl1 n f j (-conj z)) = (-1 : ℂ) ^ (j + 1) * momentPrim Lvl1 n g j z) (x y : ↥lineStab) :
    Coef.toPoly (cuspSeedCochain lineStabData lineStab_lam_mem (f := f) (kapConj x) (kapConj y)) =
      -rho Kmat (MvPolynomial.map (starRingEnd ℂ)
        (Coef.toPoly (cuspSeedCochain lineStabData lineStab_lam_mem (f := g) x y))) := by
  rw [toPoly_cuspSeedCochain, toPoly_cuspSeedCochain, map_sum, rho_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hτ := mob_kapConj y
  have hG0 : ∀ i : ℕ, momentPrim Lvl1 n f i (mob (lineStabData.lam (kapConj y)) Complex.I) =
      (-1 : ℂ) ^ (i + 1) * conj (momentPrim Lvl1 n g i (mob (lineStabData.lam y) Complex.I)) := by
    intro i
    rw [hτ]
    have h := hfg i (mob (lineStabData.lam y) Complex.I) (mob_I_im_pos lineStabData y)
    have h2 := congrArg (starRingEnd ℂ) h
    simp only [Complex.conj_conj, map_mul, map_pow, map_neg, map_one] at h2
    exact h2
  have hmono : MvPolynomial.map (starRingEnd ℂ) (X 2 ^ j * X 1 ^ (n - j) : MvPolynomial (Fin 3) ℂ) =
      X 2 ^ j * X 1 ^ (n - j) := by simp
  set P : MvPolynomial (Fin 3) ℂ := rho Kmat (rho (lineStabData.lmat x) (X 2 ^ j * X 1 ^ (n - j))) with hP
  have hL : rho (lineStabData.lmat (kapConj x)) (X 2 ^ j * X 1 ^ (n - j) : MvPolynomial (Fin 3) ℂ) =
      C ((-1 : ℂ) ^ j) * P := by
    rw [rho_kap_conj, rho_Kmat_mono, rho_C_mul, rho_C_mul]
  have hR : rho Kmat (MvPolynomial.map (starRingEnd ℂ) (C ((n.choose j : ℂ) * (-1) ^ (n - j) *
      ((lineStabData.v x 0 : ℂ) * momentPrim Lvl1 n g (j + 1) (mob (lineStabData.lam y) Complex.I) +
        (lineStabData.v x 1 : ℂ) * momentPrim Lvl1 n g j (mob (lineStabData.lam y) Complex.I))) *
      rho (lineStabData.lmat x) (X 2 ^ j * X 1 ^ (n - j)))) =
      C (conj ((n.choose j : ℂ) * (-1) ^ (n - j) *
      ((lineStabData.v x 0 : ℂ) * momentPrim Lvl1 n g (j + 1) (mob (lineStabData.lam y) Complex.I) +
        (lineStabData.v x 1 : ℂ) * momentPrim Lvl1 n g j (mob (lineStabData.lam y) Complex.I)))) * P := by
    rw [map_mul, MvPolynomial.map_C, map_conj_rho, hmono, rho_C_mul]
  rw [hL, hR, hG0 j, hG0 (j + 1), kapConj_v]
  have key : ((n.choose j : ℂ) * (-1) ^ (n - j) *
        (((![-(lineStabData.v x 0), lineStabData.v x 1] 0 : ℝ) : ℂ) *
            ((-1 : ℂ) ^ (j + 1 + 1) * conj (momentPrim Lvl1 n g (j + 1) (mob (lineStabData.lam y) Complex.I))) +
          ((![-(lineStabData.v x 0), lineStabData.v x 1] 1 : ℝ) : ℂ) *
            ((-1 : ℂ) ^ (j + 1) * conj (momentPrim Lvl1 n g j (mob (lineStabData.lam y) Complex.I)))))
        * (-1 : ℂ) ^ j =
      -conj ((n.choose j : ℂ) * (-1) ^ (n - j) *
        ((lineStabData.v x 0 : ℂ) * momentPrim Lvl1 n g (j + 1) (mob (lineStabData.lam y) Complex.I) +
          (lineStabData.v x 1 : ℂ) * momentPrim Lvl1 n g j (mob (lineStabData.lam y) Complex.I))) := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_mul, map_pow, map_neg,
      map_one, map_natCast, Complex.conj_ofReal, Complex.ofReal_neg]
    have ht : ((-1 : ℂ) ^ j) * (-1) ^ j = 1 := by rw [← mul_pow]; norm_num
    have e1 : ((-1 : ℂ) ^ (j + 1 + 1)) = (-1) ^ j := by rw [pow_succ, pow_succ]; ring
    have e2 : ((-1 : ℂ) ^ (j + 1)) = -(-1) ^ j := by rw [pow_succ]; ring
    rw [e1, e2]
    linear_combination (-(↑(n.choose j) * (-1 : ℂ) ^ (n - j) * ((lineStabData.v x 0 : ℂ) *
      conj (momentPrim Lvl1 n g (j + 1) (mob (lineStabData.lam y) Complex.I)) + (lineStabData.v x 1 : ℂ) *
      conj (momentPrim Lvl1 n g j (mob (lineStabData.lam y) Complex.I))))) * ht
  rw [← mul_assoc, ← map_mul, key, map_neg, neg_mul]

theorem momentPrim_reflect_symm {n : ℕ} (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) (j : ℕ) (z : ℂ) (hz : 0 < z.im) :
    conj (momentPrim Lvl1 n (fStar f) j (-conj z)) = (-1 : ℂ) ^ (j + 1) * momentPrim Lvl1 n f j z := by
  have hw : 0 < (-conj z).im := by simpa using hz
  have h := momentPrim_reflect f j (-conj z) hw
  have h2 := congrArg (starRingEnd ℂ) h
  simp only [Complex.conj_conj, map_neg, map_mul, map_pow, map_one] at h2
  -- `h2 : G j (-conj (-conj z)) = (-1)^(j+1) * conj (G* j (-conj z))`
  rw [neg_neg] at h2
  have h3 : conj (momentPrim Lvl1 n (fStar f) j (-conj z)) = (-1 : ℂ) ^ (j + 1) * momentPrim Lvl1 n f j z := by
    have h4 : ((-1 : ℂ) ^ (j + 1)) * ((-1 : ℂ) ^ (j + 1)) = 1 := by rw [← mul_pow]; norm_num
    calc conj (momentPrim Lvl1 n (fStar f) j (-conj z))
        = ((-1 : ℂ) ^ (j + 1)) * (((-1 : ℂ) ^ (j + 1)) * conj (momentPrim Lvl1 n (fStar f) j (-conj z))) := by
          rw [← mul_assoc, h4, one_mul]
      _ = _ := by rw [← h2]
  exact h3

/-- The reflection-isotypic seed cochain `c_f - \overline{c_{f^*}}` (for odd `n`, the combination `σ_f + (-1)^n \overline{σ_{f^*}}`). -/
def seedComb {n : ℕ} (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) (x y : ↥lineStab) : Coef n :=
  cuspSeedCochain lineStabData lineStab_lam_mem (f := f) x y +
    (((-1 : ℝ) ^ n : ℝ) : ℂ) • cuspSeedConjCochain lineStabData lineStab_lam_mem (f := fStar f) x y

/-- **The reflection `κ` fixes the seed combination** (odd `n`): `β(κxκ, κyκ) = ρ(κ) β(x, y)`, exactly, at the level of cochains. -/
theorem seedComb_kappa {n : ℕ} (hn : Odd n) (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) (x y : ↥lineStab) :
    Coef.toPoly (seedComb f (kapConj x) (kapConj y)) = rho Kmat (Coef.toPoly (seedComb f x y)) := by
  have h1 := kappa_chain f (fStar f) (momentPrim_reflect f) x y
  have h2 := kappa_chain (fStar f) f (momentPrim_reflect_symm f) x y
  have hneg : (((-1 : ℝ) ^ n : ℝ) : ℂ) = -1 := by rw [hn.neg_one_pow]; simp
  unfold seedComb
  rw [Coef.toPoly_add, Coef.toPoly_add, Coef.toPoly_smul, Coef.toPoly_smul, hneg, h1,
    cuspSeedConjCochain_eq, cuspSeedConjCochain_eq, Coef.toPoly_conjCoef, Coef.toPoly_conjCoef, h2]
  set A := (cuspSeedCochain lineStabData lineStab_lam_mem (f := f) x y).toPoly
  set B := (cuspSeedCochain lineStabData lineStab_lam_mem (f := fStar f) x y).toPoly
  have hcc : MvPolynomial.map (starRingEnd ℂ) (MvPolynomial.map (starRingEnd ℂ) A) = A := by
    rw [MvPolynomial.map_map]
    have : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := by ext z; simp
    rw [this, MvPolynomial.map_id]
  have hadd : ∀ P Q : MvPolynomial (Fin 3) ℂ, rho Kmat (P + Q) = rho Kmat P + rho Kmat Q := by
    intro P Q; unfold rho; rw [map_add, mul_add]
  have e1 : MvPolynomial.map (starRingEnd ℂ) (-rho Kmat (MvPolynomial.map (starRingEnd ℂ) A)) =
      -rho Kmat A := by
    rw [map_neg, map_conj_rho, hcc]
  have e2 : (C (-1 : ℂ) : MvPolynomial (Fin 3) ℂ) = -1 := by rw [map_neg, map_one]
  rw [e1, hadd, rho_C_mul, e2]
  ring

end TernaryPeriodPolynomials.Argument.LineSeed
