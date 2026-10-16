module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Cell.KPos
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.ReflectionSeed

@[expose] public section


/-!
# The cell with bottom entry `-1`: the finite reflection

Paper: Lemma C.3 ("the finite
reflection projection supplies the corresponding full-level statement").

If the cell element `k γ ∈ P(ℤ)` has bottom entry `-1` (Levi determinant `-1`; not covered by the
determinant-one Levi law), write `k γ = M r'` with `M ∈ planeStab` (Levi block `A ∈ SL₂(ℤ)`) and
`r' = diag(1, -1, -1) ∈ SL₃(ℤ)` (`rPrime`). `r'` acts on `Ω` as the reflection
`(u₁, u₂, x, y, t) ↦ (-u₁, u₂, -x, y, t)` (`planeAct_rPrime`) and on `E_n` by
`ρ(r')⁻¹ q = q(X₀, -X₁, -X₂)` (`rho_rPrime_inv_eq`). By `SeedC3.refl_pullback` the summand
`ρ(r')⁻¹ r'^* ω_{h|A}` is the coefficientwise conjugate of the seed of `(f|A)^*`
(`summandPoly_mul_rPrime_coeff`, with no sign: the signs `(-1)^n` of the substitution and of
`ρ(r')⁻¹` cancel on homogeneous polynomials of degree `n`, `rho_rPrime_refl`).
`faceSeriesK_class_neg`: the class of the face form is the class of the antiholomorphic seed of
`(f|A)^*`. `faceSeriesK_class_none`: without a cell the class is zero.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open MvPolynomial
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham
open TernaryPeriodPolynomials.Argument.SeedC3.Psi TernaryPeriodPolynomials.Argument.Statements.EisensteinClass
open TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4

section Refl

/-- The integral matrix `diag(1, -1, -1) ∈ SL₃(ℤ)`. -/
def rPrime : SL(3, ℤ) :=
  ⟨!![1, 0, 0; 0, -1, 0; 0, 0, -1], by
    rw [Matrix.det_fin_three]; simp⟩

theorem rPrime_val : (rPrime : Matrix (Fin 3) (Fin 3) ℤ) = !![1, 0, 0; 0, -1, 0; 0, 0, -1] := rfl

theorem rPrime_mul_self : rPrime * rPrime = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, rPrime_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem rPrime_inv : rPrime⁻¹ = rPrime := inv_eq_of_mul_eq_one_right rPrime_mul_self

theorem realMat_rPrime : realMat rPrime = !![1, 0, 0; 0, -1, 0; 0, 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [realMat_apply, rPrime_val]

theorem planeGram_refl (y : Fin 5 → ℝ) :
    realMat rPrime * planeGram y * (realMat rPrime).transpose = planeGram (reflMap5 y) := by
  rw [realMat_rPrime]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeGram, reflMap5, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose] <;> ring

theorem reflMap5_mem {y : Fin 5 → ℝ} (hy : y ∈ Omega) : reflMap5 y ∈ Omega := by
  obtain ⟨h3, h4⟩ := hy
  exact ⟨by simpa [reflMap5] using h3, by simpa [reflMap5] using h4⟩

/-- **`diag(1, -1, -1)` acts on `Ω` as the reflection** `(u₁, u₂, x, y, t) ↦ (-u₁, u₂, -x, y, t)`. -/
theorem planeAct_rPrime {y : Fin 5 → ℝ} (hy : y ∈ Omega) :
    planeAct (realMat rPrime) y = reflMap5 y := by
  unfold planeAct
  rw [planeGram_refl]
  exact planePoint_planeGram (reflMap5_mem hy)

theorem bind₁_neg_X_hom {n : ℕ} (Q : MvPolynomial (Fin 3) ℂ) (hQ : Q.IsHomogeneous n) :
    bind₁ (fun i : Fin 3 => -(X i : MvPolynomial (Fin 3) ℂ)) Q = C ((-1 : ℂ) ^ n) * Q := by
  conv_lhs => rw [Q.as_sum]
  conv_rhs => rw [Q.as_sum]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [bind₁_monomial, monomial_eq]
  have hn := hQ.degree_eq_sum_deg_support hd
  have hp : ∀ i, (-(X i : MvPolynomial (Fin 3) ℂ)) ^ (d i) =
      C ((-1 : ℂ) ^ (d i)) * X i ^ (d i) := fun i => by rw [neg_pow]; simp
  simp only [hp, Finset.prod_mul_distrib, Finsupp.prod]
  rw [← map_prod, Finset.prod_pow_eq_pow_sum, ← hn]
  ring

theorem rho_rPrime_inv_eq (q : MvPolynomial (Fin 3) ℂ) :
    rho (realMat rPrime)⁻¹ q =
      bind₁ (![X 0, -X 1, -X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ) q := by
  have hdet : ((realMat rPrime)⁻¹).det = 1 := by
    rw [Matrix.det_nonsing_inv, det_realMat]; simp
  have hu : IsUnit (realMat rPrime).det := by rw [det_realMat]; exact isUnit_one
  have hinv : ((realMat rPrime)⁻¹)⁻¹ = realMat rPrime := Matrix.nonsing_inv_nonsing_inv _ hu
  unfold rho
  rw [hdet, hinv]
  have : (fun i : Fin 3 => ∑ j : Fin 3, C (((realMat rPrime) i j : ℝ) : ℂ) * (X j : MvPolynomial (Fin 3) ℂ)) =
      (![X 0, -X 1, -X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ) := by
    funext i
    rw [realMat_rPrime]
    fin_cases i <;> simp [Fin.sum_univ_three]
  rw [this]
  simp

theorem rho_rPrime_refl {n : ℕ} (Q : MvPolynomial (Fin 3) ℂ) (hQ : Q.IsHomogeneous n) :
    rho (realMat rPrime)⁻¹ (C ((-1 : ℂ) ^ n) *
      bind₁ (![-X 0, X 1, X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ) Q) = Q := by
  rw [rho_rPrime_inv_eq, map_mul, bind₁_C_right, bind₁_bind₁]
  have : (fun i : Fin 3 => bind₁ (![X 0, -X 1, -X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ)
      ((![-X 0, X 1, X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ) i)) =
      fun i : Fin 3 => -(X i : MvPolynomial (Fin 3) ℂ) := by
    funext i
    fin_cases i <;> simp
  rw [this, bind₁_neg_X_hom Q hQ, ← mul_assoc, ← map_mul, ← mul_pow]
  simp

end Refl

section Neg

open ComplexConjugate

variable (N : ℕ) (k : SL(3, ℤ)) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

theorem cell_entry_pm_one {c₀ : Ck N k} (hc : IsCellK N k c₀) :
    ((cellMat N k c₀ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = 1 ∨
      ((cellMat N k c₀ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = -1 := by
  obtain ⟨h0, h1⟩ := hc
  rw [cuspRow_out] at h0 h1
  have hdet : ((cellMat N k c₀ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ).det = 1 :=
    (cellMat N k c₀).2
  have h0' : ((cellMat N k c₀ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0 := h0
  have h1' : ((cellMat N k c₀ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = 0 := h1
  rw [Matrix.det_fin_three, h0', h1'] at hdet
  have hu : IsUnit (((cellMat N k c₀ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2) :=
    IsUnit.of_mul_eq_one
      (((cellMat N k c₀ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 0 0 *
        ((cellMat N k c₀ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 1 1 -
        ((cellMat N k c₀ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 0 1 *
        ((cellMat N k c₀ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 1 0) (by linear_combination hdet)
  exact Int.isUnit_iff.mp hu

theorem cellMat_mul_rPrime_mem {c₀ : Ck N k} (hc : IsCellK N k c₀)
    (h22 : ((cellMat N k c₀ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = -1) :
    cellMat N k c₀ * rPrime ∈ planeStab := by
  obtain ⟨h0, h1⟩ := hc
  rw [cuspRow_out] at h0 h1
  have h0' : ((cellMat N k c₀ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0 := h0
  have h1' : ((cellMat N k c₀ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = 0 := h1
  rw [Matrix.SpecialLinearGroup.coe_mul] at *
  refine ⟨?_, ?_, ?_⟩
  · simp [rPrime_val, Matrix.mul_apply, Fin.sum_univ_three, h0']
  · simp [rPrime_val, Matrix.mul_apply, Fin.sum_univ_three, h1']
  · simp [rPrime_val, Matrix.mul_apply, Fin.sum_univ_three, h22]

/-- The summand of an element of the plane stabilizer is the seed of `h|A`. -/
theorem summandPoly_planeStab (h : ℂ → ℂ) {M : SL(3, ℤ)} (hM : M ∈ planeStab)
    {z : Fin 5 → ℝ} (hz : z ∈ Omega) (a b : Fin 5) :
    summandPoly n h (realMat M) z a b =
      seedForm n (slashTwisted (n + 3) (topBlock (realMat M)) h) z a b := by
  have e1 : realMat M = parabolicMatrix (topBlock (realMat M)) (sideVec (realMat M)) * 1 := by
    rw [Matrix.mul_one]; exact realMat_stab_eq hM
  have hone : (1 : Matrix (Fin 3) (Fin 3) ℝ).det = 1 := Matrix.det_one
  have e3 := summandPoly_parabolic_mul n h _ (det_topBlock hM) (sideVec (realMat M)) hone hz a b
  rw [← e1] at e3
  rw [e3, ← realMat_one]; exact summandPoly_one n _ hz a b

/-- **Reflection of the seed by `diag(1, -1, -1)`**: for `M ∈ P(ℤ)` with Levi block `A ∈ SL₂(ℤ)`, the
summand at `M r'` is the conjugate seed of `(f|A)^*` (no sign). -/
theorem summandPoly_mul_rPrime_coeff (M : SL(3, ℤ)) (hM : M ∈ planeStab) {y : Fin 5 → ℝ}
    (hy : y ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ) :
    (summandPoly n (hfun f) (realMat (M * rPrime)) y i j).coeff m =
      (MvPolynomial.map (starRingEnd ℂ) (seedForm n (cuspH (leviGroup N) n
        (fStarGen (leviGroup N) (leviGroup_J_stable N)
          (cuspSlash N n (leviBlock M hM) f))) y i j)).coeff m := by
  rw [realMat_mul]
  set A : SL(2, ℤ) := leviBlock M hM with hAdef
  have hAmat : topBlock (realMat M) =
      ((Matrix.SpecialLinearGroup.mapGL ℝ A : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) :=
    (coe_mapGL_leviBlock M hM).symm
  set hA : ℂ → ℂ := slashTwisted (n + 3) (topBlock (realMat M)) (hfun f) with hAdef'
  have hrefl : planeAct (realMat rPrime) =ᶠ[nhds y] reflMap5 :=
    Filter.eventuallyEq_of_mem (isOpen_Omega.mem_nhds hy) fun z hz => planeAct_rPrime hz
  have hyr : planeAct (realMat rPrime) y ∈ Omega := planeAct_mem (det_realMat rPrime) hy
  rw [summandPoly_mul_eq n (hfun f) (det_realMat M) (det_realMat rPrime) hy i j]
  have h1 : formPullback (planeAct (realMat rPrime))
      (fun y' a b => summandPoly n (hfun f) (realMat M) y' a b) y i j =
      formPullback (planeAct (realMat rPrime)) (seedForm n hA) y i j := by
    refine formPullback_congr_form y (fun a b => ?_) i j
    exact summandPoly_planeStab n (hfun f) hM hyr a b
  rw [h1, formPullback_congr _ hrefl]
  have hhs : (hStar hA) (seedTau y) = conj (hA (-conj (seedTau y))) := rfl
  rw [refl_pullback n hA (hStar hA) y hhs i j]
  have hhom : (MvPolynomial.map (starRingEnd ℂ) (seedForm n (hStar hA) y i j)).IsHomogeneous n :=
    (seedForm_isHomogeneous n (hStar hA) y i j).map _
  rw [rho_rPrime_refl _ hhom]
  congr 3
  refine seedForm_congr_value n _ _ y ?_ i j
  have hτ := seedTau_im_pos hy
  have hτ' : 0 < (-(conj (seedTau y))).im := by simpa using hτ
  rw [fStarGen_cuspH (leviGroup N) (leviGroup_J_stable N) (cuspSlash N n A f) hτ]
  show conj (hA (-conj (seedTau y))) = conj (cuspH (leviGroup N) n (cuspSlash N n A f)
    (-conj (seedTau y)))
  congr 1
  rw [hAdef', hAmat]
  exact slashTwisted_cuspSlash N n A f hτ'

/-- **The cell of bottom entry `-1` is the antiholomorphic seed of `(f|A)^*`.** -/
theorem cell_neg_coeff [NeZero N] (hN : 3 ≤ N) {c₀ : Ck N k} (hc : IsCellK N k c₀)
    (h22 : ((cellMat N k c₀ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = -1)
    {y : Fin 5 → ℝ} (hy : y ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ) :
    cellCoeffK N k n f y i j m =
      (MvPolynomial.map (starRingEnd ℂ) (seedForm n (cuspH (leviGroup N) n
        (fStarGen (leviGroup N) (leviGroup_J_stable N)
          (cuspSlash N n (leviBlock (cellMat N k c₀ * rPrime) (cellMat_mul_rPrime_mem N k hc h22))
            f))) y i j)).coeff m := by
  have hM := cellMat_mul_rPrime_mem N k hc h22
  rw [cellCoeffK_eq N k n f hN hc y i j m]
  have := summandPoly_mul_rPrime_coeff N n f _ hM hy i j m
  rw [mul_assoc, rPrime_mul_self, mul_one] at this
  exact this

open ContinuousAlternatingMap in
/-- Coordinates of the antiholomorphic seed form: the conjugate of the coordinates of the seed. -/
theorem toPoly_cuspSeedConjInv {Λ : Subgroup (GL (Fin 2) ℝ)} [Λ.HasDetOne] {G : Type} [Group G]
    (D : PlaneData G) (hΛ : ∀ g, (D.lam g : GL (Fin 2) ℝ) ∈ Λ)
    (f' : CuspForm Λ ((n + 3 : ℕ) : ℤ)) {x : Face} (hx : x ∈ faceSet) (i j : Fin 4) :
    Coef.toPoly ((((cuspSeedConjInv D hΛ (f := f') : ZigZag.invClosed isOpen_faceSet D.action
        (D.rhoR n)) : Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) x
          ![Pi.single i 1, Pi.single j 1]) =
      MvPolynomial.map (starRingEnd ℂ) (seedForm n (cuspH Λ n f') (ptOf x) i.castSucc
        j.castSucc) := by
  change Coef.toPoly (((ZigZag.twForm (conjCLM n) 2 (d isOpen_faceSet 1
    (etaForm (cuspH Λ n f') (cuspH_holo Λ n f') n)) : Form (F := Coef n) faceSet 2) :
      RawForm Face (Coef n) 2) x ![Pi.single i 1, Pi.single j 1]) = _
  rw [ZigZag.twForm_apply, coefficientFormMap_apply]
  exact congrArg (MvPolynomial.map (starRingEnd ℂ))
    (PlaneData.toPoly_d_etaForm (cuspH Λ n f') n (cuspH_holo Λ n f') hx i j)

/-- **The class of the face form at a cusp with a negative cell is the conjugate seed class of
`(f|A)^*`.** -/
theorem faceSeriesK_class_neg [NeZero N] (hN : 3 ≤ N) (hn : 4 ≤ n) {c₀ : Ck N k}
    (hc : IsCellK N k c₀)
    (h22 : ((cellMat N k c₀ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = -1) :
    ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (gammaNPlaneData N).action
        ((gammaNPlaneData N).rhoR n) (faceSeriesK N k n f hn) =
      ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (gammaNPlaneData N).action
        ((gammaNPlaneData N).rhoR n)
        (cuspSeedConjInv (gammaNPlaneData N) (gammaNPlaneData_lam_mem N)
          (f := fStarGen (leviGroup N) (leviGroup_J_stable N)
            (cuspSlash N n (leviBlock (cellMat N k c₀ * rPrime)
              (cellMat_mul_rPrime_mem N k hc h22)) f))) := by
  refine classK_eq N k n f hn _ ?_
  intro y hy i j m
  rw [toPoly_cuspSeedConjInv n (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) _ hy i j,
    cell_neg_coeff N k n f hN hc h22 (ptOf_mem hy)]

/-- **A form with no cell has zero class.** -/
theorem faceSeriesK_class_none [NeZero N] (hn : 4 ≤ n) (hnone : ∀ c : Ck N k, ¬ IsCellK N k c) :
    ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (gammaNPlaneData N).action
        ((gammaNPlaneData N).rhoR n) (faceSeriesK N k n f hn) = 0 := by
  have h := classK_eq N k n f hn 0 (fun y hy i j m => by
    rw [cellCoeffK_eq_zero N k n f hnone]
    simp)
  rw [h, _root_.map_zero]

end Neg

end TernaryPeriodPolynomials.Argument.EisensteinClass
