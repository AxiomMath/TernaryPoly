module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Line.Average

@[expose] public section


/-!
# The coefficient transport `ρ(qMat v)` of the radical of the line group `Q`: a unipotent representation of `ℝ²`

Formalized by Claude Sonnet 5.5.

The radical `{u(s,t)}` of the line parabolic `Q` acts on `E_n` by `ρ(u(s,t))`.  Transported along the involution `ȷ` (`g ↦ J (g⁻¹)ᵗ J`) to the plane face, the translation `t_v` becomes
`qMat v = [[1, -v₁, -v₀], [0, 1, 0], [0, 0, 1]]` (`= rt (t_{-v})`) and the radical acts on the coefficients by `sQ n v = ρ(qMat v)`.  This is the dual of `trL`: the substitution is
`X₀ ↦ X₀ + v₁X₁ + v₀X₂` instead of `X₀ ↦ X₀ - v₀X₂, X₁ ↦ X₁ - v₁X₂`.
* `qMat`, `qHom`, `qRep`, `sQ`, `toPoly_sQ`, `sQ_add`, `sQ_zero`;
* `rho_qMat`, `contDiff_sQ` (smoothness in `v`);
* `dQ_lowers`, `sQ_sub_one_pow_eq_zero` (`(sQ v - 1)^{n+1} = 0`: the substitution strictly lowers the `X₀`-degree), `uniRep_sQ` (a `UniRep`).
-/

open MvPolynomial
open scoped MatrixGroups ContDiff
noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham
open TernaryPeriodPolynomials.Argument.EisensteinClass
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3

/-- The unipotent matrix `[[1, -v₁, -v₀], [0, 1, 0], [0, 0, 1]]` (the image of the translation `t_v` under `ȷ`). -/
def qMat (v : Fin 2 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![1, -v 1, -v 0; 0, 1, 0; 0, 0, 1]

theorem qMat_mul (v w : Fin 2 → ℝ) : qMat v * qMat w = qMat (v + w) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem qMat_zero : qMat 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qMat]

theorem det_qMat (v : Fin 2 → ℝ) : (qMat v).det = 1 := by
  rw [Matrix.det_fin_three]; simp [qMat]

theorem qMat_inv (v : Fin 2 → ℝ) : (qMat v)⁻¹ = qMat (-v) :=
  Matrix.inv_eq_right_inv (by rw [qMat_mul, add_neg_cancel, qMat_zero])

/-- The one-parameter-family group homomorphism `ℝ² → GL₃(ℝ)`, `v ↦ qMat v`. -/
def qHom : TransGrp →* GL (Fin 3) ℝ where
  toFun s := ⟨qMat (Multiplicative.toAdd s), qMat (-Multiplicative.toAdd s),
    by rw [qMat_mul, add_neg_cancel, qMat_zero], by rw [qMat_mul, neg_add_cancel, qMat_zero]⟩
  map_one' := by
    ext i j
    simp [qMat_zero]
  map_mul' s t := by
    ext i j
    simp [qMat_mul]

/-- The complex coefficient representation of the translation group through `qHom`. -/
def qRepC (n : ℕ) : Representation ℂ TransGrp (GeneralEisenstein.HomogeneousPoly n) :=
  (GeneralEisenstein.realCoefficient n).comp qHom

theorem qRepC_coe (n : ℕ) (s : TransGrp) (q : GeneralEisenstein.HomogeneousPoly n) :
    ((qRepC n s q : GeneralEisenstein.HomogeneousPoly n) : MvPolynomial (Fin 3) ℂ) =
      rho (qMat (Multiplicative.toAdd s)) (q : MvPolynomial (Fin 3) ℂ) := by
  have hinv : (qMat (Multiplicative.toAdd s))⁻¹ = qMat (-Multiplicative.toAdd s) := qMat_inv _
  have hdet := det_qMat (Multiplicative.toAdd s)
  unfold qRepC
  change ((GeneralEisenstein.action (-1)
    (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) (qHom s))) (q : MvPolynomial (Fin 3) ℂ)) = _
  rw [GeneralEisenstein.action_apply]
  unfold rho GeneralEisenstein.substitute GeneralEisenstein.linearForm
  rw [hinv, hdet]
  simp [GeneralEisenstein.determinantCharacter, Matrix.GeneralLinearGroup.map, qHom]
  have hd : ((qMat (Multiplicative.toAdd s)).map Complex.ofReal).det = 1 := by
    have := RingHom.map_det Complex.ofRealHom (qMat (Multiplicative.toAdd s))
    rw [hdet, map_one] at this
    exact this.symm
  rw [hd, inv_one, one_smul]

/-- The real form of `qRepC` on `Coef n`. -/
def qRep (n : ℕ) : Representation ℝ TransGrp (Coef n) where
  toFun s := (qRepC n s : Coef n →ₗ[ℂ] Coef n).restrictScalars ℝ
  map_one' := by
    refine LinearMap.ext fun q => ?_
    change qRepC n 1 q = q
    rw [map_one]; rfl
  map_mul' s t := by
    refine LinearMap.ext fun q => ?_
    change qRepC n (s * t) q = qRepC n s (qRepC n t q)
    rw [map_mul]; rfl

/-- The coefficient transport `ρ(qMat v)` of the radical `Nℤ²` of `Q` (the image of `ρ(t_v)` under `ȷ`). -/
def sQ (n : ℕ) (v : Fin 2 → ℝ) : Coef n →L[ℝ] Coef n :=
  ZigZag.repCLM (qRep n) (Multiplicative.ofAdd v)

theorem toPoly_sQ (n : ℕ) (v : Fin 2 → ℝ) (q : Coef n) :
    Coef.toPoly (sQ n v q) = rho (qMat v) (Coef.toPoly q) :=
  qRepC_coe n (Multiplicative.ofAdd v) q

theorem sQ_add (n : ℕ) (v w : Fin 2 → ℝ) : sQ n (v + w) = sQ n v * sQ n w := by
  unfold sQ
  rw [ofAdd_add, ZigZag.repCLM_mul]
  rfl

theorem sQ_zero (n : ℕ) : sQ n 0 = ContinuousLinearMap.id ℝ (Coef n) := by
  ext q
  apply Coef.toPoly_injective
  rw [toPoly_sQ, qMat_zero, rho_one]
  rfl

theorem rho_qMat (v : Fin 2 → ℝ) (q : MvPolynomial (Fin 3) ℂ) :
    bind₁ (![X 0 + C ((v 1 : ℝ) : ℂ) * X 1 + C ((v 0 : ℝ) : ℂ) * X 2, X 1, X 2] :
      Fin 3 → MvPolynomial (Fin 3) ℂ) q = rho (qMat v) q := by
  unfold rho
  rw [qMat_inv, det_qMat]
  simp only [inv_one, Complex.ofReal_one, map_one, one_mul]
  congr 1
  congr 1
  funext i
  fin_cases i <;> simp [qMat, Fin.sum_univ_three]

theorem contDiff_coeff_rho_qMat (q : MvPolynomial (Fin 3) ℂ) (e : Fin 3 →₀ ℕ) :
    ContDiff ℝ ∞ (fun v : Fin 2 → ℝ => (rho (qMat v) q).coeff e) := by
  let f : Fin 3 → MvPolynomial (Fin 3 ⊕ Fin 2) ℂ :=
    ![X (Sum.inl 0) + X (Sum.inr 1) * X (Sum.inl 1) + X (Sum.inr 0) * X (Sum.inl 2),
      X (Sum.inl 1), X (Sum.inl 2)]
  let Q : MvPolynomial (Fin 3 ⊕ Fin 2) ℂ := bind₁ f q
  have hs : ∀ a : Fin 2, ContDiffOn ℝ ∞ (fun v : Fin 2 → ℝ => ((v a : ℝ) : ℂ)) Set.univ :=
    fun a => (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ a)).contDiffOn
  have key := Calc.contDiffOn_coeff_spec Set.univ (fun a (v : Fin 2 → ℝ) => ((v a : ℝ) : ℂ)) hs Q e
  have key' : ContDiff ℝ ∞ (fun v : Fin 2 → ℝ =>
      (Calc.spec (fun a => ((v a : ℝ) : ℂ)) Q).coeff e) := contDiffOn_univ.mp key
  have hfun : (fun v : Fin 2 → ℝ => (rho (qMat v) q).coeff e) =
      (fun v : Fin 2 → ℝ => (Calc.spec (fun a => ((v a : ℝ) : ℂ)) Q).coeff e) := by
    funext v
    rw [← rho_qMat]
    congr 2
    simp only [Q, Calc.spec]
    rw [MvPolynomial.aeval_bind₁]
    show aeval _ q = aeval _ q
    congr 2
    funext i
    fin_cases i <;> simp [f]
  rw [hfun]
  exact key'

theorem contDiff_sQ (n : ℕ) : ContDiff ℝ ∞ (fun v : Fin 2 → ℝ => sQ n v) := by
  rw [contDiff_clm_apply_iff]
  intro q
  refine Calc.contDiffOn_of_vec n ?_ |> contDiffOn_univ.mp
  rw [contDiffOn_univ, contDiff_pi]
  intro e
  have := contDiff_coeff_rho_qMat (Coef.toPoly q) (Finsupp.equivFunOnFinite.symm (fun k => (e k : ℕ)))
  change ContDiff ℝ ∞ (fun x : Fin 2 → ℝ =>
    (Coef.toPoly (sQ n x q)).coeff (Finsupp.equivFunOnFinite.symm (fun k => (e k : ℕ))))
  simp only [toPoly_sQ]
  exact this

/-! ### Nilpotency of `ρ(qMat v) - 1` -/

/-- The substitution `X₀ ↦ X₀ + aX₁ + bX₂`, as an algebra endomorphism. -/
def shQ (a b : ℂ) : MvPolynomial (Fin 3) ℂ →ₐ[ℂ] MvPolynomial (Fin 3) ℂ :=
  bind₁ (![X 0 + C a * X 1 + C b * X 2, X 1, X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ)

/-- `shQ a b - id`. -/
def dQ (a b : ℂ) (q : MvPolynomial (Fin 3) ℂ) : MvPolynomial (Fin 3) ℂ := shQ a b q - q

theorem monomial_fin3 (m : Fin 3 →₀ ℕ) (c : ℂ) :
    (monomial m c : MvPolynomial (Fin 3) ℂ) = C c * X 0 ^ m 0 * X 1 ^ m 1 * X 2 ^ m 2 := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
  simp [Fin.prod_univ_three, mul_assoc]

theorem degreeOf_diff_pow (a b : ℂ) (k : ℕ) :
    degreeOf 0 (((X 0 + C a * X 1 + C b * X 2 : MvPolynomial (Fin 3) ℂ)) ^ (k + 1) - X 0 ^ (k + 1)) ≤ k := by
  set Y : MvPolynomial (Fin 3) ℂ := X 0 + C a * X 1 + C b * X 2 with hY
  set L : MvPolynomial (Fin 3) ℂ := C a * X 1 + C b * X 2 with hL
  have hL0 : degreeOf 0 L = 0 := by
    have h1 : degreeOf 0 (C a * (X 1 : MvPolynomial (Fin 3) ℂ)) = 0 := by
      refine le_antisymm ?_ (Nat.zero_le _)
      calc _ ≤ degreeOf 0 (C a : MvPolynomial (Fin 3) ℂ) + degreeOf 0 (X 1 : MvPolynomial (Fin 3) ℂ) :=
            degreeOf_mul_le _ _ _
        _ = 0 := by simp [degreeOf_C, degreeOf_X_of_ne (show (0 : Fin 3) ≠ 1 by decide)]
    have h2 : degreeOf 0 (C b * (X 2 : MvPolynomial (Fin 3) ℂ)) = 0 := by
      refine le_antisymm ?_ (Nat.zero_le _)
      calc _ ≤ degreeOf 0 (C b : MvPolynomial (Fin 3) ℂ) + degreeOf 0 (X 2 : MvPolynomial (Fin 3) ℂ) :=
            degreeOf_mul_le _ _ _
        _ = 0 := by simp [degreeOf_C, degreeOf_X_of_ne (show (0 : Fin 3) ≠ 2 by decide)]
    refine le_antisymm ?_ (Nat.zero_le _)
    calc _ ≤ max (degreeOf 0 (C a * (X 1 : MvPolynomial (Fin 3) ℂ))) (degreeOf 0 (C b * (X 2 : MvPolynomial (Fin 3) ℂ))) :=
          degreeOf_add_le _ _ _
      _ = 0 := by rw [h1, h2]; simp
  have hYL : Y = X 0 + L := by simp only [hY, hL]; ring
  have hY1 : degreeOf 0 Y ≤ 1 := by
    rw [hYL]
    calc _ ≤ max (degreeOf 0 (X 0 : MvPolynomial (Fin 3) ℂ)) (degreeOf 0 L) := degreeOf_add_le _ _ _
      _ ≤ 1 := by rw [hL0]; simp
  induction k with
  | zero =>
    have : Y ^ (0 + 1) - X 0 ^ (0 + 1) = L := by simp [hY, hL]; ring
    rw [this, hL0]
  | succ k ih =>
    have e : Y ^ (k + 1 + 1) - X 0 ^ (k + 1 + 1) = Y * (Y ^ (k + 1) - X 0 ^ (k + 1)) + L * X 0 ^ (k + 1) := by
      simp only [hY, hL]; ring
    rw [e]
    refine (degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
    · calc _ ≤ degreeOf 0 Y + degreeOf 0 (Y ^ (k + 1) - X 0 ^ (k + 1)) := degreeOf_mul_le _ _ _
        _ ≤ k + 1 := by omega
    · calc _ ≤ degreeOf 0 L + degreeOf 0 ((X 0 : MvPolynomial (Fin 3) ℂ) ^ (k + 1)) := degreeOf_mul_le _ _ _
        _ ≤ k + 1 := by
          rw [hL0]
          have := degreeOf_pow_le (0 : Fin 3) (X 0 : MvPolynomial (Fin 3) ℂ) (k + 1)
          simp

theorem dQ_monomial (a b : ℂ) (m : Fin 3 →₀ ℕ) (c : ℂ) :
    dQ a b (monomial m c) = C c * (((X 0 + C a * X 1 + C b * X 2 : MvPolynomial (Fin 3) ℂ)) ^ m 0 - X 0 ^ m 0) *
      X 1 ^ m 1 * X 2 ^ m 2 := by
  unfold dQ shQ
  rw [monomial_fin3]
  simp only [map_mul, map_pow, bind₁_X_right, bind₁_C_right]
  simp
  ring

theorem dQ_sum {ι : Type*} (a b : ℂ) (s : Finset ι) (f : ι → MvPolynomial (Fin 3) ℂ) :
    dQ a b (∑ i ∈ s, f i) = ∑ i ∈ s, dQ a b (f i) := by
  unfold dQ
  rw [map_sum, Finset.sum_sub_distrib]

theorem dQ_lowers (a b : ℂ) (j : ℕ) (q : MvPolynomial (Fin 3) ℂ) (hq : degreeOf 0 q ≤ j + 1) :
    degreeOf 0 (dQ a b q) ≤ j := by
  rw [q.as_sum, dQ_sum]
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun m hm => ?_)
  have hm0 : m 0 ≤ j + 1 := degreeOf_le_iff.1 hq m (by simpa using hm)
  rw [dQ_monomial]
  rcases Nat.eq_zero_or_pos (m 0) with h0 | hpos
  · simp [h0]
  · obtain ⟨k, hk⟩ : ∃ k, m 0 = k + 1 := ⟨m 0 - 1, by omega⟩
    rw [hk]
    have h1 := degreeOf_diff_pow a b k
    have h2 : degreeOf 0 (C (q.coeff m) * (((X 0 + C a * X 1 + C b * X 2 : MvPolynomial (Fin 3) ℂ)) ^ (k + 1) -
        X 0 ^ (k + 1)) * X 1 ^ m 1 * X 2 ^ m 2) ≤ k := by
      refine (degreeOf_mul_le _ _ _).trans ?_
      have hx2 : degreeOf 0 ((X 2 : MvPolynomial (Fin 3) ℂ) ^ m 2) = 0 := by
        refine le_antisymm ?_ (Nat.zero_le _)
        exact (degreeOf_pow_le _ _ _).trans (by simp [degreeOf_X_of_ne (show (0 : Fin 3) ≠ 2 by decide)])
      have hx1 : degreeOf 0 ((X 1 : MvPolynomial (Fin 3) ℂ) ^ m 1) = 0 := by
        refine le_antisymm ?_ (Nat.zero_le _)
        exact (degreeOf_pow_le _ _ _).trans (by simp [degreeOf_X_of_ne (show (0 : Fin 3) ≠ 1 by decide)])
      rw [hx2, add_zero]
      refine (degreeOf_mul_le _ _ _).trans ?_
      rw [hx1, add_zero]
      refine (degreeOf_mul_le _ _ _).trans ?_
      rw [degreeOf_C]
      simpa using h1
    omega

theorem dQ_eq_zero (a b : ℂ) (q : MvPolynomial (Fin 3) ℂ) (hq : degreeOf 0 q ≤ 0) : dQ a b q = 0 := by
  rw [q.as_sum, dQ_sum]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hm0 : m 0 ≤ 0 := degreeOf_le_iff.1 hq m (by simpa using hm)
  rw [dQ_monomial]
  have : m 0 = 0 := by omega
  simp [this]

theorem dQ_iter_eq_zero (a b : ℂ) (j : ℕ) (q : MvPolynomial (Fin 3) ℂ) (hq : degreeOf 0 q ≤ j) :
    (dQ a b)^[j + 1] q = 0 := by
  induction j generalizing q with
  | zero => simpa using dQ_eq_zero a b q hq
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    exact ih _ (dQ_lowers a b j q hq)

theorem toPoly_sQ_sub_one (n : ℕ) (v : Fin 2 → ℝ) (q : Coef n) :
    Coef.toPoly ((sQ n v - ContinuousLinearMap.id ℝ (Coef n)) q) =
      dQ ((v 1 : ℝ) : ℂ) ((v 0 : ℝ) : ℂ) (Coef.toPoly q) := by
  simp only [_root_.sub_apply, ContinuousLinearMap.id_apply, Coef.toPoly_sub, toPoly_sQ, dQ, shQ]
  rw [rho_qMat]

theorem toPoly_sQ_sub_one_pow (n : ℕ) (v : Fin 2 → ℝ) (j : ℕ) (q : Coef n) :
    Coef.toPoly (((sQ n v - ContinuousLinearMap.id ℝ (Coef n)) ^ j) q) =
      (dQ ((v 1 : ℝ) : ℂ) ((v 0 : ℝ) : ℂ))^[j] (Coef.toPoly q) := by
  induction j generalizing q with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, mul_apply_eq_comp, ih, Function.iterate_succ_apply, toPoly_sQ_sub_one]

theorem sQ_sub_one_pow_eq_zero (n : ℕ) (v : Fin 2 → ℝ) :
    (sQ n v - ContinuousLinearMap.id ℝ (Coef n)) ^ (n + 1) = 0 := by
  ext q
  apply Coef.toPoly_injective
  rw [toPoly_sQ_sub_one_pow]
  have hdeg : degreeOf 0 (Coef.toPoly q) ≤ n := by
    by_cases h0 : Coef.toPoly q = 0
    · rw [h0]; simp
    · exact (degreeOf_le_totalDegree _ _).trans ((Coef.toPoly_isHomogeneous q).totalDegree h0).le
  rw [dQ_iter_eq_zero _ _ n _ hdeg]
  rfl

theorem sQ_sub_one_isNilpotent (n : ℕ) (v : Fin 2 → ℝ) :
    IsNilpotent (sQ n v - ContinuousLinearMap.id ℝ (Coef n)) :=
  ⟨n + 1, sQ_sub_one_pow_eq_zero n v⟩

/-- The coefficient transport `ρ(qMat v)` is a unipotent representation of `ℝ²`. -/
theorem uniRep_sQ (n : ℕ) : UniRep (sQ n) where
  add v w := sQ_add n v w
  zero := sQ_zero n
  smooth := contDiff_sQ n
  nilp v := sQ_sub_one_isNilpotent n v

end TernaryPeriodPolynomials.Argument.FormClassK
