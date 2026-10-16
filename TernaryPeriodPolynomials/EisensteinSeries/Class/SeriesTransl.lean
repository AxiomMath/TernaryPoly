module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Unfold.Sum
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Cusp.Instance
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Cusp.Equivariance
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.ConvergenceC4

@[expose] public section


/-!
# The series at the conjugate cusp `h⁻¹ P h`

For `h ∈ SL₃(ℤ)`, the cosets of `Γ_{h⁻¹Ph} = h⁻¹ Γ_P h ∩ Γ(N)` in `Γ(N)` are in bijection with the
cosets of `Γ_P` (conjugation by `h`), and the Eisenstein series at the cusp `CuspData.ofSL h` is
the translate `ρ(h)⁻¹ h^* 𝓔_P` of the standard one.
-/

open scoped MatrixGroups
open MvPolynomial
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument

/-- **A coefficientwise-summable family of polynomial-valued forms commutes with
`ρ(G) ∘ formPullback`.** -/
theorem coeff_rho_formPullback_tsum {ι : Type*} (n : ℕ) (G : Matrix (Fin 3) (Fin 3) ℝ)
    (Φ : (Fin 5 → ℝ) → (Fin 5 → ℝ)) (y : Fin 5 → ℝ) (i j : Fin 5)
    (u : ι → (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ)
    (U : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ)
    (hUhom : ∀ y' a b, MvPolynomial.IsHomogeneous (U y' a b) n)
    (huhom : ∀ c y' a b, MvPolynomial.IsHomogeneous (u c y' a b) n)
    (hsum : ∀ a b (m' : Fin 3 →₀ ℕ), Summable fun c => (u c (Φ y) a b).coeff m')
    (hUc : ∀ a b (m' : Fin 3 →₀ ℕ), (U (Φ y) a b).coeff m' = ∑' c, (u c (Φ y) a b).coeff m')
    (m : Fin 3 →₀ ℕ) :
    (rho G (formPullback Φ U y i j)).coeff m =
      ∑' c, (rho G (formPullback Φ (u c) y i j)).coeff m := by
  have hU : MvPolynomial.IsHomogeneous (formPullback Φ U y i j) n :=
    formPullback_isHomogeneous U hUhom Φ y i j
  have hu : ∀ c, MvPolynomial.IsHomogeneous (formPullback Φ (u c) y i j) n := fun c =>
    formPullback_isHomogeneous (u c) (huhom c) Φ y i j
  simp_rw [coeff_rho_expansion (hU) G m]
  have h2 : ∀ c, (rho G (formPullback Φ (u c) y i j)).coeff m = ∑ m' ∈ monSet n,
      (formPullback Φ (u c) y i j).coeff m' * (rho G (monomial m' 1)).coeff m :=
    fun c => coeff_rho_expansion (hu c) G m
  simp_rw [h2]
  have hc : ∀ (W : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ) m',
      (formPullback Φ W y i j).coeff m' = ∑ a : Fin 5, ∑ b : Fin 5,
        (((fderiv ℝ Φ y (Pi.single i 1) a * fderiv ℝ Φ y (Pi.single j 1) b : ℝ) : ℂ) *
          (W (Φ y) a b).coeff m') := by
    intro W m'
    unfold formPullback
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
  simp_rw [hc, hUc]
  set w : Fin 5 → Fin 5 → ℂ := fun a b => (((fderiv ℝ Φ y (Pi.single i 1) a *
    fderiv ℝ Φ y (Pi.single j 1) b : ℝ) : ℂ)) with hw
  set κ : (Fin 3 →₀ ℕ) → ℂ := fun m' => (rho G (monomial m' 1)).coeff m with hκ
  have hs1 : ∀ m' a b, Summable fun c => w a b * (u c (Φ y) a b).coeff m' :=
    fun m' a b => (hsum a b m').mul_left _
  have hs2 : ∀ m' a, Summable fun c => ∑ b : Fin 5, w a b * (u c (Φ y) a b).coeff m' :=
    fun m' a => summable_sum fun b _ => hs1 m' a b
  have hs3 : ∀ m', Summable fun c => ∑ a : Fin 5, ∑ b : Fin 5, w a b * (u c (Φ y) a b).coeff m' :=
    fun m' => summable_sum fun a _ => hs2 m' a
  have hs4 : ∀ m', Summable fun c => (∑ a : Fin 5, ∑ b : Fin 5, w a b * (u c (Φ y) a b).coeff m') *
      κ m' := fun m' => (hs3 m').mul_right _
  rw [Summable.tsum_finsetSum (fun m' _ => hs4 m')]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [tsum_mul_right, Summable.tsum_finsetSum (fun a _ => hs2 m' a)]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Summable.tsum_finsetSum (fun b _ => hs1 m' a b)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [tsum_mul_left]

/-! ### Reindexing the cosets of the conjugate cusp -/

section Reindex

variable (N : ℕ) (h : SL(3, ℤ))

/-- Conjugation by `h` on `Γ(N)` (normal in `SL₃(ℤ)`). -/
def cjG (a : ↥(gammaN N)) : ↥(gammaN N) :=
  ⟨h * a.1 * h⁻¹, by
    have := (gammaN_normal N).conj_mem _ a.2 h
    simpa [mul_assoc] using this⟩

theorem cjG_val (a : ↥(gammaN N)) : (cjG N h a).1 = h * a.1 * h⁻¹ := rfl

theorem cjG_rel (a b : ↥(gammaN N)) :
    (QuotientGroup.rightRel ((stabRow (CuspData.ofSL h).r).subgroupOf (gammaN N))) a b ↔
      (QuotientGroup.rightRel ((planeStab : Subgroup SL(3, ℤ)).subgroupOf (gammaN N)))
        (cjG N h a) (cjG N h b) := by
  rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf,
    Subgroup.mem_subgroupOf, mem_stabRow_ofSL]
  have : (cjG N h b * (cjG N h a)⁻¹ : ↥(gammaN N)).1 = h * (b * a⁻¹ : ↥(gammaN N)).1 * h⁻¹ := by
    simp [cjG, mul_assoc]
  rw [this]

/-- Conjugation by `h⁻¹` on `Γ(N)`. -/
def cjGinv (a : ↥(gammaN N)) : ↥(gammaN N) := cjG N h⁻¹ a

theorem cjG_cjGinv (a : ↥(gammaN N)) : cjG N h (cjGinv N h a) = a := by
  apply Subtype.ext
  simp [cjG, cjGinv, mul_assoc]

theorem cjGinv_cjG (a : ↥(gammaN N)) : cjGinv N h (cjG N h a) = a := by
  apply Subtype.ext
  simp [cjG, cjGinv, mul_assoc]

/-- **The cosets of the conjugate cusp are the cosets of `Γ_P`**: `Γ_{h⁻¹Ph} γ ↦ Γ_P (hγh⁻¹)`. -/
def cuspCosetEquiv : CuspCoset (gammaN N) (CuspData.ofSL h).r ≃ PlaneCoset (gammaN N) where
  toFun := Quotient.map (cjG N h) (fun a b hab => (cjG_rel N h a b).1 hab)
  invFun := Quotient.map (cjGinv N h) (fun a b hab => by
    have := (cjG_rel N h (cjGinv N h a) (cjGinv N h b)).2
    rw [cjG_cjGinv, cjG_cjGinv] at this
    exact this hab)
  left_inv c := by
    induction c using Quotient.inductionOn with | _ a => ?_
    exact congrArg (Quotient.mk _) (cjGinv_cjG N h a)
  right_inv c := by
    induction c using Quotient.inductionOn with | _ a => ?_
    exact congrArg (Quotient.mk _) (cjG_cjGinv N h a)

theorem cuspCosetEquiv_mk (a : ↥(gammaN N)) :
    cuspCosetEquiv N h (Quotient.mk _ a) = Quotient.mk _ (cjG N h a) := rfl

end Reindex

/-! ### The series at the conjugate cusp is the translated standard series -/

section Translate

variable (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

omit [NeZero N] in
/-- Representative independence of the summand at a point of `Ω`. -/
theorem summandPoly_coset_eq (a b : ↥(gammaN N))
    (hab : (QuotientGroup.rightRel ((planeStab : Subgroup SL(3, ℤ)).subgroupOf (gammaN N))) a b)
    {q : Fin 5 → ℝ} (hq : q ∈ Omega) (i j : Fin 5) :
    summandPoly n (hfun f) (realMat a.1) q i j = summandPoly n (hfun f) (realMat b.1) q i j := by
  apply MvPolynomial.ext
  intro m
  have := Tm_coset N n f a b hab 0 hq i j m
  simpa [Tm, nmat_zero] using this

omit [NeZero N] in
/-- The summand of a coset class, evaluated at a point of `Ω`, through any representative. -/
theorem summandPoly_out_eq (a : ↥(gammaN N)) {q : Fin 5 → ℝ} (hq : q ∈ Omega) (i j : Fin 5) :
    summandPoly n (hfun f) (realMat (Quotient.out (Quotient.mk (QuotientGroup.rightRel
      ((planeStab : Subgroup SL(3, ℤ)).subgroupOf (gammaN N))) a)).1) q i j =
      summandPoly n (hfun f) (realMat a.1) q i j := by
  have h : (Quotient.mk _ (Quotient.out (Quotient.mk (QuotientGroup.rightRel
      ((planeStab : Subgroup SL(3, ℤ)).subgroupOf (gammaN N))) a)) : PlaneCoset (gammaN N)) =
      Quotient.mk _ a := Quotient.out_eq _
  exact summandPoly_coset_eq N n f _ _ (Quotient.exact h) hq i j

theorem ofSL_a (h : SL(3, ℤ)) : (CuspData.ofSL h).a = realMat h := rfl

omit [NeZero N] in
theorem realMat_cjG (h : SL(3, ℤ)) (a : ↥(gammaN N)) :
    realMat (cjG N h a).1 * realMat h = realMat h * realMat a.1 := by
  rw [cjG_val, ← realMat_mul, ← realMat_mul]
  congr 1
  group

omit [NeZero N] in
/-- One term of the series at the conjugate cusp. -/
theorem termFunK_false_eq (h : SL(3, ℤ)) {y : Fin 5 → ℝ} (hy : y ∈ Omega) (a b : Fin 5)
    (m : Fin 3 →₀ ℕ) (c : CuspCoset (gammaN N) (CuspData.ofSL h).r) :
    termFunK false (CuspData.ofSL h) (gammaN N) n f c a b m y =
      (rho (realMat h)⁻¹ (formPullback (planeAct (realMat h)) (fun y' a' b' =>
        summandPoly n (hfun f) (realMat (cjG N h (Quotient.out c)).1) y' a' b') y a b)).coeff m := by
  unfold termFunK
  rw [summandK_false, ofSL_a, ← realMat_cjG N h (Quotient.out c)]
  rw [summandPoly_mul_eq n (hfun f) (det_realMat _) (det_realMat _) hy a b]

/-- **The series at the cusp `h⁻¹ P h` is the translate of the standard series**:
`𝓔_{h⁻¹Ph} = ρ(h)⁻¹ h^* 𝓔_P` (coefficientwise, on `Ω`). -/
theorem seriesFormK_false_eq (hn : 4 ≤ n) (h : SL(3, ℤ)) {y : Fin 5 → ℝ} (hy : y ∈ Omega)
    (a b : Fin 5) :
    seriesFormK false (CuspData.ofSL h) (gammaN N) n f y a b =
      rho (realMat h)⁻¹ (formPullback (planeAct (realMat h)) (seriesForm (gammaN N) n f) y a b) := by
  apply MvPolynomial.ext
  intro m
  rw [coeff_seriesFormK]
  have hΦ : planeAct (realMat h) y ∈ Omega := planeAct_mem (det_realMat h) hy
  unfold seriesCoeffK
  simp_rw [termFunK_false_eq N n f h hy a b m]
  have hsum : ∀ (a' b' : Fin 5) (m' : Fin 3 →₀ ℕ), Summable fun c : PlaneCoset (gammaN N) =>
      (summandPoly n (hfun f) (realMat (Quotient.out c).1) (planeAct (realMat h) y) a' b').coeff m' :=
    fun a' b' m' => summable_termFun_val (gammaN N) (leviGroup N) n f hn hΦ a' b' m'
  have hUc : ∀ (a' b' : Fin 5) (m' : Fin 3 →₀ ℕ),
      (seriesForm (gammaN N) n f (planeAct (realMat h) y) a' b').coeff m' =
        ∑' c : PlaneCoset (gammaN N),
          (summandPoly n (hfun f) (realMat (Quotient.out c).1) (planeAct (realMat h) y) a' b').coeff m' :=
    fun a' b' m' => by
      rw [coeff_seriesForm]
      rfl
  have hgen := coeff_rho_formPullback_tsum (ι := PlaneCoset (gammaN N)) n (realMat h)⁻¹
    (planeAct (realMat h)) y a b
    (fun c' y' a' b' => summandPoly n (hfun f) (realMat (Quotient.out c').1) y' a' b')
    (seriesForm (gammaN N) n f)
    (fun y' a' b' => seriesForm_isHomogeneous (gammaN N) n f y' a' b')
    (fun c' y' a' b' => summandPoly_isHomogeneous n (hfun f) (det_realMat _) y' a' b')
    hsum hUc m
  rw [hgen]
  have key : ∀ c : CuspCoset (gammaN N) (CuspData.ofSL h).r,
      (rho (realMat h)⁻¹ (formPullback (planeAct (realMat h)) (fun y' a' b' =>
        summandPoly n (hfun f) (realMat (cjG N h (Quotient.out c)).1) y' a' b') y a b)).coeff m =
      (rho (realMat h)⁻¹ (formPullback (planeAct (realMat h)) (fun y' a' b' =>
        summandPoly n (hfun f) (realMat (Quotient.out (cuspCosetEquiv N h c)).1) y' a' b')
          y a b)).coeff m := by
    intro c
    have hc : cuspCosetEquiv N h c = Quotient.mk _ (cjG N h (Quotient.out c)) := by
      conv_lhs => rw [← Quotient.out_eq c]
      rfl
    have hform : formPullback (planeAct (realMat h)) (fun y' a' b' =>
        summandPoly n (hfun f) (realMat (cjG N h (Quotient.out c)).1) y' a' b') y a b =
        formPullback (planeAct (realMat h)) (fun y' a' b' =>
        summandPoly n (hfun f) (realMat (Quotient.out (cuspCosetEquiv N h c)).1) y' a' b')
          y a b := by
      refine formPullback_congr_form y (fun a' b' => ?_) a b
      rw [hc]
      exact (summandPoly_out_eq N n f _ hΦ a' b').symm
    rw [hform]
  calc ∑' c : CuspCoset (gammaN N) (CuspData.ofSL h).r, _
      = ∑' c : CuspCoset (gammaN N) (CuspData.ofSL h).r,
        (rho (realMat h)⁻¹ (formPullback (planeAct (realMat h)) (fun y' a' b' =>
        summandPoly n (hfun f) (realMat (Quotient.out (cuspCosetEquiv N h c)).1) y' a' b')
          y a b)).coeff m := tsum_congr key
    _ = _ := (cuspCosetEquiv N h).tsum_eq (fun c' : PlaneCoset (gammaN N) =>
        (rho (realMat h)⁻¹ (formPullback (planeAct (realMat h)) (fun y' a' b' =>
        summandPoly n (hfun f) (realMat (Quotient.out c').1) y' a' b') y a b)).coeff m)

end Translate

end TernaryPeriodPolynomials.Argument.EisensteinClass
