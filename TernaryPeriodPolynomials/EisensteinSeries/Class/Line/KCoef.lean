module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.UnfoldAbs
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.UnfoldPhi
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.UnfoldBig
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.KSeries
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Unfold.K

@[expose] public section


/-!
# The line radical lattice acting on the cosets of the cusp `k⁻¹ P k`, and the coefficient layer

With "the same letters for the rational conjugates".

For `k ∈ SL₃(ℤ)` the series at the cusp `CuspData.ofSL k` (either seed type `b`) is a sum over the
cosets `Ck N k = Γ_{k⁻¹Pk}\Γ(N)` of the summands at `k γ`. The line radical lattice `latQ ℓ` acts on `Ck N k`
by right multiplication; the bottom row `(r₀, r₁, r₂)` of `k γ` becomes
`(r₀, r₁ - N r₀ ℓ₁, r₂ - N r₀ ℓ₀)`, so the action is trivial where `r₀ = 0` and free where `r₀ ≠ 0`
(`qActK`). `PhiQ0 k c w` is the `m`-th coefficient of the face pullback, along `jFace`, of the summand at
`k γ_c qMat w`; the averaged integrand of the face form of the series of type `b` is
`Σ'_c cxL b (PhiQ0 k c w)` (`coeff_avIntegrandK`).

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial
open scoped MatrixGroups ContDiff Matrix
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3S4c
  TernaryPeriodPolynomials.Argument.FormClassK TernaryPeriodPolynomials.Argument.GammaNFaces
  TernaryPeriodPolynomials.Argument.Statements.EisensteinClass TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4
  TernaryPeriodPolynomials.Argument.EisensteinDual
  TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham
  TernaryPeriodPolynomials.Argument.SeedC3.Psi

section Rows

variable (N : ℕ) (k : SL(3, ℤ))

theorem cuspRow_cmulR (δ : ↥(gammaN N)) (c : Ck N k) :
    cuspRow (gammaN N) (CuspData.ofSL k).r (cmulR N k δ c) =
      cuspRow (gammaN N) (CuspData.ofSL k).r c ᵥ* (δ.1 : Matrix (Fin 3) (Fin 3) ℤ) := by
  induction c using Quotient.inductionOn with | _ a => ?_
  rw [cmulR_mk, cuspRow_mk, cuspRow_mk]
  show _ ᵥ* ((a.1 * δ.1 : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) = _
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.vecMul_vecMul]

theorem latQ_val (ℓ : Fin 2 → ℤ) : ((latQ N ℓ).1 : Matrix (Fin 3) (Fin 3) ℤ) =
    !![1, (N : ℤ) * (-(ℓ 1)), (N : ℤ) * (-(ℓ 0)); 0, 1, 0; 0, 0, 1] := rfl

theorem cuspRow_latK (ℓ : Fin 2 → ℤ) (c : Ck N k) :
    cuspRow (gammaN N) (CuspData.ofSL k).r (cmulR N k (latQ N ℓ) c) 0 =
      cuspRow (gammaN N) (CuspData.ofSL k).r c 0 ∧
    cuspRow (gammaN N) (CuspData.ofSL k).r (cmulR N k (latQ N ℓ) c) 1 =
      cuspRow (gammaN N) (CuspData.ofSL k).r c 1 -
        (N : ℤ) * (cuspRow (gammaN N) (CuspData.ofSL k).r c 0 * ℓ 1) ∧
    cuspRow (gammaN N) (CuspData.ofSL k).r (cmulR N k (latQ N ℓ) c) 2 =
      cuspRow (gammaN N) (CuspData.ofSL k).r c 2 -
        (N : ℤ) * (cuspRow (gammaN N) (CuspData.ofSL k).r c 0 * ℓ 0) := by
  rw [cuspRow_cmulR, latQ_val]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three] <;> ring

/-- **The line radical lattice acts on the cosets of the cusp `k⁻¹Pk`**: trivially where the first
entry of the bottom row `r_k γ` vanishes, freely where it does not. -/
def qActK [NeZero N] : QAct N (Ck N k) where
  act ℓ := cmulR N k (latQ N ℓ)
  r0 c := cuspRow (gammaN N) (CuspData.ofSL k).r c 0
  act_zero c := by rw [latQ_zero, cmulR_one]
  act_add ℓ ℓ' c := by rw [latQ_add, cmulR_mul]
  r0_act ℓ c := (cuspRow_latK N k ℓ c).1
  fix ℓ c h := by
    apply cuspRow_injective (gammaN N) (CuspData.ofSL k).r
    obtain ⟨a, b, d⟩ := cuspRow_latK N k ℓ c
    funext j
    fin_cases j
    · exact a
    · simp [b, h]
    · simp [d, h]
  free c h := by
    intro ℓ ℓ' hℓ
    obtain ⟨-, b, d⟩ := cuspRow_latK N k ℓ c
    obtain ⟨-, b', d'⟩ := cuspRow_latK N k ℓ' c
    have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
    have h1 := congrFun (congrArg (cuspRow (gammaN N) (CuspData.ofSL k).r) hℓ) 1
    have h2 := congrFun (congrArg (cuspRow (gammaN N) (CuspData.ofSL k).r) hℓ) 2
    simp only at h1 h2
    rw [b, b'] at h1
    rw [d, d'] at h2
    funext i
    fin_cases i
    · have : (N : ℤ) * (cuspRow (gammaN N) (CuspData.ofSL k).r c 0) * (ℓ 0 - ℓ' 0) = 0 := by
        linarith
      rcases mul_eq_zero.1 this with h' | h'
      · exact absurd h' (mul_ne_zero hN h)
      · simpa [sub_eq_zero] using h'
    · have : (N : ℤ) * (cuspRow (gammaN N) (CuspData.ofSL k).r c 0) * (ℓ 1 - ℓ' 1) = 0 := by
        linarith
      rcases mul_eq_zero.1 this with h' | h'
      · exact absurd h' (mul_ne_zero hN h)
      · simpa [sub_eq_zero] using h'

end Rows

section Phi

variable (N : ℕ) [NeZero N] (k : SL(3, ℤ)) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

omit [NeZero N] in
/-- Representative independence of the summand at `k γ G` in the coset of the cusp `k⁻¹Pk`. -/
theorem summandPoly_cusp_coset (a b : ↥(gammaN N))
    (hab : (QuotientGroup.rightRel ((stabRow (CuspData.ofSL k).r).subgroupOf (gammaN N))) a b)
    {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : G.det = 1) {y : Fin 5 → ℝ} (hy : y ∈ Omega) (i j : Fin 5) :
    summandPoly n (hfun f) (realMat k * realMat a.1 * G) y i j =
      summandPoly n (hfun f) (realMat k * realMat b.1 * G) y i j := by
  apply MvPolynomial.ext
  intro m
  have hH : b.1 * a.1⁻¹ ∈ stabRow (CuspData.ofSL k).r := by
    have := QuotientGroup.rightRel_apply.1 hab
    simpa using Subgroup.mem_subgroupOf.1 this
  have hps : k * (b.1 * a.1⁻¹) * k⁻¹ ∈ planeStab := (mem_stabRow_ofSL k _).1 hH
  have hΓ : k * (b.1 * a.1⁻¹) * k⁻¹ ∈ gammaN N := by
    have hm : b.1 * a.1⁻¹ ∈ gammaN N := (gammaN N).mul_mem b.2 ((gammaN N).inv_mem a.2)
    have := (gammaN_normal N).conj_mem _ hm k
    simpa [mul_assoc] using this
  have hGa : (realMat k * realMat a.1 * G).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, det_realMat, det_realMat, hG]; norm_num
  have hp : (k * (b.1 * a.1⁻¹) * k⁻¹) * (k * a.1) = k * b.1 := by group
  have e : realMat k * realMat b.1 * G =
      realMat (k * (b.1 * a.1⁻¹) * k⁻¹) * (realMat k * realMat a.1 * G) := by
    calc realMat k * realMat b.1 * G = realMat (k * b.1) * G := by rw [realMat_mul]
      _ = realMat ((k * (b.1 * a.1⁻¹) * k⁻¹) * (k * a.1)) * G := by rw [hp]
      _ = _ := by simp only [realMat_mul, Matrix.mul_assoc]
  have := Tm_stab_mul N n f _ hΓ hps hGa hy i j m
  rw [← e] at this
  exact this.symm

/-- **The coefficient of the face pullback, along `jFace`, of the summand of the coset `c` of the cusp
`k⁻¹Pk` at `k γ_c · qMat w`.** -/
def PhiQ0 (x : Face) (p q : Fin 4) (m : Fin 3 →₀ ℕ) (c : Ck N k) (w : Fin 2 → ℝ) : ℂ :=
  (fPull jFace (fun y a b => summandPoly n (hfun f)
    (realMat k * realMat (Quotient.out c).1 * qMat w) y a b) x p q).coeff m

omit [NeZero N] in
theorem PhiQ0_mk {x : Face} (hx : x ∈ faceSet) (p q : Fin 4) (m : Fin 3 →₀ ℕ) (a : ↥(gammaN N))
    (w : Fin 2 → ℝ) :
    PhiQ0 N k n f x p q m (Quotient.mk _ a) w =
      (fPull jFace (fun y a' b => summandPoly n (hfun f)
        (realMat k * realMat a.1 * qMat w) y a' b) x p q).coeff m := by
  unfold PhiQ0
  have h : (Quotient.mk _ (Quotient.out (Quotient.mk (QuotientGroup.rightRel
      ((stabRow (CuspData.ofSL k).r).subgroupOf (gammaN N))) a)) : Ck N k) = Quotient.mk _ a :=
    Quotient.out_eq _
  have hy : jFace x ∈ Omega := jPlane_mem (ptOf_mem hx)
  rw [fPull_congr_at jFace _ (fun y a' b => summandPoly n (hfun f)
    (realMat k * realMat a.1 * qMat w) y a' b) x
    (fun a' b => summandPoly_cusp_coset N k n f _ _ (Quotient.exact h) (det_qMat w) hy a' b) p q]

omit [NeZero N] in
/-- **Equivariance of `PhiQ0` for the line radical lattice.** -/
theorem PhiQ0_latQ {x : Face} (hx : x ∈ faceSet) (p q : Fin 4) (m : Fin 3 →₀ ℕ) (ℓ : Fin 2 → ℤ)
    (c : Ck N k) (w : Fin 2 → ℝ) :
    PhiQ0 N k n f x p q m (cmulR N k (latQ N ℓ) c) w =
      PhiQ0 N k n f x p q m c ((N : ℝ) • intVec ℓ + w) := by
  induction c using Quotient.inductionOn with | _ a => ?_
  rw [cmulR_mk, PhiQ0_mk N k n f hx p q m, PhiQ0_mk N k n f hx p q m]
  have : realMat k * realMat (a * latQ N ℓ).1 * qMat w =
      realMat k * realMat a.1 * qMat ((N : ℝ) • intVec ℓ + w) := by
    show realMat k * realMat (a.1 * (latQ N ℓ).1) * qMat w = _
    rw [realMat_mul, realMat_latQ, ← Matrix.mul_assoc, Matrix.mul_assoc _ (qMat _) (qMat w), qMat_mul]
  rw [this]

end Phi

section Coefficients

variable (N : ℕ) [NeZero N] (k : SL(3, ℤ)) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

omit [NeZero N] in
theorem fPull_cxP (b : Bool) (Φ : Face → Fin 5 → ℝ)
    (W : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ) (x : Face) (i j : Fin 4) :
    fPull Φ (fun y a c => cxP b (W y a c)) x i j = cxP b (fPull Φ W x i j) := by
  unfold fPull
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul]
  unfold cxP
  rw [MvPolynomial.map_C, cx_ofReal]

/-- The face pullback of the series at the cusp `k⁻¹Pk` is the sum of the face pullbacks of the
summands (coefficientwise). -/
theorem coeff_fPull_seriesK (b : Bool) (hn : 4 ≤ n) (Φ : Face → Fin 5 → ℝ) {x : Face}
    (hΦ : Φ x ∈ Omega) (i j : Fin 4) (m' : Fin 3 →₀ ℕ) :
    (fPull Φ (fun y a c => seriesFormK b (CuspData.ofSL k) (gammaN N) n f y a c) x i j).coeff m' =
      ∑' c : Ck N k, (fPull Φ (fun y a c' => summandK b n (hfun f)
        (realMat k * realMat (Quotient.out c).1) y a c') x i j).coeff m' := by
  have hc : ∀ c : Ck N k, (fPull Φ (fun y a c' => summandK b n (hfun f)
      (realMat k * realMat (Quotient.out c).1) y a c') x i j).coeff m' =
        ∑ a : Fin 5, ∑ c' : Fin 5, (((fderiv ℝ Φ x (Pi.single i 1) a *
          fderiv ℝ Φ x (Pi.single j 1) c' : ℝ) : ℂ)) *
          termFunK b (CuspData.ofSL k) (gammaN N) n f c a c' m' (Φ x) := by
    intro c
    unfold fPull
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
    rfl
  have hs : ∀ a c' : Fin 5, Summable fun c : Ck N k =>
      termFunK b (CuspData.ofSL k) (gammaN N) n f c a c' m' (Φ x) := fun a c' =>
    summable_termFunK_val b (CuspData.ofSL k) (gammaN N) (leviGroup N) n f hn hΦ a c' m'
  simp_rw [hc]
  rw [Summable.tsum_finsetSum (fun a _ => summable_sum fun c' _ => (hs a c').mul_left _)]
  unfold fPull
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Summable.tsum_finsetSum (fun c' _ => (hs a c').mul_left _)]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [tsum_mul_left, coeff_seriesFormK]
  rfl

theorem summable_coeff_fPull_K (b : Bool) (hn : 4 ≤ n) (Φ : Face → Fin 5 → ℝ) {x : Face}
    (hΦ : Φ x ∈ Omega) (i j : Fin 4) (m' : Fin 3 →₀ ℕ) :
    Summable fun c : Ck N k => (fPull Φ (fun y a c' => summandK b n (hfun f)
        (realMat k * realMat (Quotient.out c).1) y a c') x i j).coeff m' := by
  have : ∀ c : Ck N k, (fPull Φ (fun y a c' => summandK b n (hfun f)
      (realMat k * realMat (Quotient.out c).1) y a c') x i j).coeff m' =
        ∑ a : Fin 5, ∑ c' : Fin 5, (((fderiv ℝ Φ x (Pi.single i 1) a *
          fderiv ℝ Φ x (Pi.single j 1) c' : ℝ) : ℂ)) *
          termFunK b (CuspData.ofSL k) (gammaN N) n f c a c' m' (Φ x) := by
    intro c
    unfold fPull
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
    rfl
  simp_rw [this]
  exact summable_sum fun a _ => summable_sum fun c' _ =>
    (summable_termFunK_val b (CuspData.ofSL k) (gammaN N) (leviGroup N) n f hn hΦ a c' m').mul_left _

/-- **The averaged integrand of the face form of the series of type `b` at the cusp `k⁻¹Pk` is the sum
over the cosets of `cxL b (PhiQ0)`**. -/
theorem coeff_avIntegrandK (b : Bool) (hn : 4 ≤ n) {x : Face} (hx : x ∈ faceSet) (w : Fin 2 → ℝ)
    (p q : Fin 4) (m : Fin 3 →₀ ℕ) :
    polyCoefCLM n m (sQ n (-w)
      ((((lineFaceForm N n (planeEisensteinAtInv b (CuspData.ofSL k) (gammaN N) (leviGroup N) n f hn
        (leviInCusp_gammaN N k)) :
        ZigZag.invClosed isOpen_faceSet (gammaNPlaneData N).action (rhoQ N n)) :
          Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) (x + shVec w)
            ![Pi.single p 1, Pi.single q 1])) =
      ∑' c : Ck N k, cxL b (PhiQ0 N k n f x p q m c w) := by
  have hxw : x + shVec w ∈ faceSet := shVec_mem hx w
  have hy₁ : jFace (x + shVec w) ∈ Omega := jPlane_mem (ptOf_mem hxw)
  rw [polyCoefCLM_apply, toPoly_sQ]
  unfold planeEisensteinAtInv
  rw [toPoly_lineFaceForm_basis N n _ hxw p q]
  have hQ : (fPull jFace (fun y a c => Coef.toPoly
      ((planeEisensteinAtComponents b (CuspData.ofSL k) (gammaN N) (leviGroup N) n f hn
        (leviInCusp_gammaN N k)).comp y a c)) (x + shVec w) p q).IsHomogeneous n :=
    fPull_isHomogeneous n jFace _ (fun y a c => seriesFormK_isHomogeneous b (CuspData.ofSL k)
      (gammaN N) n f y a c) _ _ _
  have hP : ∀ c : Ck N k, (fPull jFace (fun y a c' => summandK b n (hfun f)
      (realMat k * realMat (Quotient.out c).1) y a c') (x + shVec w) p q).IsHomogeneous n := fun c =>
    fPull_isHomogeneous n jFace _ (fun y a c' => summandK_isHomogeneous b n f
      (g := realMat k * realMat (Quotient.out c).1)
      (by rw [Matrix.det_mul, det_realMat, det_realMat]; norm_num) y a c') _ _ _
  rw [coeff_rho_tsum (qMat (-w)) _ _ hQ hP
    (fun m' => summable_coeff_fPull_K N k n f b hn jFace hy₁ p q m')
    (fun m' => coeff_fPull_seriesK N k n f b hn jFace hy₁ p q m') m]
  refine tsum_congr fun c => ?_
  have hg : (realMat k * realMat (Quotient.out c).1).det = 1 := by
    rw [Matrix.det_mul, det_realMat, det_realMat]; norm_num
  have e1 : (fPull jFace (fun y a c' => summandK b n (hfun f)
      (realMat k * realMat (Quotient.out c).1) y a c') (x + shVec w) p q) =
      cxP b (fPull jFace (fun y a c' => summandPoly n (hfun f)
        (realMat k * realMat (Quotient.out c).1) y a c') (x + shVec w) p q) := by
    rw [← fPull_cxP]
    congr 1
    funext y a c'
    exact summandK_eq b n (hfun f) _ y a c'
  rw [e1, rho_cxP, rho_fPull_shift n (hfun f) hg hx w p q, coeff_cxP, cxL_apply]
  rfl

end Coefficients

end TernaryPeriodPolynomials.Argument.EisensteinClass
