module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Cusp.Series

@[expose] public section


/-!
# Proposition C.4 at a plane cusp: Levi data, equivariance, packaging

The Levi data of a cusp (`LeviInCusp`: the Levi block of `a p a⁻¹` for `p` in the cusp stabilizer
lies in `Λ`), the independence of the term from the coset representative (`summandK_cusp_stab`,
`cosetTermK`), `Γ`-equivariance `ρ(δ)⁻¹ δ^* 𝓔 = 𝓔` of the sum (`seriesFormK_equivariant`), and the
packaging lemmas used by the export: one summable majorant for all components and coefficients
(`exists_summable_jet_bound_all_K`), closedness (`seriesFormK_closed`), smoothness
(`contDiffOn_seriesFormK_coeff`), sections of the quotient map (`seriesCoeffK_eq_tsum_section`) and
the law `δ^* 𝓔 = ρ(δ) 𝓔` (`seriesFormK_pullback`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

open scoped ContDiff
open Matrix MvPolynomial

/-! ### The right action of `Γ` on the cusp cosets -/

section CosetAction

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) (r : Fin 3 → ℤ)

/-- Right multiplication by `δ ∈ Γ` on `Γ_P \ Γ`. -/
def cuspMulR (δ : Γ) : CuspCoset Γ r → CuspCoset Γ r :=
  Quotient.map (fun a : Γ => a * δ) (by
    intro a b hab
    have h := QuotientGroup.rightRel_apply.1 hab
    refine QuotientGroup.rightRel_apply.2 ?_
    simpa [mul_assoc] using h)

theorem cuspMulR_mk (δ a : Γ) : cuspMulR Γ r δ (Quotient.mk _ a) = Quotient.mk _ (a * δ) := rfl

/-- Right multiplication by `δ` is a bijection of `Γ_P \ Γ`. -/
def cuspMulREquiv (δ : Γ) : CuspCoset Γ r ≃ CuspCoset Γ r where
  toFun := cuspMulR Γ r δ
  invFun := cuspMulR Γ r δ⁻¹
  left_inv c := by
    induction c using Quotient.inductionOn with | _ a => ?_
    simp [cuspMulR_mk]
  right_inv c := by
    induction c using Quotient.inductionOn with | _ a => ?_
    simp [cuspMulR_mk]

end CosetAction

/-! ### The Levi data of a cusp and invariance of the summand -/

section LeviData

open UpperHalfPlane ModularForm
open scoped UpperHalfPlane

/-- **The Levi data of the cusp.** The determinant-one Levi block of the conjugate `a p a⁻¹` of every
element `p` of the cusp stabilizer `Γ_P` lies in the group `Λ` for which the cusp form is modular
(`Λ_P` is the Levi projection of `Γ_P`, as in the paper). -/
def LeviInCusp (D : CuspData) (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ))
    (Λ : Subgroup (GL (Fin 2) ℝ)) : Prop :=
  ∀ p ∈ Γ, p ∈ stabRow D.r →
    ∃ g ∈ Λ, (g : Matrix (Fin 2) (Fin 2) ℝ) = topBlock (D.a * realMat p * D.a⁻¹)

theorem cusp_row_mul_stab (D : CuspData) {p : Matrix.SpecialLinearGroup (Fin 3) ℤ}
    (hp : p ∈ stabRow D.r) (j : Fin 3) : (D.a * realMat p) 2 j = D.a 2 j := by
  have hp' : D.r ᵥ* (p : Matrix (Fin 3) (Fin 3) ℤ) = D.r := hp
  rw [row_mul_eq, hp', D.row_a]

theorem cusp_conj_row (D : CuspData) {p : Matrix.SpecialLinearGroup (Fin 3) ℤ}
    (hp : p ∈ stabRow D.r) (j : Fin 3) : (D.a * realMat p * D.a⁻¹) 2 j = (1 : Matrix (Fin 3) (Fin 3) ℝ) 2 j := by
  have hu : IsUnit D.a.det := by rw [D.det_a]; exact isUnit_one
  have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv D.a hu) 2) j
  calc (D.a * realMat p * D.a⁻¹) 2 j = ∑ k, (D.a * realMat p) 2 k * D.a⁻¹ k j := Matrix.mul_apply
    _ = ∑ k, D.a 2 k * D.a⁻¹ k j :=
        Finset.sum_congr rfl fun k _ => by rw [cusp_row_mul_stab D hp k]
    _ = (D.a * D.a⁻¹) 2 j := Matrix.mul_apply.symm
    _ = (1 : Matrix (Fin 3) (Fin 3) ℝ) 2 j := h1

theorem det_cusp_conj (D : CuspData) (p : Matrix.SpecialLinearGroup (Fin 3) ℤ) :
    (D.a * realMat p * D.a⁻¹).det = 1 := by
  rw [Matrix.det_mul, Matrix.det_mul, det_realMat, Matrix.det_nonsing_inv, D.det_a]
  simp

variable {F : Type*} [FunLike F ℍ ℂ] (Λ : Subgroup (GL (Fin 2) ℝ)) [Λ.HasDetOne] (n : ℕ)
  [SlashInvariantFormClass F Λ ((n + 3 : ℕ) : ℤ)] (f : F)

/-- **Independence of the representative at the cusp.** -/
theorem summandK_cusp_stab (b : Bool) (D : CuspData)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)} (hLevi : LeviInCusp D Γ Λ)
    {p : Matrix.SpecialLinearGroup (Fin 3) ℤ} (hpΓ : p ∈ Γ) (hp : p ∈ stabRow D.r)
    (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) {q : Fin 5 → ℝ} (hq : q ∈ Omega) (i j : Fin 5) :
    summandK b n (fun z => f (ofComplex z)) (D.a * realMat (p * γ)) q i j =
      summandK b n (fun z => f (ofComplex z)) (D.a * realMat γ) q i j := by
  have hu : IsUnit D.a.det := by rw [D.det_a]; exact isUnit_one
  have h1 : ∀ M : Matrix (Fin 3) (Fin 3) ℝ, D.a⁻¹ * (D.a * M) = M := fun M => by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul D.a hu, Matrix.one_mul]
  have hfac : D.a * realMat (p * γ) = (D.a * realMat p * D.a⁻¹) * (D.a * realMat γ) := by
    rw [realMat_mul]
    simp only [Matrix.mul_assoc, h1]
  have key := summandPoly_realstab_mul Λ n f (D.a * realMat p * D.a⁻¹) (D.a * realMat γ)
    (det_cusp_conj D p) (det_cusp_mul D γ)
    (by rw [cusp_conj_row D hp 0]; simp)
    (by rw [cusp_conj_row D hp 1]; simp)
    (by rw [cusp_conj_row D hp 2]; simp)
    (hLevi p hpΓ hp) hq i j
  rw [summandK_eq, summandK_eq, hfac, key]

end LeviData

/-! ### Well-defined terms, and the equivariance of the series -/

section Equivariance

open UpperHalfPlane ModularForm
open scoped UpperHalfPlane

variable (b : Bool) (D : CuspData) (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ))
  {F : Type*} [FunLike F ℍ ℂ] (Λ : Subgroup (GL (Fin 2) ℝ)) [Λ.HasDetOne] [Λ.IsArithmetic]
  (n : ℕ) [CuspFormClass F Λ ((n + 3 : ℕ) : ℤ)] (f : F)

/-- The term attached to a coset, defined through any representative. -/
def cosetTermK (hLevi : LeviInCusp D Γ Λ) {q : Fin 5 → ℝ} (hq : q ∈ Omega) (i j : Fin 5)
    (m : Fin 3 →₀ ℕ) : CuspCoset Γ D.r → ℂ :=
  Quotient.lift (fun a : Γ =>
      (summandK b n (hfun f) (D.a * realMat a.1) q i j).coeff m) (by
    intro a c hac
    have hH : c.1 * a.1⁻¹ ∈ stabRow D.r := by
      have := QuotientGroup.rightRel_apply.1 hac
      simpa using Subgroup.mem_subgroupOf.1 this
    have hHΓ : c.1 * a.1⁻¹ ∈ Γ := Γ.mul_mem c.2 (Γ.inv_mem a.2)
    have e : c.1 = (c.1 * a.1⁻¹) * a.1 := by simp
    show (summandK b n (hfun f) (D.a * realMat a.1) q i j).coeff m =
      (summandK b n (hfun f) (D.a * realMat c.1) q i j).coeff m
    conv_rhs => rw [e]
    exact congrArg (·.coeff m) (summandK_cusp_stab Λ n f b D hLevi hHΓ hH a.1 hq i j).symm)

omit [Λ.IsArithmetic] in
theorem cosetTermK_mk (hLevi : LeviInCusp D Γ Λ) {q : Fin 5 → ℝ} (hq : q ∈ Omega) (i j : Fin 5)
    (m : Fin 3 →₀ ℕ) (a : Γ) :
    cosetTermK b D Γ Λ n f hLevi hq i j m (Quotient.mk _ a) =
      (summandK b n (hfun f) (D.a * realMat a.1) q i j).coeff m := rfl

omit [Λ.IsArithmetic] in
theorem termFunK_eq_cosetTermK (hLevi : LeviInCusp D Γ Λ) {x : Fin 5 → ℝ} (hx : x ∈ Omega)
    (i j : Fin 5) (m : Fin 3 →₀ ℕ) (c : CuspCoset Γ D.r) :
    termFunK b D Γ n f c i j m x = cosetTermK b D Γ Λ n f hLevi hx i j m c := by
  conv_rhs => rw [← Quotient.out_eq c]
  rfl

omit [Λ.IsArithmetic] [CuspFormClass F Λ ((n + 3 : ℕ) : ℤ)] [Λ.HasDetOne] in
theorem summandK_isHomogeneous (g : Matrix (Fin 3) (Fin 3) ℝ) (hg : g.det = 1) (q : Fin 5 → ℝ)
    (i j : Fin 5) : MvPolynomial.IsHomogeneous (summandK b n (hfun f) g q i j) n := by
  rw [summandK_eq]
  exact isHomogeneous_cxP b (summandPoly_isHomogeneous n (hfun f) hg q i j)

include Λ

omit [Λ.HasDetOne] in
theorem summable_coeff_pullbackK (hn : 4 ≤ n) {Φ : (Fin 5 → ℝ) → (Fin 5 → ℝ)} {x : Fin 5 → ℝ}
    (hΦ : Φ x ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ) :
    Summable (fun c : CuspCoset Γ D.r => (formPullback Φ (fun y a b' =>
      summandK b n (hfun f) (D.a * realMat (Quotient.out c).1) y a b') x i j).coeff m) := by
  simp_rw [coeff_formPullback]
  unfold scalarPullback
  refine summable_sum fun a _ => summable_sum fun c _ => ?_
  exact (summable_termFunK_val b D Γ Λ n f hn hΦ a c m).mul_left _

omit [Λ.HasDetOne] in
theorem coeff_pullback_seriesK (hn : 4 ≤ n) {Φ : (Fin 5 → ℝ) → (Fin 5 → ℝ)} {x : Fin 5 → ℝ}
    (hΦ : Φ x ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ) :
    (formPullback Φ (seriesFormK b D Γ n f) x i j).coeff m =
      ∑' c : CuspCoset Γ D.r, (formPullback Φ (fun y a b' =>
        summandK b n (hfun f) (D.a * realMat (Quotient.out c).1) y a b') x i j).coeff m := by
  simp_rw [coeff_formPullback, coeff_seriesFormK]
  unfold scalarPullback
  have h1 : ∀ a c : Fin 5, ((fderiv ℝ Φ x (Pi.single i 1) a * fderiv ℝ Φ x (Pi.single j 1) c : ℝ) : ℂ) *
      seriesCoeffK b D Γ n f a c m (Φ x) = ∑' w : CuspCoset Γ D.r,
      ((fderiv ℝ Φ x (Pi.single i 1) a * fderiv ℝ Φ x (Pi.single j 1) c : ℝ) : ℂ) *
        (summandK b n (hfun f) (D.a * realMat (Quotient.out w).1) (Φ x) a c).coeff m := by
    intro a c
    unfold seriesCoeffK termFunK
    exact tsum_mul_left.symm
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => h1 a c]
  have h2 : ∀ a c : Fin 5, Summable (fun w : CuspCoset Γ D.r =>
      ((fderiv ℝ Φ x (Pi.single i 1) a * fderiv ℝ Φ x (Pi.single j 1) c : ℝ) : ℂ) *
        (summandK b n (hfun f) (D.a * realMat (Quotient.out w).1) (Φ x) a c).coeff m) :=
    fun a c => (summable_termFunK_val b D Γ Λ n f hn hΦ a c m).mul_left _
  beta_reduce
  rw [Finset.sum_congr rfl fun a _ => (Summable.tsum_finsetSum (fun c _ => h2 a c)).symm]
  exact (Summable.tsum_finsetSum fun a _ => summable_sum fun c _ => h2 a c).symm

omit [Λ.IsArithmetic] in
theorem coeff_rho_pullback_termK (hLevi : LeviInCusp D Γ Λ) (δ : Γ) {x : Fin 5 → ℝ}
    (hx : x ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ) (c : CuspCoset Γ D.r) :
    (SeedC3.rho (realMat δ.1)⁻¹ (formPullback (planeAct (realMat δ.1)) (fun y a b' =>
      summandK b n (hfun f) (D.a * realMat (Quotient.out c).1) y a b') x i j)).coeff m =
      termFunK b D Γ n f (cuspMulR Γ D.r δ c) i j m x := by
  rw [← summandK_mul_eq b n (hfun f) (det_cusp_mul D _) (det_realMat δ.1) hx i j,
    termFunK_eq_cosetTermK b D Γ Λ n f hLevi hx i j m (cuspMulR Γ D.r δ c)]
  conv_rhs => rw [← Quotient.out_eq c]
  show (summandK b n (hfun f) (D.a * realMat (Quotient.out c).1 * realMat δ.1) x i j).coeff m =
    (summandK b n (hfun f) (D.a * realMat ((Quotient.out c).1 * δ.1)) x i j).coeff m
  rw [realMat_mul, Matrix.mul_assoc]

/-- **`Γ`-equivariance of the series at the cusp `D`.** For `δ ∈ Γ` and `x ∈ Ω`,
`ρ(δ)⁻¹ δ^* 𝓔 = 𝓔`. -/
theorem seriesFormK_equivariant (hn : 4 ≤ n) (hLevi : LeviInCusp D Γ Λ) (δ : Γ) {x : Fin 5 → ℝ}
    (hx : x ∈ Omega) (i j : Fin 5) :
    SeedC3.rho (realMat δ.1)⁻¹ (formPullback (planeAct (realMat δ.1))
      (seriesFormK b D Γ n f) x i j) = seriesFormK b D Γ n f x i j := by
  have hd := det_realMat δ.1
  have hΦ := planeAct_mem hd hx
  refine MvPolynomial.ext _ _ fun m => ?_
  have hQ := formPullback_isHomogeneous (n := n) _
    (fun y a c => seriesFormK_isHomogeneous b D Γ n f y a c) (planeAct (realMat δ.1)) x i j
  rw [coeff_rho_expansion hQ, coeff_seriesFormK]
  simp_rw [coeff_pullback_seriesK b D Γ Λ n f hn hΦ i j]
  have hPc : ∀ c : CuspCoset Γ D.r, MvPolynomial.IsHomogeneous
      (formPullback (planeAct (realMat δ.1))
        (fun y a c' => summandK b n (hfun f) (D.a * realMat (Quotient.out c).1) y a c') x i j) n :=
    fun c => formPullback_isHomogeneous _ (fun y a c' =>
      summandK_isHomogeneous b n f _ (det_cusp_mul D _) y a c') _ x i j
  have hs : ∀ m' ∈ monSet n, Summable (fun c : CuspCoset Γ D.r =>
      (formPullback (planeAct (realMat δ.1))
        (fun y a c' => summandK b n (hfun f) (D.a * realMat (Quotient.out c).1) y a c') x i j).coeff m' *
        (SeedC3.rho (realMat δ.1)⁻¹ (monomial m' 1)).coeff m) := fun m' _ =>
    (summable_coeff_pullbackK b D Γ Λ n f hn hΦ i j m').mul_right _
  calc _ = ∑ m' ∈ monSet n, ∑' c : CuspCoset Γ D.r, (formPullback (planeAct (realMat δ.1))
        (fun y a c' => summandK b n (hfun f) (D.a * realMat (Quotient.out c).1) y a c') x i j).coeff m' *
          (SeedC3.rho (realMat δ.1)⁻¹ (monomial m' 1)).coeff m :=
        Finset.sum_congr rfl fun m' _ => tsum_mul_right.symm
    _ = ∑' c : CuspCoset Γ D.r, ∑ m' ∈ monSet n, (formPullback (planeAct (realMat δ.1))
        (fun y a c' => summandK b n (hfun f) (D.a * realMat (Quotient.out c).1) y a c') x i j).coeff m' *
          (SeedC3.rho (realMat δ.1)⁻¹ (monomial m' 1)).coeff m :=
        (Summable.tsum_finsetSum hs).symm
    _ = ∑' c : CuspCoset Γ D.r, (SeedC3.rho (realMat δ.1)⁻¹ (formPullback (planeAct (realMat δ.1))
        (fun y a c' => summandK b n (hfun f) (D.a * realMat (Quotient.out c).1) y a c') x i j)).coeff m :=
        tsum_congr fun c => (coeff_rho_expansion (hPc c) _ m).symm
    _ = ∑' c : CuspCoset Γ D.r, termFunK b D Γ n f (cuspMulR Γ D.r δ c) i j m x :=
        tsum_congr fun c => coeff_rho_pullback_termK b D Γ Λ n f hLevi δ hx i j m c
    _ = seriesCoeffK b D Γ n f i j m x :=
        (cuspMulREquiv Γ D.r δ).tsum_eq (fun c => termFunK b D Γ n f c i j m x)

omit [Λ.HasDetOne] in
/-- **Normal convergence of every derivative**, with one summable majorant for all components and
coefficients. -/
theorem exists_summable_jet_bound_all_K (hn : 4 ≤ n) {K : Set (Fin 5 → ℝ)} (hK : IsCompact K)
    (hKΩ : K ⊆ Omega) (k : ℕ) :
    ∃ B : CuspCoset Γ D.r → ℝ, Summable B ∧ ∀ (c : CuspCoset Γ D.r), ∀ x ∈ K, ∀ (i j : Fin 5)
      (m : Fin 3 →₀ ℕ), ‖iteratedFDeriv ℝ k (termFunK b D Γ n f c i j m) x‖ ≤ B c := by
  have h : ∀ (i j : Fin 5) (m : Fin 3 →₀ ℕ), ∃ B : CuspCoset Γ D.r → ℝ, Summable B ∧ ∀ c, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ k (termFunK b D Γ n f c i j m) x‖ ≤ B c :=
    fun i j m => exists_summable_jet_bound_K b D Γ Λ n f hn hK hKΩ k i j m
  choose B hB hBd using h
  refine ⟨fun c => ∑ i, ∑ j, ∑ m ∈ monSet n, |B i j m c|, ?_, ?_⟩
  · exact summable_sum fun i _ => summable_sum fun j _ => summable_sum fun m _ => (hB i j m).abs
  · intro c x hx i j m
    by_cases hm : m ∈ monSet n
    · calc ‖iteratedFDeriv ℝ k (termFunK b D Γ n f c i j m) x‖ ≤ B i j m c := hBd i j m c x hx
        _ ≤ |B i j m c| := le_abs_self _
        _ ≤ ∑ m ∈ monSet n, |B i j m c| :=
          Finset.single_le_sum (f := fun m => |B i j m c|) (fun _ _ => abs_nonneg _) hm
        _ ≤ ∑ j, ∑ m ∈ monSet n, |B i j m c| :=
          Finset.single_le_sum (f := fun j => ∑ m ∈ monSet n, |B i j m c|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ j)
        _ ≤ ∑ i, ∑ j, ∑ m ∈ monSet n, |B i j m c| :=
          Finset.single_le_sum (f := fun i => ∑ j, ∑ m ∈ monSet n, |B i j m c|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
            (Finset.mem_univ i)
    · have h0 : termFunK b D Γ n f c i j m = fun _ => 0 :=
        funext fun y => termFunK_coeff_eq_zero b D Γ n f c y i j hm
      rw [h0]
      have : iteratedFDeriv ℝ k (fun _ : Fin 5 → ℝ => (0 : ℂ)) x = 0 := by simp
      rw [this, norm_zero]
      exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        abs_nonneg _

omit [Λ.HasDetOne] in
/-- **Closedness of the sum**, in the coordinate form of the `seed_closed_equivariant`. -/
theorem seriesFormK_closed (hn : 4 ≤ n) {x : Fin 5 → ℝ} (hx : x ∈ Omega) (m : Fin 3 →₀ ℕ)
    (i j k : Fin 5) :
    coordPartial (fun q => (seriesFormK b D Γ n f q j k).coeff m) i x -
        coordPartial (fun q => (seriesFormK b D Γ n f q i k).coeff m) j x +
        coordPartial (fun q => (seriesFormK b D Γ n f q i j).coeff m) k x = 0 := by
  have hd : ∀ a c, DifferentiableAt ℝ (seriesCoeffK b D Γ n f a c m) x := fun a c =>
    ((seriesCoeffK_smooth b D Γ Λ n f hn a c m).1.contDiffAt
      (isOpen_Omega.mem_nhds hx)).differentiableAt (by simp)
  simp_rw [coeff_seriesFormK]
  rw [coordPartial_eq_fderiv (hd j k) i, coordPartial_eq_fderiv (hd i k) j,
    coordPartial_eq_fderiv (hd i j) k]
  exact seriesCoeffK_closedAt b D Γ Λ n f hn hx m i j k

omit [Λ.HasDetOne] in
/-- Each coefficient of each component of the sum is `C^∞` on `Ω`. -/
theorem contDiffOn_seriesFormK_coeff (hn : 4 ≤ n) (i j : Fin 5) (m : Fin 3 →₀ ℕ) :
    ContDiffOn ℝ ∞ (fun y => (seriesFormK b D Γ n f y i j).coeff m) Omega := by
  simp_rw [coeff_seriesFormK]
  exact (seriesCoeffK_smooth b D Γ Λ n f hn i j m).1

omit [Λ.IsArithmetic] in
/-- **Independence of the coset representatives.** -/
theorem seriesCoeffK_eq_tsum_section (hLevi : LeviInCusp D Γ Λ) {x : Fin 5 → ℝ} (hx : x ∈ Omega)
    (i j : Fin 5) (m : Fin 3 →₀ ℕ) (r : CuspCoset Γ D.r → Γ)
    (hr : ∀ c, (Quotient.mk _ (r c) : CuspCoset Γ D.r) = c) :
    seriesCoeffK b D Γ n f i j m x =
      ∑' c : CuspCoset Γ D.r, (summandK b n (hfun f) (D.a * realMat (r c).1) x i j).coeff m := by
  unfold seriesCoeffK
  refine tsum_congr fun c => ?_
  rw [termFunK_eq_cosetTermK b D Γ Λ n f hLevi hx i j m c]
  conv_lhs => rw [← hr c]
  rfl

/-- **`δ^* 𝓔 = ρ(δ) 𝓔`.** -/
theorem seriesFormK_pullback (hn : 4 ≤ n) (hLevi : LeviInCusp D Γ Λ) (δ : Γ) {x : Fin 5 → ℝ}
    (hx : x ∈ Omega) (i j : Fin 5) :
    formPullback (planeAct (realMat δ.1)) (seriesFormK b D Γ n f) x i j =
      SeedC3.rho (realMat δ.1) (seriesFormK b D Γ n f x i j) := by
  rw [← seriesFormK_equivariant b D Γ Λ n f hn hLevi δ hx i j, rho_mul,
    Matrix.mul_nonsing_inv _ (by rw [det_realMat]; exact isUnit_one), rho_one]

end Equivariance

end TernaryPeriodPolynomials.Argument.ConvergenceC4
