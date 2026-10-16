module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.UnfoldCells
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.UnfoldGeom

@[expose] public section


/-!
# The coefficient family `PhiQ` of the line-face average

`PhiQ c w` is the `m`-th coefficient of the face pullback, along `jFace`, of the summand of the coset `c` at
`γ_c · qMat w`. It is independent of the representative of `c`, equivariant for the lattice
(`PhiQ_latQ`), continuous and locally summably bounded in `c` (`PhiQ_continuous`, `PhiQ_bound`), and its
closed-direction integral vanishes for the cosets with `r₀ = 0` (`PhiQ_closed`).

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial
open scoped MatrixGroups ContDiff
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3S4c
  TernaryPeriodPolynomials.Argument.FormClassK TernaryPeriodPolynomials.Argument.GammaNFaces
  TernaryPeriodPolynomials.Argument.Statements.EisensteinClass TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4
  TernaryPeriodPolynomials.Argument.EisensteinDual

section Rep

variable (N : ℕ) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

theorem Tm_coset_gen (a b : ↥(gammaN N))
    (hab : (QuotientGroup.rightRel ((planeStab : Subgroup SL(3, ℤ)).subgroupOf (gammaN N))) a b)
    {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : G.det = 1) {x : Fin 5 → ℝ} (hx : x ∈ Omega)
    (i j : Fin 5) (m : Fin 3 →₀ ℕ) :
    Tm N n f x i j m (realMat a.1 * G) = Tm N n f x i j m (realMat b.1 * G) := by
  have hH : b.1 * a.1⁻¹ ∈ planeStab := by
    have := QuotientGroup.rightRel_apply.1 hab
    simpa using Subgroup.mem_subgroupOf.1 this
  have hΓ : b.1 * a.1⁻¹ ∈ gammaN N := (gammaN N).mul_mem b.2 ((gammaN N).inv_mem a.2)
  have hGa : (realMat a.1 * G).det = 1 := by
    rw [Matrix.det_mul, det_realMat, hG]; norm_num
  have e : realMat b.1 * G = realMat (b.1 * a.1⁻¹) * (realMat a.1 * G) := by
    rw [← Matrix.mul_assoc, ← realMat_mul]; congr 2; simp
  rw [e]
  exact (Tm_stab_mul N n f _ hΓ hH hGa hx i j m).symm

theorem summandPoly_coset_gen (a b : ↥(gammaN N))
    (hab : (QuotientGroup.rightRel ((planeStab : Subgroup SL(3, ℤ)).subgroupOf (gammaN N))) a b)
    {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : G.det = 1) {y : Fin 5 → ℝ} (hy : y ∈ Omega) (i j : Fin 5) :
    summandPoly n (hfun f) (realMat a.1 * G) y i j = summandPoly n (hfun f) (realMat b.1 * G) y i j := by
  apply MvPolynomial.ext
  intro m
  exact Tm_coset_gen N n f a b hab hG hy i j m

theorem fPull_congr_at (Φ : Face → Fin 5 → ℝ)
    (W W' : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ) (x : Face)
    (h : ∀ a b, W (Φ x) a b = W' (Φ x) a b) (i j : Fin 4) :
    fPull Φ W x i j = fPull Φ W' x i j := by
  unfold fPull
  simp only [h]

variable {N n f}

theorem PhiQ_mk {x : Face} (hx : x ∈ faceSet) (p q : Fin 4) (m : Fin 3 →₀ ℕ) (a : ↥(gammaN N))
    (w : Fin 2 → ℝ) :
    PhiQ N n f x p q m (Quotient.mk _ a) w =
      (fPull jFace (fun y a' b => summandPoly n (hfun f) (realMat a.1 * qMat w) y a' b) x p q).coeff m := by
  unfold PhiQ
  have h : (Quotient.mk _ (Quotient.out (Quotient.mk (QuotientGroup.rightRel
      ((planeStab : Subgroup SL(3, ℤ)).subgroupOf (gammaN N))) a)) : PlaneCoset (gammaN N)) =
      Quotient.mk _ a := Quotient.out_eq _
  have hy : jFace x ∈ Omega := jPlane_mem (ptOf_mem hx)
  rw [fPull_congr_at jFace _ (fun y a' b => summandPoly n (hfun f) (realMat a.1 * qMat w) y a' b) x
    (fun a' b => summandPoly_coset_gen N n f _ _ (Quotient.exact h) (det_qMat w) hy a' b) p q]

/-- **Equivariance of `PhiQ` for the line radical lattice.** -/
theorem PhiQ_latQ {x : Face} (hx : x ∈ faceSet) (p q : Fin 4) (m : Fin 3 →₀ ℕ) (ℓ : Fin 2 → ℤ)
    (c : PlaneCoset (gammaN N)) (w : Fin 2 → ℝ) :
    PhiQ N n f x p q m (cosetMulR (gammaN N) (latQ N ℓ) c) w =
      PhiQ N n f x p q m c ((N : ℝ) • intVec ℓ + w) := by
  induction c using Quotient.inductionOn with | _ a => ?_
  rw [cosetMulR_mk, PhiQ_mk hx p q m, PhiQ_mk hx p q m]
  have : realMat (a * latQ N ℓ).1 * qMat w = realMat a.1 * qMat ((N : ℝ) • intVec ℓ + w) := by
    show realMat (a.1 * (latQ N ℓ).1) * qMat w = _
    rw [realMat_mul, realMat_latQ, Matrix.mul_assoc, qMat_mul]
  rw [this]

end Rep

section Analysis

/-- **Locally summably bounded families**: a finite sum of continuous weights times locally
summably dominated families is continuous and locally summably dominated. -/
theorem sum_mul_bound {Cs ι : Type*} (s : Finset ι) (A : ι → (Fin 2 → ℝ) → ℂ)
    (hA : ∀ i, Continuous (A i)) (T : ι → Cs → (Fin 2 → ℝ) → ℂ) (hT : ∀ i c, Continuous (T i c))
    (hTb : ∀ i (R : ℝ), ∃ b : Cs → ℝ, Summable b ∧ ∀ c w, (∀ k, |w k| ≤ R) → ‖T i c w‖ ≤ b c) :
    (∀ c, Continuous fun w => ∑ i ∈ s, A i w * T i c w) ∧
    ∀ R : ℝ, ∃ B : Cs → ℝ, Summable B ∧ ∀ c w, (∀ k, |w k| ≤ R) →
      ‖∑ i ∈ s, A i w * T i c w‖ ≤ B c := by
  refine ⟨fun c => continuous_finsetSum _ fun i _ => (hA i).mul (hT i c), ?_⟩
  intro R
  set Kb : Set (Fin 2 → ℝ) := Metric.closedBall 0 |R| with hKb
  have hKbc : IsCompact Kb := isCompact_closedBall _ _
  have hM : ∀ i, ∃ M : ℝ, 0 ≤ M ∧ ∀ w ∈ Kb, ‖A i w‖ ≤ M := by
    intro i
    obtain ⟨M, hM⟩ := hKbc.exists_bound_of_continuousOn (hA i).continuousOn
    exact ⟨max M 0, le_max_right _ _, fun w hw => (hM w hw).trans (le_max_left _ _)⟩
  choose M hM0 hMb using hM
  choose b hbs hbb using fun i => hTb i R
  refine ⟨fun c => ∑ i ∈ s, M i * b i c, summable_sum fun i _ => (hbs i).mul_left _, fun c w hw => ?_⟩
  have hwK : w ∈ Kb := by
    rw [hKb, mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (abs_nonneg R)]
    intro k
    simpa using (hw k).trans (le_abs_self R)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul]
  exact mul_le_mul (hMb i w hwK) (hbb i c w hw) (norm_nonneg _) (hM0 i)

end Analysis

section PhiQAnalysis

variable (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n)

/-- The weight `κ_{m'}(w) = coeff_m (ρ(qMat (-w)) x^{m'})`. -/
def kapQ (m m' : Fin 3 →₀ ℕ) (w : Fin 2 → ℝ) : ℂ := (rho (qMat (-w)) (monomial m' 1)).coeff m

theorem continuous_kapQ (m m' : Fin 3 →₀ ℕ) : Continuous (kapQ m m') :=
  (contDiff_coeff_rho_qMat (monomial m' (1 : ℂ)) m).continuous.comp continuous_neg

omit [NeZero N] in
/-- **Expansion of `PhiQ` through the translated face pullback of the terms.** -/
theorem PhiQ_expansion {x : Face} (hx : x ∈ faceSet) (p q : Fin 4) (m : Fin 3 →₀ ℕ)
    (c : PlaneCoset (gammaN N)) (w : Fin 2 → ℝ) :
    PhiQ N n f x p q m c w = ∑ m' ∈ monSet n, ∑ a : Fin 5, ∑ b : Fin 5,
      ((((fderiv ℝ jFace (x + shVec w) (Pi.single p 1) a *
        fderiv ℝ jFace (x + shVec w) (Pi.single q 1) b : ℝ) : ℂ)) * kapQ m m' w) *
        termFun (gammaN N) n f c a b m' (jFace (x + shVec w)) := by
  unfold PhiQ
  rw [← rho_fPull_shift n (hfun f) (det_realMat (Quotient.out c).1) hx w p q]
  have hhom := fPull_isHomogeneous n jFace (fun y a b => summandPoly n (hfun f)
    (realMat (Quotient.out c).1) y a b) (fun y a b => summandPoly_isHomogeneous n (hfun f)
    (det_realMat _) y a b) (x + shVec w) p q
  rw [coeff_rho_expansion hhom _ m]
  refine Finset.sum_congr rfl fun m' _ => ?_
  unfold fPull kapQ
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [termFun]
  ring

theorem continuous_shVec : Continuous fun w : Fin 2 → ℝ => shVec w := by
  refine continuous_pi fun k => ?_
  fin_cases k <;> simp [shVec] <;> fun_prop

theorem continuous_jShift {x : Face} (hx : x ∈ faceSet) :
    Continuous fun w : Fin 2 → ℝ => jFace (x + shVec w) :=
  contDiffOn_jFace.continuousOn.comp_continuous (continuous_const.add continuous_shVec)
    fun w => shVec_mem hx w

theorem continuous_fderiv_jShift {x : Face} (hx : x ∈ faceSet) (p : Fin 4) (a : Fin 5) :
    Continuous fun w : Fin 2 → ℝ => fderiv ℝ jFace (x + shVec w) (Pi.single p 1) a := by
  have h1 : ContinuousOn (fun y : Face => fderiv ℝ jFace y) faceSet :=
    contDiffOn_jFace.continuousOn_fderiv_of_isOpen isOpen_faceSet (by simp)
  have h2 : ContinuousOn (fun y : Face => fderiv ℝ jFace y (Pi.single p 1) a) faceSet := by
    have : Continuous fun L : Face →L[ℝ] (Fin 5 → ℝ) => L (Pi.single p 1) a :=
      (continuous_apply a).comp (ContinuousLinearMap.apply ℝ (Fin 5 → ℝ) (Pi.single p 1)).continuous
    exact this.comp_continuousOn h1
  exact h2.comp_continuous (continuous_const.add continuous_shVec) fun w => shVec_mem hx w

omit [NeZero N] in
theorem continuous_termFun_jShift {x : Face} (hx : x ∈ faceSet) (c : PlaneCoset (gammaN N)) (a b : Fin 5)
    (m' : Fin 3 →₀ ℕ) :
    Continuous fun w : Fin 2 → ℝ => termFun (gammaN N) n f c a b m' (jFace (x + shVec w)) := by
  have h := (contDiffOn_termFun (gammaN N) (leviGroup N) n f c a b m').continuousOn
  exact h.comp_continuous (continuous_jShift hx) fun w => jPlane_mem (ptOf_mem (shVec_mem hx w))

/-- Uniform summable bound of the terms along the translated face points. -/
theorem termFun_jShift_bound (hn : 4 ≤ n) {x : Face} (hx : x ∈ faceSet) (a b : Fin 5)
    (m' : Fin 3 →₀ ℕ) (R : ℝ) :
    ∃ B : PlaneCoset (gammaN N) → ℝ, Summable B ∧ ∀ c w, (∀ k, |w k| ≤ R) →
      ‖termFun (gammaN N) n f c a b m' (jFace (x + shVec w))‖ ≤ B c := by
  set Kb : Set (Fin 2 → ℝ) := Metric.closedBall 0 |R| with hKb
  have hKbc : IsCompact Kb := isCompact_closedBall _ _
  set K : Set (Fin 5 → ℝ) := (fun w : Fin 2 → ℝ => jFace (x + shVec w)) '' Kb with hK
  have hKc : IsCompact K := hKbc.image (continuous_jShift hx)
  have hKΩ : K ⊆ Omega := by
    rintro _ ⟨w, -, rfl⟩
    exact jPlane_mem (ptOf_mem (shVec_mem hx w))
  obtain ⟨b', hbs, hbb⟩ := Statements.ConvergenceC4.normal_convergence (gammaN N) (leviGroup N) n f hn
    hKc hKΩ 0
  refine ⟨b', hbs, fun c w hw => ?_⟩
  have hwK : w ∈ Kb := by
    rw [hKb, mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (abs_nonneg R)]
    intro k
    simpa using (hw k).trans (le_abs_self R)
  have := hbb c _ ⟨w, hwK, rfl⟩ a b m'
  simpa using this

omit [NeZero N] in
/-- `PhiQ` as a single finite sum of continuous weights times locally dominated terms. -/
theorem PhiQ_eq_sum_prod {x : Face} (hx : x ∈ faceSet) (p q : Fin 4) (m : Fin 3 →₀ ℕ)
    (c : PlaneCoset (gammaN N)) (w : Fin 2 → ℝ) :
    PhiQ N n f x p q m c w =
      ∑ i ∈ monSet n ×ˢ (Finset.univ : Finset (Fin 5)) ×ˢ (Finset.univ : Finset (Fin 5)),
        ((((fderiv ℝ jFace (x + shVec w) (Pi.single p 1) i.2.1 *
          fderiv ℝ jFace (x + shVec w) (Pi.single q 1) i.2.2 : ℝ) : ℂ)) * kapQ m i.1 w) *
          termFun (gammaN N) n f c i.2.1 i.2.2 i.1 (jFace (x + shVec w)) := by
  rw [PhiQ_expansion N n f hx p q m c w, Finset.sum_product]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [Finset.sum_product]

theorem PhiQ_continuous_bound (hn : 4 ≤ n) {x : Face} (hx : x ∈ faceSet) (p q : Fin 4)
    (m : Fin 3 →₀ ℕ) :
    (∀ c : PlaneCoset (gammaN N), Continuous (PhiQ N n f x p q m c)) ∧
    ∀ R : ℝ, ∃ B : PlaneCoset (gammaN N) → ℝ, Summable B ∧ ∀ c w, (∀ k, |w k| ≤ R) →
      ‖PhiQ N n f x p q m c w‖ ≤ B c := by
  have key := sum_mul_bound (Cs := PlaneCoset (gammaN N))
    (monSet n ×ˢ (Finset.univ : Finset (Fin 5)) ×ˢ (Finset.univ : Finset (Fin 5)))
    (fun i w => ((((fderiv ℝ jFace (x + shVec w) (Pi.single p 1) i.2.1 *
          fderiv ℝ jFace (x + shVec w) (Pi.single q 1) i.2.2 : ℝ) : ℂ)) * kapQ m i.1 w))
    (fun i => by
      refine Continuous.mul ?_ (continuous_kapQ m i.1)
      exact Complex.continuous_ofReal.comp
        ((continuous_fderiv_jShift hx p i.2.1).mul (continuous_fderiv_jShift hx q i.2.2)))
    (fun i c w => termFun (gammaN N) n f c i.2.1 i.2.2 i.1 (jFace (x + shVec w)))
    (fun i c => continuous_termFun_jShift (N := N) (n := n) (f := f) hx c i.2.1 i.2.2 i.1)
    (fun i R => termFun_jShift_bound (N := N) (n := n) (f := f) hn hx i.2.1 i.2.2 i.1 R)
  have heq : ∀ c, PhiQ N n f x p q m c = fun w => ∑ i ∈ monSet n ×ˢ (Finset.univ : Finset (Fin 5)) ×ˢ
      (Finset.univ : Finset (Fin 5)),
      ((((fderiv ℝ jFace (x + shVec w) (Pi.single p 1) i.2.1 *
        fderiv ℝ jFace (x + shVec w) (Pi.single q 1) i.2.2 : ℝ) : ℂ)) * kapQ m i.1 w) *
        termFun (gammaN N) n f c i.2.1 i.2.2 i.1 (jFace (x + shVec w)) := by
    intro c; funext w; exact PhiQ_eq_sum_prod N n f hx p q m c w
  refine ⟨fun c => ?_, fun R => ?_⟩
  · rw [heq]; exact key.1 c
  · obtain ⟨B, hBs, hBb⟩ := key.2 R
    refine ⟨B, hBs, fun c w hw => ?_⟩
    rw [PhiQ_eq_sum_prod N n f hx p q m c w]
    exact hBb c w hw

omit [NeZero N] in
theorem cosetRow_out' (c : PlaneCoset (gammaN N)) (j : Fin 3) :
    cosetRow (gammaN N) c j = ((Quotient.out c).1 : Matrix (Fin 3) (Fin 3) ℤ) 2 j := by
  conv_lhs => rw [← Quotient.out_eq c]
  rfl

omit [NeZero N] in
theorem PhiQ_as_sum {x : Face} (p q : Fin 4) (m : Fin 3 →₀ ℕ) (c : PlaneCoset (gammaN N))
    (w : Fin 2 → ℝ) :
    PhiQ N n f x p q m c w = ∑ a : Fin 5, ∑ b : Fin 5,
      ((((fderiv ℝ jFace x (Pi.single p 1) a * fderiv ℝ jFace x (Pi.single q 1) b : ℝ) : ℂ))) *
        (summandPoly n (hfun f) (realMat (Quotient.out c).1 * qMat w) (jFace x) a b).coeff m := by
  unfold PhiQ fPull
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]

/-- **The closed-direction integral of `PhiQ` vanishes on the cell `r₀ = 0`.** -/
theorem PhiQ_closed {x : Face} (hx : x ∈ faceSet) (p q : Fin 4) (m : Fin 3 →₀ ℕ)
    (c : PlaneCoset (gammaN N)) (h0 : cosetRow (gammaN N) c 0 = 0) :
    ∃ k : Fin 2, ∀ w : Fin 2 → ℝ,
      ∫ s in (0 : ℝ)..1, PhiQ N n f x p q m c (w + s • ((N : ℝ) • (Pi.single k 1 : Fin 2 → ℝ))) = 0 := by
  have hy : jFace x ∈ Omega := jPlane_mem (ptOf_mem hx)
  set γ : SL(3, ℤ) := (Quotient.out c).1 with hγ
  have hγ0 : (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0 := by
    rw [← cosetRow_out']; exact h0
  have hne : (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 1 ≠ 0 ∨ (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 2 ≠ 0 := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    have hdet : (γ : Matrix (Fin 3) (Fin 3) ℤ).det = 1 := γ.2
    rw [Matrix.det_fin_three, hγ0, hcon.1, hcon.2] at hdet
    simp at hdet
  have mk : ∀ (k : Fin 2), (∀ w : Fin 2 → ℝ,
      ∫ s in (0 : ℝ)..1, ∑ i : Fin 5, ∑ j : Fin 5,
        ((((fderiv ℝ jFace x (Pi.single p 1) i * fderiv ℝ jFace x (Pi.single q 1) j : ℝ) : ℂ))) *
          (summandPoly n (hfun f) (realMat γ * qMat (w + s • ((N : ℝ) • (Pi.single k 1 : Fin 2 → ℝ))))
            (jFace x) i j).coeff m = 0) →
      ∀ w : Fin 2 → ℝ, ∫ s in (0 : ℝ)..1,
        PhiQ N n f x p q m c (w + s • ((N : ℝ) • (Pi.single k 1 : Fin 2 → ℝ))) = 0 := by
    intro k hk w
    have := hk w
    simp_rw [PhiQ_as_sum N n f p q m c]
    exact this
  rcases hne with h1 | h2
  · refine ⟨0, mk 0 fun w => ?_⟩
    have hint : (((Pi.single 0 1 : Fin 2 → ℤ)) : Fin 2 → ℤ) = Pi.single 0 1 := rfl
    have := closed_direction_zero_Q N n f γ hγ0 (Pi.single 0 1) (by simpa [Pi.single_apply] using h1) w hy
      (fun i j => ((((fderiv ℝ jFace x (Pi.single p 1) i * fderiv ℝ jFace x (Pi.single q 1) j : ℝ) : ℂ))))
      m
    have e : intVec (Pi.single 0 1 : Fin 2 → ℤ) = (Pi.single 0 1 : Fin 2 → ℝ) := by
      funext i; fin_cases i <;> simp [intVec]
    rw [e] at this
    exact this
  · refine ⟨1, mk 1 fun w => ?_⟩
    have := closed_direction_zero_Q N n f γ hγ0 (Pi.single 1 1)
      (by simpa [Pi.single_apply] using h2) w hy
      (fun i j => ((((fderiv ℝ jFace x (Pi.single p 1) i * fderiv ℝ jFace x (Pi.single q 1) j : ℝ) : ℂ))))
      m
    have e : intVec (Pi.single 1 1 : Fin 2 → ℤ) = (Pi.single 1 1 : Fin 2 → ℝ) := by
      funext i; fin_cases i <;> simp [intVec]
    rw [e] at this
    exact this

end PhiQAnalysis

end TernaryPeriodPolynomials.Argument.EisensteinClass


