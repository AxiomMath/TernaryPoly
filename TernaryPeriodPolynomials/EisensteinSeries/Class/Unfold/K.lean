module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Unfold.Abs
public import TernaryPeriodPolynomials.EisensteinSeries.Class.RestAverage
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Cusp.Instance
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.ConvergenceC4

@[expose] public section


/-!
# Unfolding at the cusp `k⁻¹ P k`: the total averaged coefficient vanishes

Paper: "the same letters
for the rational conjugates" (unfolding table: "the integrated radical quotient is compact, so
Fubini applies").

For `k ∈ SL₃(ℤ)` the series at the cusp `CuspData.ofSL k` is a sum over the cosets
`Γ_{k⁻¹Pk}\Γ(N)` (`Ck`) of the summands `S(k γ)`. The radical lattice `Nℤ²` acts on these cosets by
right multiplication (`latActK`), the coefficient of the summand at `k γ n(v)` is `PhiK`, and the
iterated integral over the radical torus of the sum over all cosets whose bottom row `r_k γ` has
`(r₀, r₁) ≠ 0` vanishes (`totalK_zero`): `PhiK` is equivariant, continuous and locally summably
bounded (normal convergence at the cusp), and its integral over one period of the stabilizing direction
vanishes by cuspidality (`closed_direction_zero` for the integral matrix `k γ`).

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open MeasureTheory Set MvPolynomial
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3S4c

section CuspLattice

variable (N : ℕ) (k : SL(3, ℤ))

/-- The cosets `Γ_{k⁻¹Pk}\Γ(N)` of the cusp `CuspData.ofSL k`. -/
abbrev Ck := CuspCoset (gammaN N) (CuspData.ofSL k).r

/-- Right multiplication of the cusp cosets by an element of `Γ(N)`. -/
def cmulR (δ : ↥(gammaN N)) : Ck N k → Ck N k :=
  Quotient.map (fun a : ↥(gammaN N) => a * δ) (by
    intro a b hab
    have h := QuotientGroup.rightRel_apply.1 hab
    refine QuotientGroup.rightRel_apply.2 ?_
    simpa [mul_assoc] using h)

theorem cmulR_mk (δ a : ↥(gammaN N)) : cmulR N k δ (Quotient.mk _ a) = Quotient.mk _ (a * δ) := rfl

theorem cmulR_one (c : Ck N k) : cmulR N k 1 c = c := by
  induction c using Quotient.inductionOn with | _ a => ?_
  simp [cmulR_mk]

theorem cmulR_mul (δ δ' : ↥(gammaN N)) (c : Ck N k) :
    cmulR N k (δ * δ') c = cmulR N k δ' (cmulR N k δ c) := by
  induction c using Quotient.inductionOn with | _ a => ?_
  simp [cmulR_mk, mul_assoc]

theorem cuspRow_cmulR_nG (ℓ : Fin 2 → ℤ) (c : Ck N k) :
    cuspRow (gammaN N) (CuspData.ofSL k).r (cmulR N k (nG N ℓ) c) 0 =
      cuspRow (gammaN N) (CuspData.ofSL k).r c 0 ∧
    cuspRow (gammaN N) (CuspData.ofSL k).r (cmulR N k (nG N ℓ) c) 1 =
      cuspRow (gammaN N) (CuspData.ofSL k).r c 1 ∧
    cuspRow (gammaN N) (CuspData.ofSL k).r (cmulR N k (nG N ℓ) c) 2 =
      cuspRow (gammaN N) (CuspData.ofSL k).r c 2 + (N : ℤ) *
        (cuspRow (gammaN N) (CuspData.ofSL k).r c 0 * ℓ 0 +
          cuspRow (gammaN N) (CuspData.ofSL k).r c 1 * ℓ 1) := by
  induction c using Quotient.inductionOn with | _ a => ?_
  rw [cmulR_mk]
  simp only [cuspRow_mk]
  have e : ((a * nG N ℓ : ↥(gammaN N)).1 : Matrix (Fin 3) (Fin 3) ℤ) =
      (a.1 : Matrix (Fin 3) (Fin 3) ℤ) *
        ((radElt N (Multiplicative.ofAdd (ℓ 0, ℓ 1)) : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) := rfl
  rw [e, ← Matrix.vecMul_vecMul]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, radElt]
  ring

/-- **The radical lattice acts on the cosets of the cusp `k⁻¹Pk`.** -/
def latActK : LatAct N (Ck N k) where
  act ℓ := cmulR N k (nG N ℓ)
  row := cuspRow (gammaN N) (CuspData.ofSL k).r
  act_zero c := by rw [nG_zero, cmulR_one]
  act_add ℓ ℓ' c := by rw [nG_add, cmulR_mul]
  row0 ℓ c := (cuspRow_cmulR_nG N k ℓ c).1
  row1 ℓ c := (cuspRow_cmulR_nG N k ℓ c).2.1
  row2 ℓ c := (cuspRow_cmulR_nG N k ℓ c).2.2
  row_inj := cuspRow_injective (gammaN N) (CuspData.ofSL k).r


theorem cuspRow_out (c : Ck N k) (j : Fin 3) :
    cuspRow (gammaN N) (CuspData.ofSL k).r c j =
      ((k * (Quotient.out c).1 : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 j := by
  conv_lhs => rw [← Quotient.out_eq c]
  rw [cuspRow_mk]
  simp [CuspData.ofSL, Matrix.vecMul, dotProduct, Matrix.mul_apply, Fin.sum_univ_three]

end CuspLattice

section CuspTerms

variable (N : ℕ) (k : SL(3, ℤ)) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

theorem Tm_cusp_coset (a b : ↥(gammaN N))
    (hab : (QuotientGroup.rightRel ((stabRow (CuspData.ofSL k).r).subgroupOf (gammaN N))) a b)
    (v : Fin 2 → ℝ) {x : Fin 5 → ℝ} (hx : x ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ) :
    Tm N n f x i j m (realMat k * realMat a.1 * nmat v) =
      Tm N n f x i j m (realMat k * realMat b.1 * nmat v) := by
  have hH : b.1 * a.1⁻¹ ∈ stabRow (CuspData.ofSL k).r := by
    have := QuotientGroup.rightRel_apply.1 hab
    simpa using Subgroup.mem_subgroupOf.1 this
  have hps : k * (b.1 * a.1⁻¹) * k⁻¹ ∈ planeStab := (mem_stabRow_ofSL k _).1 hH
  have hΓ : k * (b.1 * a.1⁻¹) * k⁻¹ ∈ gammaN N := by
    have hm : b.1 * a.1⁻¹ ∈ gammaN N := (gammaN N).mul_mem b.2 ((gammaN N).inv_mem a.2)
    have := (gammaN_normal N).conj_mem _ hm k
    simpa [mul_assoc] using this
  have hG : (realMat k * realMat a.1 * nmat v).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, det_realMat, det_realMat, det_nmat]; norm_num
  have hp : (k * (b.1 * a.1⁻¹) * k⁻¹) * (k * a.1) = k * b.1 := by group
  have e : realMat k * realMat b.1 * nmat v =
      realMat (k * (b.1 * a.1⁻¹) * k⁻¹) * (realMat k * realMat a.1 * nmat v) := by
    calc realMat k * realMat b.1 * nmat v = realMat (k * b.1) * nmat v := by rw [realMat_mul]
      _ = realMat ((k * (b.1 * a.1⁻¹) * k⁻¹) * (k * a.1)) * nmat v := by rw [hp]
      _ = _ := by simp only [realMat_mul, Matrix.mul_assoc]
  rw [e]
  exact (Tm_stab_mul N n f _ hΓ hps hG hx i j m).symm

end CuspTerms

section PhiK

variable (N : ℕ) (k : SL(3, ℤ)) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

/-- The coefficient of the summand of a coset of the cusp `k⁻¹Pk` at `k γ n(v)`. -/
def PhiK (x : Fin 5 → ℝ) (i j : Fin 5) (m : Fin 3 →₀ ℕ) (c : Ck N k) (v : Fin 2 → ℝ) : ℂ :=
  Tm N n f x i j m (realMat k * realMat (Quotient.out c).1 * nmat v)

theorem PhiK_mk {x : Fin 5 → ℝ} (hx : x ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ)
    (a : ↥(gammaN N)) (v : Fin 2 → ℝ) :
    PhiK N k n f x i j m (Quotient.mk _ a) v =
      Tm N n f x i j m (realMat k * realMat a.1 * nmat v) := by
  unfold PhiK
  have h : (Quotient.mk _ (Quotient.out (Quotient.mk (QuotientGroup.rightRel
      ((stabRow (CuspData.ofSL k).r).subgroupOf (gammaN N))) a)) : Ck N k) = Quotient.mk _ a :=
    Quotient.out_eq _
  exact Tm_cusp_coset N k n f _ _ (Quotient.exact h) v hx i j m

theorem PhiK_mulR {x : Fin 5 → ℝ} (hx : x ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ)
    (ℓ : Fin 2 → ℤ) (c : Ck N k) (v : Fin 2 → ℝ) :
    PhiK N k n f x i j m (cmulR N k (nG N ℓ) c) v =
      PhiK N k n f x i j m c ((N : ℝ) • intVec ℓ + v) := by
  induction c using Quotient.inductionOn with | _ a => ?_
  rw [cmulR_mk, PhiK_mk N k n f hx, PhiK_mk N k n f hx]
  show Tm N n f x i j m (realMat k * realMat (a.1 * (nG N ℓ).1) * nmat v) = _
  rw [realMat_mul a.1 (nG N ℓ).1, realMat_nG, ← Matrix.mul_assoc (realMat k) (realMat a.1)
    (nmat ((N : ℝ) • intVec ℓ)), Matrix.mul_assoc _ (nmat ((N : ℝ) • intVec ℓ)) (nmat v), nmat_mul,
    Matrix.mul_assoc]

variable [NeZero N]

theorem PhiK_closed {x : Fin 5 → ℝ} (hx : x ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ)
    (c₀ : Ck N k)
    (hrow : cuspRow (gammaN N) (CuspData.ofSL k).r c₀ 0 ≠ 0 ∨
      cuspRow (gammaN N) (CuspData.ofSL k).r c₀ 1 ≠ 0)
    (d' : Fin 2 → ℤ) (hd' : d' ≠ 0)
    (hker : cuspRow (gammaN N) (CuspData.ofSL k).r c₀ 0 * d' 0 +
      cuspRow (gammaN N) (CuspData.ofSL k).r c₀ 1 * d' 1 = 0)
    (w : Fin 2 → ℝ) :
    ∫ s in (0 : ℝ)..1, PhiK N k n f x i j m c₀ (w + s • ((N : ℝ) • intVec d')) = 0 := by
  rw [cuspRow_out, cuspRow_out] at hker
  rw [cuspRow_out, cuspRow_out] at hrow
  have := closed_direction_zero N n f (k * (Quotient.out c₀).1) hrow d' hd' hker w hx i j m
  rw [← this]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [PhiK, Tm]
  rw [realMat_mul k (Quotient.out c₀).1]

omit [NeZero N] in
theorem PhiK_expansion {x : Fin 5 → ℝ} (hx : x ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ)
    (c : Ck N k) (v : Fin 2 → ℝ) :
    PhiK N k n f x i j m c v = ∑ m' ∈ monSet n,
      termFunK false (CuspData.ofSL k) (gammaN N) n f c i j m'
          (x + ![v 0, v 1, 0, 0, 0]) *
        (rho (nmat (-v)) (monomial m' 1)).coeff m := by
  unfold PhiK Tm
  have hdet : (realMat k * realMat (Quotient.out c).1).det = 1 := by
    rw [Matrix.det_mul, det_realMat, det_realMat]; norm_num
  rw [coeff_summandPoly_mul_nmat n (hfun f) hdet v hx i j m]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [termFunK_eq]
  rfl

omit [NeZero N] in
theorem PhiK_continuous {x : Fin 5 → ℝ} (hx : x ∈ Omega) (i j : Fin 5)
    (m : Fin 3 →₀ ℕ) (c : Ck N k) : Continuous (PhiK N k n f x i j m c) := by
  have : PhiK N k n f x i j m c = fun v => ∑ m' ∈ monSet n,
      termFunK false (CuspData.ofSL k) (gammaN N) n f c i j m'
          (x + ![v 0, v 1, 0, 0, 0]) *
        (rho (nmat (-v)) (monomial m' 1)).coeff m := by
    funext v; exact PhiK_expansion N k n f hx i j m c v
  rw [this]
  refine continuous_finsetSum _ fun m' _ => ?_
  refine Continuous.mul ?_ (continuous_kappa m m')
  have h := (contDiffOn_termFunK false (CuspData.ofSL k) (gammaN N) (leviGroup N) n f c i j m').continuousOn
  exact h.comp_continuous (continuous_shift x) (fun v => shift_mem_Omega hx v)

theorem PhiK_bound (hn : 4 ≤ n) {x : Fin 5 → ℝ} (hx : x ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ)
    (R : ℝ) :
    ∃ B : Ck N k → ℝ, Summable B ∧ ∀ c v, (∀ k', |v k'| ≤ R) →
      ‖PhiK N k n f x i j m c v‖ ≤ B c := by
  set Kb : Set (Fin 2 → ℝ) := Metric.closedBall 0 |R| with hKb
  have hKbc : IsCompact Kb := isCompact_closedBall _ _
  set K : Set (Fin 5 → ℝ) := (fun v : Fin 2 → ℝ => x + ![v 0, v 1, 0, 0, 0]) '' Kb with hK
  have hKc : IsCompact K := hKbc.image (continuous_shift x)
  have hKΩ : K ⊆ Omega := by
    rintro _ ⟨v, -, rfl⟩
    exact shift_mem_Omega hx v
  obtain ⟨b, hbs, hbb⟩ := Statements.ConvergenceC4.normal_convergence_at false (CuspData.ofSL k)
    (gammaN N) (leviGroup N) n f hn hKc hKΩ 0
  have hMκ : ∀ m' : Fin 3 →₀ ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ v ∈ Kb,
      ‖(rho (nmat (-v)) (monomial m' 1)).coeff m‖ ≤ M := by
    intro m'
    obtain ⟨M, hM⟩ := hKbc.exists_bound_of_continuousOn (continuous_kappa m m').continuousOn
    exact ⟨max M 0, le_max_right _ _, fun v hv => (hM v hv).trans (le_max_left _ _)⟩
  choose Mκ hMκ0 hMκb using hMκ
  refine ⟨fun c => (∑ m' ∈ monSet n, Mκ m') * b c, hbs.mul_left _, fun c v hv => ?_⟩
  have hvK : v ∈ Kb := by
    rw [hKb, mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (abs_nonneg R)]
    intro k'
    simpa using (hv k').trans (le_abs_self R)
  have hxK : x + ![v 0, v 1, 0, 0, 0] ∈ K := ⟨v, hvK, rfl⟩
  have hb0 : 0 ≤ b c := by
    have := hbb c _ hxK i j 0
    exact (norm_nonneg _).trans this
  rw [PhiK_expansion N k n f hx]
  refine (norm_sum_le _ _).trans ?_
  show _ ≤ (∑ m' ∈ monSet n, Mκ m') * b c
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun m' _ => ?_
  rw [norm_mul]
  have h1 : ‖termFunK false (CuspData.ofSL k) (gammaN N) n f c i j m'
      (x + ![v 0, v 1, 0, 0, 0])‖ ≤ b c := by
    have := hbb c _ hxK i j m'
    simpa using this
  exact mul_le_mul h1 (hMκb m' v hvK) (norm_nonneg _) hb0 |>.trans_eq (mul_comm _ _)

end PhiK

section TotalK

variable (N : ℕ) [NeZero N] (k : SL(3, ℤ)) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

open Classical in
/-- The coefficient of the summand of a non-cell coset (zero on the cells, the cosets whose bottom
row has vanishing first two entries). -/
def FcK (x : Fin 5 → ℝ) (i j : Fin 5) (m : Fin 3 →₀ ℕ) (c : Ck N k) (v : Fin 2 → ℝ) : ℂ :=
  if cuspRow (gammaN N) (CuspData.ofSL k).r c 0 = 0 ∧ cuspRow (gammaN N) (CuspData.ofSL k).r c 1 = 0
  then 0 else PhiK N k n f x i j m c v

omit [NeZero N] in
theorem FcK_mulR {x : Fin 5 → ℝ} (hx : x ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ)
    (ℓ : Fin 2 → ℤ) (c : Ck N k) (v : Fin 2 → ℝ) :
    FcK N k n f x i j m (cmulR N k (nG N ℓ) c) v =
      FcK N k n f x i j m c ((N : ℝ) • intVec ℓ + v) := by
  unfold FcK
  have e0 := (cuspRow_cmulR_nG N k ℓ c).1
  have e1 := (cuspRow_cmulR_nG N k ℓ c).2.1
  rw [e0, e1]
  by_cases hc : cuspRow (gammaN N) (CuspData.ofSL k).r c 0 = 0 ∧
      cuspRow (gammaN N) (CuspData.ofSL k).r c 1 = 0
  · rw [ite_eq_left hc, ite_eq_left hc]
  · rw [ite_eq_right hc, ite_eq_right hc]
    exact PhiK_mulR N k n f hx i j m ℓ c v

omit [NeZero N] in
theorem FcK_continuous {x : Fin 5 → ℝ} (hx : x ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ)
    (c : Ck N k) : Continuous (FcK N k n f x i j m c) := by
  unfold FcK
  by_cases hc : cuspRow (gammaN N) (CuspData.ofSL k).r c 0 = 0 ∧
      cuspRow (gammaN N) (CuspData.ofSL k).r c 1 = 0
  · simp only [ite_eq_left hc]; exact continuous_const
  · simp only [ite_eq_right hc]; exact PhiK_continuous N k n f hx i j m c

theorem FcK_bound (hn : 4 ≤ n) {x : Fin 5 → ℝ} (hx : x ∈ Omega) (i j : Fin 5)
    (m : Fin 3 →₀ ℕ) (R : ℝ) :
    ∃ B : Ck N k → ℝ, Summable B ∧ ∀ c v, (∀ k', |v k'| ≤ R) →
      ‖FcK N k n f x i j m c v‖ ≤ B c := by
  obtain ⟨B, hBs, hBb⟩ := PhiK_bound N k n f hn hx i j m R
  refine ⟨B, hBs, fun c v hv => ?_⟩
  unfold FcK
  by_cases hc : cuspRow (gammaN N) (CuspData.ofSL k).r c 0 = 0 ∧
      cuspRow (gammaN N) (CuspData.ofSL k).r c 1 = 0
  · simp only [ite_eq_left hc, norm_zero]
    exact (norm_nonneg _).trans (hBb c v hv)
  · simp only [ite_eq_right hc]
    exact hBb c v hv

/-- **The total averaged coefficient vanishes at the cusp `k⁻¹Pk`**: the iterated integral over the
radical torus of the sum over all non-cell cosets is zero (unfolding over the orbits of the radical
lattice acting on `Γ_{k⁻¹Pk}\Γ(N)`; cuspidality along the stabilizing horocycle). -/
theorem totalK_zero (hn : 4 ≤ n) {x : Fin 5 → ℝ} (hx : x ∈ Omega)
    (i j : Fin 5) (m : Fin 3 →₀ ℕ) :
    ∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..1,
      ∑' c : Ck N k, FcK N k n f x i j m c ((N : ℝ) • ![a, b]) = 0 := by
  refine (latActK N k).total_zero (FcK N k n f x i j m)
    (fun ℓ c v => FcK_mulR N k n f hx i j m ℓ c v) (FcK_continuous N k n f hx i j m)
    (fun R => FcK_bound N k n f hn hx i j m R) ?_ ?_
  · intro c₀ hrow d' hd' hker w
    have hnc : ¬ (cuspRow (gammaN N) (CuspData.ofSL k).r c₀ 0 = 0 ∧
        cuspRow (gammaN N) (CuspData.ofSL k).r c₀ 1 = 0) := by
      rintro ⟨h0, h1⟩
      rcases hrow with h | h
      · exact h h0
      · exact h h1
    have := PhiK_closed N k n f hx i j m c₀ hrow d' hd' hker w
    simpa only [FcK, ite_eq_right hnc] using this
  · intro c h0 h1 v
    unfold FcK
    rw [ite_eq_left ⟨h0, h1⟩]

end TotalK

end TernaryPeriodPolynomials.Argument.EisensteinClass
