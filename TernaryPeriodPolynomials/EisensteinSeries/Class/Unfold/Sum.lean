module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Unfold.Geom
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Unfold.Orbit
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.ConvergenceC4
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Trans
public import TernaryPeriodPolynomials.EisensteinSeries.Class.ConstantTerm
public import TernaryPeriodPolynomials.EisensteinSeries.Class.IterTsum

@[expose] public section


/-!
# Unfolding the non-identity part of the series: the total averaged coefficient vanishes

`PhiC` is the coefficient of the summand of a coset at `γ n(v)`; it is equivariant, continuous and locally
summably bounded (normal convergence, `PhiC_bound`), and its stabilizing-direction integral vanishes
(`PhiC_closed`). `total_zero`: the iterated integral over the radical torus of the sum over all
non-identity cosets vanishes (fibrewise summation over the orbits of the radical lattice,
`tsum_iterIntegral`, `Fc_orbit_zero`). Needs `3 ≤ N` so that the identity coset is exactly the coset
with bottom row `(0, 0, c₃)`.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open MeasureTheory Set MvPolynomial
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3S4c

variable (N : ℕ) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

/-- The coefficient of the summand at a real matrix. -/
def Tm (x : Fin 5 → ℝ) (i j : Fin 5) (m : Fin 3 →₀ ℕ) (G : Matrix (Fin 3) (Fin 3) ℝ) : ℂ :=
  (summandPoly n (hfun f) G x i j).coeff m

theorem Tm_stab_mul (p : SL(3, ℤ)) (hp : p ∈ gammaN N) (hps : p ∈ planeStab)
    {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : G.det = 1) {x : Fin 5 → ℝ} (hx : x ∈ Omega)
    (i j : Fin 5) (m : Fin 3 →₀ ℕ) :
    Tm N n f x i j m (realMat p * G) = Tm N n f x i j m G := by
  obtain ⟨g, hg, hgeq⟩ := leviIn_gammaN N p hp hps
  have hdetA : (topBlock (realMat p)).det = 1 := det_topBlock hps
  unfold Tm
  rw [realMat_stab_eq hps, summandPoly_parabolic_mul n (hfun f) _ hdetA _ hG hx i j,
    coeff_summandPoly_eq n _ hG, coeff_summandPoly_eq n _ hG]
  congr 1
  have hτ := seedTau_im_pos (planeAct_mem hG hx)
  rw [← hgeq]
  exact slashTwisted_cuspFunction (leviGroup N) (n + 3) f g hg _ hτ

theorem Tm_coset (a b : ↥(gammaN N))
    (hab : (QuotientGroup.rightRel ((planeStab : Subgroup SL(3, ℤ)).subgroupOf (gammaN N))) a b)
    (v : Fin 2 → ℝ) {x : Fin 5 → ℝ} (hx : x ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ) :
    Tm N n f x i j m (realMat a.1 * nmat v) = Tm N n f x i j m (realMat b.1 * nmat v) := by
  have hH : b.1 * a.1⁻¹ ∈ planeStab := by
    have := QuotientGroup.rightRel_apply.1 hab
    simpa using Subgroup.mem_subgroupOf.1 this
  have hΓ : b.1 * a.1⁻¹ ∈ gammaN N := (gammaN N).mul_mem b.2 ((gammaN N).inv_mem a.2)
  have hG : (realMat a.1 * nmat v).det = 1 := by
    rw [Matrix.det_mul, det_realMat, det_nmat]; norm_num
  have e : b.1 = (b.1 * a.1⁻¹) * a.1 := by simp
  conv_rhs => rw [e, realMat_mul, Matrix.mul_assoc]
  exact (Tm_stab_mul N n f _ hΓ hH hG hx i j m).symm

/-- The coefficient of the summand of a coset at `γ n(v)`. -/
def PhiC (x : Fin 5 → ℝ) (i j : Fin 5) (m : Fin 3 →₀ ℕ) (c : PlaneCoset (gammaN N))
    (v : Fin 2 → ℝ) : ℂ :=
  Tm N n f x i j m (realMat (Quotient.out c).1 * nmat v)

theorem PhiC_mk {x : Fin 5 → ℝ} (hx : x ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ)
    (a : ↥(gammaN N)) (v : Fin 2 → ℝ) :
    PhiC N n f x i j m (Quotient.mk _ a) v = Tm N n f x i j m (realMat a.1 * nmat v) := by
  unfold PhiC
  have h : (Quotient.mk _ (Quotient.out (Quotient.mk (QuotientGroup.rightRel
      ((planeStab : Subgroup SL(3, ℤ)).subgroupOf (gammaN N))) a)) :
      PlaneCoset (gammaN N)) = Quotient.mk _ a := Quotient.out_eq _
  exact Tm_coset N n f _ _ (Quotient.exact h) v hx i j m

theorem PhiC_mulR {x : Fin 5 → ℝ} (hx : x ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ)
    (ℓ : Fin 2 → ℤ) (c : PlaneCoset (gammaN N)) (v : Fin 2 → ℝ) :
    PhiC N n f x i j m (cosetMulR (gammaN N) (nG N ℓ) c) v =
      PhiC N n f x i j m c ((N : ℝ) • intVec ℓ + v) := by
  induction c using Quotient.inductionOn with | _ a => ?_
  rw [cosetMulR_mk, PhiC_mk N n f hx, PhiC_mk N n f hx]
  show Tm N n f x i j m (realMat (a.1 * (nG N ℓ).1) * nmat v) = _
  rw [realMat_mul, realMat_nG, Matrix.mul_assoc, nmat_mul]

theorem PhiC_closed [NeZero N] {x : Fin 5 → ℝ} (hx : x ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ)
    (c₀ : PlaneCoset (gammaN N))
    (hrow : cosetRow (gammaN N) c₀ 0 ≠ 0 ∨ cosetRow (gammaN N) c₀ 1 ≠ 0)
    (d' : Fin 2 → ℤ) (hd' : d' ≠ 0)
    (hker : cosetRow (gammaN N) c₀ 0 * d' 0 + cosetRow (gammaN N) c₀ 1 * d' 1 = 0)
    (w : Fin 2 → ℝ) :
    ∫ s in (0 : ℝ)..1, PhiC N n f x i j m c₀ (w + s • ((N : ℝ) • intVec d')) = 0 := by
  have hrow' : ∀ k, cosetRow (gammaN N) c₀ k = ((Quotient.out c₀).1 : Matrix (Fin 3) (Fin 3) ℤ) 2 k :=
    fun k => by
      conv_lhs => rw [← Quotient.out_eq c₀]
      rfl
  rw [hrow', hrow'] at hker
  rw [hrow', hrow'] at hrow
  exact closed_direction_zero N n f (Quotient.out c₀).1 hrow d' hd' hker w hx i j m

theorem shift_mem_Omega {x : Fin 5 → ℝ} (hx : x ∈ Omega) (v : Fin 2 → ℝ) :
    x + ![v 0, v 1, 0, 0, 0] ∈ Omega := by
  obtain ⟨h3, h4⟩ := hx
  exact ⟨by simpa using h3, by simpa using h4⟩

theorem continuous_shift (x : Fin 5 → ℝ) :
    Continuous fun v : Fin 2 → ℝ => x + ![v 0, v 1, 0, 0, 0] := by
  refine continuous_const.add (continuous_pi fun k => ?_)
  fin_cases k <;> simp <;> fun_prop

theorem PhiC_expansion {x : Fin 5 → ℝ} (hx : x ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ)
    (c : PlaneCoset (gammaN N)) (v : Fin 2 → ℝ) :
    PhiC N n f x i j m c v = ∑ m' ∈ monSet n,
      termFun (gammaN N) n f c i j m' (x + ![v 0, v 1, 0, 0, 0]) *
        (rho (nmat (-v)) (monomial m' 1)).coeff m := by
  unfold PhiC Tm
  rw [coeff_summandPoly_mul_nmat n (hfun f) (det_realMat _) v hx i j m]
  rfl

theorem continuous_kappa (m m' : Fin 3 →₀ ℕ) :
    Continuous fun v : Fin 2 → ℝ => (rho (nmat (-v)) (monomial m' 1)).coeff m := by
  have := (contDiff_coeff_rho_transMat (monomial m' (1 : ℂ)) m).continuous
  have h2 : Continuous fun v : Fin 2 → ℝ => -v := continuous_neg
  exact this.comp h2

theorem PhiC_continuous [NeZero N] {x : Fin 5 → ℝ} (hx : x ∈ Omega) (i j : Fin 5)
    (m : Fin 3 →₀ ℕ) (c : PlaneCoset (gammaN N)) : Continuous (PhiC N n f x i j m c) := by
  have : PhiC N n f x i j m c = fun v => ∑ m' ∈ monSet n,
      termFun (gammaN N) n f c i j m' (x + ![v 0, v 1, 0, 0, 0]) *
        (rho (nmat (-v)) (monomial m' 1)).coeff m := by
    funext v; exact PhiC_expansion N n f hx i j m c v
  rw [this]
  refine continuous_finsetSum _ fun m' _ => ?_
  refine Continuous.mul ?_ (continuous_kappa m m')
  have h := (contDiffOn_termFun (gammaN N) (leviGroup N) n f c i j m').continuousOn
  exact h.comp_continuous (continuous_shift x) (fun v => shift_mem_Omega hx v)

theorem PhiC_bound [NeZero N] (hn : 4 ≤ n) {x : Fin 5 → ℝ} (hx : x ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ)
    (R : ℝ) :
    ∃ B : PlaneCoset (gammaN N) → ℝ, Summable B ∧ ∀ c v, (∀ k, |v k| ≤ R) →
      ‖PhiC N n f x i j m c v‖ ≤ B c := by
  set Kb : Set (Fin 2 → ℝ) := Metric.closedBall 0 |R| with hKb
  have hKbc : IsCompact Kb := isCompact_closedBall _ _
  set K : Set (Fin 5 → ℝ) := (fun v : Fin 2 → ℝ => x + ![v 0, v 1, 0, 0, 0]) '' Kb with hK
  have hKc : IsCompact K := hKbc.image (continuous_shift x)
  have hKΩ : K ⊆ Omega := by
    rintro _ ⟨v, -, rfl⟩
    exact shift_mem_Omega hx v
  obtain ⟨b, hbs, hbb⟩ := Statements.ConvergenceC4.normal_convergence (gammaN N) (leviGroup N) n f hn
    hKc hKΩ 0
  -- bounds for the weights
  have hMκ : ∀ m' : Fin 3 →₀ ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ v ∈ Kb,
      ‖(rho (nmat (-v)) (monomial m' 1)).coeff m‖ ≤ M := by
    intro m'
    obtain ⟨M, hM⟩ := hKbc.exists_bound_of_continuousOn (continuous_kappa m m').continuousOn
    exact ⟨max M 0, le_max_right _ _, fun v hv => (hM v hv).trans (le_max_left _ _)⟩
  choose Mκ hMκ0 hMκb using hMκ
  refine ⟨fun c => (∑ m' ∈ monSet n, Mκ m') * b c, hbs.mul_left _, fun c v hv => ?_⟩
  have hvK : v ∈ Kb := by
    rw [hKb, mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (abs_nonneg R)]
    intro k
    simpa using (hv k).trans (le_abs_self R)
  have hxK : x + ![v 0, v 1, 0, 0, 0] ∈ K := ⟨v, hvK, rfl⟩
  have hb0 : 0 ≤ b c := by
    have := hbb c _ hxK i j 0
    exact (norm_nonneg _).trans this
  rw [PhiC_expansion N n f hx]
  refine (norm_sum_le _ _).trans ?_
  show _ ≤ (∑ m' ∈ monSet n, Mκ m') * b c
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun m' _ => ?_
  rw [norm_mul]
  have h1 : ‖termFun (gammaN N) n f c i j m' (x + ![v 0, v 1, 0, 0, 0])‖ ≤ b c := by
    have := hbb c _ hxK i j m'
    simpa using this
  exact mul_le_mul h1 (hMκb m' v hvK) (norm_nonneg _) hb0 |>.trans_eq (mul_comm _ _)

/-! ### Dropping the identity coset, and the total orbit sum -/

theorem cosetMulR_nG_id (ℓ : Fin 2 → ℤ) :
    cosetMulR (gammaN N) (nG N ℓ) (idCoset (gammaN N)) = idCoset (gammaN N) := by
  apply cosetRow_injective (gammaN N)
  obtain ⟨e0, e1, e2⟩ := cosetRow_mulR_nG N ℓ (idCoset (gammaN N))
  have r0 : cosetRow (gammaN N) (idCoset (gammaN N)) 0 = 0 := rfl
  have r1 : cosetRow (gammaN N) (idCoset (gammaN N)) 1 = 0 := rfl
  funext k
  fin_cases k
  · exact e0
  · exact e1
  · show cosetRow (gammaN N) (cosetMulR (gammaN N) (nG N ℓ) (idCoset (gammaN N))) 2 =
      cosetRow (gammaN N) (idCoset (gammaN N)) 2
    rw [e2, r0, r1]; ring

theorem cosetMulR_eq_id_iff (ℓ : Fin 2 → ℤ) (c : PlaneCoset (gammaN N)) :
    cosetMulR (gammaN N) (nG N ℓ) c = idCoset (gammaN N) ↔ c = idCoset (gammaN N) := by
  constructor
  · intro h
    have := congrArg (cosetMulR (gammaN N) (nG N (-ℓ))) h
    rw [← cosetMulR_mul, ← nG_add, add_neg_cancel, nG_zero, cosetMulR_one,
      cosetMulR_nG_id] at this
    exact this
  · rintro rfl
    exact cosetMulR_nG_id N ℓ

open Classical in
/-- The coefficient of the summand of a non-identity coset (zero on the identity coset). -/
def Fc (x : Fin 5 → ℝ) (i j : Fin 5) (m : Fin 3 →₀ ℕ) (c : PlaneCoset (gammaN N))
    (v : Fin 2 → ℝ) : ℂ :=
  if c = idCoset (gammaN N) then 0 else PhiC N n f x i j m c v

theorem Fc_mulR {x : Fin 5 → ℝ} (hx : x ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ)
    (ℓ : Fin 2 → ℤ) (c : PlaneCoset (gammaN N)) (v : Fin 2 → ℝ) :
    Fc N n f x i j m (cosetMulR (gammaN N) (nG N ℓ) c) v =
      Fc N n f x i j m c ((N : ℝ) • intVec ℓ + v) := by
  unfold Fc
  by_cases hc : c = idCoset (gammaN N)
  · rw [ite_eq_left hc, ite_eq_left ((cosetMulR_eq_id_iff N ℓ c).2 hc)]
  · rw [ite_eq_right hc, ite_eq_right (fun h => hc ((cosetMulR_eq_id_iff N ℓ c).1 h))]
    exact PhiC_mulR N n f hx i j m ℓ c v

theorem Fc_continuous [NeZero N] {x : Fin 5 → ℝ} (hx : x ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ)
    (c : PlaneCoset (gammaN N)) : Continuous (Fc N n f x i j m c) := by
  unfold Fc
  by_cases hc : c = idCoset (gammaN N)
  · simp only [ite_eq_left hc]; exact continuous_const
  · simp only [ite_eq_right hc]; exact PhiC_continuous N n f hx i j m c

theorem Fc_bound [NeZero N] (hn : 4 ≤ n) {x : Fin 5 → ℝ} (hx : x ∈ Omega) (i j : Fin 5)
    (m : Fin 3 →₀ ℕ) (R : ℝ) :
    ∃ B : PlaneCoset (gammaN N) → ℝ, Summable B ∧ ∀ c v, (∀ k, |v k| ≤ R) →
      ‖Fc N n f x i j m c v‖ ≤ B c := by
  obtain ⟨B, hBs, hBb⟩ := PhiC_bound N n f hn hx i j m R
  refine ⟨B, hBs, fun c v hv => ?_⟩
  unfold Fc
  by_cases hc : c = idCoset (gammaN N)
  · simp only [ite_eq_left hc, norm_zero]
    exact (norm_nonneg _).trans (hBb c v hv)
  · simp only [ite_eq_right hc]
    exact hBb c v hv

theorem Fc_orbit_zero [NeZero N] (hn : 4 ≤ n) {x : Fin 5 → ℝ} (hx : x ∈ Omega) (i j : Fin 5)
    (m : Fin 3 →₀ ℕ) (c₀ : PlaneCoset (gammaN N))
    (hrow : cosetRow (gammaN N) c₀ 0 ≠ 0 ∨ cosetRow (gammaN N) c₀ 1 ≠ 0) :
    ∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..1,
      ∑' c : Orb N c₀, Fc N n f x i j m c.1 ((N : ℝ) • ![a, b]) = 0 := by
  have hc0 : c₀ ≠ idCoset (gammaN N) := by
    intro h
    rw [h] at hrow
    rcases hrow with h | h <;> exact h rfl
  refine orbit_integral_zero (Fc N n f x i j m) (fun ℓ c v => Fc_mulR N n f hx i j m ℓ c v)
    (Fc_continuous N n f hx i j m) (fun R => Fc_bound N n f hn hx i j m R) c₀ hrow ?_
  intro d' hd' hker w
  have := PhiC_closed N n f hx i j m c₀ hrow d' hd' hker w
  simpa only [Fc, ite_eq_right hc0] using this

/-- **The total averaged coefficient vanishes**: the iterated integral over the radical torus of
the sum over all non-identity cosets is zero (unfolding over the orbits of the radical lattice;
cuspidality along the stabilizing horocycle). -/
theorem total_zero [NeZero N] (hN : 3 ≤ N) (hn : 4 ≤ n) {x : Fin 5 → ℝ} (hx : x ∈ Omega)
    (i j : Fin 5) (m : Fin 3 →₀ ℕ) :
    ∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..1,
      ∑' c : PlaneCoset (gammaN N), Fc N n f x i j m c ((N : ℝ) • ![a, b]) = 0 := by
  classical
  obtain ⟨B, hBs, hBb⟩ := Fc_bound N n f hn hx i j m (N : ℝ)
  let q : Cs N → Quotient (orbSetoid N) := fun c => Quotient.mk (orbSetoid N) c
  have hvbd : ∀ a b : ℝ, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 → ∀ k : Fin 2,
      |((N : ℝ) • ![a, b]) k| ≤ N := by
    intro a b ha hb k
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    fin_cases k
    · simp only [Pi.smul_apply, smul_eq_mul, abs_mul, Nat.abs_cast]
      simp
      rw [abs_of_nonneg ha.1]
      exact mul_le_of_le_one_right hN0 ha.2
    · simp only [Pi.smul_apply, smul_eq_mul, abs_mul, Nat.abs_cast]
      simp
      rw [abs_of_nonneg hb.1]
      exact mul_le_of_le_one_right hN0 hb.2
  let G : Quotient (orbSetoid N) → ℝ → ℝ → ℂ := fun o a b =>
    ∑' c : q ⁻¹' {o}, Fc N n f x i j m c.1 ((N : ℝ) • ![a, b])
  have hHB : HasSum (fun o : Quotient (orbSetoid N) => ∑' c : q ⁻¹' {o}, B c) (∑' c, B c) :=
    hBs.hasSum.tsum_fiberwise q
  have hfib : ∀ a b : ℝ, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 →
      HasSum (fun o => G o a b) (∑' c, Fc N n f x i j m c ((N : ℝ) • ![a, b])) := by
    intro a b ha hb
    have hs : Summable fun c => Fc N n f x i j m c ((N : ℝ) • ![a, b]) :=
      Summable.of_norm_bounded hBs (fun c => hBb c _ (hvbd a b ha hb))
    exact hs.hasSum.tsum_fiberwise q
  have hGc : ∀ o, Continuous (Function.uncurry (G o)) := by
    intro o
    have h1 := continuous_tsum_set (N := N) (Fc N n f x i j m)
      (Fc_continuous N n f hx i j m) (fun R => Fc_bound N n f hn hx i j m R) (q ⁻¹' {o})
    exact h1.comp (show Continuous fun p : ℝ × ℝ => (![p.1, p.2] : Fin 2 → ℝ) by fun_prop)
  have hGb : ∀ o a b, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 →
      ‖G o a b‖ ≤ ∑' c : q ⁻¹' {o}, B c := by
    intro o a b ha hb
    exact tsum_of_norm_bounded ((hBs.subtype (q ⁻¹' {o})).hasSum)
      (fun c => hBb c.1 _ (hvbd a b ha hb))
  have hG0 : ∀ o, ∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..1, G o a b = 0 := by
    intro o
    induction o using Quotient.inductionOn with | _ c₀ => ?_
    by_cases hrow : cosetRow (gammaN N) c₀ 0 ≠ 0 ∨ cosetRow (gammaN N) c₀ 1 ≠ 0
    · have hset : q ⁻¹' {Quotient.mk (orbSetoid N) c₀} = {c | OrbRel N c₀ c} := by
        ext c
        show Quotient.mk (orbSetoid N) c = Quotient.mk (orbSetoid N) c₀ ↔ OrbRel N c₀ c
        rw [Quotient.eq]
        exact ⟨fun h => OrbRel.symm N h, fun h => OrbRel.symm N h⟩
      have := Fc_orbit_zero N n f hn hx i j m c₀ hrow
      rw [← this]
      refine intervalIntegral.integral_congr fun a _ => ?_
      refine intervalIntegral.integral_congr fun b _ => ?_
      exact tsum_congr_set_coe (fun c => Fc N n f x i j m c ((N : ℝ) • ![a, b])) hset
    · rw [not_or, not_not, not_not] at hrow
      have hcid : ∀ c : q ⁻¹' {Quotient.mk (orbSetoid N) c₀}, c.1 = idCoset (gammaN N) := by
        rintro ⟨c, hc⟩
        have hc' : OrbRel N c c₀ := by
          have : Quotient.mk (orbSetoid N) c = Quotient.mk (orbSetoid N) c₀ := hc
          rw [Quotient.eq] at this
          exact this
        obtain ⟨ℓ, hℓ⟩ := hc'
        obtain ⟨e0, e1, -⟩ := cosetRow_mulR_nG N ℓ c
        rw [hℓ] at e0 e1
        exact (eq_idCoset_iff hN c).2 ⟨e0.symm.trans hrow.1, e1.symm.trans hrow.2⟩
      have hz : ∀ a b, G (Quotient.mk (orbSetoid N) c₀) a b = 0 := by
        intro a b
        show ∑' c : q ⁻¹' {Quotient.mk (orbSetoid N) c₀},
          Fc N n f x i j m c.1 ((N : ℝ) • ![a, b]) = 0
        have : ∀ c : q ⁻¹' {Quotient.mk (orbSetoid N) c₀},
            Fc N n f x i j m c.1 ((N : ℝ) • ![a, b]) = 0 := by
          intro c
          simp [Fc, hcid c]
        exact (tsum_congr this).trans tsum_zero
      simp [hz]
  have hex := tsum_iterIntegral G hGc (fun o => ∑' c : q ⁻¹' {o}, B c) hHB.summable hGb
  have hcount : ∀ o : Quotient (orbSetoid N), True := fun _ => trivial
  calc ∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..1,
        ∑' c : PlaneCoset (gammaN N), Fc N n f x i j m c ((N : ℝ) • ![a, b])
      = ∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..1, ∑' o, G o a b := by
        refine intervalIntegral.integral_congr fun a ha => ?_
        refine intervalIntegral.integral_congr fun b hb => ?_
        rw [uIcc_of_le zero_le_one] at ha hb
        exact (hfib a b ha hb).tsum_eq.symm
    _ = ∑' o, ∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..1, G o a b := hex.symm
    _ = 0 := by simp [hG0]

end TernaryPeriodPolynomials.Argument.EisensteinClass
