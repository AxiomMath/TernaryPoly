module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Heisenberg.HeisCore

@[expose] public section


/-!
# The averaging step: the homotopy `1 - A = D h + h D` from the Cartan identity and nilpotent inversion

Formalized by Claude Sonnet 5.5.

For a `StepSys` (a space `Cin` of smooth periodic cochains, the direction `v` and period `r` of one average `A = avD v r`, the index `j` of the
invariant field `X_j = ∂_v` on `Cin`), and `D`-closed `u ∈ Cin`, `StepSys.step` constructs `h ∈ Cin` with `u - A u = D h`.  Proof: the Lie derivative
`L_j = X_j + Λ_j = [D, ι_j]` commutes with `D` (as `D² = 0`) and with `A`; the partial inverse `Φ_n = Σ_{m<n} (-1)^m Λ^m q^{m+1}` satisfies
`L Φ_n u = (u - A u) - (-1)^n Λ^n q^n u`, so `L Φ_N u = u - A u` for `Λ^N = 0` (`Lop_Phi_final`); `L` is injective on mean-zero functions
(`Lop_inj`, nilpotency again); then `h = Φ_N (ι_j u)` and `D h - (u - A u)` has mean zero and is killed by `L` (`StepSys.step`).
No Fourier series, no spectral sequence.
-/


open scoped ContDiff
open MeasureTheory Set

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

omit [CompleteSpace W] in
theorem ddir_smul {f : Pt → W} (hf : ContDiff ℝ ∞ f) (c : ℝ) (w : Pt) :
    ddir w (c • f) = c • ddir w f := by
  funext p
  have hd := (hf.differentiable (by simp)).differentiableAt (x := p)
  show fderiv ℝ (c • f) p w = c • fderiv ℝ f p w
  rw [fderiv_const_smul hd]
  rfl

omit [CompleteSpace W] in
theorem Xop_smul {f : Pt → W} (hf : ContDiff ℝ ∞ f) (c : ℝ) (k : Fin 3) :
    Xop k (c • f) = c • Xop k f := by
  fin_cases k
  · exact ddir_smul hf c e1
  · funext p
    show ddir e2 (c • f) p + p.1 • ddir e3 (c • f) p = c • (ddir e2 f p + p.1 • ddir e3 f p)
    rw [ddir_smul hf c e2, ddir_smul hf c e3]
    simp only [Pi.smul_apply, smul_add, smul_comm c]
  · exact ddir_smul hf c e3

omit [CompleteSpace W] in
theorem lin_smul_fun (L : W →L[ℝ] W) (c : ℝ) (u : Pt → W) : lin L (c • u) = c • lin L u := by
  funext p; simp [lin]

omit [CompleteSpace W] in
theorem lin_comp_fun (L M : W →L[ℝ] W) (u : Pt → W) : lin L (lin M u) = lin (L * M) u := rfl

omit [CompleteSpace W] in
theorem lin_one_fun (u : Pt → W) : lin (1 : W →L[ℝ] W) u = u := rfl

omit [CompleteSpace W] in
theorem lin_zero_clm (u : Pt → W) : lin (0 : W →L[ℝ] W) u = 0 := by
  funext p; simp [lin]

omit [CompleteSpace W] in
theorem Xop_zero (k : Fin 3) : Xop k (0 : Pt → W) = 0 := by
  fin_cases k <;> (funext p; simp [Xop, ddir])

omit [CompleteSpace W] in
theorem Dop_zero (T : CartanData W) : Dop T (0 : Pt → W) = 0 := by
  unfold Dop
  funext p
  simp [Xop_zero, lin]

omit [CompleteSpace W] in
theorem Xop_sub {f g : Pt → W} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (k : Fin 3) :
    Xop k (f - g) = Xop k f - Xop k g := by
  have hg' : ContDiff ℝ ∞ ((-1 : ℝ) • g) := hg.const_smul (-1 : ℝ)
  have h := Xop_add hf hg' k
  rw [Xop_smul hg (-1) k] at h
  have e : f - g = f + (-1 : ℝ) • g := by rw [neg_one_smul, sub_eq_add_neg]
  rw [e, h, neg_one_smul, sub_eq_add_neg]

omit [CompleteSpace W] in
theorem lin_sub_fun (L : W →L[ℝ] W) (u w : Pt → W) : lin L (u - w) = lin L u - lin L w := by
  funext p; simp [lin]

section Step

variable {T : CartanData W} (S : StepSys T)

/-- The iterated Bernoulli primitive. -/
abbrev StepSys.Qn (n : ℕ) (u : Pt → W) : Pt → W := (qD S.v S.r)^[n] u

omit [CompleteSpace W] in
theorem StepSys.Qn_mem {u : Pt → W} (hu : u ∈ S.Cin) (n : ℕ) : S.Qn n u ∈ S.Cin := by
  induction n with
  | zero => exact hu
  | succ n ih =>
    rw [StepSys.Qn, Function.iterate_succ_apply']
    exact S.closedQ _ ih

omit [CompleteSpace W] in
theorem StepSys.avD_mem {u : Pt → W} (hu : u ∈ S.Cin) : avD S.v S.r u ∈ S.Cin :=
  S.outLe (S.avOut u hu)

/-- `X_j (qD w) = w - avD w`. -/
theorem StepSys.Xj_qD {w : Pt → W} (hw : w ∈ S.Cin) :
    Xop S.j (qD S.v S.r w) = w - avD S.v S.r w := by
  rw [S.xdir _ (S.closedQ w hw), ddir_qD_self S.v S.r (S.smooth w hw) (S.per w hw) S.hr]
  rfl

/-- `qD (X_j w) = w - avD w`. -/
theorem StepSys.qD_Xj {w : Pt → W} (hw : w ∈ S.Cin) :
    qD S.v S.r (Xop S.j w) = w - avD S.v S.r w := by
  rw [← S.Xq w hw S.j]
  exact S.Xj_qD hw

theorem StepSys.avD_Qn_succ {u : Pt → W} (hu : u ∈ S.Cin) (n : ℕ) :
    avD S.v S.r (S.Qn (n + 1) u) = 0 := by
  rw [StepSys.Qn, Function.iterate_succ_apply']
  exact avD_qD S.v S.r (S.smooth _ (S.Qn_mem hu n)) (S.per _ (S.Qn_mem hu n)) S.hr

theorem StepSys.Qn_lin {u : Pt → W} (hu : u ∈ S.Cin) (M : W →L[ℝ] W) (n : ℕ) :
    S.Qn n (lin M u) = lin M (S.Qn n u) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [StepSys.Qn] at ih ⊢
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact qD_lin M S.v S.r (S.smooth _ (S.Qn_mem hu n))

omit [CompleteSpace W] in
theorem StepSys.Lop_add {a b : Pt → W} (ha : a ∈ S.Cin) (hb : b ∈ S.Cin) :
    S.Lop (a + b) = S.Lop a + S.Lop b := by
  unfold StepSys.Lop
  rw [Xop_add (S.smooth a ha) (S.smooth b hb), lin_add_fun]
  abel

omit [CompleteSpace W] in
theorem StepSys.Lop_sub {a b : Pt → W} (ha : a ∈ S.Cin) (hb : b ∈ S.Cin) :
    S.Lop (a - b) = S.Lop a - S.Lop b := by
  unfold StepSys.Lop
  rw [Xop_sub (S.smooth a ha) (S.smooth b hb), lin_sub_fun]
  abel

omit [CompleteSpace W] in
theorem StepSys.Lop_smul {a : Pt → W} (ha : a ∈ S.Cin) (c : ℝ) : S.Lop (c • a) = c • S.Lop a := by
  unfold StepSys.Lop
  rw [Xop_smul (S.smooth a ha) c, lin_smul_fun, smul_add]

omit [CompleteSpace W] in
theorem StepSys.Lop_lin {a : Pt → W} (ha : a ∈ S.Cin) (M : W →L[ℝ] W) :
    S.Lop (lin M a) = lin M (Xop S.j a) + lin (T.Lam S.j * M) a := by
  unfold StepSys.Lop
  rw [Xop_lin M (S.smooth a ha), lin_comp_fun]

/-- **The partial inverse** `Φ_n = Σ_{m<n} (-1)^m Λ^m q^{m+1}` of `L_j = X_j + Λ_j` on mean-zero functions. -/
def StepSys.Phi (n : ℕ) (u : Pt → W) : Pt → W :=
  ∑ m ∈ Finset.range n, ((-1 : ℝ) ^ m) • lin ((T.Lam S.j) ^ m) (S.Qn (m + 1) u)

omit [CompleteSpace W] in
theorem StepSys.Phi_mem {u : Pt → W} (hu : u ∈ S.Cin) (n : ℕ) : S.Phi n u ∈ S.Cin := by
  unfold StepSys.Phi
  exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (S.closedLin _ (S.Qn_mem hu (m + 1)) _)

omit [CompleteSpace W] in
theorem StepSys.Phi_succ (n : ℕ) (u : Pt → W) :
    S.Phi (n + 1) u = S.Phi n u + ((-1 : ℝ) ^ n) • lin ((T.Lam S.j) ^ n) (S.Qn (n + 1) u) := by
  unfold StepSys.Phi
  rw [Finset.sum_range_succ]

/-- **`L_j Φ_n u = (u - A u) - (-1)^n Λ^n q^n u`** for `n ≥ 1`. -/
theorem StepSys.Lop_Phi {u : Pt → W} (hu : u ∈ S.Cin) (n : ℕ) (hn : 1 ≤ n) :
    S.Lop (S.Phi n u) = (u - avD S.v S.r u) - ((-1 : ℝ) ^ n) • lin ((T.Lam S.j) ^ n) (S.Qn n u) := by
  induction n, hn using Nat.le_induction with
  | base =>
    have h : S.Phi 1 u = qD S.v S.r u := by
      unfold StepSys.Phi
      simp [StepSys.Qn, lin_one_fun]
    rw [h]
    unfold StepSys.Lop
    rw [S.Xj_qD hu]
    simp [StepSys.Qn]
  | succ n hn ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hmem : ((-1 : ℝ) ^ (m + 1)) • lin ((T.Lam S.j) ^ (m + 1)) (S.Qn (m + 1 + 1) u) ∈ S.Cin :=
      Submodule.smul_mem _ _ (S.closedLin _ (S.Qn_mem hu _) _)
    have hX : Xop S.j (S.Qn (m + 1 + 1) u) = S.Qn (m + 1) u := by
      have := S.Xj_qD (S.Qn_mem hu (m + 1))
      have e : S.Qn (m + 1 + 1) u = qD S.v S.r (S.Qn (m + 1) u) := by
        simp only [StepSys.Qn]; rw [Function.iterate_succ_apply']
      rw [e, this, S.avD_Qn_succ hu m]
      simp
    rw [S.Phi_succ, S.Lop_add (S.Phi_mem hu _) hmem, ih, S.Lop_smul (S.closedLin _ (S.Qn_mem hu _) _),
      S.Lop_lin (S.Qn_mem hu _), hX]
    rw [pow_succ' (T.Lam S.j) (m + 1), pow_succ (-1 : ℝ) (m + 1)]
    module

omit [CompleteSpace W] in
theorem StepSys.nil_pow (K : ℕ) (hK : ∀ j, (T.Lam j) ^ K = 0) : (T.Lam S.j) ^ (K + 1) = 0 := by
  rw [pow_succ, hK S.j, zero_mul]

theorem StepSys.Lop_Phi_final {u : Pt → W} (hu : u ∈ S.Cin) :
    ∃ n, S.Lop (S.Phi n u) = u - avD S.v S.r u := by
  obtain ⟨K, hK⟩ := T.nilpotent
  refine ⟨K + 1, ?_⟩
  rw [S.Lop_Phi hu (K + 1) (by omega), S.nil_pow K (fun j => by simpa [CartanData.Lam] using hK j)]
  simp [lin_zero_clm]

theorem StepSys.avD_Phi {u : Pt → W} (hu : u ∈ S.Cin) (n : ℕ) : avD S.v S.r (S.Phi n u) = 0 := by
  unfold StepSys.Phi
  have hc : ∀ m, Continuous (((-1 : ℝ) ^ m) • lin ((T.Lam S.j) ^ m) (S.Qn (m + 1) u)) := fun m =>
    ((lin_contDiff _ (S.smooth _ (S.Qn_mem hu (m + 1)))).const_smul _).continuous
  rw [avD_sum_fun S.v S.r _ _ hc]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [avD_smul_fun, avD_lin _ S.v S.r (S.smooth _ (S.Qn_mem hu (m + 1))).continuous,
    S.avD_Qn_succ hu m]
  funext p
  simp [lin]

/-- **Injectivity of `L_j = X_j + Λ_j` on mean-zero functions** (by nilpotency of `Λ_j`). -/
theorem StepSys.Lop_inj {w : Pt → W} (hw : w ∈ S.Cin) (hA : avD S.v S.r w = 0) (hL : S.Lop w = 0) :
    w = 0 := by
  obtain ⟨K, hK⟩ := T.nilpotent
  have hX : Xop S.j w = lin (-(T.Lam S.j)) w := by
    unfold StepSys.Lop at hL
    funext p
    have := congrFun hL p
    simp only [Pi.add_apply, Pi.zero_apply] at this
    simp only [lin, neg_apply]
    exact eq_neg_of_add_eq_zero_left this
  have h1 : w = lin (-(T.Lam S.j)) (qD S.v S.r w) := by
    have := S.qD_Xj hw
    rw [hX, hA, sub_zero, qD_lin _ S.v S.r (S.smooth w hw)] at this
    exact this.symm
  have key : ∀ n, w = lin ((-(T.Lam S.j)) ^ n) (S.Qn n w) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      have hq : qD S.v S.r w ∈ S.Cin := S.closedQ w hw
      have e1 : S.Qn n w = S.Qn n (lin (-(T.Lam S.j)) (qD S.v S.r w)) := by rw [← h1]
      have e2 : S.Qn n (lin (-(T.Lam S.j)) (qD S.v S.r w)) =
          lin (-(T.Lam S.j)) (S.Qn (n + 1) w) := by
        rw [S.Qn_lin hq]
        simp only [StepSys.Qn]
        rw [Function.iterate_succ_apply]
      rw [e1, e2, lin_comp_fun, ← pow_succ] at ih
      exact ih
  have hKΛ : (T.Lam S.j) ^ K = 0 := hK S.j
  have hn : (-(T.Lam S.j)) ^ (K + 1) = 0 := by
    rw [pow_succ, neg_pow, hKΛ, mul_zero, zero_mul]
  have := key (K + 1)
  rw [hn, lin_zero_clm] at this
  exact this

theorem StepSys.avD_idem {u : Pt → W} (hu : u ∈ S.Cin) :
    avD S.v S.r (avD S.v S.r u) = avD S.v S.r u :=
  avD_of_inv S.v S.r (avD_inv S.v S.r (S.per u hu) S.hr)

omit [CompleteSpace W] in
theorem Dop_sub (T : CartanData W) {f g : Pt → W} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    Dop T (f - g) = Dop T f - Dop T g := by
  unfold Dop
  simp only [Xop_sub hf hg, lin_sub_fun, Finset.sum_sub_distrib]
  abel

/-- **The step homotopy**: for `u ∈ Cin` with `D u = 0` there is `h ∈ Cin` with `u - A u = D h`. -/
theorem StepSys.step {u : Pt → W} (hu : u ∈ S.Cin) (hcl : Dop T u = 0) :
    ∃ h ∈ S.Cin, u - avD S.v S.r u = Dop T h := by
  set x := lin (T.iot S.j) u with hx
  have hxm : x ∈ S.Cin := S.closedLin u hu _
  obtain ⟨n, hn⟩ := S.Lop_Phi_final hxm
  set h := S.Phi n x with hh
  have hhm : h ∈ S.Cin := S.Phi_mem hxm n
  refine ⟨h, hhm, ?_⟩
  have hAu : avD S.v S.r u ∈ S.Cin := S.avD_mem hu
  have hv1 : Dop T h ∈ S.Cin := S.Dop_mem hhm
  have hv2 : u - avD S.v S.r u ∈ S.Cin := Submodule.sub_mem _ hu hAu
  have hAxm : avD S.v S.r x ∈ S.Cin := S.avD_mem hxm
  have e1 : S.Lop u = Dop T x := by
    rw [S.Lop_eq hu, hcl, lin_zero_fun, add_zero]
  have hAD : Dop T (avD S.v S.r u) = 0 := by
    rw [S.avD_Dop hu, hcl]
    funext p; simp [avD]
  have e2 : S.Lop (avD S.v S.r u) = Dop T (lin (T.iot S.j) (avD S.v S.r u)) := by
    rw [S.Lop_eq hAu, hAD, lin_zero_fun, add_zero]
  have e3 : Dop T (lin (T.iot S.j) (avD S.v S.r u)) = avD S.v S.r (Dop T x) := by
    rw [← avD_lin _ S.v S.r (S.smooth u hu).continuous, S.avD_Dop hxm]
  have hLdiff : S.Lop (Dop T h - (u - avD S.v S.r u)) = 0 := by
    rw [S.Lop_sub hv1 hv2, S.Lop_Dop hhm, hn, S.Lop_sub hu hAu, e1, e2, e3,
      Dop_sub T (S.smooth x hxm) (S.smooth _ hAxm), S.avD_Dop hxm]
    abel
  have hAdiff : avD S.v S.r (Dop T h - (u - avD S.v S.r u)) = 0 := by
    have c1 : Continuous (Dop T h) := (S.smooth _ hv1).continuous
    have c2 : Continuous (u - avD S.v S.r u) := (S.smooth _ hv2).continuous
    rw [avD_sub S.v S.r c1 c2, ← S.avD_Dop hhm, S.avD_Phi hxm n,
      avD_sub S.v S.r (S.smooth u hu).continuous (S.smooth _ hAu).continuous, S.avD_idem hu,
      Dop_zero]
    funext p; simp
  have := S.Lop_inj (Submodule.sub_mem _ hv1 hv2) hAdiff hLdiff
  exact (sub_eq_zero.mp this).symm

end Step

end TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg
