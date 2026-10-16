module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Unfold.Term
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Periodic
public import TernaryPeriodPolynomials.EisensteinSeries.Class.IterTsum
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Equivariance
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.GammaNExt

@[expose] public section


/-!
# Orbits of the radical lattice on `Γ_P \ Γ(N)` and the abstract orbit lemma

(unfolding; "the
integrated radical quotient is compact, so Fubini applies").

The radical lattice `Nℤ²` acts on `Γ_P \ Γ(N)` by right multiplication (`nG`, `OrbRel`, `orbSetoid`). For
a coset with `r' ≠ 0` the orbit is parametrized bijectively by `ℤ` via `k ↦ c₀ n(k e')` for a basis
`(d', e')` of `ℤ²` adapted to `r'` (`exists_adapted_basis`: `d'` in the kernel, `r'·e' = g ≠ 0`).
`orbit_integral_zero`: if a family `Φ c v` is equivariant (`Φ (c n(ℓ)) v = Φ c (Nℓ + v)`), continuous, locally
summably bounded and its integral over one period of the stabilizing direction vanishes, then the
iterated integral over `[0,1]²` of the orbit sum `Σ'_{c ∈ orbit} Φ c (N (a, b))` is zero (change of
variables by the `SL₂(ℤ)` matrix with columns `d', e'`, `sqInt_zAct`, and exchange of the sum with the
integral, `tsum_iterIntegral`).

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open MeasureTheory Set
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3S4c

/-- `SL₃(ℤ)` is countable (it injects into `Fin 3 → Fin 3 → ℤ`). -/
instance instCountableSL3ZEisensteinClass : Countable SL(3, ℤ) := by
  have : Function.Injective (fun g : SL(3, ℤ) =>
      (fun i j => (g : Matrix (Fin 3) (Fin 3) ℤ) i j : Fin 3 → Fin 3 → ℤ)) := by
    intro g h hgh
    exact Subtype.ext (by ext i j; exact congrFun (congrFun hgh i) j)
  exact this.countable

variable (N : ℕ)

/-- The radical element `n(ℓ) = [[1, 0, Nℓ₀], [0, 1, Nℓ₁], [0, 0, 1]]` of `Γ(N)`. -/
def nG (ℓ : Fin 2 → ℤ) : ↥(gammaN N) :=
  ⟨radElt N (Multiplicative.ofAdd (ℓ 0, ℓ 1)), radElt_mem_gammaN N _⟩

theorem nG_zero : nG N 0 = 1 := by
  apply Subtype.ext
  show radElt N (Multiplicative.ofAdd ((0 : Fin 2 → ℤ) 0, (0 : Fin 2 → ℤ) 1)) = 1
  exact radElt_one N

theorem nG_add (ℓ ℓ' : Fin 2 → ℤ) : nG N (ℓ + ℓ') = nG N ℓ * nG N ℓ' := by
  apply Subtype.ext
  show radElt N (Multiplicative.ofAdd ((ℓ + ℓ') 0, (ℓ + ℓ') 1)) =
    radElt N (Multiplicative.ofAdd (ℓ 0, ℓ 1)) * radElt N (Multiplicative.ofAdd (ℓ' 0, ℓ' 1))
  rw [← radElt_mul]
  rfl

theorem realMat_nG (ℓ : Fin 2 → ℤ) : realMat (nG N ℓ).1 = nmat ((N : ℝ) • intVec ℓ) := by
  show realMat (radElt N (Multiplicative.ofAdd (ℓ 0, ℓ 1))) = _
  rw [realMat_radElt]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [parabolicMatrix, nmat, transMat, intVec]

/-- The coset space `Γ_P \ Γ(N)`. -/
abbrev Cs := PlaneCoset (gammaN N)

theorem cosetMulR_one (c : Cs N) : cosetMulR (gammaN N) 1 c = c := by
  induction c using Quotient.inductionOn with | _ a => ?_
  simp [cosetMulR_mk]

theorem cosetMulR_mul (δ δ' : ↥(gammaN N)) (c : Cs N) :
    cosetMulR (gammaN N) (δ * δ') c = cosetMulR (gammaN N) δ' (cosetMulR (gammaN N) δ c) := by
  induction c using Quotient.inductionOn with | _ a => ?_
  simp [cosetMulR_mk, mul_assoc]

theorem cosetRow_mulR_nG (ℓ : Fin 2 → ℤ) (c : Cs N) :
    cosetRow (gammaN N) (cosetMulR (gammaN N) (nG N ℓ) c) 0 = cosetRow (gammaN N) c 0 ∧
    cosetRow (gammaN N) (cosetMulR (gammaN N) (nG N ℓ) c) 1 = cosetRow (gammaN N) c 1 ∧
    cosetRow (gammaN N) (cosetMulR (gammaN N) (nG N ℓ) c) 2 = cosetRow (gammaN N) c 2 +
      (N : ℤ) * (cosetRow (gammaN N) c 0 * ℓ 0 + cosetRow (gammaN N) c 1 * ℓ 1) := by
  induction c using Quotient.inductionOn with | _ a => ?_
  rw [cosetMulR_mk]
  have e : ∀ j, cosetRow (gammaN N) (Quotient.mk _ (a * nG N ℓ)) j =
      ((a.1 * radElt N (Multiplicative.ofAdd (ℓ 0, ℓ 1)) : SL(3, ℤ)) :
        Matrix (Fin 3) (Fin 3) ℤ) 2 j := fun j => rfl
  have e' : ∀ j, cosetRow (gammaN N) (Quotient.mk _ a) j =
      (a.1 : Matrix (Fin 3) (Fin 3) ℤ) 2 j := fun j => rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [e, e', Matrix.SpecialLinearGroup.coe_mul]
    simp [Matrix.mul_apply, Fin.sum_univ_three, radElt]
  · rw [e, e', Matrix.SpecialLinearGroup.coe_mul]
    simp [Matrix.mul_apply, Fin.sum_univ_three, radElt]
  · rw [e, e', e', e', Matrix.SpecialLinearGroup.coe_mul]
    simp [Matrix.mul_apply, Fin.sum_univ_three, radElt]
    ring

/-- Two cosets are in the same orbit of the radical lattice acting on the right. -/
def OrbRel (c c' : Cs N) : Prop := ∃ ℓ : Fin 2 → ℤ, cosetMulR (gammaN N) (nG N ℓ) c = c'

theorem OrbRel.refl (c : Cs N) : OrbRel N c c := ⟨0, by rw [nG_zero, cosetMulR_one]⟩

theorem OrbRel.symm {c c' : Cs N} (h : OrbRel N c c') : OrbRel N c' c := by
  obtain ⟨ℓ, rfl⟩ := h
  refine ⟨-ℓ, ?_⟩
  rw [← cosetMulR_mul, ← nG_add, add_neg_cancel, nG_zero, cosetMulR_one]

theorem OrbRel.trans {c c' c'' : Cs N} (h : OrbRel N c c') (h' : OrbRel N c' c'') :
    OrbRel N c c'' := by
  obtain ⟨ℓ, rfl⟩ := h
  obtain ⟨ℓ', rfl⟩ := h'
  exact ⟨ℓ + ℓ', by rw [nG_add, cosetMulR_mul]⟩

/-- The orbit setoid of the radical lattice acting on `Γ_P \ Γ(N)` by right multiplication. -/
def orbSetoid : Setoid (Cs N) where
  r := OrbRel N
  iseqv := ⟨OrbRel.refl N, OrbRel.symm N, OrbRel.trans N⟩

/-- A basis of `ℤ²` adapted to the first two bottom entries `(r₀, r₁) ≠ 0`: the first column is in
the kernel of `(r₀, r₁)`, the second has pairing `g ≠ 0`. -/
theorem exists_adapted_basis (r0 r1 : ℤ) (h : r0 ≠ 0 ∨ r1 ≠ 0) :
    ∃ (A : SL(2, ℤ)) (g : ℤ), g ≠ 0 ∧
      r0 * (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + r1 * (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 ∧
      r0 * (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + r1 * (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = g := by
  set g : ℤ := (Int.gcd r0 r1 : ℤ) with hg
  have hg0 : g ≠ 0 := by
    intro h0
    have : Int.gcd r0 r1 = 0 := Int.ofNat_eq_zero.mp h0
    rw [Int.gcd_eq_zero_iff] at this
    rcases h with h | h
    · exact h this.1
    · exact h this.2
  obtain ⟨p0, hp0⟩ : g ∣ r0 := Int.gcd_dvd_left r0 r1
  obtain ⟨p1, hp1⟩ : g ∣ r1 := Int.gcd_dvd_right r0 r1
  have hcop : IsCoprime p0 p1 := by
    have h1 : Int.gcd (g * p0) (g * p1) = g.natAbs * Int.gcd p0 p1 := Int.gcd_mul_left g p0 p1
    rw [← hp0, ← hp1] at h1
    have h2 : (Int.gcd r0 r1 : ℕ) = g.natAbs := by simp [hg]
    rw [h2] at h1
    have hpos : 0 < g.natAbs := Int.natAbs_pos.mpr hg0
    have : Int.gcd p0 p1 = 1 := by
      have h3 : g.natAbs * Int.gcd p0 p1 = g.natAbs * 1 := by rw [mul_one]; exact h1.symm
      exact Nat.eq_of_mul_eq_mul_left hpos h3
    exact Int.isCoprime_iff_gcd_eq_one.mpr this
  obtain ⟨u, v, huv⟩ := hcop
  -- A = [[-p1, -u], [p0, -v]], det = p1 v + u p0 = 1
  let A : SL(2, ℤ) := ⟨!![-p1, -u; p0, -v], by
    rw [Matrix.det_fin_two_of]; linarith⟩
  refine ⟨A, -g, neg_ne_zero.mpr hg0, ?_, ?_⟩
  · simp [A, hp0, hp1]; ring
  · simp [A, hp0, hp1]; linear_combination (-g) * huv

/-! ### The abstract orbit lemma -/

section Orbit

/-- The orbit of `c₀` as a subtype. -/
abbrev Orb (c₀ : Cs N) := {c : Cs N // OrbRel N c₀ c}

/-- The action of `n(m)` permutes an orbit. -/
def orbShift (c₀ : Cs N) (m : Fin 2 → ℤ) : Orb N c₀ ≃ Orb N c₀ where
  toFun c := ⟨cosetMulR (gammaN N) (nG N m) c.1, OrbRel.trans N c.2 ⟨m, rfl⟩⟩
  invFun c := ⟨cosetMulR (gammaN N) (nG N (-m)) c.1, OrbRel.trans N c.2 ⟨-m, rfl⟩⟩
  left_inv c := by
    apply Subtype.ext
    show cosetMulR _ (nG N (-m)) (cosetMulR _ (nG N m) c.1) = c.1
    rw [← cosetMulR_mul, ← nG_add, add_neg_cancel, nG_zero, cosetMulR_one]
  right_inv c := by
    apply Subtype.ext
    show cosetMulR _ (nG N m) (cosetMulR _ (nG N (-m)) c.1) = c.1
    rw [← cosetMulR_mul, ← nG_add, neg_add_cancel, nG_zero, cosetMulR_one]

variable {N}

/-- Invariance of the orbit sum under the lattice translations. -/
theorem orbit_tsum_shift (Φ : Cs N → (Fin 2 → ℝ) → ℂ)
    (h1 : ∀ ℓ c v, Φ (cosetMulR (gammaN N) (nG N ℓ) c) v = Φ c ((N : ℝ) • intVec ℓ + v))
    (c₀ : Cs N) (m : Fin 2 → ℤ) (u : Fin 2 → ℝ) :
    ∑' c : Orb N c₀, Φ c.1 (u + (N : ℝ) • intVec m) = ∑' c : Orb N c₀, Φ c.1 u := by
  rw [← (orbShift N c₀ m).tsum_eq (fun c : Orb N c₀ => Φ c.1 u)]
  refine tsum_congr fun c => ?_
  rw [add_comm]
  exact (h1 m c.1 u).symm

/-- A function continuous on every box is continuous. -/
theorem continuous_of_boxes {g : (Fin 2 → ℝ) → ℂ}
    (h : ∀ R : ℝ, ContinuousOn g {t : Fin 2 → ℝ | ∀ i, |t i| < R}) : Continuous g := by
  rw [continuous_iff_continuousAt]
  intro t
  set R : ℝ := |t 0| + |t 1| + 1 with hR
  have hopen : IsOpen {t : Fin 2 → ℝ | ∀ i, |t i| < R} := by
    have : {t : Fin 2 → ℝ | ∀ i, |t i| < R} = ⋂ i, {t | |t i| < R} := by
      ext t; simp
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (by fun_prop) continuous_const
  have ht : t ∈ {t : Fin 2 → ℝ | ∀ i, |t i| < R} := by
    intro i
    fin_cases i <;> simp [hR] <;> linarith [abs_nonneg (t 0), abs_nonneg (t 1)]
  exact (h R).continuousAt (hopen.mem_nhds ht)

/-- The sum of a locally summably dominated family over any set of cosets is continuous. -/
theorem continuous_tsum_set [NeZero N] (Φ : Cs N → (Fin 2 → ℝ) → ℂ) (hc : ∀ c, Continuous (Φ c))
    (hb : ∀ R : ℝ, ∃ B : Cs N → ℝ, Summable B ∧ ∀ c v, (∀ i, |v i| ≤ R) → ‖Φ c v‖ ≤ B c)
    (S : Set (Cs N)) : Continuous fun t : Fin 2 → ℝ => ∑' c : S, Φ c.1 ((N : ℝ) • t) := by
  apply continuous_of_boxes
  intro R
  obtain ⟨B, hBs, hBb⟩ := hb ((N : ℝ) * R)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  refine continuousOn_tsum (u := fun c : S => B c.1) (fun c => ?_)
    (hBs.subtype _) (fun c t ht => ?_)
  · exact ((hc c.1).comp (continuous_id.const_smul (N : ℝ))).continuousOn
  · refine hBb c.1 _ fun i => ?_
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, Nat.abs_cast]
    exact mul_le_mul_of_nonneg_left (le_of_lt (ht i)) hNpos.le

/-- The kernel-direction vector `D` of an adapted basis, as a real vector. -/
theorem zAct_apply_cols (A : Matrix (Fin 2) (Fin 2) ℤ) (a b : ℝ) :
    zAct A ![a, b] = a • intVec (fun i => A i 0) + b • intVec (fun i => A i 1) := by
  funext i
  fin_cases i <;> simp [zAct, intVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

variable [NeZero N]

/-- **The orbit integral vanishes** (abstract form). -/
theorem orbit_integral_zero (Φ : Cs N → (Fin 2 → ℝ) → ℂ)
    (h1 : ∀ ℓ c v, Φ (cosetMulR (gammaN N) (nG N ℓ) c) v = Φ c ((N : ℝ) • intVec ℓ + v))
    (hc : ∀ c, Continuous (Φ c))
    (hb : ∀ R : ℝ, ∃ B : Cs N → ℝ, Summable B ∧ ∀ c v, (∀ i, |v i| ≤ R) → ‖Φ c v‖ ≤ B c)
    (c₀ : Cs N) (hrow : cosetRow (gammaN N) c₀ 0 ≠ 0 ∨ cosetRow (gammaN N) c₀ 1 ≠ 0)
    (hcl : ∀ d' : Fin 2 → ℤ, d' ≠ 0 →
      cosetRow (gammaN N) c₀ 0 * d' 0 + cosetRow (gammaN N) c₀ 1 * d' 1 = 0 →
        ∀ w : Fin 2 → ℝ, ∫ s in (0 : ℝ)..1, Φ c₀ (w + s • ((N : ℝ) • intVec d')) = 0) :
    ∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..1,
      ∑' c : Orb N c₀, Φ c.1 ((N : ℝ) • ![a, b]) = 0 := by
  obtain ⟨A, g, hg0, hker, hpair⟩ := exists_adapted_basis (cosetRow (gammaN N) c₀ 0)
    (cosetRow (gammaN N) c₀ 1) hrow
  set d' : Fin 2 → ℤ := fun i => (A : Matrix (Fin 2) (Fin 2) ℤ) i 0 with hd'
  set e' : Fin 2 → ℤ := fun i => (A : Matrix (Fin 2) (Fin 2) ℤ) i 1 with he'
  have hdet : d' 0 * e' 1 - e' 0 * d' 1 = 1 := by
    have := A.2
    rw [Matrix.det_fin_two] at this
    simp only [hd', he']
    linarith
  have hd'0 : d' ≠ 0 := by
    intro h
    have h0 : d' 0 = 0 := congrFun h 0
    have h1' : d' 1 = 0 := congrFun h 1
    rw [h0, h1'] at hdet
    simp at hdet
  set r0 := cosetRow (gammaN N) c₀ 0 with hr0
  set r1 := cosetRow (gammaN N) c₀ 1 with hr1
  have hker' : r0 * d' 0 + r1 * d' 1 = 0 := hker
  have hpair' : r0 * e' 0 + r1 * e' 1 = g := hpair
  have hNg : (N : ℤ) * g ≠ 0 := mul_ne_zero (by exact_mod_cast NeZero.ne N) hg0
  -- the stabilizing direction
  have hstab : ∀ a : ℤ, cosetMulR (gammaN N) (nG N (a • d')) c₀ = c₀ := by
    intro a
    apply cosetRow_injective (gammaN N)
    obtain ⟨e0, e1, e2⟩ := cosetRow_mulR_nG N (a • d') c₀
    funext j
    fin_cases j
    · exact e0
    · exact e1
    · show cosetRow (gammaN N) (cosetMulR (gammaN N) (nG N (a • d')) c₀) 2 = cosetRow (gammaN N) c₀ 2
      rw [e2]
      simp only [Pi.smul_apply, smul_eq_mul]
      have : r0 * (a * d' 0) + r1 * (a * d' 1) = 0 := by linear_combination a * hker'
      rw [this]; ring
  -- the parametrization of the orbit by `k ↦ c₀ · n(k e')`
  let ψ : ℤ → Orb N c₀ := fun k => ⟨cosetMulR (gammaN N) (nG N (k • e')) c₀, ⟨k • e', rfl⟩⟩
  have hψinj : Function.Injective ψ := by
    intro k k' hkk
    have h := congrArg (fun c : Orb N c₀ => cosetRow (gammaN N) c.1 2) hkk
    simp only [ψ] at h
    rw [(cosetRow_mulR_nG N (k • e') c₀).2.2, (cosetRow_mulR_nG N (k' • e') c₀).2.2] at h
    simp only [Pi.smul_apply, smul_eq_mul] at h
    rw [← hr0, ← hr1] at h
    have : (N : ℤ) * g * k = (N : ℤ) * g * k' := by
      linear_combination h - ((N : ℤ) * k - (N : ℤ) * k') * hpair'
    exact mul_left_cancel₀ hNg this
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨c, ℓ, rfl⟩
    refine ⟨-d' 1 * ℓ 0 + d' 0 * ℓ 1, Subtype.ext ?_⟩
    have hℓ : ℓ = (e' 1 * ℓ 0 - e' 0 * ℓ 1) • d' + (-d' 1 * ℓ 0 + d' 0 * ℓ 1) • e' := by
      funext i
      fin_cases i
      · simp only [Fin.zero_eta, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        linear_combination (-(ℓ 0)) * hdet
      · simp only [Fin.mk_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        linear_combination (-(ℓ 1)) * hdet
    show cosetMulR (gammaN N) (nG N ((-d' 1 * ℓ 0 + d' 0 * ℓ 1) • e')) c₀ =
      cosetMulR (gammaN N) (nG N ℓ) c₀
    conv_rhs => rw [hℓ, nG_add, cosetMulR_mul, hstab]
  let e : ℤ ≃ Orb N c₀ := Equiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  set D : Fin 2 → ℝ := (N : ℝ) • intVec d' with hD
  set E : Fin 2 → ℝ := (N : ℝ) • intVec e' with hE
  let gfun : (Fin 2 → ℝ) → ℂ := fun t => ∑' c : Orb N c₀, Φ c.1 ((N : ℝ) • t)
  have hgper : PerZ2 gfun := by
    intro t m
    show ∑' c : Orb N c₀, Φ c.1 ((N : ℝ) • (t + intVec m)) = ∑' c : Orb N c₀, Φ c.1 ((N : ℝ) • t)
    simp only [smul_add]
    exact orbit_tsum_shift Φ h1 c₀ m _
  have hgcont : Continuous gfun := continuous_tsum_set Φ hc hb {c | OrbRel N c₀ c}
  have key := sqInt_zAct A hgcont hgper
  show sqInt gfun = 0
  rw [← key]
  have hcomp : ∀ a b : ℝ, gfun (zAct (A : Matrix (Fin 2) (Fin 2) ℤ) ![a, b]) =
      ∑' k : ℤ, Φ (ψ k).1 (a • D + b • E) := by
    intro a b
    have hv : (N : ℝ) • zAct (A : Matrix (Fin 2) (Fin 2) ℤ) ![a, b] = a • D + b • E := by
      rw [zAct_apply_cols, smul_add, smul_comm (N : ℝ) a, smul_comm (N : ℝ) b]
    show ∑' c : Orb N c₀, Φ c.1 ((N : ℝ) • zAct (A : Matrix (Fin 2) (Fin 2) ℤ) ![a, b]) = _
    rw [hv]
    exact (e.tsum_eq (fun c : Orb N c₀ => Φ c.1 (a • D + b • E))).symm
  have hS : sqInt (fun v => gfun (zAct (A : Matrix (Fin 2) (Fin 2) ℤ) v)) =
      ∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..1, ∑' k : ℤ, Φ (ψ k).1 (a • D + b • E) := by
    unfold sqInt
    simp only [hcomp]
  rw [hS]
  set R0 : ℝ := |D 0| + |D 1| + |E 0| + |E 1| with hR0
  obtain ⟨B, hBs, hBb⟩ := hb R0
  have hFc : ∀ k : ℤ, Continuous (Function.uncurry fun a b : ℝ => Φ (ψ k).1 (a • D + b • E)) := by
    intro k
    exact (hc _).comp ((continuous_fst.smul continuous_const).add (continuous_snd.smul continuous_const))
  have hBsum : Summable fun k : ℤ => B (ψ k).1 :=
    hBs.comp_injective (fun k k' h => hψinj (Subtype.ext h))
  rw [← tsum_iterIntegral (fun k a b => Φ (ψ k).1 (a • D + b • E)) hFc (fun k => B (ψ k).1) hBsum
    (fun k a b ha hb' => hBb _ _ (fun i => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have h1' : |a * D i| ≤ |D i| := by
        rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (by rw [abs_of_nonneg ha.1]; exact ha.2)
      have h2' : |b * E i| ≤ |E i| := by
        rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (by rw [abs_of_nonneg hb'.1]; exact hb'.2)
      refine (abs_add_le _ _).trans ?_
      have hDi : |D i| ≤ |D 0| + |D 1| := by
        fin_cases i
        · simp [abs_nonneg]
        · simp [abs_nonneg]
      have hEi : |E i| ≤ |E 0| + |E 1| := by
        fin_cases i
        · simp [abs_nonneg]
        · simp [abs_nonneg]
      rw [hR0]; linarith))]
  have hterm : ∀ k : ℤ, ∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..1, Φ (ψ k).1 (a • D + b • E) = 0 := by
    intro k
    rw [integral_swap_unit _ (hFc k)]
    have hin : ∀ b : ℝ, ∫ a in (0 : ℝ)..1, Φ (ψ k).1 (a • D + b • E) = 0 := by
      intro b
      have hψk : ∀ v, Φ (ψ k).1 v = Φ c₀ ((k : ℝ) • E + v) := by
        intro v
        show Φ (cosetMulR (gammaN N) (nG N (k • e')) c₀) v = _
        rw [h1]
        congr 1
        funext i
        simp [hE, intVec]
        ring
      have := hcl d' hd'0 hker' (((k : ℝ) + b) • E)
      rw [← this]
      refine intervalIntegral.integral_congr fun a _ => ?_
      simp only [hψk]
      congr 1
      funext i
      simp only [hD, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    simp [hin]
  simp [hterm]

end Orbit

end TernaryPeriodPolynomials.Argument.EisensteinClass
