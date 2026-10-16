module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Unfold.Orbit

@[expose] public section


/-!
# The orbit lemma for an abstract right action of the radical lattice

`UnfoldOrbit`/`UnfoldSum` prove the vanishing of the averaged non-identity part of the series for the
standard cusp, with the cosets `Γ_P \ Γ(N)`. At the cusp `h⁻¹ P h` restricted to another face the
index set is `Γ_{r}\Γ(N)` for another row `r`, but the structure used is only: a right action
`act` of the radical lattice `ℤ²`, a row function `row` with `row (act ℓ c) = (r₀, r₁, r₂ + N(r₀ℓ₀ + r₁ℓ₁))`
and injective rows. `LatAct` records this; `LatAct.orbit_integral_zero` and `LatAct.total_zero`
are the orbit lemma and the total vanishing for it.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open MeasureTheory Set
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

/-- **An abstract right action of the radical lattice `ℤ²`** (translations by `N ℓ` in the first two
columns of the third column) on an index set with bottom rows. -/
structure LatAct (N : ℕ) (Cs : Type) where
  /-- The action. -/
  act : (Fin 2 → ℤ) → Cs → Cs
  /-- The bottom row. -/
  row : Cs → Fin 3 → ℤ
  act_zero : ∀ c, act 0 c = c
  act_add : ∀ ℓ ℓ' c, act (ℓ + ℓ') c = act ℓ' (act ℓ c)
  row0 : ∀ ℓ c, row (act ℓ c) 0 = row c 0
  row1 : ∀ ℓ c, row (act ℓ c) 1 = row c 1
  row2 : ∀ ℓ c, row (act ℓ c) 2 = row c 2 + (N : ℤ) * (row c 0 * ℓ 0 + row c 1 * ℓ 1)
  row_inj : Function.Injective row

namespace LatAct

variable {N : ℕ} {Cs : Type} (L : LatAct N Cs)

/-- Two indices are in the same orbit of the radical lattice. -/
def OrbRel (c c' : Cs) : Prop := ∃ ℓ : Fin 2 → ℤ, L.act ℓ c = c'

theorem OrbRel.refl (c : Cs) : L.OrbRel c c := ⟨0, L.act_zero c⟩

theorem OrbRel.symm {c c' : Cs} (h : L.OrbRel c c') : L.OrbRel c' c := by
  obtain ⟨ℓ, rfl⟩ := h
  refine ⟨-ℓ, ?_⟩
  rw [← L.act_add, add_neg_cancel, L.act_zero]

theorem OrbRel.trans {c c' c'' : Cs} (h : L.OrbRel c c') (h' : L.OrbRel c' c'') :
    L.OrbRel c c'' := by
  obtain ⟨ℓ, rfl⟩ := h
  obtain ⟨ℓ', rfl⟩ := h'
  exact ⟨ℓ + ℓ', by rw [L.act_add]⟩

/-- The orbit setoid. -/
def orbSetoid : Setoid Cs where
  r := L.OrbRel
  iseqv := ⟨OrbRel.refl L, OrbRel.symm L, OrbRel.trans L⟩

/-- The orbit of `c₀` as a subtype. -/
abbrev Orb (c₀ : Cs) := {c : Cs // L.OrbRel c₀ c}

/-- The action of `ℓ` permutes an orbit. -/
def orbShift (c₀ : Cs) (m : Fin 2 → ℤ) : L.Orb c₀ ≃ L.Orb c₀ where
  toFun c := ⟨L.act m c.1, OrbRel.trans L c.2 ⟨m, rfl⟩⟩
  invFun c := ⟨L.act (-m) c.1, OrbRel.trans L c.2 ⟨-m, rfl⟩⟩
  left_inv c := by
    apply Subtype.ext
    show L.act (-m) (L.act m c.1) = c.1
    rw [← L.act_add, add_neg_cancel, L.act_zero]
  right_inv c := by
    apply Subtype.ext
    show L.act m (L.act (-m) c.1) = c.1
    rw [← L.act_add, neg_add_cancel, L.act_zero]

/-- Invariance of the orbit sum under the lattice translations. -/
theorem orbit_tsum_shift (Φ : Cs → (Fin 2 → ℝ) → ℂ)
    (h1 : ∀ ℓ c v, Φ (L.act ℓ c) v = Φ c ((N : ℝ) • intVec ℓ + v))
    (c₀ : Cs) (m : Fin 2 → ℤ) (u : Fin 2 → ℝ) :
    ∑' c : L.Orb c₀, Φ c.1 (u + (N : ℝ) • intVec m) = ∑' c : L.Orb c₀, Φ c.1 u := by
  rw [← (L.orbShift c₀ m).tsum_eq (fun c : L.Orb c₀ => Φ c.1 u)]
  refine tsum_congr fun c => ?_
  rw [add_comm]
  exact (h1 m c.1 u).symm

/-- The sum of a locally summably dominated family over any set of indices is continuous. -/
theorem continuous_tsum_set [NeZero N] (Φ : Cs → (Fin 2 → ℝ) → ℂ) (hc : ∀ c, Continuous (Φ c))
    (hb : ∀ R : ℝ, ∃ B : Cs → ℝ, Summable B ∧ ∀ c v, (∀ i, |v i| ≤ R) → ‖Φ c v‖ ≤ B c)
    (S : Set Cs) : Continuous fun t : Fin 2 → ℝ => ∑' c : S, Φ c.1 ((N : ℝ) • t) := by
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

variable [NeZero N]

/-- **The orbit integral vanishes** (abstract form). -/
theorem orbit_integral_zero (Φ : Cs → (Fin 2 → ℝ) → ℂ)
    (h1 : ∀ ℓ c v, Φ (L.act ℓ c) v = Φ c ((N : ℝ) • intVec ℓ + v))
    (hc : ∀ c, Continuous (Φ c))
    (hb : ∀ R : ℝ, ∃ B : Cs → ℝ, Summable B ∧ ∀ c v, (∀ i, |v i| ≤ R) → ‖Φ c v‖ ≤ B c)
    (c₀ : Cs) (hrow : L.row c₀ 0 ≠ 0 ∨ L.row c₀ 1 ≠ 0)
    (hcl : ∀ d' : Fin 2 → ℤ, d' ≠ 0 →
      L.row c₀ 0 * d' 0 + L.row c₀ 1 * d' 1 = 0 →
        ∀ w : Fin 2 → ℝ, ∫ s in (0 : ℝ)..1, Φ c₀ (w + s • ((N : ℝ) • intVec d')) = 0) :
    ∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..1,
      ∑' c : L.Orb c₀, Φ c.1 ((N : ℝ) • ![a, b]) = 0 := by
  obtain ⟨A, g, hg0, hker, hpair⟩ := exists_adapted_basis (L.row c₀ 0) (L.row c₀ 1) hrow
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
  set r0 := L.row c₀ 0 with hr0
  set r1 := L.row c₀ 1 with hr1
  have hker' : r0 * d' 0 + r1 * d' 1 = 0 := hker
  have hpair' : r0 * e' 0 + r1 * e' 1 = g := hpair
  have hNg : (N : ℤ) * g ≠ 0 := mul_ne_zero (by exact_mod_cast NeZero.ne N) hg0
  -- the stabilizing direction
  have hstab : ∀ a : ℤ, L.act (a • d') c₀ = c₀ := by
    intro a
    apply L.row_inj
    funext j
    fin_cases j
    · exact L.row0 (a • d') c₀
    · exact L.row1 (a • d') c₀
    · show L.row (L.act (a • d') c₀) 2 = L.row c₀ 2
      rw [L.row2]
      simp only [Pi.smul_apply, smul_eq_mul]
      have : r0 * (a * d' 0) + r1 * (a * d' 1) = 0 := by linear_combination a * hker'
      rw [this]; ring
  -- the parametrization of the orbit by `k ↦ c₀ · n(k e')`
  let ψ : ℤ → L.Orb c₀ := fun k => ⟨L.act (k • e') c₀, ⟨k • e', rfl⟩⟩
  have hψinj : Function.Injective ψ := by
    intro k k' hkk
    have h := congrArg (fun c : L.Orb c₀ => L.row c.1 2) hkk
    simp only [ψ] at h
    rw [L.row2, L.row2] at h
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
    show L.act ((-d' 1 * ℓ 0 + d' 0 * ℓ 1) • e') c₀ = L.act ℓ c₀
    conv_rhs => rw [hℓ, L.act_add, hstab]
  let e : ℤ ≃ L.Orb c₀ := Equiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  set D : Fin 2 → ℝ := (N : ℝ) • intVec d' with hD
  set E : Fin 2 → ℝ := (N : ℝ) • intVec e' with hE
  let gfun : (Fin 2 → ℝ) → ℂ := fun t => ∑' c : L.Orb c₀, Φ c.1 ((N : ℝ) • t)
  have hgper : PerZ2 gfun := by
    intro t m
    show ∑' c : L.Orb c₀, Φ c.1 ((N : ℝ) • (t + intVec m)) = ∑' c : L.Orb c₀, Φ c.1 ((N : ℝ) • t)
    simp only [smul_add]
    exact L.orbit_tsum_shift Φ h1 c₀ m _
  have hgcont : Continuous gfun := continuous_tsum_set Φ hc hb {c | L.OrbRel c₀ c}
  have key := sqInt_zAct A hgcont hgper
  show sqInt gfun = 0
  rw [← key]
  have hcomp : ∀ a b : ℝ, gfun (zAct (A : Matrix (Fin 2) (Fin 2) ℤ) ![a, b]) =
      ∑' k : ℤ, Φ (ψ k).1 (a • D + b • E) := by
    intro a b
    have hv : (N : ℝ) • zAct (A : Matrix (Fin 2) (Fin 2) ℤ) ![a, b] = a • D + b • E := by
      rw [zAct_apply_cols, smul_add, smul_comm (N : ℝ) a, smul_comm (N : ℝ) b]
    show ∑' c : L.Orb c₀, Φ c.1 ((N : ℝ) • zAct (A : Matrix (Fin 2) (Fin 2) ℤ) ![a, b]) = _
    rw [hv]
    exact (e.tsum_eq (fun c : L.Orb c₀ => Φ c.1 (a • D + b • E))).symm
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
        show Φ (L.act (k • e') c₀) v = _
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

/-- **The total averaged coefficient vanishes** (abstract form): the iterated integral over the
radical torus of the sum of an equivariant, locally summably bounded family vanishes, if its
stabilizing-direction integrals vanish on the orbits with `(r₀, r₁) ≠ 0` and it is zero on the
indices with `(r₀, r₁) = 0` (fibrewise summation over the orbits, `tsum_iterIntegral`). -/
theorem total_zero [Countable Cs] (Φ : Cs → (Fin 2 → ℝ) → ℂ)
    (h1 : ∀ ℓ c v, Φ (L.act ℓ c) v = Φ c ((N : ℝ) • intVec ℓ + v))
    (hc : ∀ c, Continuous (Φ c))
    (hb : ∀ R : ℝ, ∃ B : Cs → ℝ, Summable B ∧ ∀ c v, (∀ i, |v i| ≤ R) → ‖Φ c v‖ ≤ B c)
    (hcl : ∀ c₀ : Cs, (L.row c₀ 0 ≠ 0 ∨ L.row c₀ 1 ≠ 0) → ∀ d' : Fin 2 → ℤ, d' ≠ 0 →
      L.row c₀ 0 * d' 0 + L.row c₀ 1 * d' 1 = 0 →
        ∀ w : Fin 2 → ℝ, ∫ s in (0 : ℝ)..1, Φ c₀ (w + s • ((N : ℝ) • intVec d')) = 0)
    (hz : ∀ c, L.row c 0 = 0 → L.row c 1 = 0 → ∀ v, Φ c v = 0) :
    ∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..1, ∑' c, Φ c ((N : ℝ) • ![a, b]) = 0 := by
  classical
  obtain ⟨B, hBs, hBb⟩ := hb (N : ℝ)
  let q : Cs → Quotient L.orbSetoid := fun c => Quotient.mk L.orbSetoid c
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
  let G : Quotient L.orbSetoid → ℝ → ℝ → ℂ := fun o a b =>
    ∑' c : q ⁻¹' {o}, Φ c.1 ((N : ℝ) • ![a, b])
  have hHB : HasSum (fun o : Quotient L.orbSetoid => ∑' c : q ⁻¹' {o}, B c) (∑' c, B c) :=
    hBs.hasSum.tsum_fiberwise q
  have hfib : ∀ a b : ℝ, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 →
      HasSum (fun o => G o a b) (∑' c, Φ c ((N : ℝ) • ![a, b])) := by
    intro a b ha hb
    have hs : Summable fun c => Φ c ((N : ℝ) • ![a, b]) :=
      Summable.of_norm_bounded hBs (fun c => hBb c _ (hvbd a b ha hb))
    exact hs.hasSum.tsum_fiberwise q
  have hGc : ∀ o, Continuous (Function.uncurry (G o)) := by
    intro o
    have h1 := continuous_tsum_set (N := N) Φ hc hb (q ⁻¹' {o})
    exact h1.comp (show Continuous fun p : ℝ × ℝ => (![p.1, p.2] : Fin 2 → ℝ) by fun_prop)
  have hGb : ∀ o a b, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 →
      ‖G o a b‖ ≤ ∑' c : q ⁻¹' {o}, B c := by
    intro o a b ha hb
    exact tsum_of_norm_bounded ((hBs.subtype (q ⁻¹' {o})).hasSum)
      (fun c => hBb c.1 _ (hvbd a b ha hb))
  have hG0 : ∀ o, ∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..1, G o a b = 0 := by
    intro o
    induction o using Quotient.inductionOn with | _ c₀ => ?_
    by_cases hrow : L.row c₀ 0 ≠ 0 ∨ L.row c₀ 1 ≠ 0
    · have hset : q ⁻¹' {Quotient.mk L.orbSetoid c₀} = {c | L.OrbRel c₀ c} := by
        ext c
        show Quotient.mk L.orbSetoid c = Quotient.mk L.orbSetoid c₀ ↔ L.OrbRel c₀ c
        rw [Quotient.eq]
        exact ⟨fun h => OrbRel.symm L h, fun h => OrbRel.symm L h⟩
      have := L.orbit_integral_zero Φ h1 hc hb c₀ hrow (hcl c₀ hrow)
      rw [← this]
      refine intervalIntegral.integral_congr fun a _ => ?_
      refine intervalIntegral.integral_congr fun b _ => ?_
      exact tsum_congr_set_coe (fun c => Φ c ((N : ℝ) • ![a, b])) hset
    · rw [not_or, not_not, not_not] at hrow
      have hcid : ∀ c : q ⁻¹' {Quotient.mk L.orbSetoid c₀}, L.row c.1 0 = 0 ∧ L.row c.1 1 = 0 := by
        rintro ⟨c, hc'⟩
        have hc'' : L.OrbRel c c₀ := by
          have : Quotient.mk L.orbSetoid c = Quotient.mk L.orbSetoid c₀ := hc'
          rw [Quotient.eq] at this
          exact this
        obtain ⟨ℓ, hℓ⟩ := hc''
        have e0 := L.row0 ℓ c
        have e1 := L.row1 ℓ c
        rw [hℓ] at e0 e1
        exact ⟨e0.symm.trans hrow.1, e1.symm.trans hrow.2⟩
      have hz' : ∀ a b, G (Quotient.mk L.orbSetoid c₀) a b = 0 := by
        intro a b
        show ∑' c : q ⁻¹' {Quotient.mk L.orbSetoid c₀}, Φ c.1 ((N : ℝ) • ![a, b]) = 0
        have : ∀ c : q ⁻¹' {Quotient.mk L.orbSetoid c₀}, Φ c.1 ((N : ℝ) • ![a, b]) = 0 :=
          fun c => hz c.1 (hcid c).1 (hcid c).2 _
        exact (tsum_congr this).trans tsum_zero
      simp [hz']
  have hex := tsum_iterIntegral G hGc (fun o => ∑' c : q ⁻¹' {o}, B c) hHB.summable hGb
  calc ∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..1, ∑' c, Φ c ((N : ℝ) • ![a, b])
      = ∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..1, ∑' o, G o a b := by
        refine intervalIntegral.integral_congr fun a ha => ?_
        refine intervalIntegral.integral_congr fun b hb => ?_
        rw [uIcc_of_le zero_le_one] at ha hb
        exact (hfib a b ha hb).tsum_eq.symm
    _ = ∑' o, ∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..1, G o a b := hex.symm
    _ = 0 := by simp [hG0]

end LatAct

end TernaryPeriodPolynomials.Argument.EisensteinClass
