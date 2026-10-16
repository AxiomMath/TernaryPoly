module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.N2Algebra
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.RelCupInvariance

@[expose] public section


/-!
# Normal-form transfer, algebraic core

Formalized by Claude Sonnet 5.5.

On a group `E` with representations `ρ`, `ρ'` on `V`, `W` and an invariant pairing `e : V → W → ℚ`, let `zb = zx + dκ`, `zb' = zy + dκ'` with `dd3T gb = cup22 zb zb'`.
Then `γ = gb - zb ∪ κ' - κ ∪ zy` satisfies `dd3T γ = cup22 zx zy` (`nfGamma0_dd3T`), it can be normalised on a radical `inl : ℤ² → E` (`nfGamma_exists`), and for every
group `H` with `ι : H → E` and a primitive `w̄` of `zb ∘ ι` the flag cochain `w̄ ∪ zb' ∘ ι - gb ∘ ι` of `H` differs by a coboundary `dd2T ψ` from `(w̄ - κ ∘ ι) ∪ zy ∘ ι - γ ∘ ι`
(`nfTheta_eq`), a cocycle (`nfTheta_dd3T`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

section NF

variable {E : Type} [Group E] {V W : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
  (ρ : Representation ℚ E V) (ρ' : Representation ℚ E W) (e : V →ₗ[ℚ] W →ₗ[ℚ] ℚ)

theorem dd3T_sub (c c' : E → E → E → ℚ) : dd3T (c - c') = dd3T c - dd3T c' := by
  funext g1 g2 g3 g4
  simp only [dd3T, Pi.sub_apply]
  ring

theorem dd3T_dd2T (ε : E → E → ℚ) : dd3T (dd2T ε) = 0 := by
  funext g1 g2 g3 g4
  simp only [dd3T, dd2T, Pi.zero_apply, mul_assoc]
  ring

theorem cup22_sub_left (α α' : E → E → V) (β : E → E → W) :
    cup22 ρ' e (α - α') β = cup22 ρ' e α β - cup22 ρ' e α' β := by
  funext g1 g2 g3 g4
  simp [cup22, map_sub, LinearMap.sub_apply]

/-- The combination `gb - zb ∪ κ' - κ ∪ zy`. -/
def nfGamma0 (zb : E → E → V) (κ : E → V) (κ' : E → W) (zy : E → E → W) (gb : E → E → E → ℚ) : E → E → E → ℚ :=
  gb - cup21 ρ' e zb κ' - cup12 ρ' e κ zy

variable {ρ ρ' e}

/-- **`dd3T` of the normal-form primitive** is `cup22 zx zy`. -/
theorem nfGamma0_dd3T (he : ∀ (g : E) (v : V) (w : W), e (ρ g v) (ρ' g w) = e v w)
    (zx zb : E → E → V) (zy zb' : E → E → W) (κ : E → V) (κ' : E → W) (gb : E → E → E → ℚ)
    (hzb : dd2 ρ zb = 0) (hzy : dd2 ρ' zy = 0) (h1 : zb = zx + dd1 ρ κ) (h2 : zb' = zy + dd1 ρ' κ')
    (hγ : dd3T gb = cup22 ρ' e zb zb') :
    dd3T (nfGamma0 ρ' e zb κ κ' zy gb) = cup22 ρ' e zx zy := by
  unfold nfGamma0
  rw [dd3T_sub, dd3T_sub, hγ, leibniz21 he zb hzb κ', leibniz12 he κ zy, hzy, cup13_zero, h2, cup22_add_right]
  have h3 : cup22 ρ' e zb zy = cup22 ρ' e zx zy + cup22 ρ' e (dd1 ρ κ) zy := by
    rw [h1, cup22_add_left]
  funext g1 g2 g3 g4
  have h4 := congrFun (congrFun (congrFun (congrFun h3 g1) g2) g3) g4
  simp only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply] at h4 ⊢
  linarith

section Pull

variable {H : Type} [Group H] (ι : H →* E) {ρH : Representation ℚ H V} {ρH' : Representation ℚ H W}

theorem pull_inv (hρ : ∀ (s : H) (v : V), ρ (ι s) v = ρH s v) (hρ' : ∀ (s : H) (w : W), ρ' (ι s) w = ρH' s w)
    (he : ∀ (g : E) (v : V) (w : W), e (ρ g v) (ρ' g w) = e v w) (g : H) (v : V) (w : W) :
    e (ρH g v) (ρH' g w) = e v w := by
  rw [← hρ, ← hρ']
  exact he _ v w

theorem dd1_pull (hρ : ∀ (s : H) (v : V), ρ (ι s) v = ρH s v) (u : E → V) :
    dd1 ρH (fun s => u (ι s)) = fun s t => dd1 ρ u (ι s) (ι t) := by
  funext s t
  simp only [dd1, map_mul, hρ]

theorem dd2T_pull (ε : E → E → ℚ) :
    dd2T (fun s t : H => ε (ι s) (ι t)) = fun a b c => dd2T ε (ι a) (ι b) (ι c) := by
  funext a b c
  simp only [dd2T, map_mul]

/-- **The flag cochain of `H` changes by a coboundary under the normal-form transfer.** -/
theorem nfTheta_eq (hρ : ∀ (s : H) (v : V), ρ (ι s) v = ρH s v) (hρ' : ∀ (s : H) (w : W), ρ' (ι s) w = ρH' s w)
    (he : ∀ (g : E) (v : V) (w : W), e (ρ g v) (ρ' g w) = e v w)
    (zb : E → E → V) (zy zb' : E → E → W) (κ : E → V) (κ' : E → W) (gb : E → E → E → ℚ) (ε : E → E → ℚ)
    (h2 : zb' = zy + dd1 ρ' κ')
    (wb : H → V) (hw : dd1 ρH wb = fun s t => zb (ι s) (ι t)) :
    (fun a b c : H => cup12 ρH' e wb (fun s t => zb' (ι s) (ι t)) a b c - gb (ι a) (ι b) (ι c)) =
      (fun a b c : H => cup12 ρH' e (wb - fun s => κ (ι s)) (fun s t => zy (ι s) (ι t)) a b c -
        (nfGamma0 ρ' e zb κ κ' zy gb - dd2T ε) (ι a) (ι b) (ι c)) +
      dd2T (-(cup11 ρH' e wb (fun s => κ' (ι s))) - fun s t : H => ε (ι s) (ι t)) := by
  have heH := pull_inv ι hρ hρ' he
  have hl := leibniz11 heH wb (fun s => κ' (ι s))
  rw [hw] at hl
  have hd : dd1 ρH' (fun s => κ' (ι s)) = fun s t => dd1 ρ' κ' (ι s) (ι t) := by
    funext s t
    simp only [dd1, map_mul, hρ']
  rw [hd] at hl
  have f3 : ∀ (a b : H) (w : W), ρ' (ι a * ι b) w = ρH' (a * b) w := by
    intro a b w
    rw [← ι.map_mul]
    exact hρ' _ _
  funext a b c
  have hl' := congrFun (congrFun (congrFun hl a) b) c
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, nfGamma0, dd2T, cup12, cup21, cup11, h2, dd1, ι.map_mul, f3, hρ',
    map_add, map_sub, LinearMap.sub_apply] at hl' ⊢
  linear_combination hl'

theorem dd3T_pull (c : E → E → E → ℚ) :
    dd3T (fun a b d : H => c (ι a) (ι b) (ι d)) = fun a b c' d => dd3T c (ι a) (ι b) (ι c') (ι d) := by
  funext a b c' d
  simp only [dd3T, map_mul]

theorem dd2_pull (hρ : ∀ (s : H) (w : W), ρ' (ι s) w = ρH' s w) (u : E → E → W) :
    dd2 ρH' (fun s t => u (ι s) (ι t)) = fun a b c => dd2 ρ' u (ι a) (ι b) (ι c) := by
  funext a b c
  simp only [dd2, map_mul, hρ]

theorem cup22_pull (hρ' : ∀ (s : H) (w : W), ρ' (ι s) w = ρH' s w) (α : E → E → V) (β : E → E → W) :
    cup22 ρH' e (fun s t => α (ι s) (ι t)) (fun s t => β (ι s) (ι t)) =
      fun a b c d => cup22 ρ' e α β (ι a) (ι b) (ι c) (ι d) := by
  funext a b c d
  simp only [cup22, ← ι.map_mul, hρ']

/-- The primitive `wb - κ ∘ ι` of `zx ∘ ι`. -/
theorem nf_primitive (hρ : ∀ (s : H) (v : V), ρ (ι s) v = ρH s v)
    (zx zb : E → E → V) (κ : E → V) (h1 : zb = zx + dd1 ρ κ)
    (wb : H → V) (hw : dd1 ρH wb = fun s t => zb (ι s) (ι t)) :
    dd1 ρH (wb - fun s => κ (ι s)) = fun s t => zx (ι s) (ι t) := by
  have hk := dd1_pull ι hρ κ
  funext s t
  have h3 := congrFun (congrFun hw s) t
  have h4 := congrFun (congrFun hk s) t
  have h5 := congrFun (congrFun h1 (ι s)) (ι t)
  simp only [dd1, Pi.add_apply, Pi.sub_apply, map_sub, ι.map_mul, hρ] at h3 h4 h5 ⊢
  linear_combination (norm := module) h3 + h5

/-- **The transferred flag cochain is a cocycle.** -/
theorem nfTheta_dd3T (hρ' : ∀ (s : H) (w : W), ρ' (ι s) w = ρH' s w)
    (heH : ∀ (g : H) (v : V) (w : W), e (ρH g v) (ρH' g w) = e v w)
    (zx : E → E → V) (zy : E → E → W) (gn : E → E → E → ℚ) (hzy : dd2 ρ' zy = 0)
    (hγ : dd3T gn = cup22 ρ' e zx zy) (wn : H → V) (hwn : dd1 ρH wn = fun s t => zx (ι s) (ι t)) :
    dd3T (fun a b c : H => cup12 ρH' e wn (fun s t => zy (ι s) (ι t)) a b c - gn (ι a) (ι b) (ι c)) = 0 := by
  have h0 : dd3T (fun a b c : H => cup12 ρH' e wn (fun s t => zy (ι s) (ι t)) a b c - gn (ι a) (ι b) (ι c)) =
      dd3T (cup12 ρH' e wn (fun s t => zy (ι s) (ι t))) - dd3T (fun a b c : H => gn (ι a) (ι b) (ι c)) := dd3T_sub _ _
  rw [h0, leibniz12 heH, hwn, dd2_pull ι hρ' zy, hzy, dd3T_pull, hγ, cup22_pull ι hρ' zx zy]
  funext a b c d
  simp [cup13]

end Pull

section Normalize

/-- **Normalisation on the radical** of the transferred primitive. -/
theorem nfGamma_exists (inl : Multiplicative (ℤ × ℤ) →* E) (hinj : Function.Injective inl)
    (he : ∀ (g : E) (v : V) (w : W), e (ρ g v) (ρ' g w) = e v w)
    (zx zb : E → E → V) (zy zb' : E → E → W) (κ : E → V) (κ' : E → W) (gb : E → E → E → ℚ)
    (hzb : dd2 ρ zb = 0) (hzy : dd2 ρ' zy = 0) (h1 : zb = zx + dd1 ρ κ) (h2 : zb' = zy + dd1 ρ' κ')
    (hγ : dd3T gb = cup22 ρ' e zb zb') (hrad : ∀ a b : Multiplicative (ℤ × ℤ), zx (inl a) (inl b) = 0) :
    ∃ ε : E → E → ℚ, ∀ a b c : Multiplicative (ℤ × ℤ),
      (nfGamma0 ρ' e zb κ κ' zy gb - dd2T ε) (inl a) (inl b) (inl c) = 0 := by
  have hd := nfGamma0_dd3T he zx zb zy zb' κ κ' gb hzb hzy h1 h2 hγ
  obtain ⟨ε, hε⟩ := normalize_on_radical inl hinj (nfGamma0 ρ' e zb κ κ' zy gb) (fun a b c d => by
    rw [hd]
    simp [cup22, hrad])
  exact ⟨ε, fun a b c => by simpa using hε a b c⟩

end Normalize

end NF

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
