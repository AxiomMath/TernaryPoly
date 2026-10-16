module

public import TernaryPeriodPolynomials.Polynomial.Homogeneous
public import TernaryPeriodPolynomials.Polynomial.Parity
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section


/-!
# eq:H-symmetry and the parity of `p`

Formalized by Claude Haiku 5.5.

Statements are literal. `v` is a ternary polynomial over `ℚ` with variables `X 0 = X`, `X 1 = Y`
after substitution. The hypotheses are the paper's:
* `S v = v` and `C v = v` (`(Sf)(x,y,z) = f(y,x,z)`, `(Cf)(x,y,z) = f(y,z,x)`;
  symmetry `ε = 1`), written as `bind₁ ![X 1, X 0, X 2] v = v` and `bind₁ ![X 1, X 2, X 0] v = v`;
* `v` homogeneous of degree `m`, with `m` odd for the parity part (`lem:period-extraction`);
* `p` is characterised by `∂_X p = -H`, `p(0,Y) = 0` (that is, `p = -∫₀^X H`), and
  `C_v = 0`, i.e. `p(X-Y,Y) - p(X,Y) - h(X,Y) = 0`.
  Existence of the integral is not formalized here; the theorems take `p` as a hypothesis.

Definitions: `h(X,Y) = v(-Y,X,Y-X)`, `H(X,Y) = (∂₁+∂₂) v(-Y,X,Y-X)`.
Here `∂₁ = pderiv 0` and `∂₂ = pderiv 1` on the first two of `Fin 3`-variables of `v`.

Main results:
* `eq_H_symmetry`: `h_X = H(X,Y) - H(Y-X,Y)` and `H(-Y,-X) = H(X,Y)`, from
  `S v = v`, `C v = v` alone.
* `p_parity`: `H(-X,Y) = H(X,Y)`, `H(X,-Y) = H(X,Y)` (the latter from homogeneity),
  `p` odd in `X`, even in `Y`, and `p_X(X,Y) = p_X(Y,-X)`.

The proofs use only Mathlib's `bind₁`, `pderiv`, `coeff_pderiv` and two the library lemmas
(`TernaryPoly.isHomogeneous_bind₁_linear`, `TernaryPoly.homogeneous_bind_smul`).
-/

open MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities.HSymmetry

/-- Ternary substitutions with codomain `MvPolynomial (Fin 3) ℚ`. -/
abbrev HSub3 := Fin 3 → MvPolynomial (Fin 3) ℚ

/-- Binary substitutions with codomain `MvPolynomial (Fin 2) ℚ`. -/
abbrev HSub2 := Fin 2 → MvPolynomial (Fin 2) ℚ

/-- Ternary-to-binary substitutions, e.g. `(X₀,X₁,X₂) ↦ (-X₁, X₀ - X₁, X₀)`. -/
abbrev HJetSub := Fin 3 → MvPolynomial (Fin 2) ℚ

/-- The substitution `(X₀, X₁, X₂) ↦ (-Y, X, Y - X)` of the paper, with `X = X 0`, `Y = X 1`. -/
def jetSub : Fin 3 → MvPolynomial (Fin 2) ℚ := ![-X 1, X 0, X 1 - X 0]

/-- `h(X,Y) = v(-Y, X, Y - X)`. -/
def hJet (v : MvPolynomial (Fin 3) ℚ) : MvPolynomial (Fin 2) ℚ := bind₁ jetSub v

/-- `H(X,Y) = (∂₁ + ∂₂) v(-Y, X, Y - X)`. -/
def HJet (v : MvPolynomial (Fin 3) ℚ) : MvPolynomial (Fin 2) ℚ :=
  bind₁ jetSub (pderiv 0 v + pderiv 1 v)

/-! ### Generic tools -/

theorem bind₁_eq_of_fun_eq {σ τ R : Type*} [CommSemiring R] {f g : σ → MvPolynomial τ R}
    (h : ∀ i, f i = g i) (φ : MvPolynomial σ R) : bind₁ f φ = bind₁ g φ := by
  rw [show f = g from funext h]

/-- Chain rule for a substitution: `∂_k (f̂ p) = ∑_j (∂_j p)^ f · ∂_k (f j)`. -/
theorem pderiv_bind₁_chain {σ τ : Type*} [Fintype σ] [DecidableEq σ] [DecidableEq τ]
    (f : σ → MvPolynomial τ ℚ) (p : MvPolynomial σ ℚ) (k : τ) :
    pderiv k (bind₁ f p) = ∑ j, bind₁ f (pderiv j p) * pderiv k (f j) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, add_mul, Finset.sum_add_distrib, hp, hq]
  | mul_X p i ih =>
    have hX : ∀ j, bind₁ f (pderiv j (X i : MvPolynomial σ ℚ)) = if j = i then 1 else 0 := by
      intro j
      rw [pderiv_X]
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    simp only [map_mul, bind₁_X_right, pderiv_mul, map_add, ih, hX]
    simp [Finset.sum_add_distrib, add_mul, mul_assoc, mul_comm, ite_mul]
    rw [Finset.mul_sum]

/-! ### Zero `X₀`-derivative -/

/-- A polynomial with vanishing `X₀`-derivative has no monomial with positive `X₀`-exponent. -/
theorem coeff_eq_zero_of_pderiv_zero (f : MvPolynomial (Fin 2) ℚ) (hf : pderiv 0 f = 0)
    (m : Fin 2 →₀ ℕ) (hm : m 0 ≠ 0) : f.coeff m = 0 := by
  have h1 := coeff_pderiv (i := 0) f (m - Finsupp.single 0 1)
  rw [hf, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h1
  have hle : Finsupp.single (0 : Fin 2) 1 ≤ m :=
    Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hm)
  rw [tsub_add_cancel_of_le hle] at h1
  rcases mul_eq_zero.mp h1.symm with h | h
  · exact h
  · exfalso
    have hnn : (0 : ℚ) ≤ ((m - Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) 0 : ℕ) :=
      Nat.cast_nonneg _
    linarith

/-- If `∂_{X₀} f = 0` then `f = f(0, X₁)`. -/
theorem eq_bind_of_pderiv_zero (f : MvPolynomial (Fin 2) ℚ) (hf : pderiv 0 f = 0) :
    f = bind₁ (![0, X 1] : HSub2) f := by
  conv_lhs => rw [as_sum f]
  conv_rhs => rw [as_sum f]
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h0 : s 0 = 0
  · simp only [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
    simp [h0]
  · rw [coeff_eq_zero_of_pderiv_zero f hf s h0]
    simp

/-- A polynomial with `∂_{X₀} f = 0` and `f(0,Y) = 0` is zero. -/
theorem eq_zero_of_pderiv_zero_of_bind_zero (f : MvPolynomial (Fin 2) ℚ) (hf : pderiv 0 f = 0)
    (h0 : bind₁ (![0, X 1] : HSub2) f = 0) : f = 0 :=
  (eq_bind_of_pderiv_zero f hf).trans h0

/-! ### Chain rules for the substitutions used -/

/-- `∂_{X₀}` of `p(X-Y, Y)`. -/
theorem pderiv0_shift (p : MvPolynomial (Fin 2) ℚ) :
    pderiv 0 (bind₁ (![X 0 - X 1, X 1] : HSub2) p) =
      bind₁ (![X 0 - X 1, X 1] : HSub2) (pderiv 0 p) := by
  rw [pderiv_bind₁_chain]
  simp [Fin.sum_univ_two, pderiv_X]

/-- `∂_{X₀}` of `p(-X, Y)`. -/
theorem pderiv0_negfix (p : MvPolynomial (Fin 2) ℚ) :
    pderiv 0 (bind₁ (![-X 0, X 1] : HSub2) p) =
      -bind₁ (![-X 0, X 1] : HSub2) (pderiv 0 p) := by
  rw [pderiv_bind₁_chain]
  simp [Fin.sum_univ_two, pderiv_X]

/-- `∂_{X₀}` of `p(X, -Y)`. -/
theorem pderiv0_fix0 (p : MvPolynomial (Fin 2) ℚ) :
    pderiv 0 (bind₁ (![X 0, -X 1] : HSub2) p) =
      bind₁ (![X 0, -X 1] : HSub2) (pderiv 0 p) := by
  rw [pderiv_bind₁_chain]
  simp [Fin.sum_univ_two, pderiv_X]

/-! ### Permutation identities for `v` -/

/-- `T := (X₀, X₂, X₁)` (exchange of the last two variables), from `S v = v` and `C v = v`:
`T = S ∘ C` on indices. -/
theorem swapT_eq (v : MvPolynomial (Fin 3) ℚ)
    (hS : bind₁ (![X 1, X 0, X 2] : HSub3) v = v)
    (hC : bind₁ (![X 1, X 2, X 0] : HSub3) v = v) :
    bind₁ (![X 0, X 2, X 1] : HSub3) v = v := by
  calc bind₁ (![X 0, X 2, X 1] : HSub3) v
      = bind₁ (![X 1, X 0, X 2] : HSub3) (bind₁ (![X 1, X 2, X 0] : HSub3) v) := by
        rw [bind₁_bind₁]
        exact bind₁_eq_of_fun_eq (fun i => by fin_cases i <;> simp) v
    _ = v := by rw [hC, hS]

theorem swapT_involutive (w : MvPolynomial (Fin 3) ℚ) :
    bind₁ (![X 0, X 2, X 1] : HSub3) (bind₁ (![X 0, X 2, X 1] : HSub3) w) = w := by
  rw [bind₁_bind₁]
  have e : (fun i => bind₁ (![X 0, X 2, X 1] : HSub3) ((![X 0, X 2, X 1] : HSub3) i) :
      Fin 3 → MvPolynomial (Fin 3) ℚ) = X := by
    funext i
    fin_cases i <;> simp
  rw [e]
  simp

theorem pderiv_swapT (v : MvPolynomial (Fin 3) ℚ) :
    pderiv 0 (bind₁ (![X 0, X 2, X 1] : HSub3) v) =
        bind₁ (![X 0, X 2, X 1] : HSub3) (pderiv 0 v) ∧
      pderiv 1 (bind₁ (![X 0, X 2, X 1] : HSub3) v) =
        bind₁ (![X 0, X 2, X 1] : HSub3) (pderiv 2 v) := by
  constructor
  · rw [pderiv_bind₁_chain]
    simp [Fin.sum_univ_three, pderiv_X]
  · rw [pderiv_bind₁_chain]
    simp [Fin.sum_univ_three, pderiv_X]

theorem pderiv_swapS (v : MvPolynomial (Fin 3) ℚ) :
    pderiv 0 (bind₁ (![X 1, X 0, X 2] : HSub3) v) =
        bind₁ (![X 1, X 0, X 2] : HSub3) (pderiv 1 v) ∧
      pderiv 1 (bind₁ (![X 1, X 0, X 2] : HSub3) v) =
        bind₁ (![X 1, X 0, X 2] : HSub3) (pderiv 0 v) := by
  constructor
  · rw [pderiv_bind₁_chain]
    simp [Fin.sum_univ_three, pderiv_X]
  · rw [pderiv_bind₁_chain]
    simp [Fin.sum_univ_three, pderiv_X]

/-- `∂₁ + ∂₂` of `v` is invariant under `S`. -/
theorem sum_S_invariant (v : MvPolynomial (Fin 3) ℚ)
    (hS : bind₁ (![X 1, X 0, X 2] : HSub3) v = v) :
    bind₁ (![X 1, X 0, X 2] : HSub3) (pderiv 0 v + pderiv 1 v) =
      pderiv 0 v + pderiv 1 v := by
  have hd0 : pderiv 0 v = bind₁ (![X 1, X 0, X 2] : HSub3) (pderiv 1 v) := by
    have h := (pderiv_swapS v).1
    rw [hS] at h
    exact h
  have hd1 : pderiv 1 v = bind₁ (![X 1, X 0, X 2] : HSub3) (pderiv 0 v) := by
    have h := (pderiv_swapS v).2
    rw [hS] at h
    exact h
  rw [map_add, ← hd1, ← hd0, add_comm]

/-- `∂₁ + ∂₂` of `v` is sent to `∂₁ + ∂₃` by `T`. -/
theorem sum_T_pair (v : MvPolynomial (Fin 3) ℚ)
    (hS : bind₁ (![X 1, X 0, X 2] : HSub3) v = v)
    (hC : bind₁ (![X 1, X 2, X 0] : HSub3) v = v) :
    bind₁ (![X 0, X 2, X 1] : HSub3) (pderiv 0 v + pderiv 1 v) = pderiv 0 v + pderiv 2 v := by
  have hT := swapT_eq v hS hC
  have hd0 : pderiv 0 v = bind₁ (![X 0, X 2, X 1] : HSub3) (pderiv 0 v) := by
    have h := (pderiv_swapT v).1
    rw [hT] at h
    exact h
  have hd1 : pderiv 1 v = bind₁ (![X 0, X 2, X 1] : HSub3) (pderiv 2 v) := by
    have h := (pderiv_swapT v).2
    rw [hT] at h
    exact h
  have h2 : bind₁ (![X 0, X 2, X 1] : HSub3) (pderiv 1 v) = pderiv 2 v := by
    rw [hd1, swapT_involutive]
  rw [map_add, ← hd0, h2]

/-! ### Substitution comparisons -/

/-- `∂_{X₀} h = v₂ - v₃` ( `h_X = v_2 - v_3`). -/
theorem pderiv_hJet (v : MvPolynomial (Fin 3) ℚ) :
    pderiv 0 (hJet v) = bind₁ jetSub (pderiv 1 v) - bind₁ jetSub (pderiv 2 v) := by
  unfold hJet
  rw [pderiv_bind₁_chain]
  simp [Fin.sum_univ_three, jetSub, pderiv_X, sub_eq_add_neg]

/-- `H(Y-X, Y)` as a substitution of `∂₁v + ∂₂v`. -/
theorem HJet_shift (v : MvPolynomial (Fin 3) ℚ) :
    bind₁ (![X 1 - X 0, X 1] : HSub2) (HJet v) =
      bind₁ (![-X 1, X 1 - X 0, X 0] : HJetSub) (pderiv 0 v + pderiv 1 v) := by
  unfold HJet
  rw [bind₁_bind₁]
  exact bind₁_eq_of_fun_eq (fun i => by fin_cases i <;> simp [jetSub]) _

theorem bind_T_jetSub (w : MvPolynomial (Fin 3) ℚ) :
    bind₁ (![-X 1, X 1 - X 0, X 0] : HJetSub) w =
      bind₁ jetSub (bind₁ (![X 0, X 2, X 1] : HSub3) w) := by
  rw [bind₁_bind₁]
  exact bind₁_eq_of_fun_eq (fun i => by fin_cases i <;> simp [jetSub]) w

theorem bind_S_jetSub (w : MvPolynomial (Fin 3) ℚ) :
    bind₁ (![X 0, -X 1, X 1 - X 0] : HJetSub) w =
      bind₁ jetSub (bind₁ (![X 1, X 0, X 2] : HSub3) w) := by
  rw [bind₁_bind₁]
  exact bind₁_eq_of_fun_eq (fun i => by fin_cases i <;> simp [jetSub]) w

/-! ### eq:H-symmetry -/

/-- **eq:H-symmetry, first two identities**, for `v` symmetric (`S v = v`,
`C v = v`): `h_X = H(X,Y) - H(Y-X,Y)` and `H(-Y,-X) = H(X,Y)`. -/
theorem eq_H_symmetry (v : MvPolynomial (Fin 3) ℚ)
    (hS : bind₁ (![X 1, X 0, X 2] : HSub3) v = v)
    (hC : bind₁ (![X 1, X 2, X 0] : HSub3) v = v) :
    pderiv 0 (hJet v) = HJet v - bind₁ (![X 1 - X 0, X 1] : HSub2) (HJet v) ∧
      bind₁ (![-X 1, -X 0] : HSub2) (HJet v) = HJet v := by
  constructor
  · rw [pderiv_hJet, HJet_shift, bind_T_jetSub, sum_T_pair v hS hC]
    unfold HJet
    rw [map_add, map_add]
    ring
  · unfold HJet
    calc bind₁ (![-X 1, -X 0] : HSub2) (bind₁ jetSub (pderiv 0 v + pderiv 1 v))
        = bind₁ (![X 0, -X 1, X 1 - X 0] : HJetSub) (pderiv 0 v + pderiv 1 v) := by
          rw [bind₁_bind₁]
          exact bind₁_eq_of_fun_eq (fun i => by fin_cases i <;> first | (simp [jetSub]; done) | (simp [jetSub]; ring)) _
      _ = bind₁ jetSub (bind₁ (![X 1, X 0, X 2] : HSub3) (pderiv 0 v + pderiv 1 v)) :=
          bind_S_jetSub _
      _ = bind₁ jetSub (pderiv 0 v + pderiv 1 v) := by rw [sum_S_invariant v hS]

/-! ### Homogeneity of `H` and evenness -/

/-- `H` is homogeneous of degree `m - 1` when `v` is homogeneous of degree `m`. -/
theorem HJet_homogeneous {m : ℕ} {v : MvPolynomial (Fin 3) ℚ} (hv : v.IsHomogeneous m) :
    (HJet v).IsHomogeneous (m - 1) := by
  have h0 : (pderiv 0 v).IsHomogeneous (m - 1) := hv.pderiv
  have h1 : (pderiv 1 v).IsHomogeneous (m - 1) := hv.pderiv
  have hg : ∀ i, (jetSub i).IsHomogeneous 1 := by
    intro i
    fin_cases i
    · exact (isHomogeneous_X ℚ 1).neg
    · exact isHomogeneous_X ℚ 0
    · exact (isHomogeneous_X ℚ 1).sub (isHomogeneous_X ℚ 0)
  unfold HJet
  exact TernaryPoly.isHomogeneous_bind₁_linear (h0.add h1) jetSub hg

/-- For `m` odd, `H` of degree `m - 1` (even) is invariant under `(X, Y) ↦ (-X, -Y)`. -/
theorem HJet_neg_both {m : ℕ} (hm : Odd m) {v : MvPolynomial (Fin 3) ℚ}
    (hv : v.IsHomogeneous m) :
    bind₁ (![-X 0, -X 1] : HSub2) (HJet v) = HJet v := by
  have hH := HJet_homogeneous hv
  have e : bind₁ (![-X 0, -X 1] : HSub2) (HJet v) =
      bind₁ (fun i => (-1 : ℚ) • X i) (HJet v) :=
    bind₁_eq_of_fun_eq (fun i => by fin_cases i <;> simp [neg_smul]) _
  rw [e, TernaryPoly.homogeneous_bind_smul hH (-1 : ℚ)]
  obtain ⟨k, hk⟩ := hm
  have hmk : m - 1 = 2 * k := by omega
  rw [hmk, pow_mul]
  simp

/-! ### Parity of `p` -/

/-- The parity theorem. `p` is characterised by `∂_X p = -H` and `p(0,Y) = 0` (that is,
`p = -∫₀^X H`), and `C_v = 0`. Conclusions: `H(-X,Y) = H(X,Y)`,
`H(X,-Y) = H(X,Y)`, `p` odd in `X` and even in `Y`, and `p_X(X,Y) = p_X(Y,-X)`. -/
theorem p_parity {m : ℕ} (hm : Odd m) (v : MvPolynomial (Fin 3) ℚ) (hv : v.IsHomogeneous m)
    (hS : bind₁ (![X 1, X 0, X 2] : HSub3) v = v)
    (hC : bind₁ (![X 1, X 2, X 0] : HSub3) v = v)
    (p : MvPolynomial (Fin 2) ℚ) (hp₁ : pderiv 0 p = -HJet v)
    (hp₀ : bind₁ (![0, X 1] : HSub2) p = 0)
    (hCv : bind₁ (![X 0 - X 1, X 1] : HSub2) p - p - hJet v = 0) :
    bind₁ (![-X 0, X 1] : HSub2) (HJet v) = HJet v ∧
      bind₁ (![X 0, -X 1] : HSub2) (HJet v) = HJet v ∧
      bind₁ (![-X 0, X 1] : HSub2) p = -p ∧
      bind₁ (![X 0, -X 1] : HSub2) p = p ∧
      pderiv 0 p = bind₁ (![X 1, -X 0] : HSub2) (pderiv 0 p) := by
  obtain ⟨hX, hConj2⟩ := eq_H_symmetry v hS hC
  -- `K`: `H(X-Y,Y) = H(Y-X,Y)`, obtained by differentiating `C_v = 0` in `X`
  have hK : bind₁ (![X 0 - X 1, X 1] : HSub2) (HJet v) =
      bind₁ (![X 1 - X 0, X 1] : HSub2) (HJet v) := by
    have h := congrArg (pderiv 0) hCv
    rw [map_sub, map_sub, map_zero, pderiv0_shift, hp₁, hX, map_neg] at h
    linear_combination -h
  -- substitution helpers (composition of substitutions, `bind₁_bind₁`)
  have L_a : ∀ f : MvPolynomial (Fin 2) ℚ,
      bind₁ (![X 0 + X 1, X 1] : HSub2) (bind₁ (![X 0 - X 1, X 1] : HSub2) f) = f := by
    intro f
    rw [bind₁_bind₁]
    refine (bind₁_eq_of_fun_eq (g := X) (fun i => by fin_cases i <;> simp) f).trans ?_
    simp
  have L_b : ∀ f : MvPolynomial (Fin 2) ℚ,
      bind₁ (![X 0 + X 1, X 1] : HSub2) (bind₁ (![X 1 - X 0, X 1] : HSub2) f) =
        bind₁ (![-X 0, X 1] : HSub2) f := by
    intro f
    rw [bind₁_bind₁]
    exact bind₁_eq_of_fun_eq (fun i => by fin_cases i <;> simp) f
  have L_c : ∀ f : MvPolynomial (Fin 2) ℚ,
      bind₁ (![-X 0, -X 1] : HSub2) (bind₁ (![-X 0, X 1] : HSub2) f) =
        bind₁ (![X 0, -X 1] : HSub2) f := by
    intro f
    rw [bind₁_bind₁]
    exact bind₁_eq_of_fun_eq (fun i => by fin_cases i <;> simp) f
  have L_d : ∀ f : MvPolynomial (Fin 2) ℚ,
      bind₁ (![X 0, -X 1] : HSub2) (bind₁ (![-X 1, -X 0] : HSub2) f) =
        bind₁ (![X 1, -X 0] : HSub2) f := by
    intro f
    rw [bind₁_bind₁]
    exact bind₁_eq_of_fun_eq (fun i => by fin_cases i <;> simp) f
  have L_f : ∀ f : MvPolynomial (Fin 2) ℚ,
      bind₁ (![0, -X 1] : HSub2) (bind₁ (![0, X 1] : HSub2) f) =
        bind₁ (![0, -X 1] : HSub2) f := by
    intro f
    rw [bind₁_bind₁]
    exact bind₁_eq_of_fun_eq (fun i => by fin_cases i <;> simp) f
  have L_g : ∀ f : MvPolynomial (Fin 2) ℚ,
      bind₁ (![0, X 1] : HSub2) (bind₁ (![X 0, -X 1] : HSub2) f) =
        bind₁ (![0, -X 1] : HSub2) f := by
    intro f
    rw [bind₁_bind₁]
    exact bind₁_eq_of_fun_eq (fun i => by fin_cases i <;> simp) f
  have L_h : ∀ f : MvPolynomial (Fin 2) ℚ,
      bind₁ (![0, X 1] : HSub2) (bind₁ (![-X 0, X 1] : HSub2) f) =
        bind₁ (![0, X 1] : HSub2) f := by
    intro f
    rw [bind₁_bind₁]
    exact bind₁_eq_of_fun_eq (fun i => by fin_cases i <;> simp) f
  -- `E1`: `H(-X,Y) = H(X,Y)`
  have E1 : bind₁ (![-X 0, X 1] : HSub2) (HJet v) = HJet v := by
    calc bind₁ (![-X 0, X 1] : HSub2) (HJet v)
        = bind₁ (![X 0 + X 1, X 1] : HSub2) (bind₁ (![X 1 - X 0, X 1] : HSub2) (HJet v)) :=
          (L_b _).symm
      _ = bind₁ (![X 0 + X 1, X 1] : HSub2) (bind₁ (![X 0 - X 1, X 1] : HSub2) (HJet v)) := by
          rw [hK]
      _ = HJet v := L_a _
  -- `E3`: `H(X,-Y) = H(X,Y)`
  have E3 : bind₁ (![X 0, -X 1] : HSub2) (HJet v) = HJet v := by
    calc bind₁ (![X 0, -X 1] : HSub2) (HJet v)
        = bind₁ (![-X 0, -X 1] : HSub2) (bind₁ (![-X 0, X 1] : HSub2) (HJet v)) :=
          (L_c _).symm
      _ = bind₁ (![-X 0, -X 1] : HSub2) (HJet v) := by rw [E1]
      _ = HJet v := HJet_neg_both hm hv
  -- `E6`: `H(Y,-X) = H(X,Y)`
  have E6 : bind₁ (![X 1, -X 0] : HSub2) (HJet v) = HJet v := by
    calc bind₁ (![X 1, -X 0] : HSub2) (HJet v)
        = bind₁ (![X 0, -X 1] : HSub2) (bind₁ (![-X 1, -X 0] : HSub2) (HJet v)) :=
          (L_d _).symm
      _ = bind₁ (![X 0, -X 1] : HSub2) (HJet v) := by rw [hConj2]
      _ = HJet v := E3
  have hp0m : bind₁ (![0, -X 1] : HSub2) p = 0 := by
    rw [← L_f p, hp₀, map_zero]
  refine ⟨E1, E3, ?_, ?_, ?_⟩
  · -- `p` is odd in `X`
    have hd : pderiv 0 (bind₁ (![-X 0, X 1] : HSub2) p + p) = 0 := by
      rw [map_add, pderiv0_negfix, hp₁, map_neg, E1, neg_neg, add_neg_cancel]
    have hz : bind₁ (![0, X 1] : HSub2) (bind₁ (![-X 0, X 1] : HSub2) p + p) = 0 := by
      rw [map_add, L_h, hp₀, add_zero]
    exact eq_neg_of_add_eq_zero_left
      (eq_zero_of_pderiv_zero_of_bind_zero _ hd hz)
  · -- `p` is even in `Y`
    have hd : pderiv 0 (bind₁ (![X 0, -X 1] : HSub2) p - p) = 0 := by
      rw [map_sub, pderiv0_fix0, hp₁, map_neg, E3, sub_self]
    have hz : bind₁ (![0, X 1] : HSub2) (bind₁ (![X 0, -X 1] : HSub2) p - p) = 0 := by
      rw [map_sub, L_g, hp0m, hp₀, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_pderiv_zero_of_bind_zero _ hd hz)
  · -- `p_X(X,Y) = p_X(Y,-X)`
    rw [hp₁, map_neg, E6]

/-- The parity of `H` is not a consequence of the symmetry of `v` and its odd homogeneity:
`v = XYZ` is symmetric of degree `3`, but `H(X,Y) = -(X-Y)^2` is not even in `X`.  So the
hypothesis `hCv` of `p_parity` carries the paper's step "`J_v = 0` gives `C_v = 0`". -/
theorem H_parity_not_from_symmetry :
    ∃ v : MvPolynomial (Fin 3) ℚ, v.IsHomogeneous 3 ∧
      bind₁ (![X 1, X 0, X 2] : HSub3) v = v ∧ bind₁ (![X 1, X 2, X 0] : HSub3) v = v ∧
      bind₁ (![-X 0, X 1] : HSub2) (HJet v) ≠ HJet v := by
  refine ⟨(X 0 * X 1 * X 2 : MvPolynomial (Fin 3) ℚ), ?_, ?_, ?_, ?_⟩
  · have h := ((isHomogeneous_X ℚ (0 : Fin 3)).mul (isHomogeneous_X ℚ (1 : Fin 3))).mul
      (isHomogeneous_X ℚ (2 : Fin 3))
    simpa using h
  · simp [mul_comm]
  · simp
    ring
  · intro h
    have h2 := congrArg (MvPolynomial.eval ![(1:ℚ), 1]) h
    simp [HJet, jetSub, pderiv_X] at h2

end TernaryPeriodPolynomials.Argument.Identities.HSymmetry

end
