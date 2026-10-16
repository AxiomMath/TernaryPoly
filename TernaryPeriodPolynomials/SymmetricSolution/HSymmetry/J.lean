module

public import TernaryPeriodPolynomials.SymmetricSolution.HSymmetry.HSymmetry
public import TernaryPeriodPolynomials.PeriodPolynomial.PeriodCZero

@[expose] public section


/-!
# `J_v = 0` discharges `C_v = 0`, so `eq:H-symmetry` holds under the paper's hypotheses

Formalized by Claude Haiku 5.5.
The hypothesis `hCv` of `HSymmetry.p_parity` is supplied by S5's lemma
`NormalJet.periodC_eq_zero_of_J_zero` (`J_v = 0` forces `C_v = 0`).

Bridge. A ℚ-polynomial `v` in three variables is complexified by `cpx`; the ℚ-polynomial
`p` in two variables is complexified and moved to three variables by `liftJ = rename castSucc ∘ cpx`.
Then `periodP (cpx v) = liftJ p` by uniqueness of the `X₀`-antiderivative (a three-variable
statement over ℂ, `pderiv0_eq_zero_bind`), and `periodC (cpx v) = 0` pulls back to `hCv` by
injectivity of `liftJ`.
-/

open MvPolynomial GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities.HSymmetryJ

open TernaryPeriodPolynomials.Argument.Identities

/-- The substitution `(X₀, X₁, X₂) ↦ (0, X₁, X₂)` of the uniqueness argument. -/
abbrev s0C : Fin 3 → MvPolynomial (Fin 3) ℂ := ![0, X 1, X 2]

/-- Complex coefficients of a ℚ-polynomial. -/
def cpx {σ : Type*} (f : MvPolynomial σ ℚ) : MvPolynomial σ ℂ := map (algebraMap ℚ ℂ) f

/-- A binary ℚ-polynomial as a ternary ℂ-polynomial in `X₀, X₁` (the third variable unused). -/
def liftJ (f : MvPolynomial (Fin 2) ℚ) : MvPolynomial (Fin 3) ℂ := rename Fin.castSucc (cpx f)

/-- The complexification of a homogeneous ternary ℚ-polynomial, as a `HomogeneousPoly`. -/
def complexify {m : ℕ} (v : MvPolynomial (Fin 3) ℚ) (hv : v.IsHomogeneous m) : HomogeneousPoly m :=
  ⟨cpx v, (mem_homogeneousSubmodule m _).2 (hv.map (algebraMap ℚ ℂ))⟩

/-! ### Injectivity and linearity of the bridge -/

theorem cpx_injective : Function.Injective (cpx (σ := Fin 2)) :=
  MvPolynomial.map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective

theorem liftJ_injective : Function.Injective liftJ := fun _ _ h =>
  cpx_injective (rename_injective Fin.castSucc (Fin.castSucc_injective 2) h)

theorem liftJ_zero : liftJ 0 = 0 := by simp [liftJ, cpx]

theorem liftJ_sub (f g : MvPolynomial (Fin 2) ℚ) : liftJ (f - g) = liftJ f - liftJ g := by
  simp [liftJ, cpx]

theorem liftJ_neg (f : MvPolynomial (Fin 2) ℚ) : liftJ (-f) = -liftJ f := by
  simp [liftJ, cpx]

/-! ### Transport of the substitutions -/

theorem liftJ_jet (φ : MvPolynomial (Fin 3) ℚ) :
    liftJ (HSymmetry.hJet φ) = bind₁ NormalJet.hFrame (cpx φ) := by
  unfold liftJ HSymmetry.hJet cpx
  rw [map_bind₁, rename_bind₁]
  refine HSymmetry.bind₁_eq_of_fun_eq (fun i => ?_) _
  fin_cases i <;> simp [HSymmetry.jetSub, NormalJet.hFrame]

theorem liftJ_bind_tau (p : MvPolynomial (Fin 2) ℚ) :
    liftJ (bind₁ (![X 0 - X 1, X 1] : HSymmetry.HSub2) p) = bind₁ NormalJet.tauSub (liftJ p) := by
  unfold liftJ cpx
  rw [map_bind₁, rename_bind₁, bind₁_rename]
  refine HSymmetry.bind₁_eq_of_fun_eq (fun i => ?_) _
  fin_cases i <;> simp [NormalJet.tauSub]

theorem periodH_cpx (v : MvPolynomial (Fin 3) ℚ) :
    NormalJet.periodH (cpx v) = liftJ (HSymmetry.HJet v) := by
  have key : NormalJet.periodH (cpx v) = bind₁ NormalJet.hFrame (cpx (pderiv 0 v + pderiv 1 v)) := by
    simp only [NormalJet.periodH, cpx, map_add, pderiv_map]
  rw [key]
  exact (liftJ_jet _).symm

theorem pderiv0_liftJ (p : MvPolynomial (Fin 2) ℚ) : pderiv 0 (liftJ p) = liftJ (pderiv 0 p) := by
  have h := pderiv_rename (Fin.castSucc_injective 2) (0 : Fin 2) (cpx p)
  rw [Fin.castSucc_zero] at h
  unfold liftJ
  rw [h]
  unfold cpx
  rw [pderiv_map]

theorem pderiv0_periodP (v : MvPolynomial (Fin 3) ℚ) :
    pderiv 0 (NormalJet.periodP (cpx v)) = -liftJ (HSymmetry.HJet v) := by
  unfold NormalJet.periodP
  rw [map_neg, NormalJet.pderiv_antiderivX, periodH_cpx]

/-! ### The `X₀`-uniqueness over ℂ -/

/-- A three-variable polynomial with `∂_{X₀} h = 0` equals its substitution `X₀ ↦ 0`. -/
theorem pderiv0_eq_zero_bind (h : MvPolynomial (Fin 3) ℂ) (hh : pderiv 0 h = 0) :
    h = bind₁ s0C h := by
  have hcoeff : ∀ s : Fin 3 →₀ ℕ, s 0 ≠ 0 → h.coeff s = 0 := by
    intro s hs
    have hle : Finsupp.single (0 : Fin 3) 1 ≤ s :=
      Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hs)
    have h1 := coeff_pderiv (i := 0) h (s - Finsupp.single 0 1)
    rw [hh, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, tsub_add_cancel_of_le hle] at h1
    have hpos : ((s - Finsupp.single (0 : Fin 3) 1 : Fin 3 →₀ ℕ) 0) + 1 = s 0 := by
      simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
      omega
    have hne : ((((s - Finsupp.single (0 : Fin 3) 1 : Fin 3 →₀ ℕ) 0 : ℕ)) : ℂ) + 1 ≠ 0 := by
      have hc : ((((s - Finsupp.single (0 : Fin 3) 1 : Fin 3 →₀ ℕ) 0 : ℕ)) : ℂ) + 1 = (s 0 : ℂ) := by
        exact_mod_cast hpos
      rw [hc]
      exact_mod_cast hs
    exact (mul_eq_zero.mp h1.symm).resolve_right hne
  conv_lhs => rw [as_sum h]
  conv_rhs => rw [as_sum h]
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h0 : s 0 = 0
  · simp only [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three]
    simp [s0C, h0]
  · rw [hcoeff s h0]
    simp

/-- Two three-variable polynomials with equal `∂_{X₀}` and equal `X₀ ↦ 0` substitutions agree. -/
theorem eq_of_pderiv0_of_bind (f g : MvPolynomial (Fin 3) ℂ) (h1 : pderiv 0 f = pderiv 0 g)
    (h2 : bind₁ s0C f = bind₁ s0C g) : f = g := by
  have h := pderiv0_eq_zero_bind (f - g) (by rw [map_sub, h1, sub_self])
  rw [map_sub, h2, sub_self] at h
  exact sub_eq_zero.mp h

theorem antiderivX_bind_zero (c : MvPolynomial (Fin 3) ℂ) :
    bind₁ s0C (NormalJet.antiderivX c) = 0 := by
  unfold NormalJet.antiderivX
  rw [map_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  have hz : ∏ i ∈ (s + Finsupp.single (0 : Fin 3) 1 : Fin 3 →₀ ℕ).support,
      s0C i ^ (s + Finsupp.single (0 : Fin 3) 1 : Fin 3 →₀ ℕ) i = 0 :=
    Finset.prod_eq_zero (i := 0) (by simp) (by simp [s0C])
  rw [bind₁_monomial, hz, mul_zero]

/-- Substitution into `liftJ` of a binary substitution. -/
theorem liftJ_bind (g : Fin 2 → MvPolynomial (Fin 2) ℚ) (p : MvPolynomial (Fin 2) ℚ) :
    liftJ (bind₁ g p) = bind₁ (fun j => rename Fin.castSucc (cpx (g j))) (cpx p) := by
  unfold liftJ cpx
  rw [map_bind₁, rename_bind₁]

theorem s0C_bind_liftJ (p : MvPolynomial (Fin 2) ℚ)
    (hp₀ : bind₁ (![0, X 1] : HSymmetry.HSub2) p = 0) : bind₁ s0C (liftJ p) = 0 := by
  have h := liftJ_bind (![0, X 1] : HSymmetry.HSub2) p
  rw [hp₀, liftJ_zero] at h
  have hs0 : (s0C ∘ Fin.castSucc) =
      fun j => rename Fin.castSucc (cpx ((![0, X 1] : HSymmetry.HSub2) j)) := by
    funext j
    fin_cases j <;> simp [s0C, cpx]
  unfold liftJ
  rw [bind₁_rename, hs0]
  exact h.symm

theorem bind_s0_periodP (v : MvPolynomial (Fin 3) ℚ) :
    bind₁ s0C (NormalJet.periodP (cpx v)) = 0 := by
  unfold NormalJet.periodP
  rw [map_neg, antiderivX_bind_zero, neg_zero]

theorem periodP_eq_liftJ (v : MvPolynomial (Fin 3) ℚ) (p : MvPolynomial (Fin 2) ℚ)
    (hp₁ : pderiv 0 p = -HSymmetry.HJet v)
    (hp₀ : bind₁ (![0, X 1] : HSymmetry.HSub2) p = 0) :
    NormalJet.periodP (cpx v) = liftJ p := by
  apply eq_of_pderiv0_of_bind
  · rw [pderiv0_periodP, pderiv0_liftJ, hp₁, liftJ_neg]
  · rw [bind_s0_periodP, s0C_bind_liftJ p hp₀]

/-! ### Full S₃-invariance of `v` from `S v = v` and `C v = v` -/

/-- The 3-cycle `X₀ ↦ X₁ ↦ X₂ ↦ X₀` (so `X ∘ cyc = (X₁, X₂, X₀)`). -/
def cyc : Equiv.Perm (Fin 3) :=
  ⟨![1, 2, 0], ![2, 0, 1], fun x => by fin_cases x <;> rfl, fun x => by fin_cases x <;> rfl⟩

/-- The transposition `X₀ ↔ X₁` (so `X ∘ swp = (X₁, X₀, X₂)`). -/
def swp : Equiv.Perm (Fin 3) := Equiv.swap 0 1

theorem perm_cases (σ : Equiv.Perm (Fin 3)) :
    σ = 1 ∨ σ = cyc ∨ σ = cyc * cyc ∨ σ = swp ∨ σ = cyc * swp ∨ σ = cyc * cyc * swp := by
  revert σ
  decide

theorem perm_invariant (v : MvPolynomial (Fin 3) ℚ)
    (hS : bind₁ (![X 1, X 0, X 2] : HSymmetry.HSub3) v = v)
    (hC : bind₁ (![X 1, X 2, X 0] : HSymmetry.HSub3) v = v) (σ : Equiv.Perm (Fin 3)) :
    bind₁ (fun i => (X (σ i) : MvPolynomial (Fin 3) ℚ)) v = v := by
  have key : ∀ σ τ : Equiv.Perm (Fin 3),
      bind₁ (fun i => (X (τ i) : MvPolynomial (Fin 3) ℚ)) v = v →
      bind₁ (fun i => (X ((σ * τ) i) : MvPolynomial (Fin 3) ℚ)) v =
        bind₁ (fun i => (X (σ i) : MvPolynomial (Fin 3) ℚ)) v := by
    intro σ τ hτ
    conv_rhs => rw [← hτ]
    rw [bind₁_bind₁]
    refine HSymmetry.bind₁_eq_of_fun_eq (fun i => ?_) v
    simp [Equiv.Perm.mul_apply]
  have hcyc : (fun i => (X (cyc i) : MvPolynomial (Fin 3) ℚ)) = ![X 1, X 2, X 0] := by
    funext i
    fin_cases i <;> rfl
  have hswp : (fun i => (X (swp i) : MvPolynomial (Fin 3) ℚ)) = ![X 1, X 0, X 2] := by
    funext i
    fin_cases i <;> rfl
  have hc : bind₁ (fun i => (X (cyc i) : MvPolynomial (Fin 3) ℚ)) v = v := by
    rw [hcyc]; exact hC
  have hs : bind₁ (fun i => (X (swp i) : MvPolynomial (Fin 3) ℚ)) v = v := by
    rw [hswp]; exact hS
  rcases perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · exact hc
  · rw [key cyc cyc hc]; exact hc
  · exact hs
  · rw [key cyc swp hs]; exact hc
  · rw [key (cyc * cyc) swp hs, key cyc cyc hc]; exact hc

/-- The ℂ-form of the symmetry hypothesis of `NormalJet.periodC_eq_zero_of_J_zero`. -/
theorem complex_perm (v : MvPolynomial (Fin 3) ℚ)
    (hS : bind₁ (![X 1, X 0, X 2] : HSymmetry.HSub3) v = v)
    (hC : bind₁ (![X 1, X 2, X 0] : HSymmetry.HSub3) v = v) :
    ∀ p : Equiv.Perm (Fin 3), bind₁ (fun i => (X (p i) : MvPolynomial (Fin 3) ℂ)) (cpx v) = cpx v := by
  intro p
  have h : cpx (bind₁ (fun i => (X (p i) : MvPolynomial (Fin 3) ℚ)) v) = cpx v := by
    rw [perm_invariant v hS hC p]
  unfold cpx at h ⊢
  rw [map_bind₁] at h
  simp only [map_X] at h
  exact h

/-! ### The theorem -/

/-- **`p_parity` with `hCv` discharged by `J_v = 0`**. For a homogeneous symmetric
odd `v`, `J_v = 0` (the Bernoulli obstruction of the complexification of `v`) gives `C_v = 0`,
hence the relation `hCv` of `HSymmetry.p_parity`, and so its conclusions. -/
theorem p_parity_of_J_zero {m : ℕ} (hm : Odd m) (v : MvPolynomial (Fin 3) ℚ)
    (hv : v.IsHomogeneous m)
    (hS : bind₁ (![X 1, X 0, X 2] : HSymmetry.HSub3) v = v)
    (hC : bind₁ (![X 1, X 2, X 0] : HSymmetry.HSub3) v = v)
    (p : MvPolynomial (Fin 2) ℚ) (hp₁ : pderiv 0 p = -HSymmetry.HJet v)
    (hp₀ : bind₁ (![0, X 1] : HSymmetry.HSub2) p = 0)
    (hJ : bernoulliObstruction (complexify v hv) = 0) :
    bind₁ (![-X 0, X 1] : HSymmetry.HSub2) (HSymmetry.HJet v) = HSymmetry.HJet v ∧
      bind₁ (![X 0, -X 1] : HSymmetry.HSub2) (HSymmetry.HJet v) = HSymmetry.HJet v ∧
      bind₁ (![-X 0, X 1] : HSymmetry.HSub2) p = -p ∧
      bind₁ (![X 0, -X 1] : HSymmetry.HSub2) p = p ∧
      pderiv 0 p = bind₁ (![X 1, -X 0] : HSymmetry.HSub2) (pderiv 0 p) := by
  have hP0 : bind₁ NormalJet.tauSub (NormalJet.periodP (cpx v)) - NormalJet.periodP (cpx v) -
      bind₁ NormalJet.hFrame (cpx v) = 0 :=
    NormalJet.periodC_eq_zero_of_J_zero (complexify v hv) hm (complex_perm v hS hC) hJ
  rw [periodP_eq_liftJ v p hp₁ hp₀] at hP0
  have h2 : liftJ (bind₁ (![X 0 - X 1, X 1] : HSymmetry.HSub2) p - p - HSymmetry.hJet v) = 0 := by
    rw [liftJ_sub, liftJ_sub, liftJ_bind_tau, liftJ_jet]
    exact hP0
  have hCv : bind₁ (![X 0 - X 1, X 1] : HSymmetry.HSub2) p - p - HSymmetry.hJet v = 0 :=
    liftJ_injective (h2.trans liftJ_zero.symm)
  exact HSymmetry.p_parity hm v hv hS hC p hp₁ hp₀ hCv

end TernaryPeriodPolynomials.Argument.Identities.HSymmetryJ
