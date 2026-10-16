module

public import TernaryPeriodPolynomials.SymmetricSolution.NormalJet.Operators
public import TernaryPeriodPolynomials.SymmetricSolution.NormalJet.Line
public import TernaryPeriodPolynomials.SymmetricSolution.NormalJet.Calculus
public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.RadicalBernoulli

@[expose] public section


/-!
# The second normal-jet identity: `∂_Z J_v |_{Z=3Y} = τ² B(3𝒟) B(𝒟) C_v` (MR-7)

Formalized by Claude Sonnet 5.5.  Proof of Lemma `lem:period-extraction`, equation `eq:normal-jet`.

For an odd symmetric homogeneous `v` of degree `m` (no norm hypothesis): `h(X,Y) = v(-Y,X,Y-X)`, `H = (∂₁+∂₂)v(-Y,X,Y-X)`, `p = -∫₀^X H(s,Y) ds` (`antiderivX`, `periodP`),
`C_v = p(X-Y,Y) - p(X,Y) - h` (`periodC`), `𝒟 = -Y∂_X` (`Dop`), `τ = e^𝒟` the translation `X ↦ X - Y` (`bind₁ tauSub`), `B(t) = bernoulliOperator`.
`phi` evaluates power series at `𝒟` (a ring homomorphism into `End(ℂ[X,Y,Z]_m)`), and the three cancellations of the paper enter through `normal_jet_operator_identity`
(`B(3t)(1+eᵗ+e²ᵗ) = 3B(t)`, `-B + tB'(3t)(1+eᵗ+e²ᵗ) + te²ᵗB(3t) = -e²ᵗB(3t)B`, `B(eᵗ-1) = t`).
The result is `normal_jet_derivative` (any `p` with `∂_X p = -H`) and `normal_jet_derivative_literal` (the paper's `p`).
-/

open MvPolynomial GeneralEisenstein PowerSeries

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities.NormalJet

open TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

section Phi

variable {m : ℕ}

/-- `𝒟 = -Y ∂_X` on homogeneous polynomials of degree `m`. -/
def Dop (hm : 0 < m) : Module.End ℂ (HomogeneousPoly m) :=
  polynomialTranslationDerivative m hm (X 1) x1_hom

theorem Dop_nil (hm : 0 < m) : (Dop hm) ^ (m + 1) = 0 :=
  polynomialTranslationDerivative_nilpotent m hm (X 1) x1_hom indep1

theorem Dop_val (hm : 0 < m) (q : HomogeneousPoly m) : ((Dop hm) q).val = -X 1 * pderiv 0 q.val := rfl

/-- Evaluation of power series at `𝒟`. -/
abbrev phi (hm : 0 < m) : PowerSeries ℂ →+* Module.End ℂ (HomogeneousPoly m) :=
  evHom (Dop hm) (Nat.succ_pos m) (Dop_nil hm)

theorem phi_X (hm : 0 < m) : phi hm PowerSeries.X = Dop hm :=
  evHom_X (Dop hm) (by omega) (Dop_nil hm)

theorem phi_C (hm : 0 < m) (c : ℂ) : phi hm (PowerSeries.C c) = algebraMap ℂ _ c := by
  change Polynomial.aeval (Dop hm) (PowerSeries.trunc (m + 1) (PowerSeries.C c)) = _
  rw [PowerSeries.trunc_C, Polynomial.aeval_C]

theorem phi_exp_val (hm : 0 < m) (q : HomogeneousPoly m) :
    (phi hm (PowerSeries.exp ℂ) q).val = bind₁ tauSub q.val := by
  have h : phi hm (PowerSeries.exp ℂ) =
      ∑ k ∈ Finset.range (m + 1), (k.factorial : ℂ)⁻¹ • (Dop hm) ^ k :=
    aeval_trunc_exp (m + 1) (Dop hm)
  rw [h]
  simp only [LinearMap.sum_apply, Submodule.coe_sum, LinearMap.smul_apply, Submodule.coe_smul]
  have := homogeneous_translation_taylor q (X 1)
  refine Eq.trans ?_ this.symm
  exact Finset.sum_congr rfl fun k _ => by
    rw [← polynomialTranslationDerivative_pow m hm (X 1) x1_hom indep1 q k]
    rfl

theorem phi_bernoulli_val (hm : 0 < m) (q : HomogeneousPoly m) :
    (phi hm (bernoulliPowerSeries ℂ) q).val = bernoulliOperator m (X 1) q.val := by
  have h : phi hm (bernoulliPowerSeries ℂ) =
      ∑ k ∈ Finset.range (m + 1), ((bernoulli k : ℂ) / (k.factorial : ℂ)) • (Dop hm) ^ k :=
    aeval_trunc_bernoulli (m + 1) (Dop hm)
  rw [h]
  exact (bernoulliOperator_eq_endomorphism m hm (X 1) x1_hom indep1 q).symm

theorem Dop_three (hm : 0 < m) :
    polynomialTranslationDerivative m hm (3 * X 1) x3_hom = (3 : ℂ) • Dop hm := by
  apply LinearMap.ext; intro p; apply Subtype.ext
  show -(3 * X 1) * pderiv 0 p.val = (3 : ℂ) • (-(X 1) * pderiv 0 p.val)
  rw [MvPolynomial.smul_eq_C_mul, ← three_eq]; ring

theorem phi_rescale_val (hm : 0 < m) (q : HomogeneousPoly m) :
    (phi hm (rescale (3 : ℂ) (bernoulliPowerSeries ℂ)) q).val =
      bernoulliOperator m (3 * X 1) q.val := by
  have first : phi hm (rescale (3 : ℂ) (bernoulliPowerSeries ℂ)) =
      ∑ k ∈ Finset.range (m + 1), ((bernoulli k : ℂ) / (k.factorial : ℂ)) • ((3 : ℂ) • Dop hm) ^ k := by
    change Polynomial.aeval (Dop hm) (PowerSeries.trunc (m + 1) (rescale (3 : ℂ) (bernoulliPowerSeries ℂ))) = _
    rw [Polynomial.aeval_def, PowerSeries.eval₂_trunc_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k _
    have hc : coeff k (rescale (3 : ℂ) (bernoulliPowerSeries ℂ)) = 3 ^ k * ((bernoulli k : ℂ) / (k.factorial : ℂ)) := by
      simp [coeff_rescale, bernoulliPowerSeries]
    rw [hc, ← Algebra.smul_def, smul_pow, smul_smul, mul_comm]
  rw [first, ← Dop_three hm]
  exact (bernoulliOperator_eq_endomorphism m hm (3 * X 1) x3_hom indep3 q).symm



theorem phi_XU_val (hm : 0 < m) (q : HomogeneousPoly m) :
    (phi hm (PowerSeries.X * rescale (3 : ℂ) (d⁄dX (bernoulliPowerSeries ℂ))) q).val =
      X 1 * bernoulliParam m (3 * X 1) q.val := by
  change ((evHom (Dop hm) (Nat.succ_pos m) (Dop_nil hm)) _ q).val = _
  rw [evHom_apply]
  simp only [LinearMap.sum_apply, Submodule.coe_sum, LinearMap.smul_apply, Submodule.coe_smul]
  unfold bernoulliParam
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hpow : ∀ k, (((Dop hm) ^ k) q).val = (-X 1) ^ k * ((fun x : Poly => pderiv 0 x)^[k]) q.val :=
    fun k => polynomialTranslationDerivative_pow m hm (X 1) x1_hom indep1 q k
  rw [hpow]
  cases r with
  | zero => simp [PowerSeries.coeff_zero_X_mul]
  | succ j =>
    rw [PowerSeries.coeff_succ_X_mul, coeff_rescale, coeff_derivative]
    have h3 : (-(3 * X 1 : Poly)) = MvPolynomial.C 3 * (-X 1) := by rw [three_eq]; ring
    rw [MvPolynomial.smul_eq_C_mul, Nat.add_sub_cancel, h3, mul_pow, pow_succ]
    simp only [bernoulliPowerSeries, coeff_mk, map_mul, map_pow, map_neg, map_add, map_natCast,
      map_one, map_div₀, eq_ratCast, Nat.cast_succ, Nat.factorial_succ, Nat.cast_mul]
    ring


end Phi

section Relations

variable {m : ℕ}

theorem bernoulliParam_neg (n : ℕ) (t p : Poly) :
    bernoulliParam n t (-p) = -bernoulliParam n t p := by
  have h : ∀ r : ℕ, ((fun x : Poly => pderiv 0 x)^[r]) (-p) =
      -((fun x : Poly => pderiv 0 x)^[r]) p := by
    intro r
    induction r with
    | zero => rfl
    | succ r ih => rw [Function.iterate_succ_apply', ih, map_neg, Function.iterate_succ_apply']
  simp only [bernoulliParam, h, mul_neg, Finset.sum_neg_distrib]

/-- `X₁ · ∂_i v(-Y, X, Y - X)` as a homogeneous polynomial of degree `m`. -/
def wOf (hm : 0 < m) (v : HomogeneousPoly m) (i : Fin 3) : HomogeneousPoly m :=
  ⟨X 1 * bind₁ hFrame (pderiv i v.val), by
    have hv : v.val.IsHomogeneous m := (mem_homogeneousSubmodule m v.val).mp v.2
    have h1 := pderiv_homogeneous v.val hv i
    have h2 := TernaryPoly.isHomogeneous_bind₁_linear h1 hFrame hFrame_hom
    have h3 := x1_hom.mul h2
    rw [show 1 + (m - 1) = m by omega] at h3
    exact (mem_homogeneousSubmodule m _).mpr h3⟩

theorem wOf_val (hm : 0 < m) (v : HomogeneousPoly m) (i : Fin 3) :
    (wOf hm v i).val = X 1 * bind₁ hFrame (pderiv i v.val) := rfl

theorem Dop_hOf (hm : 0 < m) (v : HomogeneousPoly m) :
    Dop hm (hOf v) = wOf hm v 2 - wOf hm v 1 := by
  apply Subtype.ext
  rw [Dop_val, hOf_val, Submodule.coe_sub, wOf_val, wOf_val, pderiv_zero_hFrame]
  ring

theorem Dop_antiderivative (hm : 0 < m) (v p : HomogeneousPoly m)
    (hp : pderiv 0 p.val = -(bind₁ hFrame (pderiv 0 v.val + pderiv 1 v.val))) :
    Dop hm p = wOf hm v 0 + wOf hm v 1 := by
  apply Subtype.ext
  rw [Dop_val, hp, Submodule.coe_add, wOf_val, wOf_val, map_add]
  ring

end Relations


section Final

variable {m : ℕ}

theorem tau_X1_mul (x : Poly) : bind₁ tauSub (X 1 * x) = X 1 * bind₁ tauSub x := by
  rw [map_mul, bind₁_X_right]; rfl

theorem smul_three_val (x : Poly) : (3 : ℂ) • x = 3 * x := by
  rw [MvPolynomial.smul_eq_C_mul, ← three_eq]

/-- The four power series occurring in the operator identity, as named operators. -/
theorem V1 (hm : 0 < m) (hh : HomogeneousPoly m) :
    ((phi hm (-bernoulliPowerSeries ℂ +
        (PowerSeries.X * rescale (3 : ℂ) (d⁄dX (bernoulliPowerSeries ℂ))) *
          (1 + exp ℂ + exp ℂ * exp ℂ))) • hh).val =
      -bernoulliOperator m (X 1) hh.val +
        X 1 * bernoulliParam m (3 * X 1) (hh.val + bind₁ tauSub hh.val + bind₁ tauSub (bind₁ tauSub hh.val)) := by
  rw [map_add, map_neg, map_mul (phi hm) (PowerSeries.X * rescale (3 : ℂ) (d⁄dX (bernoulliPowerSeries ℂ))) _,
    map_add, map_add, map_one, map_mul (phi hm) (exp ℂ) (exp ℂ)]
  change (((-phi hm (bernoulliPowerSeries ℂ)) +
    phi hm (PowerSeries.X * rescale (3 : ℂ) (d⁄dX (bernoulliPowerSeries ℂ))) *
      (1 + phi hm (exp ℂ) + phi hm (exp ℂ) * phi hm (exp ℂ))) hh).val = _
  rw [LinearMap.add_apply, LinearMap.neg_apply, Module.End.mul_apply, Submodule.coe_add,
    Submodule.coe_neg, phi_bernoulli_val, phi_XU_val]
  simp only [LinearMap.add_apply, Module.End.one_apply, Module.End.mul_apply, Submodule.coe_add,
    phi_exp_val]

theorem V2 (hm : 0 < m) (w1 : HomogeneousPoly m) :
    ((phi hm (PowerSeries.C (3 : ℂ) * bernoulliPowerSeries ℂ -
        rescale (3 : ℂ) (bernoulliPowerSeries ℂ) * (1 + exp ℂ))) • w1).val =
      3 * bernoulliOperator m (X 1) w1.val -
        bernoulliOperator m (3 * X 1) (w1.val + bind₁ tauSub w1.val) := by
  rw [map_sub, map_mul, map_mul, phi_C, map_add, map_one]
  change ((algebraMap ℂ (Module.End ℂ (HomogeneousPoly m)) 3 * phi hm (bernoulliPowerSeries ℂ) -
    phi hm (rescale (3 : ℂ) (bernoulliPowerSeries ℂ)) * (1 + phi hm (exp ℂ))) w1).val = _
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, Submodule.coe_sub,
    Module.algebraMap_end_apply, Submodule.coe_smul, smul_three_val, phi_bernoulli_val, phi_rescale_val]
  simp only [LinearMap.add_apply, Module.End.one_apply, Submodule.coe_add, phi_exp_val]

theorem V3 (hm : 0 < m) (w3 : HomogeneousPoly m) :
    ((phi hm (rescale (3 : ℂ) (bernoulliPowerSeries ℂ) * (exp ℂ * exp ℂ))) • w3).val =
      bernoulliOperator m (3 * X 1) (bind₁ tauSub (bind₁ tauSub w3.val)) := by
  rw [map_mul, map_mul (phi hm) (exp ℂ) (exp ℂ)]
  change ((phi hm (rescale (3 : ℂ) (bernoulliPowerSeries ℂ)) *
    (phi hm (exp ℂ) * phi hm (exp ℂ))) w3).val = _
  rw [Module.End.mul_apply, phi_rescale_val, Module.End.mul_apply, phi_exp_val, phi_exp_val]

theorem V4 (hm : 0 < m) (p hh : HomogeneousPoly m) :
    ((phi hm (exp ℂ * exp ℂ * rescale (3 : ℂ) (bernoulliPowerSeries ℂ) * bernoulliPowerSeries ℂ)) •
        (phi hm (exp ℂ) • p - p - hh)).val =
      bind₁ tauSub (bind₁ tauSub (bernoulliOperator m (3 * X 1) (bernoulliOperator m (X 1)
        (bind₁ tauSub p.val - p.val - hh.val)))) := by
  rw [map_mul, map_mul, map_mul]
  change ((phi hm (exp ℂ) * phi hm (exp ℂ) * phi hm (rescale (3 : ℂ) (bernoulliPowerSeries ℂ)) *
    phi hm (bernoulliPowerSeries ℂ)) (phi hm (exp ℂ) p - p - hh)).val = _
  rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, phi_exp_val, phi_exp_val,
    phi_rescale_val, phi_bernoulli_val, Submodule.coe_sub, Submodule.coe_sub, phi_exp_val]


/-- **The second normal-jet identity** (`eq:normal-jet`, second display): for odd symmetric `v` of degree `m` and
`p` homogeneous of degree `m` with `∂_X p = -(∂₁v + ∂₂v)(-Y,X,Y-X)` (the paper's `p = -∫₀^X H(s,Y) ds`),
`∂_Z J_v|_{Z=3Y} = τ² B(3𝒟) B(𝒟) C_v`, `C_v = p(X-Y,Y) - p(X,Y) - h(X,Y)`. -/
theorem normal_jet_derivative (v : HomogeneousPoly m) (hodd : Odd m)
    (hs : ∀ p : Equiv.Perm (Fin 3), bind₁ (fun i => (X (p i) : Poly)) v.val = v.val)
    (p : HomogeneousPoly m)
    (hp : pderiv 0 p.val = -(bind₁ hFrame (pderiv 0 v.val + pderiv 1 v.val))) :
    bind₁ sigma3 (pderiv 2 (bernoulliObstruction v)) =
      bind₁ tauSub (bind₁ tauSub (bernoulliOperator m (3 * X 1) (bernoulliOperator m (X 1)
        (bind₁ tauSub p.val - p.val - bind₁ hFrame v.val)))) := by
  have hm : 0 < m := hodd.pos
  rw [bind_sigma3_pderiv_two_obstruction v hodd hs]
  have key := normal_jet_operator_identity (Dop hm) (N := m + 1) (by omega) (Dop_nil hm)
    (hOf v) (wOf hm v 0) (wOf hm v 1) (wOf hm v 2) p (Dop_hOf hm v) (Dop_antiderivative hm v p hp)
  have keyv := congrArg Subtype.val key
  rw [Submodule.coe_add, Submodule.coe_add] at keyv
  rw [V1 hm, V2 hm, V3 hm, V4 hm] at keyv
  simp only [hOf_val, wOf_val] at keyv
  rw [← keyv]
  have e1 : bernoulliOperator m (X 1) (X 1 * bind₁ hFrame (pderiv 0 v.val)) =
      X 1 * bernoulliOperator m (X 1) (bind₁ hFrame (pderiv 0 v.val)) :=
    TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers.bernoulliOperator_mul_constant
      m (X 1) (X 1) _ indep1
  have e3 : ∀ y : Poly, bernoulliOperator m (3 * X 1) (X 1 * y) =
      X 1 * bernoulliOperator m (3 * X 1) y := fun y =>
    TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers.bernoulliOperator_mul_constant
      m (3 * X 1) (X 1) y indep1
  have hy : ∀ a b c : Poly, a - b + c = (a + c) + -b := fun a b c => by ring
  rw [bernoulliOperator_neg m (X 1), bernoulliParam_neg, hy,
    TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers.bernoulliOperator_add,
    bernoulliOperator_neg m (3 * X 1)]
  simp only [tau_X1_mul, e1, ← mul_add, e3]
  ring

end Final

section Literal

variable {m : ℕ}

/-- The polynomial antiderivative in `X`, `∫₀^X c(s, Y, Z) ds`: `X^a ↦ X^(a+1)/(a+1)` on each monomial. -/
def antiderivX (c : Poly) : Poly :=
  ∑ s ∈ c.support, monomial (s + Finsupp.single 0 1) (c.coeff s / ((s 0 : ℂ) + 1))

theorem pderiv_antiderivX (c : Poly) : pderiv 0 (antiderivX c) = c := by
  conv_rhs => rw [c.as_sum]
  unfold antiderivX
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [pderiv_monomial]
  simp only [add_tsub_cancel_right, Finsupp.add_apply, Finsupp.single_eq_same]
  congr 1
  push_cast
  have : ((s 0 : ℂ) + 1) ≠ 0 := by
    have : ((s 0 + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
    simpa using this
  field_simp

theorem antiderivX_isHomogeneous (c : Poly) (n : ℕ) (hc : c.IsHomogeneous n) :
    (antiderivX c).IsHomogeneous (n + 1) := by
  unfold antiderivX
  refine IsHomogeneous.sum _ _ (n + 1) fun s hs => ?_
  refine isHomogeneous_monomial _ ?_
  have := hc (mem_support_iff.mp hs)
  have h2 : Finsupp.degree s = n := by rw [Finsupp.degree_eq_weight_one]; exact this
  simp [h2]

/-- `H(X,Y) = (∂₁ + ∂₂)v(-Y, X, Y - X)`. -/
def periodH (v : Poly) : Poly := bind₁ hFrame (pderiv 0 v + pderiv 1 v)

/-- `p(X,Y) = -∫₀^X H(s,Y) ds`. -/
def periodP (v : Poly) : Poly := -antiderivX (periodH v)

/-- `C_v(X,Y) = p(X - Y, Y) - p(X, Y) - h(X, Y)`. -/
def periodC (v : Poly) : Poly := bind₁ tauSub (periodP v) - periodP v - bind₁ hFrame v

theorem periodP_isHomogeneous (v : HomogeneousPoly m) (hm : 0 < m) :
    (periodP v.val).IsHomogeneous m := by
  have hv : v.val.IsHomogeneous m := (mem_homogeneousSubmodule m v.val).mp v.2
  have h0 := pderiv_homogeneous v.val hv 0
  have h1 := pderiv_homogeneous v.val hv 1
  have hH : (periodH v.val).IsHomogeneous (m - 1) :=
    TernaryPoly.isHomogeneous_bind₁_linear (h0.add h1) hFrame hFrame_hom
  have := (antiderivX_isHomogeneous _ _ hH).neg
  rwa [show m - 1 + 1 = m by omega] at this

/-- **`eq:normal-jet`, second identity, with the paper's `p` and `C_v`:**
`∂_Z J_v |_{Z=3Y} = τ² B(3𝒟) B(𝒟) C_v`. -/
theorem normal_jet_derivative_literal (v : HomogeneousPoly m) (hodd : Odd m)
    (hs : ∀ p : Equiv.Perm (Fin 3), bind₁ (fun i => (X (p i) : Poly)) v.val = v.val) :
    bind₁ sigma3 (pderiv 2 (bernoulliObstruction v)) =
      bind₁ tauSub (bind₁ tauSub (bernoulliOperator m (3 * X 1)
        (bernoulliOperator m (X 1) (periodC v.val)))) := by
  have hm : 0 < m := hodd.pos
  have hp : pderiv 0 (periodP v.val) = -(bind₁ hFrame (pderiv 0 v.val + pderiv 1 v.val)) := by
    rw [periodP, map_neg, pderiv_antiderivX]; rfl
  exact normal_jet_derivative v hodd hs
    ⟨periodP v.val, (mem_homogeneousSubmodule m _).mpr (periodP_isHomogeneous v hm)⟩ hp

end Literal

end TernaryPeriodPolynomials.Argument.Identities.NormalJet
