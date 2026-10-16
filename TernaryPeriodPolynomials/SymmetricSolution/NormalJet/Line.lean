module

public import TernaryPeriodPolynomials.SymmetricSolution.Bernoulli.Triple
public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.RadicalBernoulli
public import TernaryPeriodPolynomials.Building.BoundaryApartments
public import TernaryPeriodPolynomials.Polynomial.Homogeneous
public import TernaryPeriodPolynomials.Polynomial.Parity

@[expose] public section


/-!
# The normal jet: `J_v(X, Y, 3Y) = 0` for odd symmetric `v`, without the norm hypothesis (MR-7, first identity)

Formalized by Claude Sonnet 5.5.  Proof of Lemma `lem:period-extraction`, equation `eq:normal-jet`, first identity, with the displayed values
`ψ₁|_{Z=3Y} = -h`, `ψ₂|_{Z=3Y} = -(1 + τ + τ²) h`, `h(X,Y) = v(-Y, X, Y-X)`, `τ` the translation `X ↦ X - Y`, and the cancellation `B(3t)(1 + eᵗ + e²ᵗ) = 3 B(t)` (`bernoulli_triple`).
-/

open MvPolynomial GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities.NormalJet

open TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
open TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers (polynomialValue polynomialValue_bind)

section Commute

/-- The Bernoulli operator commutes with a substitution that fixes `X` and sends the other variables to polynomials independent of `X`. -/
theorem bind_bernoulliOperator (σ : Fin 3 → Poly)
    (hσ : ∀ i, pderiv 0 (σ i) = bind₁ σ (pderiv 0 (X i))) (n : ℕ) (t p : Poly) :
    bind₁ σ (bernoulliOperator n t p) = bernoulliOperator n (bind₁ σ t) (bind₁ σ p) := by
  have hd := TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers.pderiv_bind_commutes σ hσ
  unfold bernoulliOperator
  simp only [map_sum, map_mul, map_pow, map_neg, bind₁_C_right]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers.derivative_iterate_bind_commutes σ hd]

end Commute


section Frames

theorem three_eq : (3 : Poly) = C 3 := (map_ofNat C 3).symm

theorem pderiv_three : pderiv (0 : Fin 3) (3 : Poly) = 0 := by rw [three_eq]; exact pderiv_C

/-- The normal-jet substitution `Z = 3Y`. -/
def sigma3 : Fin 3 → Poly := ![X 0, X 1, 3 * X 1]

theorem sigma3_two : sigma3 2 = 3 * X 1 := rfl
theorem sigma3_one : sigma3 1 = X 1 := rfl
theorem sigma3_zero : sigma3 0 = X 0 := rfl

theorem sigma3_deriv (i : Fin 3) : pderiv 0 (sigma3 i) = bind₁ sigma3 (pderiv 0 (X i)) := by
  fin_cases i
  · simp [sigma3]
  · simp [sigma3]
  · simp [sigma3, pderiv_three]

/-- `h(X, Y) = v(-Y, X, Y - X)`. -/
def hFrame : Fin 3 → Poly := ![-X 1, X 0, X 1 - X 0]

/-- The translation `τ : X ↦ X - Y`. -/
def tauSub : Fin 3 → Poly := ![X 0 - X 1, X 1, X 2]

variable {m : ℕ}

/-- Odd degree: simultaneous negation of the arguments negates `v`. -/
theorem bind_neg_odd (v : HomogeneousPoly m) (hodd : Odd m) :
    bind₁ (fun i => -(X i : Poly)) v.val = -v.val := by
  have hv : v.val.IsHomogeneous m := (mem_homogeneousSubmodule m v.val).mp v.2
  have h := TernaryPoly.homogeneous_bind_smul hv (-1 : ℂ)
  have ht : (fun i : Fin 3 => (-1 : ℂ) • (X i : Poly)) = fun i => -(X i : Poly) := by
    funext i; simp
  rw [ht, hodd.neg_one_pow, neg_one_smul] at h
  exact h

theorem bind_frame_neg (v : HomogeneousPoly m) (hodd : Odd m) (F G : Fin 3 → Poly)
    (hFG : ∀ i, bind₁ F (-(X i : Poly)) = G i) : bind₁ G v.val = -bind₁ F v.val := by
  have h1 := congrArg (bind₁ F) (bind_neg_odd v hodd)
  rw [map_neg, bind₁_bind₁] at h1
  have : (fun i => bind₁ F (-(X i : Poly))) = G := funext hFG
  rw [this] at h1
  exact h1

end Frames


section Normal

variable {m : ℕ}

theorem bind_comp_coords (σ F G : Fin 3 → Poly) (hFG : ∀ i, bind₁ σ (F i) = G i) (p : Poly) :
    bind₁ σ (bind₁ F p) = bind₁ G p := by
  rw [bind₁_bind₁, funext hFG]

/-- First frame: `ψ₁|_{Z=3Y} = -h`. -/
theorem psi1_at_three (v : HomogeneousPoly m) (hodd : Odd m) :
    bind₁ sigma3 (bind₁ ![X 2 - 2 * X 1, -X 0, X 0 - X 1] v.val) = -bind₁ hFrame v.val := by
  have e1 : ∀ i, bind₁ sigma3 ((![X 2 - 2 * X 1, -X 0, X 0 - X 1] : Fin 3 → Poly) i) =
      (![X 1, -X 0, X 0 - X 1] : Fin 3 → Poly) i := by
    intro i
    fin_cases i
    · simp [sigma3_two, sigma3_one, map_ofNat]; ring
    · simp [sigma3_zero]
    · simp [sigma3_one, sigma3_zero]
  have e2 : ∀ i, bind₁ hFrame (-(X i : Poly)) = (![X 1, -X 0, X 0 - X 1] : Fin 3 → Poly) i := by
    intro i
    fin_cases i
    · simp [hFrame]
    · simp [hFrame]
    · simp [hFrame]
  rw [bind_comp_coords sigma3 _ _ e1]
  exact bind_frame_neg v hodd hFrame _ e2

/-- The frame of `τ h`. -/
def T1 : Fin 3 → Poly := ![-X 1, X 0 - X 1, 2 * X 1 - X 0]

/-- The frame of `τ² h`. -/
def T2 : Fin 3 → Poly := ![-X 1, X 0 - 2 * X 1, 3 * X 1 - X 0]

theorem psi2_term3 (v : HomogeneousPoly m) (hodd : Odd m) :
    bind₁ sigma3 (bind₁ ![X 2 - 2 * X 1, X 1 - X 0, X 0 - 2 * X 1] v.val) = -bind₁ T1 v.val := by
  have e1 : ∀ i, bind₁ sigma3 ((![X 2 - 2 * X 1, X 1 - X 0, X 0 - 2 * X 1] : Fin 3 → Poly) i) =
      (![X 1, X 1 - X 0, X 0 - 2 * X 1] : Fin 3 → Poly) i := by
    intro i
    fin_cases i
    · simp [sigma3_two, sigma3_one, map_ofNat]; ring
    · simp [sigma3_one, sigma3_zero]
    · simp [sigma3_one, sigma3_zero, map_ofNat]
  have e2 : ∀ i, bind₁ T1 (-(X i : Poly)) = (![X 1, X 1 - X 0, X 0 - 2 * X 1] : Fin 3 → Poly) i := by
    intro i
    fin_cases i
    · simp [T1]
    · simp [T1]
    · simp [T1]
  rw [bind_comp_coords sigma3 _ _ e1]
  exact bind_frame_neg v hodd T1 _ e2

theorem psi2_term2 (v : HomogeneousPoly m)
    (hs : ∀ p : Equiv.Perm (Fin 3), bind₁ (fun i => (X (p i) : Poly)) v.val = v.val) :
    bind₁ sigma3 (bind₁ ![X 2 - X 0, X 0 - 2 * X 1, -X 1] v.val) = bind₁ T2 v.val := by
  have e1 : ∀ i, bind₁ sigma3 ((![X 2 - X 0, X 0 - 2 * X 1, -X 1] : Fin 3 → Poly) i) =
      (![3 * X 1 - X 0, X 0 - 2 * X 1, -X 1] : Fin 3 → Poly) i := by
    intro i
    fin_cases i
    · simp [sigma3_two, sigma3_zero]
    · simp [sigma3_one, sigma3_zero, map_ofNat]
    · simp [sigma3_one]
  rw [bind_comp_coords sigma3 _ _ e1]
  have h := congrArg (bind₁ (![3 * X 1 - X 0, X 0 - 2 * X 1, -X 1] : Fin 3 → Poly)) (hs (Equiv.swap 0 2))
  rw [bind₁_bind₁] at h
  rw [← h]
  have s0 : Equiv.swap (0 : Fin 3) 2 0 = 2 := by decide
  have s1 : Equiv.swap (0 : Fin 3) 2 1 = 1 := by decide
  have s2 : Equiv.swap (0 : Fin 3) 2 2 = 0 := by decide
  have hf : (fun i => bind₁ (![3 * X 1 - X 0, X 0 - 2 * X 1, -X 1] : Fin 3 → Poly) (X (Equiv.swap (0 : Fin 3) 2 i))) = T2 := by
    funext i
    fin_cases i
    · simp [T2, s0]
    · simp [T2, s1]
    · simp [T2, s2]
  rw [hf]

end Normal


section Operator

variable {m : ℕ}

theorem x1_hom : (X 1 : Poly).IsHomogeneous 1 := isHomogeneous_X ℂ 1

theorem x3_hom : (3 * X 1 : Poly).IsHomogeneous 1 := by
  rw [three_eq]; exact (isHomogeneous_X ℂ (1 : Fin 3)).C_mul 3

theorem indep1 : pderiv (0 : Fin 3) (X 1 : Poly) = 0 := by simp [pderiv_X]

theorem indep3 : pderiv (0 : Fin 3) (3 * X 1 : Poly) = 0 := by
  rw [pderiv_mul, pderiv_three]; simp [pderiv_X]

theorem hFrame_hom (i : Fin 3) : (hFrame i).IsHomogeneous 1 := by
  fin_cases i
  · exact (isHomogeneous_X ℂ (1 : Fin 3)).neg
  · exact isHomogeneous_X ℂ (0 : Fin 3)
  · exact (isHomogeneous_X ℂ (1 : Fin 3)).sub (isHomogeneous_X ℂ (0 : Fin 3))

/-- `h(X, Y) = v(-Y, X, Y - X)` as a homogeneous polynomial of the same degree as `v`. -/
def hOf (v : HomogeneousPoly m) : HomogeneousPoly m :=
  ⟨bind₁ hFrame v.val, (mem_homogeneousSubmodule m _).mpr
    (TernaryPoly.isHomogeneous_bind₁_linear ((mem_homogeneousSubmodule m _).mp v.2) hFrame hFrame_hom)⟩

theorem hOf_val (v : HomogeneousPoly m) : (hOf v).val = bind₁ hFrame v.val := rfl

/-- **`B(3Y ∂)(h + τh + τ²h) = 3 B(Y ∂) h`** at the polynomial level. -/
theorem bernoulli_three_translates (hm : 0 < m) (hh : HomogeneousPoly m) :
    bernoulliOperator m (3 * X 1) (hh.val + bind₁ tauSub hh.val + bind₁ tauSub (bind₁ tauSub hh.val)) =
      3 * bernoulliOperator m (X 1) hh.val := by
  let D := polynomialTranslationDerivative m hm (X 1) x1_hom
  let D3 := polynomialTranslationDerivative m hm (3 * X 1) x3_hom
  have hD3 : D3 = (3 : ℂ) • D := by
    apply LinearMap.ext; intro p; apply Subtype.ext
    show -(3 * X 1) * pderiv 0 p.val = (3 : ℂ) • (-(X 1) * pderiv 0 p.val)
    rw [smul_eq_C_mul, ← three_eq]; ring
  let E : Module.End ℂ (HomogeneousPoly m) :=
    ∑ k ∈ Finset.range (m+1), (k.factorial : ℂ)⁻¹ • D^k
  have hE : ∀ p : HomogeneousPoly m, (E p).val = bind₁ tauSub p.val := by
    intro p
    dsimp only [E, D]
    simp only [LinearMap.sum_apply, Submodule.coe_sum, LinearMap.smul_apply,
      Submodule.coe_smul, polynomialTranslationDerivative_pow m hm (X 1) x1_hom indep1]
    exact (homogeneous_translation_taylor p (X 1)).symm
  have hB1 : ∀ p : HomogeneousPoly m, bernoulliOperator m (X 1) p.val =
      ((∑ k ∈ Finset.range (m+1), ((bernoulli k : ℂ) / (k.factorial : ℂ)) • D^k) p).val :=
    fun p => bernoulliOperator_eq_endomorphism m hm (X 1) x1_hom indep1 p
  have hB3 : ∀ p : HomogeneousPoly m, bernoulliOperator m (3 * X 1) p.val =
      ((∑ k ∈ Finset.range (m+1), ((bernoulli k : ℂ) / (k.factorial : ℂ)) • ((3 : ℂ) • D)^k) p).val := by
    intro p
    rw [← hD3]
    exact bernoulliOperator_eq_endomorphism m hm (3 * X 1) x3_hom indep3 p
  have triple := bernoulli_triple D (N := m+1) (Nat.succ_pos m)
    (polynomialTranslationDerivative_nilpotent m hm (X 1) x1_hom indep1)
  have key := congrArg (fun T : Module.End ℂ (HomogeneousPoly m) => (T hh).val) triple
  have hq : (hh + E hh + E (E hh) : HomogeneousPoly m).val =
      hh.val + bind₁ tauSub hh.val + bind₁ tauSub (bind₁ tauSub hh.val) := by
    rw [Submodule.coe_add, Submodule.coe_add, hE (E hh), hE hh]
  rw [← hq, hB3]
  have hmul : ((∑ k ∈ Finset.range (m+1), ((bernoulli k : ℂ) / (k.factorial : ℂ)) • ((3 : ℂ) • D)^k)
      (hh + E hh + E (E hh)) : HomogeneousPoly m) =
      ((∑ k ∈ Finset.range (m+1), ((bernoulli k : ℂ) / (k.factorial : ℂ)) • ((3 : ℂ) • D)^k) *
        (1 + E + E * E)) hh := by
    simp [Module.End.mul_apply]
  rw [hmul]
  rw [key, hB1 hh]
  simp [smul_eq_C_mul, three_eq]

end Operator


section Main

variable {m : ℕ}

theorem tau_hFrame (v : HomogeneousPoly m) :
    bind₁ tauSub (bind₁ hFrame v.val) = bind₁ T1 v.val := by
  apply bind_comp_coords
  intro i
  fin_cases i
  · simp [tauSub, hFrame, T1]
  · simp [tauSub, hFrame, T1]
  · simp [tauSub, hFrame, T1]; ring

theorem tau_T1 (v : HomogeneousPoly m) :
    bind₁ tauSub (bind₁ T1 v.val) = bind₁ T2 v.val := by
  apply bind_comp_coords
  intro i
  fin_cases i
  · simp [tauSub, T1, T2]
  · simp [tauSub, T1, T2]; ring
  · simp [tauSub, T1, T2, map_ofNat]; ring

/-- **The normal jet vanishes** (`eq:normal-jet`, first identity): for odd symmetric `v` of any
norm, `J_v(X, Y, 3Y) = 0`, as an identity in `ℂ[X, Y]`. -/
theorem bind_sigma3_bernoulliObstruction (v : HomogeneousPoly m) (hodd : Odd m)
    (hs : ∀ p : Equiv.Perm (Fin 3), bind₁ (fun i => (X (p i) : Poly)) v.val = v.val) :
    bind₁ sigma3 (bernoulliObstruction v) = 0 := by
  have hm : 0 < m := hodd.pos
  have hX1 : bind₁ sigma3 (X 1 : Poly) = X 1 := by rw [bind₁_X_right]; rfl
  have hX2 : bind₁ sigma3 (X 2 : Poly) = 3 * X 1 := by rw [bind₁_X_right]; rfl
  unfold bernoulliObstruction
  simp only [map_sub, map_mul, map_add, bind_bernoulliOperator sigma3 sigma3_deriv, hX1, hX2,
    psi1_at_three v hodd, psi2_term2 v hs, psi2_term3 v hodd]
  have harg : -bind₁ hFrame v.val - bind₁ T2 v.val + -bind₁ T1 v.val =
      -(bind₁ hFrame v.val + bind₁ tauSub (bind₁ hFrame v.val) +
        bind₁ tauSub (bind₁ tauSub (bind₁ hFrame v.val))) := by
    rw [tau_hFrame, tau_T1]; ring
  rw [harg, TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers.bernoulliOperator_neg,
    TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers.bernoulliOperator_neg]
  have h3 := bernoulli_three_translates hm (hOf v)
  rw [hOf_val] at h3
  rw [h3]
  ring

/-- The same, as vanishing of the values on the line `Z = 3Y`. -/
theorem J_normal_line (v : HomogeneousPoly m) (hodd : Odd m)
    (hs : ∀ p : Equiv.Perm (Fin 3), bind₁ (fun i => (X (p i) : Poly)) v.val = v.val)
    (a b : ℂ) : polynomialValue (bernoulliObstruction v) a b (3 * b) = 0 := by
  have h := congrArg (fun P : Poly => polynomialValue P a b 0) (bind_sigma3_bernoulliObstruction v hodd hs)
  rw [polynomialValue_bind] at h
  have coords : (fun i => polynomialValue (sigma3 i) a b 0) = ![a, b, 3 * b] := by
    funext i
    fin_cases i <;> simp [polynomialValue, sigma3]
  rw [coords] at h
  simpa [polynomialValue] using h

end Main

end TernaryPeriodPolynomials.Argument.Identities.NormalJet
