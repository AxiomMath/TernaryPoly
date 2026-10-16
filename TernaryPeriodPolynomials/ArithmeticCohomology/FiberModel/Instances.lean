module

public import TernaryPeriodPolynomials.SymmetricSolution.SinglePole.Action
public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.Spec
public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.Lemma43

@[expose] public section


/-!
# Polynomial and rational-function coefficients

The two coefficient modules of Lemma 4.3: the polynomial ring `ℚ[x,y,z]` and its field of
fractions, each with the untwisted substitution action `ρ₀` of `GL₃(ℤ)` and the determinant
twist `ρ = ρ_{-1}` (that is, `E_{·,1}`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FiberModel

open TernaryPoly TernaryPoly.ModThreeGoodAction TernaryPoly.OrdinaryApartmentFrames

section

variable {M : Type*} [AddCommGroup M] [Module ℚ M]

/-- A determinant twist by `-1` of a representation of `GL₃(ℚ)` is the determinant twist of
the restriction to `GL₃(ℤ)`. -/
theorem isTwist_of_det (U R₀ R₁ : Representation ℚ PolynomialGLAction.GL3 M)
    (h₀ : ∀ g x, R₀ g x = U g x)
    (h₁ : ∀ g x, R₁ g x = ((Matrix.GeneralLinearGroup.det g : ℚˣ) : ℚ) ^ (-1 : ℤ) • U g x) :
    IsTwist (R₀.comp ReferenceCoefficientMatrices.rational)
      (R₁.comp ReferenceCoefficientMatrices.rational) := by
  intro g x
  change R₁ (ReferenceCoefficientMatrices.rational g) x = _ • R₀ (ReferenceCoefficientMatrices.rational g) x
  rw [h₁, h₀, rational_det, zpow_neg_one]
  rcases Int.units_eq_one_or (Matrix.GeneralLinearGroup.det g) with h | h
  · have h' : g.val.det = 1 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply, h]; rfl
    rw [h, h']
    simp
  · have h' : g.val.det = -1 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply, h]; rfl
    rw [h, h']
    simp

end

/-- The untwisted substitution action of `GL₃(ℤ)` on `ℚ[x,y,z]`. -/
abbrev polyRho0 : Representation ℚ IntegralGL (MvPolynomial (Fin 3) ℚ) :=
  ReferenceCoefficientMatrices.coefficientAction 0

/-- The determinant-twisted action `g · f(x) = det(g)^{-1} f(g⁻¹ x)` on `ℚ[x,y,z]`. -/
abbrev polyRho : Representation ℚ IntegralGL (MvPolynomial (Fin 3) ℚ) :=
  ReferenceCoefficientMatrices.coefficientAction (-1)

theorem determinantCharacter_zero (g : PolynomialGLAction.GL3) :
    PolynomialGLAction.determinantCharacter 0 g = 1 := by
  unfold PolynomialGLAction.determinantCharacter
  simp

theorem isTwist_poly : IsTwist polyRho0 polyRho := by
  apply isTwist_of_det (PolynomialGLAction.untwisted) (PolynomialGLAction.action 0)
    (PolynomialGLAction.action (-1))
  · intro g x
    rw [PolynomialGLAction.action_apply, determinantCharacter_zero, one_smul]
    rfl
  · intro g x
    rw [PolynomialGLAction.action_apply]
    rfl


theorem slash_poly (x : MvPolynomial (Fin 3) ℚ) (h : IntegralGL) :
    slash polyRho0 x h = bar h.val x := by
  change PolynomialGLAction.action 0 (ReferenceCoefficientMatrices.rational h⁻¹) x = _
  rw [PolynomialGLAction.action_apply, determinantCharacter_zero, one_smul, map_inv, inv_inv,
    bar_eq_substitute]

/-- The field of rational functions in `x, y, z`. -/
abbrev RatFun : Type := SinglePole.Frac

/-- The untwisted substitution action of `GL₃(ℤ)` on rational functions, the extension of the
action on polynomials. -/
abbrev fracRho0 : Representation ℚ IntegralGL RatFun :=
  (SinglePole.fractionAction 0).comp ReferenceCoefficientMatrices.rational

/-- The determinant-twisted action on rational functions. -/
abbrev fracRho : Representation ℚ IntegralGL RatFun :=
  (SinglePole.fractionAction (-1)).comp ReferenceCoefficientMatrices.rational

theorem isTwist_frac : IsTwist fracRho0 fracRho := by
  apply isTwist_of_det (SinglePole.fractionUntwisted) (SinglePole.fractionAction 0)
    (SinglePole.fractionAction (-1))
  · intro g x
    rw [SinglePole.fractionAction_apply, determinantCharacter_zero, one_smul]
    rfl
  · intro g x
    rw [SinglePole.fractionAction_apply]
    rfl

/-- On polynomials (embedded in the rational functions) the substitution is the polynomial one. -/
theorem slash_frac_embed (p : MvPolynomial (Fin 3) ℚ) (h : IntegralGL) :
    slash fracRho0 (SinglePole.embed p) h = SinglePole.embed (bar h.val p) := by
  change SinglePole.fractionAction 0 (ReferenceCoefficientMatrices.rational h⁻¹)
    (SinglePole.embed p) = _
  rw [SinglePole.fractionAction_embed]
  congr 1
  exact slash_poly p h


/-- The list of Lemma 4.3 for polynomial seeds, with the substitutions written as explicit
integer matrices acting by `(f ∣ h)(x) = f(h x)`:
`f` symmetric; `Q(a,b,c) = Q(b,a,c) = -Q(a,b,-c)`; `P(a,b,c) = P(a,c,b) = -P(a,-b,c) = -P(a,b,-c)`;
`N₁₂ f = N₁₂ Q = N₂₃ P = 0`;
`Q(a,b,c+a) - Q(a,b,c) = f(a+c,-c,b)` (`eq:mixed1`);
`P(a,c+a,b) - P(a,c,b) = Q(-c,a+c,b)` (`eq:mixed2`). -/
structure PolySeeds (f P Q : MvPolynomial (Fin 3) ℚ) : Prop where
  f_symm : ∀ π : Equiv.Perm (Fin 3), bar (Equiv.Perm.permMatrix ℤ π) f = f
  q_swap : bar !![0, 1, 0; 1, 0, 0; 0, 0, 1] Q = Q
  q_odd : bar !![1, 0, 0; 0, 1, 0; 0, 0, -1] Q = -Q
  p_swap : bar !![1, 0, 0; 0, 0, 1; 0, 1, 0] P = P
  p_odd2 : bar !![1, 0, 0; 0, -1, 0; 0, 0, 1] P = -P
  p_odd3 : bar !![1, 0, 0; 0, 1, 0; 0, 0, -1] P = -P
  nf : f + bar Amat f + bar (Amat * Amat) f = 0
  nq : Q + bar Amat Q + bar (Amat * Amat) Q = 0
  np : P + bar !![1, 0, 0; 0, 0, -1; 0, 1, -1] P + bar !![1, 0, 0; 0, -1, 1; 0, -1, 0] P = 0
  mixed1 : bar !![1, 0, 0; 0, 1, 0; 1, 0, 1] Q - Q = bar !![1, 0, 1; 0, 0, -1; 0, 1, 0] f
  mixed2 : bar !![1, 0, 0; 1, 0, 1; 0, 1, 0] P - bar !![1, 0, 0; 0, 0, 1; 0, 1, 0] P =
    bar !![0, 0, -1; 1, 0, 1; 0, 1, 0] Q

theorem polySeeds_iff (f P Q : MvPolynomial (Fin 3) ℚ) :
    PolySeeds f P Q ↔ SeedList polyRho0 f P Q := by
  have e1 : (permFrame (Equiv.swap 0 1)).val = !![0, 1, 0; 1, 0, 0; 0, 0, 1] := by decide +kernel
  have e2 : (permFrame (Equiv.swap 1 2)).val = !![1, 0, 0; 0, 0, 1; 0, 1, 0] := by decide +kernel
  have e3 : (signFrame {2}).val = !![1, 0, 0; 0, 1, 0; 0, 0, -1] := by decide +kernel
  have e4 : (signFrame {1}).val = !![1, 0, 0; 0, -1, 0; 0, 0, 1] := by decide +kernel
  have e5 : (aG ^ 2).val = Amat * Amat := a_sq_val
  constructor
  · intro h
    exact {
      f_symm := fun π => by
        rw [slash_poly, permFrame_val]
        exact h.f_symm π⁻¹
      q_swap := by rw [slash_poly, e1]; exact h.q_swap
      q_odd := by rw [slash_poly, e3]; exact h.q_odd
      p_swap := by rw [slash_poly, e2]; exact h.p_swap
      p_odd2 := by rw [slash_poly, e4]; exact h.p_odd2
      p_odd3 := by rw [slash_poly, e3]; exact h.p_odd3
      nf := by rw [slash_poly, slash_poly, e5]; exact h.nf
      nq := by rw [slash_poly, slash_poly, e5]; exact h.nq
      np := by rw [slash_poly, slash_poly]; exact h.np
      mixed1 := by rw [slash_poly, slash_poly]; exact h.mixed1
      mixed2 := by rw [slash_poly, slash_poly, slash_poly]; exact h.mixed2 }
  · intro h
    exact {
      f_symm := fun π => by
        have := h.f_symm π⁻¹
        rw [slash_poly, permFrame_val, inv_inv] at this
        exact this
      q_swap := by have := h.q_swap; rwa [slash_poly, e1] at this
      q_odd := by have := h.q_odd; rwa [slash_poly, e3] at this
      p_swap := by have := h.p_swap; rwa [slash_poly, e2] at this
      p_odd2 := by have := h.p_odd2; rwa [slash_poly, e4] at this
      p_odd3 := by have := h.p_odd3; rwa [slash_poly, e3] at this
      nf := by have := h.nf; rwa [slash_poly, slash_poly, e5] at this
      nq := by have := h.nq; rwa [slash_poly, slash_poly, e5] at this
      np := by have := h.np; rwa [slash_poly, slash_poly] at this
      mixed1 := by have := h.mixed1; rwa [slash_poly, slash_poly] at this
      mixed2 := by have := h.mixed2; rwa [slash_poly, slash_poly, slash_poly] at this }


/-- `eq:fiber-signed` for the symmetric case `t = 1` and polynomial values:
`F(rh) = χ₁(h) F(r) ∣ h` for every signed permutation matrix `h = Dπ`. -/
def PolySigned (F : Covectors → MvPolynomial (Fin 3) ℚ) : Prop :=
  ∀ (D : Fin 3 → ℤˣ) (π : Equiv.Perm (Fin 3)) (r r' : Covectors),
    r'.1 = Matrix.vecMul r.1 (mod3 (signedPermMatrix D π)) →
      F r' = (chi 1 D π : ℚ) • bar (signedPermMatrix D π) (F r)

/-- `eq:fiber-norm` for polynomial values: `F(r) + F(rA²) ∣ A + F(rA) ∣ A² = 0`. -/
def PolyNorm (F : Covectors → MvPolynomial (Fin 3) ℚ) : Prop :=
  ∀ r r₁ r₂ : Covectors,
    r₁.1 = Matrix.vecMul r.1 (mod3 (Amat * Amat)) → r₂.1 = Matrix.vecMul r.1 (mod3 Amat) →
      F r + bar Amat (F r₁) + bar (Amat * Amat) (F r₂) = 0

theorem prod_Dof : ∀ s : Finset (Fin 3), ∏ i, ((Dof s i : ℤˣ) : ℤ) = (-1 : ℤ) ^ s.card := by
  decide +kernel

theorem polySigned_iff (F : Covectors → MvPolynomial (Fin 3) ℚ) :
    PolySigned F ↔ PaperSigned polyRho0 F := by
  constructor
  · intro h s π r
    have h1 := h (Dof s) π⁻¹ r (act r (signedPerm s π)) (by rw [act_val, signedPerm_val])
    rw [slash_poly, signedPerm_val]
    have h2 : (chi 1 (Dof s) π⁻¹ : ℚ) = ((-1 : ℤ) ^ s.card : ℤ) := by
      simp only [chi]
      rw [ite_eq_right (by decide), prod_Dof]
    rw [h1, h2, Int.cast_smul_eq_zsmul]
  · intro h D π r r' hr'
    have e : r' = act r (signedPerm (sOf D) π⁻¹) := by
      apply Subtype.ext
      rw [hr', act_val, signedPerm_val, Dof_sOf, inv_inv]
    have h1 := h (sOf D) π⁻¹ r
    rw [slash_poly, signedPerm_val, Dof_sOf, inv_inv] at h1
    rw [e, h1]
    have h2 : (chi 1 D π : ℚ) = (((-1 : ℤ) ^ (sOf D).card : ℤ) : ℚ) := by
      have := prod_Dof (sOf D)
      rw [Dof_sOf] at this
      simp only [chi]
      rw [ite_eq_right (by decide), this]
    rw [h2, Int.cast_smul_eq_zsmul]

theorem polyNorm_iff (F : Covectors → MvPolynomial (Fin 3) ℚ) :
    PolyNorm F ↔ PaperNorm polyRho0 F := by
  constructor
  · intro h r
    rw [slash_poly, slash_poly, a_val, a_sq_val]
    exact h r (act r (aG ^ 2)) (act r aG) (by rw [act_val, a_sq_val]) (by rw [act_val, a_val])
  · intro h r r₁ r₂ h1 h2
    have e1 : r₁ = act r (aG ^ 2) := Subtype.ext (by rw [h1, act_val, a_sq_val])
    have e2 : r₂ = act r aG := Subtype.ext (by rw [h2, act_val, a_val])
    subst e1 e2
    have := h r
    rwa [slash_poly, slash_poly, a_val, a_sq_val] at this


theorem slash_frac_embed' (p : MvPolynomial (Fin 3) ℚ) (h : IntegralGL) :
    slash fracRho0 (SinglePole.embed p) h = SinglePole.embed (slash polyRho0 p h) := by
  rw [slash_frac_embed, slash_poly]

/-- On embedded polynomials, the list of Lemma 4.3 for rational functions is the polynomial list. -/
theorem seedList_frac_embed_iff (f P Q : MvPolynomial (Fin 3) ℚ) :
    SeedList fracRho0 (SinglePole.embed f) (SinglePole.embed P) (SinglePole.embed Q) ↔
      SeedList polyRho0 f P Q := by
  have hi : Function.Injective (SinglePole.embed : MvPolynomial (Fin 3) ℚ → RatFun) :=
    IsFractionRing.injective _ _
  have e0 : (0 : RatFun) = SinglePole.embed 0 := (map_zero _).symm
  constructor
  · intro h
    refine ⟨fun π => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := h.f_symm π
      rw [slash_frac_embed'] at this
      exact hi this
    · have := h.q_swap
      rw [slash_frac_embed'] at this
      exact hi this
    · have := h.q_odd
      rw [slash_frac_embed', ← map_neg] at this
      exact hi this
    · have := h.p_swap
      rw [slash_frac_embed'] at this
      exact hi this
    · have := h.p_odd2
      rw [slash_frac_embed', ← map_neg] at this
      exact hi this
    · have := h.p_odd3
      rw [slash_frac_embed', ← map_neg] at this
      exact hi this
    · have := h.nf
      rw [slash_frac_embed', slash_frac_embed', ← map_add, ← map_add, e0] at this
      exact hi this
    · have := h.nq
      rw [slash_frac_embed', slash_frac_embed', ← map_add, ← map_add, e0] at this
      exact hi this
    · have := h.np
      rw [slash_frac_embed', slash_frac_embed', ← map_add, ← map_add, e0] at this
      exact hi this
    · have := h.mixed1
      rw [slash_frac_embed', slash_frac_embed', ← map_sub] at this
      exact hi this
    · have := h.mixed2
      rw [slash_frac_embed', slash_frac_embed', slash_frac_embed', ← map_sub] at this
      exact hi this
  · intro h
    refine ⟨fun π => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [slash_frac_embed', h.f_symm π]
    · rw [slash_frac_embed', h.q_swap]
    · rw [slash_frac_embed', h.q_odd, map_neg]
    · rw [slash_frac_embed', h.p_swap]
    · rw [slash_frac_embed', h.p_odd2, map_neg]
    · rw [slash_frac_embed', h.p_odd3, map_neg]
    · rw [slash_frac_embed', slash_frac_embed', ← map_add, ← map_add, h.nf, map_zero]
    · rw [slash_frac_embed', slash_frac_embed', ← map_add, ← map_add, h.nq, map_zero]
    · rw [slash_frac_embed', slash_frac_embed', ← map_add, ← map_add, h.np, map_zero]
    · rw [slash_frac_embed', slash_frac_embed', ← map_sub, h.mixed1]
    · rw [slash_frac_embed', slash_frac_embed', slash_frac_embed', ← map_sub, h.mixed2]

end TernaryPeriodPolynomials.Argument.FiberModel
