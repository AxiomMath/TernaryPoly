module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.RhoAction
public import TernaryPeriodPolynomials.BoundaryComparison.StokesComparison
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.NumberTheory.ModularForms.SlashInvariantForms
public import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
public import Batteries.Data.List.Count
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup

@[expose] public section


/-!
# Lemma C.3 of Appendix C.3: `Γ_P`-equivariance of the seed

Paper: Lemma C.3
(`ar:lem:seed`): "the form `ω_h` is closed and is equivariant for `Γ_P` with coefficients `E`".
The `seed_closed_equivariant` proves closedness, the radical-translation clause and the Levi
transformation law `g^*ω_h = ρ(g) ω_{δ^{k/2}(h|_k A)}`. At the neat integral stabilizer
(`t = δ = 1`) the paper concludes "the modular transformation law proves equivariance". This
file carries out that last step for an actual slash-invariant form of the determinant-one Levi
group `Λ_P`, with the literal action `ρ(g)f(𝐗) = det(g)⁻¹ f(g⁻¹𝐗)` of `RhoAction`.

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial UpperHalfPlane ModularForm
open scoped UpperHalfPlane

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3

/-- The modular-transformation law of a slash-invariant form, as the identity
`slashTwisted k γ h τ = h τ` at every point `τ` of the upper half-plane,
where `h = f ∘ ofComplex` and `γ` is a determinant-one element of the group. -/
theorem slashTwisted_cuspFunction {F : Type*} [FunLike F ℍ ℂ] (Λ : Subgroup (GL (Fin 2) ℝ))
    [Λ.HasDetOne] (k : ℕ) [SlashInvariantFormClass F Λ (k : ℤ)] (f : F)
    (γ : GL (Fin 2) ℝ) (hγ : γ ∈ Λ) (τ : ℂ) (hτ : 0 < τ.im) :
    slashTwisted k (γ : Matrix (Fin 2) (Fin 2) ℝ) (fun z => f (ofComplex z)) τ =
      f (ofComplex τ) := by
  have hdet : (γ : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    have := Subgroup.HasDetOne.det_eq hγ
    simpa [Matrix.GeneralLinearGroup.det] using congrArg Units.val this
  set z : ℍ := ⟨τ, hτ⟩ with hz
  have hden : denom γ τ ≠ 0 := denom_ne_zero γ z
  have hpos : 0 < γ.det.val := by
    have := Subgroup.HasDetOne.det_eq hγ
    simp [this]
  have hsm : ((γ • z : ℍ) : ℂ) = ((γ 0 0 : ℝ) * τ + γ 0 1) / ((γ 1 0 : ℝ) * τ + γ 1 1) :=
    coe_smul_of_det_pos hpos z
  have hmod := SlashInvariantForm.slash_action_eqn'' (F := F) (k := (k : ℤ)) f hγ z
  unfold slashTwisted
  rw [hdet, ← hsm]
  have e1 : ofComplex ((γ • z : ℍ) : ℂ) = γ • z := ofComplex_apply _
  have e2 : ofComplex τ = z := ofComplex_apply_of_im_pos hτ
  have hd : denom γ (z : ℂ) = (γ 1 0 : ℝ) * τ + γ 1 1 := rfl
  simp only [e1, e2, hmod, hd, one_pow, one_mul, Complex.ofReal_one]
  rw [zpow_neg, zpow_natCast]
  have hden' : (((γ 1 0 : ℝ) : ℂ) * τ + ((γ 1 1 : ℝ) : ℂ)) ≠ 0 := hd ▸ hden
  field_simp

/-- The seed depends on `h` only through the value `h (τ)` at the point. -/
theorem seedForm_congr_value (n : ℕ) (h h' : ℂ → ℂ) (p : Fin 5 → ℝ)
    (hh : h' (seedTau p) = h (seedTau p)) (i j : Fin 5) :
    seedForm n h' p i j = seedForm n h p i j := by
  unfold seedForm
  rw [hh]

/-- A radical translation after any change of coordinates acts on the pulled-back seed by the
coefficient substitution of the `seed_closed_equivariant`. -/
theorem formPullback_translate (n : ℕ) (h : ℂ → ℂ) (Φ : (Fin 5 → ℝ) → (Fin 5 → ℝ))
    (v w : ℝ) (p : Fin 5 → ℝ) (i j : Fin 5) :
    formPullback (fun q => Φ q + ![v, w, 0, 0, 0]) (seedForm n h) p i j =
      bind₁ (![X 0 - C (v : ℂ) * X 2, X 1 - C (w : ℂ) * X 2, X 2] :
          Fin 3 → MvPolynomial (Fin 3) ℂ) (formPullback Φ (seedForm n h) p i j) := by
  unfold formPullback
  rw [fderiv_add_const]
  simp only [map_sum, map_mul, bind₁_C_right, lemma_C3_ii]

/-- **Lemma C.3, equivariance for `Γ_P`.** Let `Λ` be a group of determinant-one binary matrices
and `f` a (cusp) form of weight `n + 3` for `Λ`, `h = f ∘ ofComplex` its extension to `ℂ`. For
`γ ∈ Λ`, `w ∈ ℝ²` and the parabolic element `[[γ, w], [0, 1]]` (plane coordinates
`p ↦ (γu + w, γτ, p₄)`) one has `g^* ω_h = ρ(g) ω_h` at every point of the plane. -/
theorem seed_parabolic_equivariant {F : Type*} [FunLike F ℍ ℂ] (Λ : Subgroup (GL (Fin 2) ℝ))
    [Λ.HasDetOne] (n : ℕ) [SlashInvariantFormClass F Λ ((n + 3 : ℕ) : ℤ)] (f : F)
    (γ : GL (Fin 2) ℝ) (hγ : γ ∈ Λ) (w : Fin 2 → ℝ) (p : Fin 5 → ℝ) (hp : 0 < p 3) (i j : Fin 5) :
    formPullback (parabolicMap (γ : Matrix (Fin 2) (Fin 2) ℝ) w)
        (seedForm n (fun z => f (ofComplex z))) p i j =
      rho (parabolicMatrix (γ : Matrix (Fin 2) (Fin 2) ℝ) w)
        (seedForm n (fun z => f (ofComplex z)) p i j) := by
  have hdet : (γ : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    have := Subgroup.HasDetOne.det_eq hγ
    simpa [Matrix.GeneralLinearGroup.det] using congrArg Units.val this
  have hτ : 0 < (seedTau p).im := by simpa [seedTau] using hp
  unfold parabolicMap
  rw [formPullback_translate, lemma_C3_iii n _ _ 1 (by rw [hdet]; exact one_pos) one_pos p hp i j,
    seedForm_congr_value n (fun z => f (ofComplex z)) _ p
      (slashTwisted_cuspFunction Λ (n + 3) f γ hγ _ hτ),
    rho_parabolicMatrix _ _ (by rw [hdet]; exact one_ne_zero)]

end TernaryPeriodPolynomials.Argument.SeedC3
