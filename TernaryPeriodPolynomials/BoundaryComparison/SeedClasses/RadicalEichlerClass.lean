module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.RadicalLieClass
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.EichlerClass
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Analysis.Calculus.FDeriv.Star
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.GroupTheory.ArchimedeanDensely
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Perm.ConjAct
public import Mathlib.LinearAlgebra.Center
public import Mathlib.LinearAlgebra.Complex.Determinant
public import Mathlib.LinearAlgebra.Matrix.Integer
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.Localization.NumDen
public import Mathlib.SetTheory.Cardinal.Embedding
public import Mathlib.Topology.Algebra.IsUniformGroup.Order

@[expose] public section


/-!
# Lemma C.3: the radical class is the Eichler--Shimura class, for every `Λ_P`

Paper: Lemma C.3 (`ar:lem:seed`): "Its radical class is the binary degree-`n+1` cusp-form
class, up to a nonzero scalar." Here `Λ_P` is an arbitrary group of determinant-one binary
matrices: in the paper's application `Γ_P` is the stabilizer of a plane flag in a neat
principal congruence subgroup `Γ(N)` of `SL₃(ℤ)` with `3 ∣ N`, so `Λ_P` is `Γ(N) ⊂ SL₂(ℤ)` or a
rational conjugate (Mathlib supplies `HasDetOne` for `Γ(N)`'s image in `GL₂(ℝ)` and for its
`ConjAct`-conjugates).

For a cusp form `f` of weight `n + 3` for `Λ_P` and `h = f ∘ ofComplex`:

* the Eichler cocycle `c_γ` (the value at `γ i` of the `i`-normalized primitive of
  `h(z)(zy - x)^{n+1}`) is a homogeneous binary form of degree `n + 1` and a 1-cocycle of `Λ_P`
  for the action on binary forms (`eichlerCocycle_mul`): this is the binary cusp-form class;
* the radical form of the seed `ω_h` (`radicalContraction`) is `-(n+1)⁻¹ h(τ)(τY - X)^{n+1}`, the
  same family of closed forms, and `-(n+1)⁻¹ ∑ ...` times the same primitive is a primitive of it;
  its period cocycle is therefore `-(n+1)⁻¹ c_γ`: the radical class equals the binary class up to
  the nonzero scalar `-(n+1)⁻¹`, as a class in `H¹(Λ_P, Sym^{n+1})`.

Formalized by Claude Sonnet 5.5.
-/

open UpperHalfPlane
open scoped UpperHalfPlane

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3

open TernaryPeriodPolynomials.Argument

/-- Evaluating the radical class of the seed `ω_h` at `(x, y, 0)` gives `-(n+1)⁻¹` times the binary
Eichler--Shimura integrand `h(τ)(τy - x)^{n+1}`, for every function `h`. -/
theorem seedRadical_eval_eq_binaryIntegrand (n : ℕ) (h : ℂ → ℂ) (p : Fin 5 → ℝ) (x y : ℂ) :
    MvPolynomial.eval ![x, y, 0] (radicalContraction n (seedForm n h p 0 2) (seedForm n h p 1 2)) =
      -(((n : ℂ) + 1)⁻¹ * binaryIntegrand n h ![x, y] (seedTau p)) := by
  rw [seedRadical_contraction]
  simp [binaryIntegrand]
  ring

/-- The radical cocycle: `-(n+1)⁻¹` times the Eichler cocycle. -/
def radicalCocycle (n : ℕ) (G : ℕ → ℂ → ℂ) (γ : GL (Fin 2) ℝ) : MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.C (-(((n : ℂ) + 1)⁻¹)) * eichlerCocycle n G γ

theorem radicalCocycle_isHomogeneous (n : ℕ) (G : ℕ → ℂ → ℂ) (γ : GL (Fin 2) ℝ) :
    MvPolynomial.IsHomogeneous (radicalCocycle n G γ) (n + 1) := by
  have := (MvPolynomial.isHomogeneous_C (Fin 2) (-(((n : ℂ) + 1)⁻¹))).mul
    (eichlerCocycle_isHomogeneous n G γ)
  rwa [zero_add] at this

/-- The radical cocycle is a 1-cocycle for the action on binary forms. -/
theorem radicalCocycle_mul (n : ℕ) (h : ℂ → ℂ) (G : ℕ → ℂ → ℂ) (hG0 : ∀ j, G j Complex.I = 0)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (G j) (h z * z ^ j) z) (γ δ : GL (Fin 2) ℝ)
    (hγ : γ.det = 1) (hδ : δ.det = 1)
    (hmodγ : ∀ z : ℂ, 0 < z.im → h (mob γ z) = dnm γ z ^ (n + 3) * h z) :
    radicalCocycle n G (γ * δ) =
      radicalCocycle n G γ + MvPolynomial.bind₁ (invCoordPoly γ) (radicalCocycle n G δ) := by
  unfold radicalCocycle
  rw [eichlerCocycle_mul n h G hG0 hG γ δ hγ hδ hmodγ, map_mul, mul_add]
  simp

/-- The `I`-normalized primitive of the radical binary form, as a polynomial in `(x, y)`. -/
def radicalPrimitive (n : ℕ) (G : ℕ → ℂ → ℂ) (w : ℂ) : MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.C (-(((n : ℂ) + 1)⁻¹)) * eichlerPoly n G w

theorem radicalCocycle_eq (n : ℕ) (G : ℕ → ℂ → ℂ) (γ : GL (Fin 2) ℝ) :
    radicalCocycle n G γ = radicalPrimitive n G (mob γ Complex.I) := rfl

/-- The radical primitive is a primitive, on the upper half-plane, of the radical class of the
seed `ω_h` (at any point `p`, evaluated at `(x, y, 0)`). -/
theorem radicalPrimitive_hasDerivAt (n : ℕ) (h : ℂ → ℂ) (G : ℕ → ℂ → ℂ)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (G j) (h z * z ^ j) z) (p : Fin 5 → ℝ) (hp : 0 < p 3)
    (x y : ℂ) :
    HasDerivAt (fun w => MvPolynomial.eval ![x, y] (radicalPrimitive n G w))
      (MvPolynomial.eval ![x, y, 0]
        (radicalContraction n (seedForm n h p 0 2) (seedForm n h p 1 2))) (seedTau p) := by
  have hτ : 0 < (seedTau p).im := by simpa [seedTau] using hp
  rw [seedRadical_eval_eq_binaryIntegrand]
  have := (eichlerPoly_hasDerivAt n h G hG ![x, y] hτ).const_mul (-(((n : ℂ) + 1)⁻¹))
  simpa [radicalPrimitive, neg_mul] using this

/-- The statement packaged by `seed_radical_class_eq_eichler_class` for a given system `G` of
moment primitives of `h(z) z^j`, `h = f ∘ ofComplex`:

1. the Eichler cocycle `c_γ` is a homogeneous binary form of degree `n + 1`;
2. `c_{γδ} = c_γ + γ·c_δ` for `γ, δ ∈ Λ_P`;
3. the radical cocycle is `-(n+1)⁻¹ c_γ`, a homogeneous binary form of degree `n + 1` and a
   cocycle with the same relation;
4. `radicalPrimitive` is the `i`-normalized primitive, on the upper half-plane, of the radical
   class of the seed `ω_h` at every plane point `p`. -/
def RadicalEichlerPackage (Λ : Subgroup (GL (Fin 2) ℝ)) (n : ℕ)
    (f : CuspForm Λ ((n + 3 : ℕ) : ℤ)) (G : ℕ → ℂ → ℂ) : Prop :=
  (∀ j, G j Complex.I = 0) ∧
    (∀ j z, 0 < z.im → HasDerivAt (G j) (f (ofComplex z) * z ^ j) z) ∧
    (∀ γ : GL (Fin 2) ℝ, MvPolynomial.IsHomogeneous (eichlerCocycle n G γ) (n + 1)) ∧
    (∀ γ ∈ Λ, ∀ δ ∈ Λ, eichlerCocycle n G (γ * δ) = eichlerCocycle n G γ +
      MvPolynomial.bind₁ (invCoordPoly γ) (eichlerCocycle n G δ)) ∧
    (∀ γ : GL (Fin 2) ℝ, radicalCocycle n G γ =
      MvPolynomial.C (-(((n : ℂ) + 1)⁻¹)) * eichlerCocycle n G γ) ∧
    (∀ γ : GL (Fin 2) ℝ, MvPolynomial.IsHomogeneous (radicalCocycle n G γ) (n + 1)) ∧
    (∀ γ ∈ Λ, ∀ δ ∈ Λ, radicalCocycle n G (γ * δ) = radicalCocycle n G γ +
      MvPolynomial.bind₁ (invCoordPoly γ) (radicalCocycle n G δ)) ∧
    (∀ (p : Fin 5 → ℝ), 0 < p 3 → ∀ x y : ℂ,
      HasDerivAt (fun w => MvPolynomial.eval ![x, y] (radicalPrimitive n G w))
        (MvPolynomial.eval ![x, y, 0] (radicalContraction n
          (seedForm n (fun z => f (ofComplex z)) p 0 2)
          (seedForm n (fun z => f (ofComplex z)) p 1 2))) (seedTau p))

/-- **Lemma C.3, the radical class is the Eichler--Shimura class (class level).**
For a cusp form `f` of weight `n + 3` for a determinant-one group `Λ_P` (e.g. a principal
congruence subgroup `Γ(N) ⊂ SL₂(ℤ)` with `3 ∣ N`, or a rational conjugate of it), the moment
primitives `G` of `h(z) z^j` satisfy `RadicalEichlerPackage`. -/
theorem seed_radical_class_eq_eichler_class (Λ : Subgroup (GL (Fin 2) ℝ)) [Λ.HasDetOne] (n : ℕ)
    (f : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    ∃ G : ℕ → ℂ → ℂ, RadicalEichlerPackage Λ n f G := by
  have hh : DifferentiableOn ℂ (fun z => f (ofComplex z)) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo f)
  obtain ⟨G, hG0, hG⟩ := exists_moment_primitives _ hh
  have hmod : ∀ γ ∈ Λ, ∀ z : ℂ, 0 < z.im →
      f (ofComplex (mob γ z)) = dnm γ z ^ (n + 3) * f (ofComplex z) :=
    fun γ hγ z hz => modular_of_slashInvariant Λ (n + 3) f γ hγ z hz
  refine ⟨G, hG0, hG, fun γ => eichlerCocycle_isHomogeneous n G γ, ?_, fun γ => rfl,
    fun γ => radicalCocycle_isHomogeneous n G γ, ?_, fun p hp x y =>
      radicalPrimitive_hasDerivAt n _ G hG p hp x y⟩
  · intro γ hγ δ hδ
    exact eichlerCocycle_mul n _ G hG0 hG γ δ (Subgroup.HasDetOne.det_eq hγ)
      (Subgroup.HasDetOne.det_eq hδ) (hmod γ hγ)
  · intro γ hγ δ hδ
    exact radicalCocycle_mul n _ G hG0 hG γ δ (Subgroup.HasDetOne.det_eq hγ)
      (Subgroup.HasDetOne.det_eq hδ) (hmod γ hγ)

end TernaryPeriodPolynomials.Argument.SeedC3
