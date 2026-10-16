module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.Coefficients
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.Topology.Algebra.Module.UniformConvergence
public import Mathlib.Topology.Algebra.SeparationQuotient.Section

@[expose] public section


/-!
# A normed model of the coefficient space `E_n = Sym^n((ℂ³)*) ⊗ det⁻¹`

The library's coefficient module `GeneralEisenstein.HomogeneousPoly n` is a complex vector space of
homogeneous polynomials in `(X, Y, Z)`. To apply the smooth de Rham zig-zag it is given the norm
induced by its (injective) coefficient vector in `ℂ^{3 × (n+1)}`; the induced norm is local to
this development.

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3

open GeneralEisenstein

/-- The coefficient vector of a homogeneous polynomial of degree `n`. -/
def coefVec (n : ℕ) : HomogeneousPoly n →ₗ[ℂ] ((Fin 3 → Fin (n + 1)) → ℂ) where
  toFun q := fun e => (q : MvPolynomial (Fin 3) ℂ).coeff (Finsupp.equivFunOnFinite.symm (fun i => (e i : ℕ)))
  map_add' q r := by
    funext e
    simp
  map_smul' c q := by
    funext e
    simp

theorem coefVec_injective (n : ℕ) : Function.Injective (coefVec n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro q hq
  apply Subtype.ext
  ext m
  by_contra hne
  have hne' : (q : MvPolynomial (Fin 3) ℂ).coeff m ≠ 0 := by simpa using hne
  have hmem : (q : MvPolynomial (Fin 3) ℂ) ∈ homogeneousSubmodule (Fin 3) ℂ n := q.2
  have hdeg : m.degree = n := by
    have := ((mem_homogeneousSubmodule n _).mp hmem) hne'
    rw [Finsupp.degree_eq_weight_one]
    exact this
  have hle : ∀ i, m i ≤ n := fun i => by
    rw [← hdeg]
    exact Finsupp.le_degree i m
  have := congrFun hq (fun i => ⟨m i, Nat.lt_succ_of_le (hle i)⟩)
  simp only [coefVec, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
  apply hne'
  convert this using 2
  ext i
  simp

/-- The coefficient space `E_n`, as a type synonym carrying the induced norm. -/
def Coef (n : ℕ) : Type := HomogeneousPoly n

namespace Coef

variable {n : ℕ}

instance : AddCommGroup (Coef n) := inferInstanceAs (AddCommGroup (HomogeneousPoly n))

instance : Module ℂ (Coef n) := inferInstanceAs (Module ℂ (HomogeneousPoly n))

/-- The vector of coefficients, as a linear map out of the synonym. -/
def vec (n : ℕ) : Coef n →ₗ[ℂ] ((Fin 3 → Fin (n + 1)) → ℂ) := coefVec n

theorem vec_injective (n : ℕ) : Function.Injective (vec n) := coefVec_injective n

/-- The norm on `E_n` induced by its coefficient vector. -/
instance : NormedAddCommGroup (Coef n) :=
  NormedAddCommGroup.induced (Coef n) ((Fin 3 → Fin (n + 1)) → ℂ) (vec n) (vec_injective n)

instance : NormedSpace ℂ (Coef n) :=
  NormedSpace.induced ℂ (Coef n) ((Fin 3 → Fin (n + 1)) → ℂ) (vec n)

instance : FiniteDimensional ℂ (Coef n) :=
  Module.Finite.of_injective (vec n) (vec_injective n)

instance : FiniteDimensional ℝ (Coef n) := Module.Finite.trans ℂ (Coef n)

instance : CompleteSpace (Coef n) := FiniteDimensional.complete ℝ (Coef n)

/-- The element of the synonym. -/
def mk (q : HomogeneousPoly n) : Coef n := q

/-- The underlying homogeneous polynomial. -/
def val (q : Coef n) : HomogeneousPoly n := q

/-- The underlying polynomial of an element of `E_n`. -/
def toPoly (q : Coef n) : MvPolynomial (Fin 3) ℂ := (q : HomogeneousPoly n).1

@[simp] theorem toPoly_add (q r : Coef n) : toPoly (q + r) = toPoly q + toPoly r := rfl

@[simp] theorem toPoly_sub (q r : Coef n) : toPoly (q - r) = toPoly q - toPoly r := rfl

@[simp] theorem toPoly_neg (q : Coef n) : toPoly (-q) = -toPoly q := rfl

@[simp] theorem toPoly_zero : toPoly (0 : Coef n) = 0 := rfl

@[simp] theorem toPoly_smul (c : ℂ) (q : Coef n) : toPoly (c • q) = MvPolynomial.C c * toPoly q :=
  MvPolynomial.smul_eq_C_mul _ _

theorem toPoly_injective : Function.Injective (toPoly : Coef n → MvPolynomial (Fin 3) ℂ) :=
  fun _ _ h => Subtype.ext h

theorem toPoly_isHomogeneous (q : Coef n) : (toPoly q).IsHomogeneous n :=
  (MvPolynomial.mem_homogeneousSubmodule n _).mp q.2

end Coef

end TernaryPeriodPolynomials.Argument.SeedC3
