module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.Frame

@[expose] public section


/-!
# Cochain vocabulary for the constant-term argument

Homogeneous cochains on rational vertex tuples with values in a representation `ρ` of
`GL₃(ℚ)`, written as plain functions so that translated families of cochains (real
translations along the unipotent radical of a flag) can be compared with their rational
transports.

Written by AxiomCode.
-/

open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- The homogeneous 2-cocycle condition on rational vertex tuples. -/
def IsCocycle₂ (ω : (Fin 3 → RationalGL3) → V) : Prop :=
  ∀ x : Fin 4 → RationalGL3,
    ω ![x 1, x 2, x 3] - ω ![x 0, x 2, x 3] + ω ![x 0, x 1, x 3] - ω ![x 0, x 1, x 2] = 0

/-- The homogeneous differential of a 1-cochain. -/
def codiff (P : (Fin 2 → RationalGL3) → V) : (Fin 3 → RationalGL3) → V :=
  fun x => P ![x 1, x 2] - P ![x 0, x 2] + P ![x 0, x 1]

/-- Equivariance of a `k`-cochain under a subgroup. -/
def Equivariant (Γ : Subgroup RationalGL3) (ρ : Representation ℂ RationalGL3 V) {k : ℕ}
    (ω : (Fin k → RationalGL3) → V) : Prop :=
  ∀ γ ∈ Γ, ∀ x : Fin k → RationalGL3, ω (fun i => γ * x i) = ρ γ (ω x)

/-- A `Γ`-equivariant 2-cochain is a coboundary of a `Γ`-equivariant 1-cochain. -/
def IsCoboundary (Γ : Subgroup RationalGL3) (ρ : Representation ℂ RationalGL3 V)
    (ω : (Fin 3 → RationalGL3) → V) : Prop :=
  ∃ P : (Fin 2 → RationalGL3) → V, Equivariant Γ ρ P ∧ ω = codiff P

/-- Transport of a vertex cochain by a rational element `g`: `x ↦ ρ g (ω (g⁻¹ x))`. -/
def transport (ρ : Representation ℂ RationalGL3 V) (g : RationalGL3)
    (ω : (Fin 3 → RationalGL3) → V) : (Fin 3 → RationalGL3) → V :=
  fun x => ρ g (ω (fun i => g⁻¹ * x i))

/-- The average of a real-parameter family over the `K × K` grid of the torus. -/
def gridAverage (Θ : ℝ × ℝ → (Fin 3 → RationalGL3) → V) (K : ℕ) :
    (Fin 3 → RationalGL3) → V :=
  fun x => (1 / (K : ℂ) ^ 2) • ∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K,
    Θ ((a : ℝ) / K, (b : ℝ) / K) x

end TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm
