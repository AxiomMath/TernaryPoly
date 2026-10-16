module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.Automorphic
public import TernaryPeriodPolynomials.ArithmeticGroup.Adelic.Integers

@[expose] public section


/-!
# Rational lattice reduction of finite-adelic `GL₂` (step (2) data)

Formalized by Claude Haiku 5.5.
Paper: (`v_h(g_∞, g_f) = F_h(γ g_∞)` for `γ ∈ GL₂⁺(ℚ)` with `γ g_f ∈ GL₂(ℤ̂)`).

This file defines only the reduction data:

* `binaryIntegralFinite`: `GL₂(ℤ̂)` inside `GL₂(𝔸_f)`, the range of `GeneralLinearGroup.map integralEmbedding`.
* `binaryRationalFinite`, `binaryRationalReal`: the rational embeddings.
* `LatticeReduction gf`: data `γ ∈ GL₂(ℚ)` with `0 < det γ` and `γ gf ∈ GL₂(ℤ̂)`.
* `LatticeReductionExists`: the global input the paper uses without proof. It is NOT proved here.

The adelic `v_h` is not defined here, and its well-definedness is not proved.
-/

open Matrix
open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.FiniteReduction

/-- `GL₂(ℤ̂)` inside `GL₂(𝔸_f)`: the image of `GL₂` over the integral finite adeles. -/
def binaryIntegralFinite : Subgroup BinaryFiniteGL :=
  (GeneralLinearGroup.map integralEmbedding).range

/-- The rational matrices `GL₂(ℚ)` embedded in `GL₂(𝔸_f)`. -/
def binaryRationalFinite : BinaryRationalGL →* BinaryFiniteGL :=
  GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles)

/-- The real image of a rational matrix. -/
def binaryRationalReal : BinaryRationalGL →* BinaryRealGL :=
  GeneralLinearGroup.map (Rat.castHom ℝ)

/-- Data of a rational lattice reduction of `gf`: `γ ∈ GL₂⁺(ℚ)` with `γ gf ∈ GL₂(ℤ̂)`. -/
structure LatticeReduction (gf : BinaryFiniteGL) where
  /-- The rational basis change. -/
  γ : BinaryRationalGL
  /-- Positive determinant, the `GL₂⁺(ℚ)` condition. -/
  det_pos : 0 < (Matrix.GeneralLinearGroup.det γ).val
  /-- The reduced matrix `γ gf` is integral. -/
  integral : binaryRationalFinite γ * gf ∈ binaryIntegralFinite

/-- The global input that the paper uses without proof: every finite-adelic
matrix has a rational lattice reduction with positive determinant. Stated, not proved. -/
def LatticeReductionExists : Prop :=
  ∀ gf : BinaryFiniteGL, Nonempty (LatticeReduction gf)

end TernaryPeriodPolynomials.Argument.LatticeCounts.FiniteReduction
