module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.RightTranslation

@[expose] public section


/-!
# Transformation laws of the lattice sum (inputs for `hecke_right_everywhere`)

Formalized by Claude Haiku 5.5.

For a finite index family `x : ι → GL₂(𝔸_f)` (the lattice matrices `ι_p(A_Λ)`), the lattice sum
`latSum k h x gInf gf = ∑_i v_h(g_∞, g_f · x_i)` is the left-hand side of eq:lattice-hecke.
Proved here:
* `latSum_diag`: diagonal `GL₂⁺(ℚ)`-equivariance (from `vhValue_rational`, termwise);
* `latSum_mul_integral_of_perm`: right `GL₂(ℤ̂)`-invariance, given the lattice-permutation input
  `IsLatticePerm u x σ` for the integral element `u` (from `sum_perm`);
* `vhRight_mul_integral`, `vhRight_diag`: the same laws for the right-hand side `c · v_h(g_∞, ·)`.

Hypothesis: `hPerm`, the lattice permutation for every `u ∈ GL₂(ℤ̂)`:
`∀ u ∈ binaryIntegralFinite, ∃ σ, IsLatticePerm u x σ`.
-/

open Matrix
open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.FiniteReduction
open TernaryPeriodPolynomials.Argument.LatticeCounts.AdelicValue
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation

noncomputable section

open scoped Classical

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeTransform

/-- The lattice sum `∑_i v_h(g_∞, g_f · x_i)` over a finite index family `x`. -/
def latSum {ι : Type*} [Fintype ι] (k : ℤ)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne k)
    (x : ι → BinaryFiniteGL) (gInf : BinaryRealGL) (gf : BinaryFiniteGL) : ℂ :=
  ∑ i, vhValue k h gInf (gf * x i)

/-- The right-hand side `c · v_h(g_∞, g_f)` of the identity. -/
def vhRight (k : ℤ)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne k)
    (c : ℂ) (gInf : BinaryRealGL) (gf : BinaryFiniteGL) : ℂ :=
  c * vhValue k h gInf gf

/-- Diagonal equivariance of the lattice sum: `L(g_∞, δ g_f) = L(δ⁻¹ g_∞, g_f)`. -/
theorem latSum_diag {ι : Type*} [Fintype ι] (k : ℤ)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne k)
    (x : ι → BinaryFiniteGL) (gInf : BinaryRealGL) (hgInf : 0 < (Matrix.GeneralLinearGroup.det gInf).val)
    (δ : BinaryRationalGL) (hδ : 0 < (Matrix.GeneralLinearGroup.det δ).val) (gf : BinaryFiniteGL) :
    latSum k h x gInf (binaryRationalFinite δ * gf) =
      latSum k h x (binaryRationalReal δ⁻¹ * gInf) gf := by
  unfold latSum
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc]
  exact vhValue_rational k h gInf hgInf δ hδ (gf * x i)

/-- Right `GL₂(ℤ̂)`-invariance of the lattice sum, given the lattice-permutation input for `u`. -/
theorem latSum_mul_integral_of_perm {ι : Type*} [Fintype ι] (k : ℤ)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne k)
    (x : ι → BinaryFiniteGL) (gInf : BinaryRealGL) (hgInf : 0 < (Matrix.GeneralLinearGroup.det gInf).val)
    (gf u : BinaryFiniteGL) (σ : ι ≃ ι)
    (hP : TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation.IsLatticePerm u x σ) :
    latSum k h x gInf (gf * u) = latSum k h x gInf gf := by
  unfold latSum
  have e : ∀ i, vhValue k h gInf (gf * u * x i) = vhValue k h gInf (gf * (u * x i)) :=
    fun i => by rw [mul_assoc]
  simp only [e]
  exact TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation.sum_perm
    k h gInf hgInf gf u x σ hP

/-- Right invariance of the right-hand side: `c · v_h(g_∞, g_f u) = c · v_h(g_∞, g_f)`. -/
theorem vhRight_mul_integral (k : ℤ)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne k)
    (c : ℂ) (gInf : BinaryRealGL) (hgInf : 0 < (Matrix.GeneralLinearGroup.det gInf).val)
    (gf u : BinaryFiniteGL) (hu : u ∈ binaryIntegralFinite) :
    vhRight k h c gInf (gf * u) = vhRight k h c gInf gf := by
  unfold vhRight
  rw [vhValue_mul_integral k h gInf hgInf gf u hu]

/-- Diagonal equivariance of the right-hand side. -/
theorem vhRight_diag (k : ℤ)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne k)
    (c : ℂ) (gInf : BinaryRealGL) (hgInf : 0 < (Matrix.GeneralLinearGroup.det gInf).val)
    (δ : BinaryRationalGL) (hδ : 0 < (Matrix.GeneralLinearGroup.det δ).val) (gf : BinaryFiniteGL) :
    vhRight k h c gInf (binaryRationalFinite δ * gf) =
      vhRight k h c (binaryRationalReal δ⁻¹ * gInf) gf := by
  unfold vhRight
  rw [vhValue_rational k h gInf hgInf δ hδ gf]

end TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeTransform
