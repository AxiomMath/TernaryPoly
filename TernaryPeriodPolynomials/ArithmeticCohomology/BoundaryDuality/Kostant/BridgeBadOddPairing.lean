module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.BridgeBadLevi

@[expose] public section


/-!
# The Kostant identity of the odd-degree level-three bridge at the bad line

For odd `n` the degree `N = n + 1` of the binary forms is even, so the exchange of the two binary
variables is *symmetric* for the classical pairing, `⟨σ x, y⟩ = ⟨x, σ y⟩` (in odd degree it is
skew-symmetric).  The same computation as for even `n` therefore gives

  `κ(f, g) = -(n+1)!/3 · binaryPairing (n+1) (Φ f) (Ψ g)`    (`kostantBad_eq_binaryPairing_odd`),

where now the dual coordinate `Ψ` transforms through `Sym^{n+1} ⊗ det⁻¹` (`PsiBad_levi_odd`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

attribute [local instance] TernaryPeriodPolynomials.SphericalDetection.Helpers.complexEndRationalAlgebra

namespace TernaryPeriodPolynomials.BoundaryDuality.Kostant

open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly (latL0)
open TernaryPeriodPolynomials.BoundaryDuality.FiberKostant (UCocycle)
open TernaryPeriodPolynomials.BoundaryDuality.FiberFormula (kostant)
open TernaryPeriodPolynomials.BoundaryDuality.FiberL1 (dualRep)
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives (dualityData)

/-- **Symmetry of the pairing under the exchange of the variables** in even degree:
`⟨σ x, y⟩ = ⟨x, σ y⟩`. -/
theorem binaryPairing_swapVar_even (N : ℕ) (heven : Even N) (x y : Binary.HomogeneousPoly N) :
    BinaryPairing.binaryPairing N (binarySwapVar N x) y =
      BinaryPairing.binaryPairing N x (binarySwapVar N y) := by
  have h := BinaryPairing.binaryPairing_homogeneousAction N 0 0 swapUnit x (binarySwapVar N y)
  have hz : ((GeneralLinearGroup.det swapUnit : ℂˣ) : ℂ) ^ ((0 : ℤ) + 0 - (N : ℤ)) = 1 := by
    rw [det_swapUnit]
    have h0 : (0 : ℤ) + 0 - (N : ℤ) = -(N : ℤ) := by ring
    have heven' : Even (N : ℤ) := (Int.even_coe_nat N).mpr heven
    rw [h0, _root_.zpow_neg, heven'.neg_one_zpow]
    norm_num
  change BinaryPairing.binaryPairing N (binarySwapVar N x) (binarySwapVar N (binarySwapVar N y)) =
    _ at h
  rw [hz, binarySwapVar_involutive, one_mul] at h
  exact h

/-- **The Kostant identity of the odd-degree level-three bridge**:
`κ(f, g) = -(n+1)!/3 · binaryPairing (n+1) (Φ f) (Ψ g)` for odd `n`. -/
theorem kostantBad_eq_binaryPairing_odd (n : ℕ) (positive : 0 < n) (hodd : Odd n)
    {f g : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hf : UCocycle (rationalCoefficientComponent n trivialCharacter) latL0.sub f)
    (hg : UCocycle (dualRep (dualityData n trivialCharacter)) latL0.sub g) :
    kostant (dualityData n trivialCharacter).B latL0.σ f g =
      (-((n + 1).factorial : ℂ) / 3) *
        BinaryPairing.binaryPairing (n + 1) (PhiBad n positive f) (PsiBad n g) := by
  rw [kostantBad_eq_neg_K n positive hf hg, badLineKostantValue_eq n positive (zBad n hf) (wBad n hg),
    ← PhiBad_eq n positive hf, ← upperTotalBad_eq n hg, binApolar_eq_binaryPairing,
    binaryPairing_swapVar_even (n + 1) hodd.add_one]
  simp only [PsiBad, LinearMap.comp_apply]
  ring

end TernaryPeriodPolynomials.BoundaryDuality.Kostant

end
