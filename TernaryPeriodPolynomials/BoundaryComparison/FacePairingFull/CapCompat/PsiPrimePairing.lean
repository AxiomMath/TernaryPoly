module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.PsiPrime
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.PairingComparison

@[expose] public section


/-!
# Pairing of two degree-two cochains on the model cone and on the boundary

For the carrier-respecting quasi-isomorphism `Ψ' : coneR ⟶ boundaryChains` of `exists_PsiPrime`, every cycle `Ω` of
the coinvariant complex of `coneR` in degree four, all cocycles `b`, `a` of degree two of the boundary chains and
every invariant pairing `π`: the model pairing `π ∘ (Ψ'^*b ⊗ Ψ'^*a) ∘ Δ_{2,2} Ω` equals the boundary pairing
`π ∘ (b ⊗ a) ∘ Δ_{2,2} (Ψ' Ω)`, the cochain `b` being evaluated on the front face.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory
open TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology (boundaryChains)
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

theorem exists_PsiPrime_pairing : ∃ Ψ : coneR ⟶ boundaryChains, QuasiIso Ψ ∧
    ∀ {W W' : Rep.{0} ℚ Γ6} (π : W ⊗ W' ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
      (b : boundaryChains.X 2 ⟶ W) (_hb : boundaryChains.d (2+1) 2 ≫ b = 0)
      (a : boundaryChains.X 2 ⟶ W') (_ha : boundaryChains.d (2+1) 2 ≫ a = 0)
      (Ω : coneR.X 4) (_hΩ : IsCoinvCycle Ω),
      π.hom (((Ψ.f 2 ≫ b) ⊗ₘ (Ψ.f 2 ≫ a)).hom ((modelDiagSystem.Δ 2 2 4 rfl).hom Ω)) =
        π.hom ((b ⊗ₘ a).hom ((boundaryDiagSystem.Δ 2 2 4 rfl).hom ((Ψ.f 4).hom Ω))) := by
  obtain ⟨Ψ, hq, H⟩ := exists_PsiPrime
  exact ⟨Ψ, hq, fun π b hb a ha Ω hΩ =>
    pairing_comparison modelDiagSystem boundaryDiagSystem Ψ π (n := 2) (q := 1) b hb a ha (H b hb) Ω hΩ⟩

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
