module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BPG5
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.StabCd

@[expose] public section


/-!
# Plane geometry package, part 6: the test cocycle on the plane group of a face

Formalized by Claude Sonnet 5.5.

On `E = gammaNPAt 6 h` (the plane group of the frame `h`) the matrix homomorphism `planeEHom h : p ↦ tau (h p h⁻¹)` has line type; with an additive `ψ` on `Γ(6)` the **plane test cocycle** is
`planeTestE h ψ = cupCochain (planeEHom h) (ψ ∘ rightHom)`, i.e. `x ↦ ψ(L x₀) β^τ(x₁, x₂)` with `L` the Levi projection of the face extension `faceExt 6 h`.
-/

open scoped MatrixGroups
open CongruenceSubgroup Matrix CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.GammaNFaceFactor (planeStabEquiv)
open TernaryPeriodPolynomials.Argument.FlagH3

/-- The matrix homomorphism `p ↦ h p h⁻¹` of the plane group of `h` (plane type). -/
def planeEM (h : SL(3, ℤ)) : ↥(gammaNPAt 6 h) →* SL(3, ℤ) := (MulAut.conj h).toMonoidHom.comp (gammaNPAt 6 h).subtype

theorem planeEM_planeType (h : SL(3, ℤ)) : PlaneType (planeEM h) := fun p => by
  have := p.2.2
  exact ⟨this.1, this.2.1, this.2.2⟩

/-- The line-type homomorphism `p ↦ tau (h p h⁻¹)`. -/
def planeEHom (h : SL(3, ℤ)) : ↥(gammaNPAt 6 h) →* SL(3, ℤ) := tau.comp (planeEM h)

theorem planeEHom_lineType (h : SL(3, ℤ)) : LineType (planeEHom h) := lineType_tau (planeEM_planeType h)

/-- The additive function `ψ ∘ rightHom` on the plane group. -/
def planeTestU (h : SL(3, ℤ)) (ψ : Gamma 6 → ℚ) (p : ↥(gammaNPAt 6 h)) : ℚ := ψ ((faceExt 6 h).rightHom p)

theorem planeTestU_mul (h : SL(3, ℤ)) (ψ : Gamma 6 → ℚ) (hψ : ∀ a b, ψ (a * b) = ψ a + ψ b) (p q : ↥(gammaNPAt 6 h)) :
    planeTestU h ψ (p * q) = planeTestU h ψ p + planeTestU h ψ q := by
  simp only [planeTestU, map_mul, hψ]

/-- **The plane test cocycle** on the plane group of `h`. -/
def planeTestE (h : SL(3, ℤ)) (ψ : Gamma 6 → ℚ) : (Fin 3 → ↥(gammaNPAt 6 h)) → ℚ :=
  cupCochain (planeEHom h) (planeEHom_lineType h) (planeTestU h ψ)

theorem planeTestE_cocycle (h : SL(3, ℤ)) (ψ : Gamma 6 → ℚ) (hψ : ∀ a b, ψ (a * b) = ψ a + ψ b) :
    dThree (planeTestE h ψ) = 0 :=
  cupCochain_cocycle _ _ _ (planeTestU_mul h ψ hψ)

end TernaryPeriodPolynomials.Argument.GammaNStokes
