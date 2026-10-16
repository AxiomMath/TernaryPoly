module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Line.ThetaForm

@[expose] public section


/-!
# The zig-zag datum, the closed form and the class of the line seed (LS7)

`seedDatum`: `(η, θ_g)`; `seedInv`: `σ_h = dη` as a closed `ρ`-equivariant 2-form; `seedClass`: the class in `H²(G, E_n)`;
`deRhamClass_seedInv`: the de Rham class of `σ_h` is `seedClass`.

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial
open scoped ContDiff

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.SeedC3.Psi

namespace LineData

variable {G : Type} [Group G] (D : LineData G) (h : ℂ → ℂ) (n : ℕ) (Gm : ℕ → ℂ → ℂ)

open TernaryPoly.SmoothLocalDeRham ZigZag in
/-- **The zig-zag datum of the line seed.** `η = Ψ dτ`, `θ_g`; the form is `σ_h = dη`. -/
def seedDatum (hh : DifferentiableOn ℂ h upperSet)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (Gm j) (h z * z ^ j) z)
    (hmod : ∀ g : G, ∀ z : ℂ, 0 < z.im →
      h (mob (D.lam g) z) = dnm (D.lam g) z ^ (n + 3) * h z) :
    Datum (d isOpen_faceSet 0 : Form (F := Coef n) faceSet 0 →ₗ[ℝ] Form (F := Coef n) faceSet 1)
      (d isOpen_faceSet 1) (fun g => pullForm isOpen_faceSet D.action g 1)
      (fun g => twForm (repCLM (D.rhoR n) g) 1) (d isOpen_faceSet 1 (lineEtaForm h n hh)) where
  η := lineEtaForm h n hh
  θ g := D.thetaForm h n Gm g hG
  dη := rfl
  dθ g := D.dTheta_eq h n Gm hh hG hmod g

open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothSingularComparison ZigZag in
/-- The line seed `σ_h = dη` as a closed `ρ`-equivariant 2-form on the face. -/
def seedInv (hh : DifferentiableOn ℂ h upperSet)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (Gm j) (h z * z ^ j) z)
    (hmod : ∀ g : G, ∀ z : ℂ, 0 < z.im →
      h (mob (D.lam g) z) = dnm (D.lam g) z ^ (n + 3) * h z) :
    invClosed isOpen_faceSet D.action (D.rhoR n) :=
  ⟨d isOpen_faceSet 1 (lineEtaForm h n hh), d_squared isOpen_faceSet 1 _, fun g => by
    have e := D.dTheta_eq h n Gm hh hG hmod g
    have e' : pullForm isOpen_faceSet D.action g 1 (lineEtaForm h n hh) =
        d isOpen_faceSet 0 (D.thetaForm h n Gm g hG) +
          twForm (repCLM (D.rhoR n) g) 1 (lineEtaForm h n hh) := by rw [e]; abel
    rw [← d_pullForm, e', map_add, d_squared, zero_add, d_twForm]⟩

open CategoryTheory TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothSingularComparison ZigZag in
/-- **The class of the line seed** in `H²(G, E_n)`: the class of the zig-zag datum `(η, θ_g)`. -/
def seedClass (hh : DifferentiableOn ℂ h upperSet)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (Gm j) (h z * z ^ j) z)
    (hmod : ∀ g : G, ∀ z : ℂ, 0 < z.im →
      h (mob (D.lam g) z) = dnm (D.lam g) z ^ (n + 3) * h z) :
    groupCohomology.H2 (Rep.of (D.rhoR n)) :=
  zigzagClass (laws isOpen_faceSet convex_faceSet faceSet_nonempty D.action (D.rhoR n))
    (D.seedDatum h n Gm hh hG hmod)

open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothSingularComparison ZigZag in
/-- The de Rham class map of the face sends the line seed to `seedClass`. -/
theorem deRhamClass_seedInv (hh : DifferentiableOn ℂ h upperSet)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (Gm j) (h z * z ^ j) z)
    (hmod : ∀ g : G, ∀ z : ℂ, 0 < z.im →
      h (mob (D.lam g) z) = dnm (D.lam g) z ^ (n + 3) * h z) :
    deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty D.action (D.rhoR n)
      (D.seedInv h n Gm hh hG hmod) = D.seedClass h n Gm hh hG hmod :=
  deRhamClass_eq isOpen_faceSet convex_faceSet faceSet_nonempty D.action (D.rhoR n)
    (D.seedInv h n Gm hh hG hmod) (D.seedDatum h n Gm hh hG hmod)

end LineData

end TernaryPeriodPolynomials.Argument.LineSeed
