module

public import Mathlib

@[expose] public section


/-!
# Algebraic core of the form identity at the base point

At the base point `L = w₀⁻¹u(s,t) = entryFrame s t` (Gram matrix `L Lᵀ`, `R = r² = 1 + s² + t²`) the six symmetric
directions `p₀₀, p₀₁, p₀₂, p₁₁, p₁₂, p₂₂` have the "symbols" `(Ψ, Π, D)` (`Symbols`), in terms of which the wedge
`β ∧ dτ` of two directions is `wedgeSym` (`ν = s - τ t`, with `ν² = R(1+τ²)`).  With the substitution
`ξ = (t + i s)/(r + 1)` (so `w = ξ² = (τ-i)/(τ+i)`)

  `t = ((r+1)ξ + (r-1)/ξ)/2`, `s = ((r+1)ξ - (r-1)/ξ)/(2i)`, `τ = i(1+ξ²)/(1-ξ²)`  (`tOf`, `sOf`, `tauOf`)

each wedge is `i/(2r³) · N_{ab}(ξ)` with `N_{ab}` a rational function of `ξ` alone (the 15 theorems `wedge_*`),
with only nonnegative powers of `ξ`: the mean-value property of holomorphic functions then evaluates the
angular integrals at `ξ = 0`.  The constants `N_{ab}(0)` match the pairing of the line seed
`(i dp₀₁ + dp₀₂) ∧ (dp₁₂ + (i/2)(dp₁₁ - dp₂₂))` (checked by hand and numerically).

Formalized by Claude Sonnet 5.5.  The closed forms were found with a small
exact-arithmetic computer-algebra script; each is verified by `field_simp; ring_nf`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

open Complex

/-- The symbols `(Ψ, Π, D)` of a symmetric tangent direction at `L Lᵀ`, `L = w₀⁻¹ u(s,t)`. -/
structure Symbols where
  psi : ℂ
  pi : ℂ
  d : ℂ

/-- The wedge `β ∧ dτ` of two directions given through their symbols, with `R = r²`,
`ν = s - τ t`:  `(i r/2) [ (Ψ Π' - Ψ' Π)/R - (1+τ²)(Ψ D' - Ψ' D)/R² - ν (D Π' - D' Π)/R² ]`. -/
def wedgeSym (r s t τ : ℂ) (a b : Symbols) : ℂ :=
  I * r / 2 * ((a.psi * b.pi - b.psi * a.pi) / r ^ 2
    - (1 + τ ^ 2) * (a.psi * b.d - b.psi * a.d) / r ^ 4
    - (s - τ * t) * (a.d * b.pi - b.d * a.pi) / r ^ 4)

def sym00 : Symbols := ⟨0, 0, 1⟩
def sym01 (s : ℂ) : Symbols := ⟨1, 0, 2 * s⟩
def sym02 (t τ : ℂ) : Symbols := ⟨-τ, 0, 2 * t⟩
def sym11 (s : ℂ) : Symbols := ⟨s, 1, s ^ 2⟩
def sym12 (s t τ : ℂ) : Symbols := ⟨t - τ * s, -2 * τ, 2 * s * t⟩
def sym22 (t τ : ℂ) : Symbols := ⟨-τ * t, τ ^ 2, t ^ 2⟩

/-- The parametrisation of the base point by `(r, ξ)`. -/
def sOf (r ξ : ℂ) : ℂ := ((r + 1) * ξ - (r - 1) / ξ) / (2 * I)
def tOf (r ξ : ℂ) : ℂ := ((r + 1) * ξ + (r - 1) / ξ) / 2
def tauOf (ξ : ℂ) : ℂ := I * (1 + ξ ^ 2) / (1 - ξ ^ 2)

theorem wedge_02_12 (r ξ : ℂ) (hξ : ξ ≠ 0) (hw : 1 - ξ ^ 2 ≠ 0) (hr : r ≠ 0) :
    wedgeSym r (sOf r ξ) (tOf r ξ) (tauOf ξ) (sym02 (tOf r ξ) (tauOf ξ)) (sym12 (sOf r ξ) (tOf r ξ) (tauOf ξ)) =
      I / (2 * r ^ 3) * (-2) := by
  simp only [wedgeSym, sym02, sym12, sOf, tOf, tauOf]
  field_simp
  ring_nf
  all_goals try simp
  all_goals try ring

theorem wedge_00_11 (r ξ : ℂ) (hξ : ξ ≠ 0) (hw : 1 - ξ ^ 2 ≠ 0) (hr : r ≠ 0) :
    wedgeSym r (sOf r ξ) (tOf r ξ) (tauOf ξ) (sym00) (sym11 (sOf r ξ)) =
      I / (2 * r ^ 3) * (2*I*(ξ+ξ^3)/(1-ξ^2)^2) := by
  simp only [wedgeSym, sym00, sym11, sOf, tOf, tauOf]
  field_simp
  ring_nf

theorem wedge_00_22 (r ξ : ℂ) (hξ : ξ ≠ 0) (hw : 1 - ξ ^ 2 ≠ 0) (hr : r ≠ 0) :
    wedgeSym r (sOf r ξ) (tOf r ξ) (tauOf ξ) (sym00) (sym22 (tOf r ξ) (tauOf ξ)) =
      I / (2 * r ^ 3) * (-2*I*(ξ+ξ^3)/(1-ξ^2)^2) := by
  simp only [wedgeSym, sym00, sym22, sOf, tOf, tauOf]
  field_simp
  ring_nf

theorem wedge_00_01 (r ξ : ℂ) (hξ : ξ ≠ 0) (hw : 1 - ξ ^ 2 ≠ 0) (hr : r ≠ 0) :
    wedgeSym r (sOf r ξ) (tOf r ξ) (tauOf ξ) (sym00) (sym01 (sOf r ξ)) =
      I / (2 * r ^ 3) * (-4*ξ^2/(1-ξ^2)^2) := by
  simp only [wedgeSym, sym00, sym01, sOf, tOf, tauOf]
  field_simp
  ring_nf
  all_goals try simp
  all_goals try ring

theorem wedge_00_02 (r ξ : ℂ) (hξ : ξ ≠ 0) (hw : 1 - ξ ^ 2 ≠ 0) (hr : r ≠ 0) :
    wedgeSym r (sOf r ξ) (tOf r ξ) (tauOf ξ) (sym00) (sym02 (tOf r ξ) (tauOf ξ)) =
      I / (2 * r ^ 3) * (4*I*(ξ^2+ξ^4)/(1-ξ^2)^3) := by
  simp only [wedgeSym, sym00, sym02, sOf, tOf, tauOf]
  field_simp
  ring_nf
  all_goals try simp
  all_goals try ring

theorem wedge_00_12 (r ξ : ℂ) (hξ : ξ ≠ 0) (hw : 1 - ξ ^ 2 ≠ 0) (hr : r ≠ 0) :
    wedgeSym r (sOf r ξ) (tOf r ξ) (tauOf ξ) (sym00) (sym12 (sOf r ξ) (tOf r ξ) (tauOf ξ)) =
      I / (2 * r ^ 3) * (4*(ξ+ξ^5)/(1-ξ^2)^3) := by
  simp only [wedgeSym, sym00, sym12, sOf, tOf, tauOf]
  field_simp
  ring_nf
  all_goals try simp
  all_goals try ring

theorem wedge_11_22 (r ξ : ℂ) (hξ : ξ ≠ 0) (hw : 1 - ξ ^ 2 ≠ 0) (hr : r ≠ 0) :
    wedgeSym r (sOf r ξ) (tOf r ξ) (tauOf ξ) (sym11 (sOf r ξ)) (sym22 (tOf r ξ) (tauOf ξ)) =
      I / (2 * r ^ 3) * (2*I*(ξ+ξ^3)/(1-ξ^2)^2) := by
  simp only [wedgeSym, sym11, sym22, sOf, tOf, tauOf]
  field_simp
  ring_nf
  all_goals try simp
  all_goals try ring

theorem wedge_11_01 (r ξ : ℂ) (hξ : ξ ≠ 0) (hw : 1 - ξ ^ 2 ≠ 0) (hr : r ≠ 0) :
    wedgeSym r (sOf r ξ) (tOf r ξ) (tauOf ξ) (sym11 (sOf r ξ)) (sym01 (sOf r ξ)) =
      I / (2 * r ^ 3) * (-(1+2*ξ^2+ξ^4)/(1-ξ^2)^2) := by
  simp only [wedgeSym, sym11, sym01, sOf, tOf, tauOf]
  field_simp
  ring_nf
  all_goals try simp
  all_goals try ring

theorem wedge_11_02 (r ξ : ℂ) (hξ : ξ ≠ 0) (hw : 1 - ξ ^ 2 ≠ 0) (hr : r ≠ 0) :
    wedgeSym r (sOf r ξ) (tOf r ξ) (tauOf ξ) (sym11 (sOf r ξ)) (sym02 (tOf r ξ) (tauOf ξ)) =
      I / (2 * r ^ 3) * (I*(1-5*ξ^2-5*ξ^4+ξ^6)/(1-ξ^2)^3) := by
  simp only [wedgeSym, sym11, sym02, sOf, tOf, tauOf]
  field_simp
  ring_nf
  all_goals try simp
  all_goals try ring

theorem wedge_11_12 (r ξ : ℂ) (hξ : ξ ≠ 0) (hw : 1 - ξ ^ 2 ≠ 0) (hr : r ≠ 0) :
    wedgeSym r (sOf r ξ) (tOf r ξ) (tauOf ξ) (sym11 (sOf r ξ)) (sym12 (sOf r ξ) (tOf r ξ) (tauOf ξ)) =
      I / (2 * r ^ 3) * (-2*(ξ+2*ξ^3+ξ^5)/(1-ξ^2)^3) := by
  simp only [wedgeSym, sym11, sym12, sOf, tOf, tauOf]
  field_simp
  ring_nf
  all_goals try simp
  all_goals try ring

theorem wedge_22_01 (r ξ : ℂ) (hξ : ξ ≠ 0) (hw : 1 - ξ ^ 2 ≠ 0) (hr : r ≠ 0) :
    wedgeSym r (sOf r ξ) (tOf r ξ) (tauOf ξ) (sym22 (tOf r ξ) (tauOf ξ)) (sym01 (sOf r ξ)) =
      I / (2 * r ^ 3) * ((1+6*ξ^2+ξ^4)/(1-ξ^2)^2) := by
  simp only [wedgeSym, sym22, sym01, sOf, tOf, tauOf]
  field_simp
  ring_nf
  all_goals try simp
  all_goals try ring

theorem wedge_22_02 (r ξ : ℂ) (hξ : ξ ≠ 0) (hw : 1 - ξ ^ 2 ≠ 0) (hr : r ≠ 0) :
    wedgeSym r (sOf r ξ) (tOf r ξ) (tauOf ξ) (sym22 (tOf r ξ) (tauOf ξ)) (sym02 (tOf r ξ) (tauOf ξ)) =
      I / (2 * r ^ 3) * (-I*(1+ξ^2)/(1-ξ^2)) := by
  simp only [wedgeSym, sym22, sym02, sOf, tOf, tauOf]
  field_simp
  ring_nf
  all_goals try simp
  all_goals try ring

theorem wedge_22_12 (r ξ : ℂ) (hξ : ξ ≠ 0) (hw : 1 - ξ ^ 2 ≠ 0) (hr : r ≠ 0) :
    wedgeSym r (sOf r ξ) (tOf r ξ) (tauOf ξ) (sym22 (tOf r ξ) (tauOf ξ)) (sym12 (sOf r ξ) (tOf r ξ) (tauOf ξ)) =
      I / (2 * r ^ 3) * (-2*ξ/(1-ξ^2)) := by
  simp only [wedgeSym, sym22, sym12, sOf, tOf, tauOf]
  field_simp
  ring_nf
  all_goals try simp
  all_goals try ring

theorem wedge_01_02 (r ξ : ℂ) (hξ : ξ ≠ 0) (hw : 1 - ξ ^ 2 ≠ 0) (hr : r ≠ 0) :
    wedgeSym r (sOf r ξ) (tOf r ξ) (tauOf ξ) (sym01 (sOf r ξ)) (sym02 (tOf r ξ) (tauOf ξ)) =
      I / (2 * r ^ 3) * (16*ξ^3/(1-ξ^2)^3) := by
  simp only [wedgeSym, sym01, sym02, sOf, tOf, tauOf]
  field_simp
  ring_nf
  all_goals try simp
  all_goals try ring

theorem wedge_01_12 (r ξ : ℂ) (hξ : ξ ≠ 0) (hw : 1 - ξ ^ 2 ≠ 0) (hr : r ≠ 0) :
    wedgeSym r (sOf r ξ) (tOf r ξ) (tauOf ξ) (sym01 (sOf r ξ)) (sym12 (sOf r ξ) (tOf r ξ) (tauOf ξ)) =
      I / (2 * r ^ 3) * (-2*I*(1+3*ξ^2+3*ξ^4+ξ^6)/(1-ξ^2)^3) := by
  simp only [wedgeSym, sym01, sym12, sOf, tOf, tauOf]
  field_simp
  ring_nf
  all_goals try simp
  all_goals try ring

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
