module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Cusp.SeriesForm

@[expose] public section


/-!
# The constant term of the series at the plane cusp `h⁻¹ P h`

For `3 ≤ N`, `4 ≤ n` and every `h ∈ SL₃(ℤ)`, the class of the pullback of the (holomorphic) series at
the cusp `h⁻¹ P h` to the boundary model `e(P)` equals the seed class transported to `h`:
the pullback is the `ρ(h⁻¹)`-twist of the standard face form (`cuspFaceForm_eq_twist`), the standard
face form is the seed plus a form of vanishing torus average (`restAverageVanishes`), and a form of
vanishing average has zero class along the conjugated plane group (`deRhamClass_comapInv_eq_zero`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory groupCohomology
open scoped ContDiff MatrixGroups
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPoly.SmoothLocalDeRham
  TernaryPeriodPolynomials.Argument.Statements.EisensteinClass
  TernaryPeriodPolynomials.Argument.SeedC3.Psi TernaryPoly.SmoothCoveringDeRham

section Final

variable (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (h : SL(3, ℤ))

/-- The standard-cusp form transported to the plane group `Γ_{h⁻¹Ph}` along `conjP N h` (same
cochain, the action `cuspFaceAction N h`, coefficient representation still that of `Γ_P`). -/
def comapAt (F : ZigZag.invClosed isOpen_faceSet (gammaNPlaneData N).action
    ((gammaNPlaneData N).rhoR n)) :
    ZigZag.invClosed isOpen_faceSet (cuspFaceAction N h)
      ((planeDataComap (gammaNPlaneData N) (conjP N h).toMonoidHom).rhoR n) :=
  comapInv (gammaNPlaneData N) (conjP N h).toMonoidHom n F

omit [NeZero N] in
/-- Transport along the conjugation is additive. -/
theorem comapAt_sub (a b : ZigZag.invClosed isOpen_faceSet (gammaNPlaneData N).action
    ((gammaNPlaneData N).rhoR n)) :
    comapAt N n h (a - b) = comapAt N n h a - comapAt N n h b := rfl

/-- **The seed at the plane cusp `h⁻¹ P h`**: the standard seed transported along the conjugation
`conjP N h` and the coefficient comparison `ρ(h⁻¹)`. -/
def cuspSeedAt : ZigZag.invClosed isOpen_faceSet (cuspFaceAction N h) (rhoAt N h n) :=
  twInv (intertwines_rhoAt N n h) (comapAt N n h
    (cuspSeedInv (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) (f := f)))

variable (hn : 4 ≤ n)

/-- **The constant term of the series at the plane cusp `h⁻¹ P h` along its own face is the seed
class at `h`** (`3 ≤ N`, `4 ≤ n`, holomorphic seed). -/
theorem constant_term_identity_cusp (hN : 3 ≤ N) :
    ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (cuspFaceAction N h)
        (rhoAt N h n)
        (cuspFaceForm N h (planeEisensteinAtComponents false (CuspData.ofSL h) (gammaN N)
          (leviGroup N) n f hn (leviInCusp_gammaN N h))) =
      ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (cuspFaceAction N h)
        (rhoAt N h n) (cuspSeedAt N n f h) := by
  have hT := intertwines_rhoAt N n h
  have e : cuspFaceForm N h (planeEisensteinAtComponents false (CuspData.ofSL h) (gammaN N)
      (leviGroup N) n f hn (leviInCusp_gammaN N h)) =
      twInv hT (comapAt N n h (eisensteinFace N n f hn)) :=
    Subtype.ext (cuspFaceForm_eq_twist N n f hn h)
  rw [e]
  have h0 : ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty
      (cuspFaceAction N h) ((planeDataComap (gammaNPlaneData N) (conjP N h).toMonoidHom).rhoR n)
      (comapAt N n h (restFaceForm N n f hn)) = 0 :=
    deRhamClass_comapInv_eq_zero (gammaNPlaneData N) (conjP N h).toMonoidHom n (latticeData_gammaN N)
      (Nat.cast_ne_zero.mpr (NeZero.ne N)) (conjP N h).surjective _
      (restAverageVanishes N n f hn hN)
  have h1 := deRhamClass_twist_eq_zero convex_faceSet faceSet_nonempty hT _ h0
  have h2 : twInv hT (comapAt N n h (restFaceForm N n f hn)) =
      twInv hT (comapAt N n h (eisensteinFace N n f hn)) - cuspSeedAt N n f h := by
    unfold restFaceForm cuspSeedAt
    rw [comapAt_sub, twInv_sub]
  rw [h2] at h1
  have h3 := (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty
    (cuspFaceAction N h) (rhoAt N h n)).map_sub (twInv hT (comapAt N n h (eisensteinFace N n f hn)))
    (cuspSeedAt N n f h)
  exact sub_eq_zero.1 (h3.symm.trans h1)

end Final

end TernaryPeriodPolynomials.Argument.EisensteinClass
