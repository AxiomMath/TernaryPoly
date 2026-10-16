module

public import TernaryPeriodPolynomials.EisensteinSeries.Dual.PlaneInvolution
public import TernaryPeriodPolynomials.EisensteinSeries.EisensteinClass

@[expose] public section


open MvPolynomial UpperHalfPlane ModularForm
open scoped UpperHalfPlane MatrixGroups ContDiff

/-!
# The dual series `ℰ^∨` as an equivariant closed form and its class

Formalized by Claude Sonnet 5.5.

Paper: "The dual series and the boundary relation": apply the construction of `ℰ_P` to `ȷ(Γ)` and pull back along
`ȷ`.  For `Γ ⊆ SL₃(ℤ)` and `Γ' ⊇ ȷ(Γ)` (with `α : Γ → Γ'`, `α(g) = ȷ(g)`; for `Γ(N)` take `Γ' = Γ`), `jEquivMap` is the involution `ȷ̃`
of `Ω ≅ 𝒳` (`PlaneInvolution`) as an equivariant map in the sense of `EisensteinClass.deRhamClass_natural`.  For a series
`planeEisensteinInv Γ' Λ n f hn hLevi` of `Γ'` (the convergent-series construction):

* `dualRho`: the coefficient system `E^∨`, `δ ↦ ρ(ȷ(δ))` on the model `Coef n` of `E_n` (contragredient `E*` after the change `J`:
  see `DualCoefficients`);
* `dualSeriesInv`: the closed `Γ`-equivariant `E^∨`-valued two-form `ȷ̃^* ℰ` (`pullInv`); `dualSeriesInv_apply`: its coordinates;
* `dualSeriesClass`: its class in `H²(Γ, E^∨)`, and `dualSeriesClass_eq : [ȷ̃^* ℰ] = H²(ȷ)[ℰ]` (`deRhamClass_natural`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinDual

open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.ConvergenceC4
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.Statements.EisensteinClass
open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham

section Equivariant

variable (Γ Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) (α : Γ →* Γ')

/-- **The involution of `Ω` is equivariant along `α : Γ → Γ'`, `α(g) = ȷ(g)`**. -/
def jEquivMap (hα : ∀ g : Γ, (α g).1 = jmath g.1) : EquivMap isOpen_Omega isOpen_Omega (gammaAct Γ) (gammaAct Γ') α where
  φ := jPlane
  smooth := contDiffOn_jPlane
  mapsTo _ hp := jPlane_mem hp
  equiv g x hx := by
    change jPlane (planeAct (realMat g.1) x) = planeAct (realMat (α g).1) (jPlane x)
    rw [hα g]
    exact jPlane_equivariant g.1 hx


/-- **The coefficient system `E^∨`** of the dual series: the coefficient representation of `Γ' ⊇ ȷ(Γ)` pulled back along `ȷ`,
`δ ↦ ρ(ȷ(δ))`.  After the fixed linear change of coefficient coordinates by `J` this is the contragredient `E*` of `E` (see
`DualCoefficients`): `ρ(ȷ δ) f (𝐗) = det(δ) f (J δᵗ J 𝐗)`. -/
def dualRho (n : ℕ) : Representation ℝ Γ (Coef n) := (gammaRho Γ' n).comp α

theorem dualRho_apply (n : ℕ) (δ : Γ) (q : Coef n) : dualRho Γ Γ' α n δ q = gammaRho Γ' n (α δ) q := rfl

theorem toPoly_dualRho (hα : ∀ g : Γ, (α g).1 = jmath g.1) (n : ℕ) (δ : Γ) (q : Coef n) :
    Coef.toPoly (dualRho Γ Γ' α n δ q) = SeedC3.rho (realMat (jmath δ.1)) (Coef.toPoly q) := by
  rw [dualRho_apply, gammaRho_apply, toPoly_gammaRhoCoef, hα]

section Series

variable (hα : ∀ g : Γ, (α g).1 = jmath g.1) {F : Type*} [FunLike F ℍ ℂ] (Λ : Subgroup (GL (Fin 2) ℝ)) [Λ.HasDetOne] [Λ.IsArithmetic]
  (n : ℕ) [CuspFormClass F Λ ((n + 3 : ℕ) : ℤ)] (f : F) (hn : 4 ≤ n) (hLevi : LeviIn Γ' Λ)

/-- **The dual series `ℰ^∨` as a closed `Γ`-equivariant `E^∨`-valued two-form**: the pullback along `ȷ̃ : Ω → Ω` of the series
`ℰ_P(ω_f)` of `Γ' ⊇ ȷ(Γ)` ("apply the preceding construction to `ȷ(Γ)` and pull back"). -/
def dualSeriesInv : ZigZag.invClosed isOpen_Omega (gammaAct Γ) (dualRho Γ Γ' α n) :=
  pullInv (jEquivMap Γ Γ' α hα) (fun _ => rfl) (planeEisensteinInv Γ' Λ n f hn hLevi)

/-- **The class of the dual series** in `H²(Γ, E^∨)`. -/
def dualSeriesClass : groupCohomology.H2 (Rep.of (dualRho Γ Γ' α n)) :=
  ZigZag.deRhamClass isOpen_Omega convex_Omega Omega_nonempty (gammaAct Γ) (dualRho Γ Γ' α n)
    (dualSeriesInv Γ Γ' α hα Λ n f hn hLevi)

/-- **The class of the dual series is the `ȷ`-pullback of the class of the series of `Γ'`** (`deRhamClass_natural`). -/
theorem dualSeriesClass_eq :
    dualSeriesClass Γ Γ' α hα Λ n f hn hLevi =
      (groupCohomology.map α (resMor α (dualRho Γ Γ' α n) (gammaRho Γ' n) (fun _ => rfl)) 2).hom
        (eisensteinClass Γ' Λ n f hn hLevi) :=
  TernaryPeriodPolynomials.Argument.EisensteinClass.deRhamClass_natural (jEquivMap Γ Γ' α hα) convex_Omega Omega_nonempty convex_Omega Omega_nonempty
    (fun _ => rfl) (planeEisensteinInv Γ' Λ n f hn hLevi)

/-- The coordinates of the dual series: the pullback of the series along `ȷ̃`. -/
theorem dualSeriesInv_apply {x : Fin 5 → ℝ} (hx : x ∈ Omega) :
    ((dualSeriesInv Γ Γ' α hα Λ n f hn hLevi : Form (F := Coef n) Omega 2) : RawForm (Fin 5 → ℝ) (Coef n) 2) x =
      pullRaw jPlane
        ((planeEisensteinInv Γ' Λ n f hn hLevi : Form (F := Coef n) Omega 2) : RawForm (Fin 5 → ℝ) (Coef n) 2) x :=
  pullBack_apply isOpen_Omega contDiffOn_jPlane (fun _ hp => jPlane_mem hp) _ hx

/-- **The dual series at an arbitrary plane cusp and seed type** (the series `ℰ_P` at the cusp `D` for the seed of type `b`,
pulled back along `ȷ̃`). -/
def dualSeriesAtInv (b : Bool) (D : CuspData) (hLeviC : LeviInCusp D Γ' Λ) :
    ZigZag.invClosed isOpen_Omega (gammaAct Γ) (dualRho Γ Γ' α n) :=
  pullInv (jEquivMap Γ Γ' α hα) (fun _ => rfl) (planeEisensteinAtInv b D Γ' Λ n f hn hLeviC)

/-- The class of the dual series at the cusp `D`. -/
def dualSeriesAtClass (b : Bool) (D : CuspData) (hLeviC : LeviInCusp D Γ' Λ) :
    groupCohomology.H2 (Rep.of (dualRho Γ Γ' α n)) :=
  ZigZag.deRhamClass isOpen_Omega convex_Omega Omega_nonempty (gammaAct Γ) (dualRho Γ Γ' α n)
    (dualSeriesAtInv Γ Γ' α hα Λ n f hn b D hLeviC)

theorem dualSeriesAtClass_eq (b : Bool) (D : CuspData) (hLeviC : LeviInCusp D Γ' Λ) :
    dualSeriesAtClass Γ Γ' α hα Λ n f hn b D hLeviC =
      (groupCohomology.map α (resMor α (dualRho Γ Γ' α n) (gammaRho Γ' n) (fun _ => rfl)) 2).hom
        (eisensteinAtClass b D Γ' Λ n f hn hLeviC) :=
  TernaryPeriodPolynomials.Argument.EisensteinClass.deRhamClass_natural (jEquivMap Γ Γ' α hα) convex_Omega
    Omega_nonempty convex_Omega Omega_nonempty (fun _ => rfl) (planeEisensteinAtInv b D Γ' Λ n f hn hLeviC)

end Series

end Equivariant

end TernaryPeriodPolynomials.Argument.EisensteinDual
