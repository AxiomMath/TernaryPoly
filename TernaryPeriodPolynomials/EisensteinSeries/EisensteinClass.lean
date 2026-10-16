module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Restrict
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Complexify
public import TernaryPeriodPolynomials.EisensteinSeries.Class.FaceRestriction
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.GammaNPlane

@[expose] public section


/-!
# The class of the Eisenstein series `𝓔_P(ω_h)` in `H²(Γ, E)` (Appendix C.3-C.4)

Paper: Proposition C.4
(`ar:prop:convergence`), the choice of seeds and "the class of `𝓔_P(ω_h)`", the restriction `r_R` realized by group restriction along `i_{R,t}`,
and the constant terms.

`ConvergenceC4.prop_C_4_gammaN` (and `prop_C_4_cusp_gammaN`) shows that the series
`𝓔_P(ω_h) = ∑ ρ(γ)⁻¹ γ^* ω_h` defines, in coordinates on `Ω ≅ 𝒳`, a smooth, closed,
`Γ`-equivariant `E_n`-valued two-form. This file packages it as an element of the de Rham zig-zag
package `ZigZag.invClosed` (OB3) and attaches its class.

## Contents
* `planeEisensteinComponents`, `planeEisensteinAtComponents`: the series (for the seed of type `b`
  at the cusp `D`) as `InvComponents`.
* `planeEisensteinInv`, `planeEisensteinAtInv`: the corresponding elements of
  `ZigZag.invClosed isOpen_Omega (gammaAct Γ) (gammaRho Γ n)`; `planeEisenstein_mem_invClosed`,
  `planeEisensteinAt_mem_invClosed`: their coordinates are those of `planeEisenstein`
  (`planeEisensteinAt`).
* `eisensteinClass`, `eisensteinAtClass`: the literal class `ZigZag.deRhamClass` in
  `groupCohomology.H2 (Rep.of (gammaRho Γ n))`, the real coefficient representation `Coef n` of
  `E_n`; `eisensteinClassC`, `eisensteinAtClassC` their complexifications in `H²(Γ, E_n)_ℂ`
  (as for the seed classes).
* `eisensteinClass_gammaN`, `eisensteinAtClass_gammaN`: the paper's group `Γ(N)`, with
  `Λ_P = Γ₂(N)`.
* `eisensteinClass_gammaN_face`, `eisensteinFaceForm_gammaN_basis`: the restriction to the plane
  boundary model `e(P) = ℝ² × ℍ` of `Γ_P = Γ(N) ∩ P(ℤ)`: the class of the
  pullback `i^*𝓔_P(ω_h)` to the face is the group restriction `H²(Γ(N), E_n) → H²(Γ_P, E_n)` of
  `eisensteinClass_gammaN`, and `(i^*𝓔)(∂ᵢ, ∂ⱼ)(u, τ) = 𝓔_{ij}(u, τ, 1)`.
* Naturality (OB4): `deRhamClass_natural` (any equivariant smooth map), and
  `eisensteinClass_restrict`: the class of the series regarded as an equivariant form for a
  subgroup `H ≤ Γ` is the restriction of its class along `H ↪ Γ`.

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial UpperHalfPlane ModularForm
open scoped UpperHalfPlane MatrixGroups ContDiff

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.EisensteinClass

open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.ConvergenceC4
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4
open TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.SeedC3.Psi
open TernaryPoly.SmoothLocalDeRham

section Parametric

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ))
  {F : Type*} [FunLike F ℍ ℂ] (Λ : Subgroup (GL (Fin 2) ℝ)) [Λ.HasDetOne] [Λ.IsArithmetic]
  (n : ℕ) [CuspFormClass F Λ ((n + 3 : ℕ) : ℤ)] (f : F)

/-- **The series `𝓔_P(ω_h)` as an `InvComponents`**: antisymmetric, coefficientwise smooth, closed
and `Γ`-equivariant components (Proposition C.4). -/
def planeEisensteinComponents (hn : 4 ≤ n) (hLevi : LeviIn Γ Λ) : InvComponents Γ n where
  comp y a b := Coef.mk (planeEisenstein Γ n f y a b)
  anti _ a b := planeEisenstein_antisymm Γ n f _ a b
  smooth i j m := planeEisenstein_smooth Γ Λ n f hn i j m
  closed _ hx m i j k := planeEisenstein_closed Γ Λ n f hn hx m i j k
  equiv δ _ hx i j := planeEisenstein_pullback Γ Λ n f hn hLevi δ hx i j

/-- **OB3.** The series `𝓔_P(ω_h)` as a closed `Γ`-equivariant `E_n`-valued two-form on `Ω ≅ 𝒳`, an
element of the de Rham zig-zag package. -/
def planeEisensteinInv (hn : 4 ≤ n) (hLevi : LeviIn Γ Λ) :
    ZigZag.invClosed isOpen_Omega (gammaAct Γ) (gammaRho Γ n) :=
  (planeEisensteinComponents Γ Λ n f hn hLevi).toInv

/-- **OB3 (statement).** The series defines an element `om` of `ZigZag.invClosed` (closed,
`ρ`-equivariant, smooth chart two-form on `Ω ≅ 𝒳`) whose coordinates on the coordinate vectors
are the components of `planeEisenstein`. -/
theorem planeEisenstein_mem_invClosed (hn : 4 ≤ n) (hLevi : LeviIn Γ Λ) :
    ∃ om : ZigZag.invClosed isOpen_Omega (gammaAct Γ) (gammaRho Γ n),
      ∀ y ∈ Omega, ∀ i j : Fin 5,
        ((om : Form (F := Coef n) Omega 2) : RawForm (Fin 5 → ℝ) (Coef n) 2) y
            ![Pi.single i 1, Pi.single j 1] = Coef.mk (planeEisenstein Γ n f y i j) :=
  ⟨planeEisensteinInv Γ Λ n f hn hLevi, fun _ hy i j =>
    (planeEisensteinComponents Γ Λ n f hn hLevi).toInv_basis hy i j⟩

/-- **The class of `𝓔_P(ω_h)`** in `H²(Γ, E_n)`, with `E_n` the real coefficient representation
`gammaRho Γ n` (the normed model `Coef n` of `Sym^n((ℂ³)*) ⊗ det⁻¹`): the literal class of the
closed equivariant form `planeEisensteinInv` under the Čech-de Rham zig-zag. -/
def eisensteinClass (hn : 4 ≤ n) (hLevi : LeviIn Γ Λ) :
    groupCohomology.H2 (Rep.of (gammaRho Γ n)) :=
  ZigZag.deRhamClass isOpen_Omega convex_Omega Omega_nonempty (gammaAct Γ) (gammaRho Γ n)
    (planeEisensteinInv Γ Λ n f hn hLevi)

/-- The class of `𝓔_P(ω_h)` is the class of ANY zig-zag datum of the form (a primitive `η`, functions
`θ_δ` with `dθ_δ = δ^*η - ρ(δ)η`). -/
theorem eisensteinClass_eq (hn : 4 ≤ n) (hLevi : LeviIn Γ Λ)
    (Dt : ZigZag.Datum (TernaryPoly.SmoothLocalDeRham.d isOpen_Omega 0)
      (TernaryPoly.SmoothLocalDeRham.d isOpen_Omega 1)
      (fun g => ZigZag.pullForm isOpen_Omega (gammaAct Γ) g 1)
      (fun g => ZigZag.twForm (ZigZag.repCLM (gammaRho Γ n) g) 1)
      (planeEisensteinInv Γ Λ n f hn hLevi : Form (F := Coef n) Omega 2)) :
    eisensteinClass Γ Λ n f hn hLevi =
      ZigZag.zigzagClass (ZigZag.laws isOpen_Omega convex_Omega Omega_nonempty (gammaAct Γ)
        (gammaRho Γ n)) Dt :=
  ZigZag.deRhamClass_eq isOpen_Omega convex_Omega Omega_nonempty (gammaAct Γ) (gammaRho Γ n) _ Dt

/-- The class of `𝓔_P(ω_h)` with complex coefficients `E_n`, in `H²(Γ, E_n)_ℂ`. -/
def eisensteinClassC (hn : 4 ≤ n) (hLevi : LeviIn Γ Λ) : groupCohomology.H2 (gammaRep Γ n) :=
  complexify Γ n (eisensteinClass Γ Λ n f hn hLevi)

/-- **Restriction to a subgroup**: the class of the series regarded as an
`H`-equivariant form is the group restriction `H²(Γ, E_n) → H²(H, E_n)` of its class. -/
theorem eisensteinClass_restrict (hn : 4 ≤ n) (hLevi : LeviIn Γ Λ)
    {H : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)} (hH : H ≤ Γ) :
    ZigZag.deRhamClass isOpen_Omega convex_Omega Omega_nonempty (gammaAct H) (gammaRho H n)
        ((planeEisensteinComponents Γ Λ n f hn hLevi).restrict hH).toInv =
      (groupCohomology.map (Subgroup.inclusion hH)
          (resMor (Subgroup.inclusion hH) (gammaRho H n) (gammaRho Γ n) (gammaRho_incl hH)) 2).hom
        (eisensteinClass Γ Λ n f hn hLevi) :=
  deRhamClass_restrict (planeEisensteinComponents Γ Λ n f hn hLevi) hH

end Parametric

/-! ### Both seeds, every plane cusp -/

section Cusps

variable (b : Bool) (D : CuspData) (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ))
  {F : Type*} [FunLike F ℍ ℂ] (Λ : Subgroup (GL (Fin 2) ℝ)) [Λ.HasDetOne] [Λ.IsArithmetic]
  (n : ℕ) [CuspFormClass F Λ ((n + 3 : ℕ) : ℤ)] (f : F)

/-- The series at the cusp `D` for the seed of type `b` as an `InvComponents`. -/
def planeEisensteinAtComponents (hn : 4 ≤ n) (hLevi : LeviInCusp D Γ Λ) : InvComponents Γ n where
  comp y a c := Coef.mk (planeEisensteinAt b D Γ n f y a c)
  anti _ a c := planeEisensteinAt_antisymm b D Γ n f _ a c
  smooth i j m := planeEisensteinAt_smooth b D Γ Λ n f hn i j m
  closed _ hx m i j k := planeEisensteinAt_closed b D Γ Λ n f hn hx m i j k
  equiv δ _ hx i j := planeEisensteinAt_pullback b D Γ Λ n f hn hLevi δ hx i j

/-- **OB3 at every cusp, for both seeds**: the series is an element of `ZigZag.invClosed`. -/
def planeEisensteinAtInv (hn : 4 ≤ n) (hLevi : LeviInCusp D Γ Λ) :
    ZigZag.invClosed isOpen_Omega (gammaAct Γ) (gammaRho Γ n) :=
  (planeEisensteinAtComponents b D Γ Λ n f hn hLevi).toInv

theorem planeEisensteinAt_mem_invClosed (hn : 4 ≤ n) (hLevi : LeviInCusp D Γ Λ) :
    ∃ om : ZigZag.invClosed isOpen_Omega (gammaAct Γ) (gammaRho Γ n),
      ∀ y ∈ Omega, ∀ i j : Fin 5,
        ((om : Form (F := Coef n) Omega 2) : RawForm (Fin 5 → ℝ) (Coef n) 2) y
            ![Pi.single i 1, Pi.single j 1] = Coef.mk (planeEisensteinAt b D Γ n f y i j) :=
  ⟨planeEisensteinAtInv b D Γ Λ n f hn hLevi, fun _ hy i j =>
    (planeEisensteinAtComponents b D Γ Λ n f hn hLevi).toInv_basis hy i j⟩

/-- The class of the series at the cusp `D` for the seed of type `b`. -/
def eisensteinAtClass (hn : 4 ≤ n) (hLevi : LeviInCusp D Γ Λ) :
    groupCohomology.H2 (Rep.of (gammaRho Γ n)) :=
  ZigZag.deRhamClass isOpen_Omega convex_Omega Omega_nonempty (gammaAct Γ) (gammaRho Γ n)
    (planeEisensteinAtInv b D Γ Λ n f hn hLevi)

/-- The complexified class of the series at the cusp `D`. -/
def eisensteinAtClassC (hn : 4 ≤ n) (hLevi : LeviInCusp D Γ Λ) :
    groupCohomology.H2 (gammaRep Γ n) :=
  complexify Γ n (eisensteinAtClass b D Γ Λ n f hn hLevi)

theorem eisensteinAtClass_restrict (hn : 4 ≤ n) (hLevi : LeviInCusp D Γ Λ)
    {H : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)} (hH : H ≤ Γ) :
    ZigZag.deRhamClass isOpen_Omega convex_Omega Omega_nonempty (gammaAct H) (gammaRho H n)
        ((planeEisensteinAtComponents b D Γ Λ n f hn hLevi).restrict hH).toInv =
      (groupCohomology.map (Subgroup.inclusion hH)
          (resMor (Subgroup.inclusion hH) (gammaRho H n) (gammaRho Γ n) (gammaRho_incl hH)) 2).hom
        (eisensteinAtClass b D Γ Λ n f hn hLevi) :=
  deRhamClass_restrict (planeEisensteinAtComponents b D Γ Λ n f hn hLevi) hH

end Cusps

/-! ### The paper's group `Γ(N)` -/

section GammaN

variable (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

/-- **OB3 for `Γ(N)`**: the series `𝓔_P(ω_h)` of Proposition C.4 is an element of
`ZigZag.invClosed` for `Γ = Γ(N)` and `Λ_P = Γ₂(N)`, with the coordinates of `planeEisenstein`. -/
theorem planeEisenstein_mem_invClosed_gammaN (hn : 4 ≤ n) :
    ∃ om : ZigZag.invClosed isOpen_Omega (gammaAct (gammaN N)) (gammaRho (gammaN N) n),
      ∀ y ∈ Omega, ∀ i j : Fin 5,
        ((om : Form (F := Coef n) Omega 2) : RawForm (Fin 5 → ℝ) (Coef n) 2) y
            ![Pi.single i 1, Pi.single j 1] = Coef.mk (planeEisenstein (gammaN N) n f y i j) :=
  planeEisenstein_mem_invClosed (gammaN N) (leviGroup N) n f hn (leviIn_gammaN N)

/-- The class of `𝓔_P(ω_h) ∈ H²(Γ(N), E_n)`. -/
def eisensteinClass_gammaN (hn : 4 ≤ n) : groupCohomology.H2 (Rep.of (gammaRho (gammaN N) n)) :=
  eisensteinClass (gammaN N) (leviGroup N) n f hn (leviIn_gammaN N)

/-- The complexified class of `𝓔_P(ω_h)` in `H²(Γ(N), E_n)_ℂ`. -/
def eisensteinClassC_gammaN (hn : 4 ≤ n) : groupCohomology.H2 (gammaRep (gammaN N) n) :=
  complexify (gammaN N) n (eisensteinClass_gammaN N n f hn)

/-- The class of the series at the plane cusp `h⁻¹ P h` of `Γ(N)` for the seed of type `b`. -/
def eisensteinAtClass_gammaN (h : SL(3, ℤ)) (b : Bool) (hn : 4 ≤ n) :
    groupCohomology.H2 (Rep.of (gammaRho (gammaN N) n)) :=
  eisensteinAtClass b (CuspData.ofSL h) (gammaN N) (leviGroup N) n f hn (leviInCusp_gammaN N h)

/-- **Restriction to the face**. The plane stabilizer `Γ_P = Γ(N) ∩ P(ℤ)` acts on the
face `e(P) = ℝ² × ℍ` (`gammaNPlaneData`), and the inclusion `i : e(P) → Ω`, `(u, τ) ↦ (u, τ, 1)`, is
equivariant for `Γ_P ↪ Γ(N)`. The de Rham class of the pullback `i^*𝓔_P(ω_h)` to the face is the
group restriction of `eisensteinClass_gammaN` to `Γ_P`. -/
theorem eisensteinClass_gammaN_face (hn : 4 ≤ n) :
    ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty
        (gammaNPlaneData N).action ((gammaNPlaneData N).rhoR n)
        (faceForm (gammaNPlaneData N) (Subgroup.inclusion (inf_le_left : gammaNP N ≤ gammaN N))
          (fun g => gammaNPlaneData_plm N g)
          (planeEisensteinComponents (gammaN N) (leviGroup N) n f hn (leviIn_gammaN N))) =
      (groupCohomology.map (Subgroup.inclusion (inf_le_left : gammaNP N ≤ gammaN N))
          (resMor (Subgroup.inclusion (inf_le_left : gammaNP N ≤ gammaN N))
            ((gammaNPlaneData N).rhoR n) (gammaRho (gammaN N) n)
            (rhoR_eq_gammaRho (gammaNPlaneData N) (Subgroup.inclusion (inf_le_left : gammaNP N ≤ gammaN N))
              (fun g => gammaNPlaneData_plm N g))) 2).hom
        (eisensteinClass_gammaN N n f hn) :=
  faceForm_class (gammaNPlaneData N) (Subgroup.inclusion (inf_le_left : gammaNP N ≤ gammaN N))
    (fun g => gammaNPlaneData_plm N g)
    (planeEisensteinComponents (gammaN N) (leviGroup N) n f hn (leviIn_gammaN N))

/-- The coordinates of `i^*𝓔_P(ω_h)` on the face are the components of the series at the points
`(u, τ, 1)`. -/
theorem eisensteinFaceForm_gammaN_basis (hn : 4 ≤ n) {x : Face} (hx : x ∈ faceSet) (i j : Fin 4) :
    ((faceForm (gammaNPlaneData N) (Subgroup.inclusion (inf_le_left : gammaNP N ≤ gammaN N))
          (fun g => gammaNPlaneData_plm N g)
          (planeEisensteinComponents (gammaN N) (leviGroup N) n f hn (leviIn_gammaN N)) :
        Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) x
        ![Pi.single i 1, Pi.single j 1] =
      Coef.mk (planeEisenstein (gammaN N) n f (ptOf x) i.castSucc j.castSucc) :=
  faceForm_basis (gammaNPlaneData N) (Subgroup.inclusion (inf_le_left : gammaNP N ≤ gammaN N))
    (fun g => gammaNPlaneData_plm N g)
    (planeEisensteinComponents (gammaN N) (leviGroup N) n f hn (leviIn_gammaN N)) hx i j

end GammaN

/-! ### Naturality of the de Rham class (OB4) -/

section Natural

open TernaryPeriodPolynomials.Argument.EisensteinClass in
/-- **OB4.** Naturality of `ZigZag.deRhamClass`: for a smooth map `φ : s → t` of open convex sets which
is equivariant along `α : G → G'` (`φ ∘ g = α(g) ∘ φ`), and coefficient representations with
`ρ g = ρ' (α g)`, the class of the pullback `φ^* ω ∈ invClosed hs A ρ` is the image of the class of
`ω` under `groupCohomology.map α` (along the identity of the coefficient module). -/
theorem deRhamClass_natural {D E F : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [CompleteSpace F]
    {s : Set D} {t : Set E} {G G' : Type} [Group G] [Group G']
    {hs : IsOpen s} {ht : IsOpen t} {A : ZigZag.Action G s} {B : ZigZag.Action G' t}
    {α : G →* G'} (Φ : EquivMap hs ht A B α) (hc : Convex ℝ s) (hne : s.Nonempty)
    (hc' : Convex ℝ t) (hne' : t.Nonempty)
    {ρ : Representation ℝ G F} {ρ' : Representation ℝ G' F} (hρ : ∀ g, ρ g = ρ' (α g))
    (om : ZigZag.invClosed ht B ρ') :
    ZigZag.deRhamClass hs hc hne A ρ (pullInv Φ hρ om) =
      (groupCohomology.map α (resMor α ρ ρ' hρ) 2).hom (ZigZag.deRhamClass ht hc' hne' B ρ' om) :=
  TernaryPeriodPolynomials.Argument.EisensteinClass.deRhamClass_natural Φ hc hne hc' hne' hρ om

end Natural


end TernaryPeriodPolynomials.Argument.Statements.EisensteinClass
