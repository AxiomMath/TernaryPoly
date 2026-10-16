module

public import TernaryPeriodPolynomials.EisensteinSeries.Dual.ComplexifyGen
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.Cusps
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.StandardCusp
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.PlaneCusps

@[expose] public section


open CategoryTheory groupCohomology
open scoped MatrixGroups

/-!
# `𝒞_Q(E*)`, complexification and the literal contragredient for the dual series

Formalized by Claude Sonnet 5.5.

`dualRhoC`: the complex dual coefficient system `ρ_ℂ ∘ ȷ`; `facePullC`, `cx_facePull`: the complex `ȷ`-pullback of faces and its
compatibility with complexification (`ComplexifyGen.cxGen_map`).  `dualCuspidalQ N n h` is `𝒞_Q(E^∨)` at the line cusp `h⁻¹Qh`, defined as the paper
defines it (apply the construction for `𝒞_P`, the `faceCuspidalInH2` at the plane cusp `ȷ(h)⁻¹Pȷ(h)`, and pull back along `ȷ`); `rQ_mem_dualCuspidal`: a class
with mixed cuspidal complexified plane restriction at `ȷ(h)` has dual with complexified line restriction in `𝒞_Q(E^∨)`.  `toLiteral` (bijective:
`toLiteral_bijective`) is the map on `H²` of the equivariant isomorphism `dualIso : E^∨ → E*`; `dualCuspidalQLiteral` is `𝒞_Q(E*)` in `H²(Γ_Q, E*)` for the literal
contragredient, `rQ_mem_dualCuspidalLiteral` the corresponding membership and `dual_rQ_standard_literal` the standard-cusp identity `r_Q ℰ_Q^∨ = η` for `E*`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinDual

open GeneralEisenstein TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.ConvergenceC4
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.GammaNFaces

variable {N : ℕ} {n : ℕ}

/-- The complex dual coefficient system of `Γ(N)`: `δ ↦ ρ_ℂ(ȷ(δ))`. -/
abbrev dualRhoC (N n : ℕ) : Representation ℂ (gammaN N) (HomogeneousPoly n) :=
  (gammaRhoC (gammaN N) n).comp (jN N)

theorem facePull_compat {S S' : Subgroup SL(3, ℤ)} (hS : S ≤ gammaN N) (hS' : S' ≤ gammaN N)
    (hSS' : ∀ s : S, jmath s.1 ∈ S') (s : S) :
    ((dualRhoN N n).comp (Subgroup.inclusion hS)) s =
      ((gammaRho (gammaN N) n).comp (Subgroup.inclusion hS')) (jRestr S S' hSS' s) := by
  simp only [MonoidHom.coe_comp, Function.comp_apply, dualRho]
  rw [jRestr_comm (gammaN N) (gammaN N) (jN N) (fun _ => rfl) S S' hS hS' hSS' s]

theorem facePullC_compat {S S' : Subgroup SL(3, ℤ)} (hS : S ≤ gammaN N) (hS' : S' ≤ gammaN N)
    (hSS' : ∀ s : S, jmath s.1 ∈ S') (s : S) :
    ((dualRhoC N n).comp (Subgroup.inclusion hS)) s =
      ((gammaRhoC (gammaN N) n).comp (Subgroup.inclusion hS')) (jRestr S S' hSS' s) := by
  simp only [MonoidHom.coe_comp, Function.comp_apply]
  rw [← jRestr_comm (gammaN N) (gammaN N) (jN N) (fun _ => rfl) S S' hS hS' hSS' s]

/-- The complex `ȷ`-pullback of face classes. -/
def facePullC {S S' : Subgroup SL(3, ℤ)} (hS : S ≤ gammaN N) (hS' : S' ≤ gammaN N)
    (hSS' : ∀ s : S, jmath s.1 ∈ S') (n : ℕ) :
    groupCohomology.H2 (Rep.of ((gammaRhoC (gammaN N) n).comp (Subgroup.inclusion hS'))) →ₗ[ℂ]
      groupCohomology.H2 (Rep.of ((dualRhoC N n).comp (Subgroup.inclusion hS))) :=
  (groupCohomology.map (jRestr S S' hSS')
    (resMorK (jRestr S S' hSS') ((dualRhoC N n).comp (Subgroup.inclusion hS))
      ((gammaRhoC (gammaN N) n).comp (Subgroup.inclusion hS')) (facePullC_compat hS hS' hSS')) 2).hom

/-- Complexification of face classes (real `Coef n` → complex `HomogeneousPoly n`), for the coefficient `E` restricted to a face. -/
abbrev cxFace (S : Subgroup SL(3, ℤ)) (hS : S ≤ gammaN N) (n : ℕ) :=
  cxGen ((gammaRho (gammaN N) n).comp (Subgroup.inclusion hS))
    ((gammaRhoC (gammaN N) n).comp (Subgroup.inclusion hS)) (fun _ _ => rfl)

/-- Complexification of face classes for the dual coefficient system. -/
abbrev cxFaceDual (S : Subgroup SL(3, ℤ)) (hS : S ≤ gammaN N) (n : ℕ) :=
  cxGen ((dualRhoN N n).comp (Subgroup.inclusion hS))
    ((dualRhoC N n).comp (Subgroup.inclusion hS)) (fun _ _ => rfl)

/-- **Complexification commutes with the `ȷ`-pullback of faces.** -/
theorem cx_facePull {S S' : Subgroup SL(3, ℤ)} (hS : S ≤ gammaN N) (hS' : S' ≤ gammaN N)
    (hSS' : ∀ s : S, jmath s.1 ∈ S')
    (x : groupCohomology.H2 (Rep.of ((gammaRho (gammaN N) n).comp (Subgroup.inclusion hS')))) :
    cxFaceDual S hS n (facePull hS hS' hSS' n x) =
      facePullC hS hS' hSS' n (cxFace S' hS' n x) :=
  cxGen_map _ _ (fun _ _ => rfl) _ _ (fun _ _ => rfl) (jRestr S S' hSS')
    (facePull_compat hS hS' hSS') (facePullC_compat hS hS' hSS') x

section Cuspidal

variable [NeZero N]

/-- **The mixed cuspidal group `𝒞_Q(E^∨)` at the line cusp `h⁻¹ Q h`** (image in `H²(Γ_Q, E^∨)`), defined as the paper defines it: by applying the
construction of `𝒞_P` (`faceCuspidalInH2`, at the plane cusp `ȷ(h)⁻¹ P ȷ(h)`) and pulling back along `ȷ`. -/
def dualCuspidalQ (N n : ℕ) [NeZero N] (h : SL(3, ℤ)) :
    Submodule ℂ (groupCohomology.H2 (Rep.of ((dualRhoC N n).comp (Subgroup.inclusion (gammaNQAt_le_N N h))))) :=
  Submodule.map (facePullC (gammaNQAt_le_N N h) (gammaNPAt_le N (jmath h)) (jmath_Q_to_P h) n)
    (faceCuspidalInH2 N (jmath h) n)

/-- **The line restriction of the dual of a class with mixed cuspidal plane restriction is mixed cuspidal for `E^∨`**: if the complexified plane
restriction of `c'` at `ȷ(h)` lies in `𝒞_P`, then the complexified line restriction of `ȷ^* c'` at `h` lies in `𝒞_Q(E^∨)`. -/
theorem rQ_mem_dualCuspidal (c' : groupCohomology.H2 (Rep.of (gammaRho (gammaN N) n))) (h : SL(3, ℤ))
    (hx : cxFace (gammaNPAt N (jmath h)) (gammaNPAt_le N (jmath h)) n
      (resTo (gammaNPAt N (jmath h)) (gammaNPAt_le N (jmath h)) (gammaRho (gammaN N) n) c') ∈
        faceCuspidalInH2 N (jmath h) n) :
    cxFaceDual (gammaNQAt N h) (gammaNQAt_le_N N h) n
      (resTo (gammaNQAt N h) (gammaNQAt_le_N N h) (dualRhoN N n) (jPull N n c')) ∈ dualCuspidalQ N n h := by
  rw [(dual_restrictions_transport (N := N) (n := n) c').1 h]
  change cxFaceDual _ _ n (facePull _ _ _ n _) ∈ _
  rw [cx_facePull]
  exact Submodule.mem_map_of_mem hx

end Cuspidal

section Literal

/-- The equivariant isomorphism `dualIso : E^∨ → E*` as a morphism of representations of a subgroup `S ≤ Γ(N)`. -/
def dualIsoMor (S : Subgroup SL(3, ℤ)) (hS : S ≤ gammaN N) (n : ℕ) :
    Rep.of ((dualRhoC N n).comp (Subgroup.inclusion hS)) ⟶
      Rep.of ((dualRepC (gammaN N) n).comp (Subgroup.inclusion hS)) :=
  Rep.ofHom ⟨(dualIso n).toLinearMap, fun s => by
    apply LinearMap.ext
    intro v
    exact (dualIso_dualRho (gammaN N) (gammaN N) (jN N) (fun _ => rfl) n (Subgroup.inclusion hS s)
      (v : Coef n))⟩

/-- **From `E^∨` to the literal contragredient `E*` in cohomology**: the map on `H²(S, ·)` induced by the equivariant isomorphism `dualIso`
(identity on the group). -/
def toLiteral (S : Subgroup SL(3, ℤ)) (hS : S ≤ gammaN N) (n : ℕ) :
    groupCohomology.H2 (Rep.of ((dualRhoC N n).comp (Subgroup.inclusion hS))) →ₗ[ℂ]
      groupCohomology.H2 (Rep.of ((dualRepC (gammaN N) n).comp (Subgroup.inclusion hS))) :=
  (groupCohomology.map (MonoidHom.id S) (dualIsoMor S hS n) 2).hom

/-- `toLiteral` is bijective: it is the isomorphism of cohomology induced by the equivariant isomorphism `dualIso`. -/
theorem toLiteral_bijective (S : Subgroup SL(3, ℤ)) (hS : S ≤ gammaN N) (n : ℕ) :
    Function.Bijective (toLiteral S hS n) := by
  let e : S ≃* S := MulEquiv.refl S
  let e' : (Rep.of ((dualRhoC N n).comp (Subgroup.inclusion hS))).V ≃ₗ[ℂ]
      (Rep.of ((dualRepC (gammaN N) n).comp (Subgroup.inclusion hS))).V := dualIso n
  have he : ∀ g, e' ∘ₗ (Rep.of ((dualRhoC N n).comp (Subgroup.inclusion hS))).ρ g =
      (Rep.of ((dualRepC (gammaN N) n).comp (Subgroup.inclusion hS))).ρ (e g) ∘ₗ e' := by
    intro g
    apply LinearMap.ext
    intro v
    exact dualIso_dualRho (gammaN N) (gammaN N) (jN N) (fun _ => rfl) n (Subgroup.inclusion hS g) (v : Coef n)
  have h := CategoryTheory.ConcreteCategory.bijective_of_isIso (groupCohomology.mapIso e e' he 2).hom
  have hfun : toLiteral S hS n = (groupCohomology.mapIso e e' he 2).hom.hom := by
    unfold toLiteral
    congr 1
  rw [hfun]
  exact h

end Literal

section CuspidalLiteral

variable [NeZero N]

/-- **`𝒞_Q(E*)` for the literal contragredient `E*`**: `𝒞_Q(E^∨)` carried to `H²(Γ_Q, E*)` by the isomorphism `dualIso`. -/
def dualCuspidalQLiteral (N n : ℕ) [NeZero N] (h : SL(3, ℤ)) :
    Submodule ℂ (groupCohomology.H2 (Rep.of ((dualRepC (gammaN N) n).comp (Subgroup.inclusion (gammaNQAt_le_N N h))))) :=
  Submodule.map (toLiteral (gammaNQAt N h) (gammaNQAt_le_N N h) n) (dualCuspidalQ N n h)

/-- **`r_Q ℰ_Q^∨ ∈ 𝒞_Q(E*)` for the literal dual**, for every cusp `h`, given that `r_P ℰ_P` is mixed cuspidal at `ȷ(h)`. -/
theorem rQ_mem_dualCuspidalLiteral (c' : groupCohomology.H2 (Rep.of (gammaRho (gammaN N) n))) (h : SL(3, ℤ))
    (hx : cxFace (gammaNPAt N (jmath h)) (gammaNPAt_le N (jmath h)) n
      (resTo (gammaNPAt N (jmath h)) (gammaNPAt_le N (jmath h)) (gammaRho (gammaN N) n) c') ∈
        faceCuspidalInH2 N (jmath h) n) :
    toLiteral (gammaNQAt N h) (gammaNQAt_le_N N h) n
      (cxFaceDual (gammaNQAt N h) (gammaNQAt_le_N N h) n
        (resTo (gammaNQAt N h) (gammaNQAt_le_N N h) (dualRhoN N n) (jPull N n c'))) ∈
      dualCuspidalQLiteral N n h :=
  Submodule.mem_map_of_mem (rQ_mem_dualCuspidal c' h hx)

end CuspidalLiteral

section StandardLiteral

open TernaryPeriodPolynomials.Argument.Statements.EisensteinClass in
/-- **`r_Q ℰ_Q^∨ = η` at the standard cusp, for the literal contragredient `E*` and complex coefficients**: the complexified line restriction of the dual
series, carried to `H²(Γ_Q, E*)` by `dualIso`, is the carried complexification of `η = ȷ^*[seed]`. -/
theorem dual_rQ_standard_literal [NeZero N] (hn : 4 ≤ n) (hN : 3 ≤ N) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    toLiteral (gammaNQAt N (1 : SL(3, ℤ))) (gammaNQAt_le_N N 1) n
      (cxFaceDual (gammaNQAt N (1 : SL(3, ℤ))) (gammaNQAt_le_N N 1) n
        (resTo (gammaNQAt N (1 : SL(3, ℤ))) (gammaNQAt_le_N N 1) (dualRhoN N n) (dualSeriesClass_gammaN N n f hn))) =
    toLiteral (gammaNQAt N (1 : SL(3, ℤ))) (gammaNQAt_le_N N 1) n
      (cxFaceDual (gammaNQAt N (1 : SL(3, ℤ))) (gammaNQAt_le_N N 1) n (dualSeedClass N n f)) := by
  rw [dual_rQ_standard N n hn hN f]

end StandardLiteral

end TernaryPeriodPolynomials.Argument.EisensteinDual
