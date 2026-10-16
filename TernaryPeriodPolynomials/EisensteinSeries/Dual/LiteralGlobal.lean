module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.DualFlags
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Gamma.NDual
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Gamma6.Final

@[expose] public section


open CategoryTheory groupCohomology
open scoped MatrixGroups DirectSum

/-!
# The dual classes of `Γ(N)` as classes of the literal contragredient `E_n^*`, with the zero-flag format

Formalized by Claude Sonnet 5.5.

the Stokes statement at level `Γ(6)` (`GammaNStokes.gamma6_stokes_En`) is stated for classes of `H²(Γ(N), E_n^*)` with `E_n^*` the literal contragredient
`gammaNRepAllDual N n = Rep.of ((gammaNRepAll N n).ρ.dual)` and zero restrictions `twoCohomologyRestriction (Subgroup.inclusion …) (gammaNRepAllDual N n)` to all flag groups.  the admissible
dual classes `Hd` live in `H²(Γ(N), E^∨_ℂ)` (`E^∨ = E ∘ ȷ`).  Here:

* `toLiteralG`: the isomorphism `H²(Γ(N), E^∨) ≅ H²(Γ(N), E_n^*)` induced by the equivariant isomorphism `dualIso` (`toLiteralG_bijective`); `rep_dual_eq`: `Rep.of (dualRepC …) = gammaNRepAllDual`;
* `toLiteralG_res`: it commutes with restriction to every subgroup of `Γ(N)` (`toLiteral S` of `resToC S` is `twoCohomologyRestriction` of `toLiteralG`);
* `toLiteralG_zeroFlags`, `HdLit`, `HdLit_zeroFlags`: `HdLit = toLiteralG(range dualE)` and every element has zero restriction to every `Γ(N) ∩ h⁻¹Bh` in the exact format of `gamma6_stokes_En`;
* `gamma6_stokes_dualSeries`: the `gamma6_stokes_En` instantiated at the actual dual series `toLiteralG(ℰ_Q^∨(u))`, `u` any tuple of cusp forms, `c` any class of `H²(Γ(6), E_n)` with zero flags.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinDual

open GeneralEisenstein TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.ConvergenceC4
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.SphericalDetection.Helpers (twoCohomologyRestriction)

section Generic

variable {G S : Type} [Group G] [Group S] {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
  (ρ₁ : Representation ℂ G V₁) (ρ₂ : Representation ℂ G V₂) (T : V₁ →ₗ[ℂ] V₂)
  (hT : ∀ g v, T (ρ₁ g v) = ρ₂ g (T v))

/-- The map on `H²` induced by an equivariant linear map of two coefficient modules of the same group. -/
def mapId : groupCohomology.H2 (Rep.of ρ₁) →ₗ[ℂ] groupCohomology.H2 (Rep.of ρ₂) :=
  (groupCohomology.map (MonoidHom.id G) (Rep.ofHom ⟨T, fun g => LinearMap.ext fun v => hT g v⟩ :
    Rep.res (MonoidHom.id G) (Rep.of ρ₁) ⟶ Rep.of ρ₂) 2).hom

/-- The group restriction of a class to a subgroup. -/
def resG (ι : S →* G) (ρ : Representation ℂ G V₁) :
    groupCohomology.H2 (Rep.of ρ) →ₗ[ℂ] groupCohomology.H2 (Rep.of (ρ.comp ι)) :=
  (groupCohomology.map ι (resMorK ι (ρ.comp ι) ρ (fun _ => rfl)) 2).hom

/-- **`mapId` commutes with restriction to a subgroup.** -/
theorem mapId_resG (ι : S →* G) (x : groupCohomology.H2 (Rep.of ρ₁)) :
    mapId (ρ₁.comp ι) (ρ₂.comp ι) T (fun s v => hT (ι s) v) (resG ι ρ₁ x) = resG ι ρ₂ (mapId ρ₁ ρ₂ T hT x) := by
  induction x using groupCohomology.H2_induction_on with
  | h z =>
    unfold mapId resG
    rw [groupCohomology.H2π_comp_map_apply, groupCohomology.H2π_comp_map_apply, groupCohomology.H2π_comp_map_apply,
      groupCohomology.H2π_comp_map_apply]
    congr 1

/-- A bijective equivariant map of coefficient modules induces a bijection on `H²`. -/
theorem mapId_bijective (e : V₁ ≃ₗ[ℂ] V₂) (hT : ∀ g v, e (ρ₁ g v) = ρ₂ g (e v)) :
    Function.Bijective (mapId ρ₁ ρ₂ e.toLinearMap hT) := by
  let eG : G ≃* G := MulEquiv.refl G
  let e' : (Rep.of ρ₁).V ≃ₗ[ℂ] (Rep.of ρ₂).V := e
  have he : ∀ g, e' ∘ₗ (Rep.of ρ₁).ρ g = (Rep.of ρ₂).ρ (eG g) ∘ₗ e' := by
    intro g
    exact LinearMap.ext fun v => hT g v
  have h := CategoryTheory.ConcreteCategory.bijective_of_isIso (groupCohomology.mapIso eG e' he 2).hom
  have hfun : mapId ρ₁ ρ₂ e.toLinearMap hT = (groupCohomology.mapIso eG e' he 2).hom.hom := by
    unfold mapId
    congr 1
  rw [hfun]
  exact h

end Generic

variable (N n : ℕ)
theorem dualIso_equivariant_G (g : gammaN N) (v : GeneralEisenstein.HomogeneousPoly n) :
    dualIso n (dualRhoC N n g v) = dualRepC (gammaN N) n g (dualIso n v) :=
  dualIso_dualRho (gammaN N) (gammaN N) (jN N) (fun _ => rfl) n g (v : Coef n)

/-- **From `E^∨` to the literal contragredient in cohomology of `Γ(N)`.** -/
def toLiteralG : groupCohomology.H2 (Rep.of (dualRhoC N n)) →ₗ[ℂ] groupCohomology.H2 (Rep.of (dualRepC (gammaN N) n)) :=
  mapId (dualRhoC N n) (dualRepC (gammaN N) n) (dualIso n).toLinearMap (dualIso_equivariant_G N n)

theorem toLiteralG_bijective : Function.Bijective (toLiteralG N n) :=
  mapId_bijective (dualRhoC N n) (dualRepC (gammaN N) n) (dualIso n) (dualIso_equivariant_G N n)

/-- The literal dual of `E_n` over `Γ(N)` in S1's notation is the contragredient of `gammaRhoC`. -/
theorem rep_dual_eq : Rep.of (dualRepC (gammaN N) n) = TernaryPeriodPolynomials.Argument.GammaNStokes.gammaNRepAllDual N n := rfl

/-- **`toLiteralG` commutes with restriction to every subgroup of `Γ(N)`.** -/
theorem toLiteralG_res (S : Subgroup SL(3, ℤ)) (hS : S ≤ gammaN N) (c : groupCohomology.H2 (Rep.of (dualRhoC N n))) :
    mapId ((dualRhoC N n).comp (Subgroup.inclusion hS)) ((dualRepC (gammaN N) n).comp (Subgroup.inclusion hS))
        (dualIso n).toLinearMap (fun s v => dualIso_equivariant_G N n (Subgroup.inclusion hS s) v)
        (resG (Subgroup.inclusion hS) (dualRhoC N n) c) =
      twoCohomologyRestriction (Subgroup.inclusion hS) (Rep.of (dualRepC (gammaN N) n)) (toLiteralG N n c) :=
  mapId_resG (dualRhoC N n) (dualRepC (gammaN N) n) (dualIso n).toLinearMap (dualIso_equivariant_G N n)
    (Subgroup.inclusion hS) c

/-- The dual series classes (literal contragredient) have zero restriction to every flag group, in the format of S1's `gamma6_stokes_En`. -/
theorem toLiteralG_zeroFlags (c : groupCohomology.H2 (Rep.of (dualRhoC N n)))
    (hc : TernaryPeriodPolynomials.Argument.FormClassK.DualZeroFlags N n c) (g : SL(3, ℤ)) :
    twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNBAt_le_gammaN N g hp)) (TernaryPeriodPolynomials.Argument.GammaNStokes.gammaNRepAllDual N n)
      (toLiteralG N n c) = 0 := by
  have h0 : resG (Subgroup.inclusion (fun _ hp => gammaNBAt_le_gammaN N g hp)) (dualRhoC N n) c = 0 := hc g
  have := toLiteralG_res N n (gammaNBAt N g) (fun _ hp => gammaNBAt_le_gammaN N g hp) c
  rw [h0, map_zero] at this
  exact this.symm

section Hd

open TernaryPeriodPolynomials.Argument.FormClassK

variable {N n} [NeZero N]

/-- **The literal dual classes generated by the dual series**: `toLiteralG` of S7's `Hd`. -/
def HdLit (hn : 4 ≤ n) :
    Submodule ℂ (groupCohomology.H2 (TernaryPeriodPolynomials.Argument.GammaNStokes.gammaNRepAllDual N n)) :=
  LinearMap.range ((toLiteralG N n) ∘ₗ (dualE (N := N) (n := n) hn))

/-- **Admissibility in S1's format**: every element of `HdLit` has zero restriction to every flag group `Γ(N) ∩ h⁻¹Bh` (the hypothesis `hz'` of `gamma6_stokes_En`). -/
theorem HdLit_zeroFlags (hN : 3 ≤ N) (hn : 4 ≤ n)
    (c' : groupCohomology.H2 (TernaryPeriodPolynomials.Argument.GammaNStokes.gammaNRepAllDual N n)) (hc' : c' ∈ HdLit hn) (g : SL(3, ℤ)) :
    twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNBAt_le_gammaN N g hp))
      (TernaryPeriodPolynomials.Argument.GammaNStokes.gammaNRepAllDual N n) c' = 0 := by
  obtain ⟨u, rfl⟩ := hc'
  exact toLiteralG_zeroFlags N n _ (Hd_zeroFlags N n hN hn ⟨dualE hn u, LinearMap.mem_range_self _ u⟩) g

open TernaryPeriodPolynomials.Argument.GammaNStokes TernaryPeriodPolynomials.Argument.GammaNFaces in
/-- **S1's Stokes relation at level `Γ(6)` for the actual dual series**: for a class `c` of `H²(Γ(6), E_n)` with zero flag restrictions and any tuple `u` of cusp forms, the literal dual class
`toLiteralG (ℰ_Q^∨(u))` is admissible (`HdLit_zeroFlags`) and `gamma6_stokes_En` applies to the pair. -/
theorem gamma6_stokes_dualSeries (hn : 4 ≤ n) (c : groupCohomology.H2 (gammaNRepAll 6 n)) (hz : ZeroFlags 6 n c)
    (u : DualTuple 6 n) :
    ∑ i : LineFaces 6, lineFacePairM (rhoEn n) i (rLine 6 n i.rep c)
        (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp))
          (gammaNRepAllDual 6 n) (toLiteralG 6 n (dualE hn u))) +
      ∑ i : PlaneFaces 6, planeFacePairM (rhoEn n) i (rPlane 6 n (planeFaceRepr i) c)
        (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp))
          (gammaNRepAllDual 6 n) (toLiteralG 6 n (dualE hn u))) = 0 :=
  gamma6_stokes_En n c _ hz (HdLit_zeroFlags (by norm_num) hn _ ⟨u, rfl⟩)

end Hd

end TernaryPeriodPolynomials.Argument.EisensteinDual
