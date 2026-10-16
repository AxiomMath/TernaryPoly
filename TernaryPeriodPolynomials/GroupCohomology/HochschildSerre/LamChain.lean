module

public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.TreeInstance
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.ResolutionZ

@[expose] public section


/-!
# The tree map on a pure tensor, in `P`-coinvariants of `A ⊗ R`

Formalized by Claude Sonnet 5.5.

`ZIsoR_Lam_mk`: if `t₃(ℓ ⊗ y) = [r]_U`, then the cycle `Λ[(a ⊗ ℓ) ⊗ y]` of `(Z ⊗ 1)_{P/U}` corresponds under
`ZIsoR` to the class `[a ⊗ r]` of the `P`-coinvariants of `A ⊗ R₃`.
-/

open CategoryTheory MonoidalCategory Representation Limits
open scoped TensorProduct

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HochschildSerre

variable {P : Type} [Group P] (U : Subgroup P) [U.Normal] (A : Rep.{0} ℚ P)
  [Representation.IsTrivial (A.ρ.comp U.subtype)] (R : ProjectiveResolution (Rep.trivial ℚ P ℚ))
  {L P1' : Rep.{0} ℚ (P ⧸ U)}

theorem coinvIso_hom_app_mk (X : Rep.{0} ℚ P) (v : X.V) :
    ((coinvIso U).hom.app X).hom
      (Coinvariants.mk (((Phi U).obj X ⊗ 𝟙_ (Rep.{0} ℚ (P ⧸ U))).ρ)
        (Coinvariants.mk (X.ρ.comp U.subtype) v ⊗ₜ[ℚ] (1 : ℚ))) =
      Coinvariants.mk X.ρ v := by
  have hu : ∀ z : ((Phi U).obj X).V, (ρ_ ((Phi U).obj X)).hom.hom (z ⊗ₜ[ℚ] (1 : ℚ)) = z := by
    intro z
    simp
  change coinvIterTo U X (Coinvariants.mk _ ((ρ_ ((Phi U).obj X)).hom.hom
    (Coinvariants.mk (X.ρ.comp U.subtype) v ⊗ₜ[ℚ] (1 : ℚ)))) = _
  have hu' := hu (Coinvariants.mk (X.ρ.comp U.subtype) v : ((Phi U).obj X).V)
  exact (congrArg (fun z => coinvIterTo U X (Coinvariants.mk _ z)) hu').trans rfl

theorem ZIsoR_Lam_mk (t3 : L ⊗ P1' ⟶ (Phi U).obj (R.complex.X 3)) (a : A.V) (ℓ : L.V) (y : P1'.V)
    (r : (R.complex.X 3).V)
    (hr : t3.hom (ℓ ⊗ₜ[ℚ] y) = Coinvariants.mk ((R.complex.X 3).ρ.comp U.subtype) r) :
    ((ZIsoR U R A).hom.f 3).hom
      ((Lam (Abar U A ⊗ L) (ZR U R A) P1' (ThetaIn U A R t3)).hom
        (Coinvariants.mk ((Abar U A ⊗ L).ρ.tprod P1'.ρ) ((a ⊗ₜ[ℚ] ℓ) ⊗ₜ[ℚ] y))) =
      Coinvariants.mk ((YAR R A).X 3).ρ (a ⊗ₜ[ℚ] r) := by
  rw [Lam_mk]
  have h1 : (ThetaIn U A R t3).hom ((a ⊗ₜ[ℚ] ℓ) ⊗ₜ[ℚ] y) =
      Coinvariants.mk (((A ⊗ R.complex.X 3)).ρ.comp U.subtype) (a ⊗ₜ[ℚ] r) := by
    change (nuRep U A (R.complex.X 3)).hom (a ⊗ₜ[ℚ] t3.hom (ℓ ⊗ₜ[ℚ] y)) = _
    rw [hr]
    rfl
  rw [h1]
  exact coinvIso_hom_app_mk U ((YAR R A).X 3) (a ⊗ₜ[ℚ] r)

end TernaryPeriodPolynomials.Argument.HochschildSerre
