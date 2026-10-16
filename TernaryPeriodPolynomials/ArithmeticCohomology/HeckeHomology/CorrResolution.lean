module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.ResolutionModel
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.Mackey

@[expose] public section


/-!
# The resolution model for a general correspondence `(S, f, c)`

Formalized by Claude Sonnet 5.5.

`ResolutionModel.lean` computes the Hecke operator of a `HeckeDatum` in an arbitrary projective resolution.  The proof uses only
the three data of a correspondence: a finite-index subgroup `S ≤ Γ`, a homomorphism `f : S →* Γ` and a coefficient morphism
`c : Res_S A ⟶ Res_f A`.  This file states the same theorem for such raw data (`ResCorr`, `corr_resolution`), which is what
the Hochschild-Serre comparison of the `P_H`-level correspondences uses.
-/

open CategoryTheory Representation Representation.Coinvariants MonoidalCategory
open TernaryPeriodPolynomials.Argument.GroupHomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeHomology

section Corr

open scoped Classical

variable {Γ : Type} [Group Γ] (A : Rep.{0} ℚ Γ) (R : ProjectiveResolution (Rep.trivial ℚ Γ ℚ))
  (S : Subgroup Γ) [S.FiniteIndex] (f : S →* Γ)

/-- A lift of the correspondence `(S, f)` to the resolution `R`: a chain map `Res_S R ⟶ Res_f R`. -/
abbrev LiftG :=
  ((Rep.resFunctor S.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj R.complex ⟶
    ((Rep.resFunctor f).mapHomologicalComplex (ComplexShape.down ℕ)).obj R.complex

/-- A lift is over the identity of the trivial module. -/
def LiftGOverId (lam : LiftG R S f) : Prop :=
  lam.f 0 ≫ (Rep.resFunctor f).map (R.π.f 0) = (Rep.resFunctor S.subtype).map (R.π.f 0)

variable (c : Rep.res S.subtype A ⟶ Rep.res f A)

/-- **The ambient operator of a correspondence in the resolution `R`**: transfer followed by `[a ⊗ r] ↦ [c a ⊗ lam r]`. -/
def ResCorr (lam : LiftG R S f) :
    R.complex.coinvariantsTensorObj A ⟶ R.complex.coinvariantsTensorObj A :=
  TYR S (YR A R) ≫
    PhiMap (AH := Rep.res S.subtype A) (AG := A)
      (P := ((Rep.resFunctor S.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj R.complex)
      (Z := R.complex) f c lam

/-- **The resolution model for a general correspondence.** -/
theorem corr_resolution (lam : LiftG R S f) (hlam : LiftGOverId R S f lam)
    (hproj : ∀ q, Projective ((Rep.resFunctor f).obj (R.complex.X q))) (n : ℕ) :
    (groupHomologyIso A n R).hom ≫ HomologicalComplex.homologyMap (ResCorr A R S f c lam) n =
      (trR S A n ≫ groupHomology.map f c n) ≫ (groupHomologyIso A n R).hom := by
  have hT := groupHomologyIso_TYR S A R n
  have hP := groupHomologyIso_PhiMap f c R hproj
    ((Rep.resFunctor S.subtype).mapProjectiveResolution R) lam hlam n
  unfold ResCorr
  erw [HomologicalComplex.homologyMap_comp, ← Category.assoc, hT, Category.assoc, hP, Category.assoc]

/-- The ambient operator on generators: `[a ⊗ r] ↦ ∑_{S x ∈ S\Γ} [c (x a) ⊗ lam (x r)]`. -/
theorem ResCorr_f_mk (lam : LiftG R S f) (q : ℕ) (a : A) (r : R.complex.X q) :
    ((ResCorr A R S f c lam).f q).hom (Coinvariants.mk _ (a ⊗ₜ[ℚ] r)) =
      ∑ x : RC S, Coinvariants.mk (A.ρ.tprod (R.complex.X q).ρ)
        (c.hom (A.ρ x.out a) ⊗ₜ[ℚ] (lam.f q).hom ((R.complex.X q).ρ x.out r)) := by
  have h1 : ((TYR S (YR A R)).f q).hom (Coinvariants.mk _ (a ⊗ₜ[ℚ] r)) =
      ∑ x : RC S, Coinvariants.mk (((A.ρ.tprod (R.complex.X q).ρ)).comp S.subtype)
        ((A.ρ.tprod (R.complex.X q).ρ) x.out (a ⊗ₜ[ℚ] r)) := tSumR_apply _ _ _
  have h2 := fun (a : Rep.res S.subtype A) (p : (Rep.resFunctor S.subtype).obj (R.complex.X q)) =>
    PhiMap_f_mk (AH := Rep.res S.subtype A) (AG := A)
      (P := ((Rep.resFunctor S.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj R.complex)
      (Z := R.complex) f c lam q a p
  refine (congrArg (fun z => (PhiMap (AH := Rep.res S.subtype A) (AG := A)
      (P := ((Rep.resFunctor S.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj R.complex)
      (Z := R.complex) f c lam |>.f q).hom z) h1).trans ?_
  exact (map_sum _ _ _).trans (Finset.sum_congr rfl fun x _ => h2 _ _)

end Corr

section CorrGeneric

variable {Γ : Type} [Group Γ] [DecidableEq Γ] (A : Rep.{0} ℚ Γ)
  (R : ProjectiveResolution (Rep.trivial ℚ Γ ℚ)) (S : Subgroup Γ) [S.FiniteIndex] (f : S →* Γ)
  (c : Rep.res S.subtype A ⟶ Rep.res f A)

/-- `corr_resolution` for an arbitrary `DecidableEq Γ` instance (the instance enters only through `groupHomologyIso`, and
`groupHomologyIso_inst_irrel` shows that it does not matter). -/
theorem corr_resolution_generic (lam : LiftG R S f) (hlam : LiftGOverId R S f lam)
    (hproj : ∀ q, Projective ((Rep.resFunctor f).obj (R.complex.X q))) (n : ℕ) :
    (groupHomologyIso A n R).hom ≫ HomologicalComplex.homologyMap (ResCorr A R S f c lam) n =
      (trR S A n ≫ groupHomology.map f c n) ≫ (groupHomologyIso A n R).hom := by
  have h := corr_resolution A R S f c lam hlam hproj n
  have e : groupHomologyIso A n R = @groupHomologyIso ℚ Γ _ _ (fun a b => Classical.propDecidable (a = b)) A n R :=
    groupHomologyIso_inst_irrel _ _ _ _ _
  rw [e]
  exact h

end CorrGeneric

end TernaryPeriodPolynomials.Argument.HeckeHomology
