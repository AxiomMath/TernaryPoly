module

public import TernaryPeriodPolynomials.Topology.Rational.Cohomology.Descent
public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.SmallCochains

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFullTransfer
open CategoryTheory HomologicalComplex EquivariantSingularSmall RationalCohomologyDescent

variable {G : Type} [Group G] (H : Subgroup G)

abbrev restrictedComplex (C : ChainComplex (Rep ℚ G) ℕ) :=
  ((Rep.resFunctor H.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj C

/-- Restriction retains the literal underlying linear map. -/
def restrictHom (A V : Rep.{0} ℚ G) :
    (A ⟶ V) →ₗ[ℚ] (Rep.res H.subtype A ⟶ Rep.res H.subtype V) where
  toFun f := (Rep.resFunctor H.subtype).map f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restriction on arbitrary genuine Hom complexes, without a projectivity assumption. -/
def restriction (C : ChainComplex (Rep ℚ G) ℕ) (V : Rep.{0} ℚ G) :
    homCochains C V ⟶ homCochains (restrictedComplex H C) (Rep.res H.subtype V) where
  f n := ModuleCat.ofHom (restrictHom H (C.X n) V)
  comm' _ _ _ := by ext f; rfl

@[simp] theorem restriction_apply (C : ChainComplex (Rep ℚ G) ℕ) (V : Rep.{0} ℚ G)
    (n : ℕ) (f : C.X n ⟶ V) :
    (restriction H C V).f n f = (Rep.resFunctor H.subtype).map f := rfl

variable [H.FiniteIndex]

/-- Finite-index descent is adjunction followed by the genuine normalized trace. -/
def transferHom (A V : Rep.{0} ℚ G) :
    (Rep.res H.subtype A ⟶ Rep.res H.subtype V) →ₗ[ℚ] (A ⟶ V) where
  toFun f := Rep.resCoindToHom H.subtype A (Rep.res H.subtype V) f ≫ coindRetraction H V
  map_add' f g := by
    change (Rep.resCoindHomEquiv.{0} H.subtype A (Rep.res H.subtype V)) (f+g) ≫ _ = _
    rw [map_add,Preadditive.add_comp]
    rfl
  map_smul' r f := by
    change (Rep.resCoindHomEquiv.{0} H.subtype A (Rep.res H.subtype V)) (r • f) ≫ _ = _
    rw [map_smul,Linear.smul_comp]
    rfl

omit [H.FiniteIndex] in
/-- Adjunction commutes with literal precomposition. -/
theorem adjunction_precomp {A B V : Rep.{0} ℚ G} (u : A ⟶ B)
    (f : Rep.res H.subtype B ⟶ Rep.res H.subtype V) :
    Rep.resCoindToHom H.subtype A (Rep.res H.subtype V)
      ((Rep.resFunctor H.subtype).map u ≫ f) =
      u ≫ Rep.resCoindToHom H.subtype B (Rep.res H.subtype V) f := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext g
  change f.hom (u.hom (A.ρ g x)) = f.hom (B.ρ g (u.hom x))
  exact congrArg (fun y => f.hom y) (LinearMap.congr_fun (u.hom.isIntertwining' g) x)

theorem transferHom_precomp {A B V : Rep.{0} ℚ G} (u : A ⟶ B)
    (f : Rep.res H.subtype B ⟶ Rep.res H.subtype V) :
    transferHom H A V ((Rep.resFunctor H.subtype).map u ≫ f) =
      u ≫ transferHom H B V f := by
  change _ ≫ coindRetraction H V = _ ≫ (_ ≫ coindRetraction H V)
  rw [adjunction_precomp,Category.assoc]

/-- The normalized transfer is a cochain map in every degree. -/
def transfer (C : ChainComplex (Rep ℚ G) ℕ) (V : Rep.{0} ℚ G) :
    homCochains (restrictedComplex H C) (Rep.res H.subtype V) ⟶ homCochains C V where
  f n := ModuleCat.ofHom (transferHom H (C.X n) V)
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact (transferHom_precomp H (C.d j i) f).symm

/-- Full-level cochains are fixed by normalized restriction followed by transfer. -/
theorem restrict_transferHom (A V : Rep.{0} ℚ G) (f : A ⟶ V) :
    transferHom H A V (restrictHom H A V f) = f := by
  have h := adjunction_precomp H f (𝟙 (Rep.res H.subtype V))
  simp only [Category.comp_id] at h
  change Rep.resCoindToHom H.subtype A (Rep.res H.subtype V)
    ((Rep.resFunctor H.subtype).map f) ≫ coindRetraction H V = f
  rw [h,Category.assoc]
  change f ≫ (coindUnit H V ≫ coindRetraction H V) = f
  rw [coindUnit_retraction,Category.comp_id]

/-- Genuine full-level restriction has a cochain-level left inverse. -/
theorem restriction_transfer (C : ChainComplex (Rep ℚ G) ℕ) (V : Rep.{0} ℚ G) :
    restriction H C V ≫ transfer H C V = 𝟙 (homCochains C V) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact restrict_transferHom H (C.X n) V

end TernaryPoly.SymmetricSpaceBoundaryFullTransfer
