module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryResolution.Quotient
public import TernaryPeriodPolynomials.Topology.Equivariant.MayerVietoris.HomologySequence

@[expose] public section


noncomputable section
namespace TernaryPoly.BoundaryFaceResolutionComparison
open CategoryTheory Category Limits HomologicalComplex

section Functor
variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  [HasBinaryBiproducts C]
  (F : C ⥤ D) [F.PreservesZeroMorphisms] [PreservesBinaryBiproducts F]
  {A B A' B' : C} (f : A ⟶ A') (g : B ⟶ B')

theorem mapBiprod_square : F.map (biprod.map f g) ≫ (F.mapBiprod A' B').hom=
    (F.mapBiprod A B).hom ≫ biprod.map (F.map f) (F.map g) := by
  apply biprod.hom_ext <;>
    simp only [Category.assoc,Functor.mapBiprod_hom,biprod.lift_fst,biprod.lift_snd,
      biprod.map_fst,biprod.map_snd,biprod.lift_fst_assoc,biprod.lift_snd_assoc,←F.map_comp]

theorem mapBiprod_isIso [IsIso (F.map f)] [IsIso (F.map g)] : IsIso (F.map (biprod.map f g)) := by
  let e := F.mapBiprod A B ≪≫ biprod.mapIso (asIso (F.map f)) (asIso (F.map g)) ≪≫ (F.mapBiprod A' B').symm
  have h : F.map (biprod.map f g)=e.hom := by
    apply (cancel_mono (F.mapBiprod A' B').hom).mp
    refine (mapBiprod_square F f g).trans ?_
    change (F.mapBiprod A B).hom ≫ biprod.map (F.map f) (F.map g)=
      ((F.mapBiprod A B).hom ≫ biprod.map (F.map f) (F.map g) ≫ (F.mapBiprod A' B').inv) ≫
        (F.mapBiprod A' B').hom
    simp only [Category.assoc,Iso.inv_hom_id,comp_id]
  rw [h]
  infer_instance
end Functor

variable {G : Type} [Group G] {A B A' B' : ChainComplex (Rep ℚ G) ℕ}
  (f : A ⟶ A') (g : B ⟶ B') [QuasiIso f] [QuasiIso g]

theorem biprodMap_quasiIso : QuasiIso (biprod.map f g) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : IsIso ((homologyFunctor (Rep ℚ G) (ComplexShape.down ℕ) n).map f) :=
    inferInstanceAs (IsIso (homologyMap f n))
  have : IsIso ((homologyFunctor (Rep ℚ G) (ComplexShape.down ℕ) n).map g) :=
    inferInstanceAs (IsIso (homologyMap g n))
  exact mapBiprod_isIso (homologyFunctor (Rep ℚ G) (ComplexShape.down ℕ) n) f g

section Projective
variable {C : Type*} [Category* C] [Abelian C] {K L : ChainComplex C ℕ} (a : K ⟶ L)
  [∀ n, Projective (K.X n)] [∀ n, Projective (L.X n)]

/-- A cone of degreewise projective nonnegative complexes is degreewise projective. -/
theorem projectiveCone (n : ℕ) : Projective ((homotopyCofiber a).X n) := by
  cases n with
  | zero => exact Projective.of_iso (homotopyCofiber.XIso a 0 (by simp [ComplexShape.down_Rel])).symm inferInstance
  | succ n => exact Projective.of_iso (homotopyCofiber.XIsoBiprod a (n+1) n (Cone.downRel n)).symm inferInstance
end Projective

end TernaryPoly.BoundaryFaceResolutionComparison
