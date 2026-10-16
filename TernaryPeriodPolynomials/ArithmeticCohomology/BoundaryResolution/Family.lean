module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryResolution.Orbit
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

@[expose] public section

noncomputable section
namespace TernaryPoly.BoundaryFaceResolutionComparison.Family
open CategoryTheory Category Limits HomologicalComplex

variable {G : Type} [Group G] {I : Type}

/-- The actual discrete family of representation chain complexes. -/
def complex (C : I → ChainComplex (Rep.{0} ℚ G) ℕ) :
    ChainComplex (Discrete I ⥤ Rep ℚ G) ℕ where
  X n := Discrete.functor (fun i => (C i).X n)
  d i j := Discrete.natTrans (fun x => (C x.as).d i j)
  shape i j h := by apply NatTrans.ext; funext x; exact (C x.as).shape i j h
  d_comp_d' i j k _ _ := by apply NatTrans.ext; funext x; exact (C x.as).d_comp_d i j k

/-- Evaluating this family recovers each original complex. -/
def evaluationIso (C : I → ChainComplex (Rep.{0} ℚ G) ℕ) (i : I) :
    (((evaluation (Discrete I) (Rep ℚ G)).obj ⟨i⟩).mapHomologicalComplex _).obj (complex C) ≅ C i :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (fun n m _ => by
    change 𝟙 ((C i).X n) ≫ (C i).d n m=(C i).d n m ≫ 𝟙 ((C i).X m)
    simp only [id_comp,comp_id])

variable {A : I → Rep.{0} ℚ G} (P : ∀ i, ProjectiveResolution (A i))

/-- The genuine augmentation of a full discrete family of resolutions. -/
def augmentation : complex (fun i => (P i).complex) ⟶
    (ChainComplex.single₀ (Discrete I ⥤ Rep ℚ G)).obj (Discrete.functor A) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨Discrete.natTrans (fun i => (P i.as).π.f 0), by
    apply NatTrans.ext
    funext i
    exact (P i.as).complex_d_comp_π_f_zero⟩

def singleEvaluationIso (i : I) :
    (((evaluation (Discrete I) (Rep ℚ G)).obj ⟨i⟩).mapHomologicalComplex _).obj
      ((ChainComplex.single₀ (Discrete I ⥤ Rep ℚ G)).obj (Discrete.functor A)) ≅
        (ChainComplex.single₀ (Rep ℚ G)).obj (A i) :=
  (singleMapHomologicalComplex ((evaluation (Discrete I) (Rep ℚ G)).obj ⟨i⟩)
    (ComplexShape.down ℕ) 0).app (Discrete.functor A)

theorem augmentation_evaluation (i : I) :
    (((evaluation (Discrete I) (Rep ℚ G)).obj ⟨i⟩).mapHomologicalComplex _).map (augmentation P) ≫
      (singleEvaluationIso (A := A) i).hom=
        (evaluationIso (fun i => (P i).complex) i).hom ≫ (P i).π := by
  apply (ChainComplex.toSingle₀Equiv _ _).injective
  apply Subtype.ext
  change _ ≫ _ = _ ≫ _
  simp only [augmentation,singleEvaluationIso,evaluationIso,HomologicalComplex.Hom.isoOfComponents,Functor.mapHomologicalComplex_map_f,ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
  change (P i).π.f 0 ≫ 𝟙 (A i)=𝟙 ((P i).complex.X 0) ≫ (P i).π.f 0
  exact (Category.comp_id ((P i).π.f 0)).trans (Category.id_comp ((P i).π.f 0)).symm

instance augmentation_quasiIso : QuasiIso (augmentation P) := by
  rw [quasiIso_iff_evaluation]
  intro i
  have h : QuasiIso
      ((((evaluation (Discrete I) (Rep ℚ G)).obj i).mapHomologicalComplex _).map (augmentation P) ≫
        (singleEvaluationIso (A := A) i.as).hom) := by
    rw [augmentation_evaluation]
    infer_instance
  exact quasiIso_of_comp_right _ (singleEvaluationIso (A := A) i.as).hom

instance coproducts_exact : HasExactColimitsOfShape (Discrete I) (Rep.{0} ℚ G) :=
  HasExactColimitsOfShape.domain_of_functor (Discrete I) (forget₂ (Rep ℚ G) (ModuleCat ℚ))

instance colim_additive : (colim (J := Discrete I) (C := Rep.{0} ℚ G)).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The actual direct sum of a full family of chain complexes. -/
abbrev sumComplex (C : I → ChainComplex (Rep.{0} ℚ G) ℕ) :=
  ((colim (J := Discrete I) (C := Rep ℚ G)).mapHomologicalComplex _).obj (complex C)

/-- Arbitrary coproducts of genuine projective resolutions resolve the literal coproduct. -/
def sumResolution : ProjectiveResolution (∐ A) where
  complex := sumComplex (fun i => (P i).complex)
  projective n := by
    change Projective (∐ fun i => (P i).complex.X n)
    infer_instance
  π := ((colim (J := Discrete I) (C := Rep ℚ G)).mapHomologicalComplex _).map (augmentation P) ≫
    (singleMapHomologicalComplex (colim (J := Discrete I) (C := Rep ℚ G)) (ComplexShape.down ℕ) 0).hom.app _
  quasiIso := by infer_instance

end TernaryPoly.BoundaryFaceResolutionComparison.Family
