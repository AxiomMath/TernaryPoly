module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryResolution.Family

@[expose] public section

noncomputable section
namespace TernaryPoly.BoundaryFaceResolutionComparison.Family
open CategoryTheory Category Limits HomologicalComplex EquivariantSingularSmall

variable {G : Type} [Group G] {I : Type}

/-- The summand inclusion retains the specified individual chain complex. -/
def inclusion (C : I → ChainComplex (Rep.{0} ℚ G) ℕ) (i : I) : C i ⟶ sumComplex C where
  f n := Sigma.ι (fun i => (C i).X n) i
  comm' n m _ := by
    exact colimit.ι_map ((complex C).d n m) ⟨i⟩

/-- Hom out of the actual coproduct is the full product, with literal summand evaluation. -/
def coproductHomLinearEquiv (A : I → Rep.{0} ℚ G) (W : Rep.{0} ℚ G) :
    ((∐ A) ⟶ W) ≃ₗ[ℚ] (∀ i,A i ⟶ W) where
  toFun f i := Sigma.ι A i ≫ f
  invFun f := Sigma.desc f
  left_inv f := by apply Sigma.hom_ext; intro i; simp
  right_inv f := by funext i; exact Sigma.ι_comp_desc f i
  map_add' f g := by funext i; simp only [Pi.add_apply,Preadditive.comp_add]
  map_smul' r f := by funext i; simp only [Pi.smul_apply,RingHom.id_apply,Linear.comp_smul]

/-- Product of all genuine Hom cochain complexes, with no finite-support condition on cochains. -/
def productCochains (C : I → ChainComplex (Rep.{0} ℚ G) ℕ) (W : Rep.{0} ℚ G) :
    CochainComplex (ModuleCat ℚ) ℕ where
  X n := ModuleCat.of ℚ (∀ i,(C i).X n ⟶ W)
  d n m := ModuleCat.ofHom {
    toFun f i := (C i).d m n ≫ f i
    map_add' f g := by funext i; simp only [Pi.add_apply,Preadditive.comp_add]
    map_smul' r f := by funext i; simp only [Pi.smul_apply,RingHom.id_apply,Linear.comp_smul] }
  shape n m h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    funext i
    change (C i).d m n ≫ f i=0
    rw [(C i).shape m n (by exact fun hh => h hh),zero_comp]
  d_comp_d' n m k _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    funext i
    change (C i).d k m ≫ ((C i).d m n ≫ f i)=0
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun u => u ≫ f i) ((C i).d_comp_d k m n)).trans zero_comp)

/-- The full-family Hom model is isomorphic as cochains to the product of all orbit factors. -/
def sumHomIso (C : I → ChainComplex (Rep.{0} ℚ G) ℕ) (W : Rep.{0} ℚ G) :
    homCochains (sumComplex C) W ≅ productCochains C W :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (coproductHomLinearEquiv (fun i => (C i).X n) W).toModuleIso)
    (fun n m _ => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      funext i
      change (C i).d m n ≫ (Sigma.ι (fun i => (C i).X n) i ≫ f)=
        Sigma.ι (fun i => (C i).X m) i ≫ ((sumComplex C).d m n ≫ f)
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun u => u ≫ f) ((inclusion C i).comm m n).symm).trans (Category.assoc _ _ _)))

end TernaryPoly.BoundaryFaceResolutionComparison.Family
