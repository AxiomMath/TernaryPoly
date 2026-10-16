module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.IncidenceHomologyNaturality
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.IncidencePaths
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.LinearAlgebra.Finsupp.SumProd

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
open CategoryTheory Limits IntegralGL3Congruence OrdinaryIncidence
open SymmetricSpaceBoundaryMV SymmetricSpaceBoundaryFaceAugmentation
open scoped MonoidAlgebra

def labelSumLinear (ι : Type) : ℚ[ι] →ₗ[ℚ] ℚ :=
  (Finsupp.linearCombination ℚ (fun _ : ι => (1 : ℚ))).comp
    (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

@[simp] theorem labelSumLinear_single (ι : Type) (i : ι) (r : ℚ) :
    labelSumLinear ι (MonoidAlgebra.single i r)=r := by
  change Finsupp.linearCombination ℚ (fun _ : ι => (1 : ℚ)) (Finsupp.single i r)=r
  simp only [Finsupp.linearCombination_single,smul_eq_mul,mul_one]

/-- Total coefficient of a label permutation module, with its actual equivariance. -/
def labelSum {ι : Type} [MulAction principalSix ι] : Rep.ofMulAction ℚ principalSix ι ⟶
    Rep.trivial ℚ principalSix ℚ :=
  Rep.ofHom ⟨labelSumLinear ι,fun g => by
    apply MonoidAlgebra.lhom_ext'
    intro i
    apply LinearMap.ext
    intro r
    change labelSumLinear ι (Representation.ofMulAction ℚ principalSix ι g (MonoidAlgebra.single i r))=
      labelSumLinear ι (MonoidAlgebra.single i r)
    rw [Representation.ofMulAction_single,labelSumLinear_single,labelSumLinear_single]⟩

@[simp] theorem labelSum_single {ι : Type} [MulAction principalSix ι] (i : ι) (r : ℚ) :
    labelSum (MonoidAlgebra.single i r)=r := labelSumLinear_single ι i r

/-- Equivariant label maps preserve the literal total coefficient. -/
theorem permutationMap_labelSum {ι κ : Type} [MulAction principalSix ι] [MulAction principalSix κ]
    (u : ι → κ) (hu : ∀ (g : principalSix) i,u (g • i)=g • u i) :
    SingularComponentAugmentation.permutationMap u hu ≫ labelSum=labelSum (ι := ι) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  intro i
  apply LinearMap.ext
  intro r
  change labelSum (SingularComponentAugmentation.permutationMap u hu (MonoidAlgebra.single i r))=
    labelSum (MonoidAlgebra.single i r)
  rw [SingularComponentAugmentation.permutationMap_single,labelSum_single,labelSum_single]

/-- Total coefficient on the actual line/plane biproduct. -/
def vertexAugmentation : lineLabels ⊞ planeLabels ⟶ Rep.trivial ℚ principalSix ℚ :=
  biprod.desc labelSum labelSum

theorem incidence_vertexAugmentation : incidence ≫ vertexAugmentation=0 := by
  rw [incidence,vertexAugmentation,biprod.lift_desc,Preadditive.neg_comp]
  have hL : lineIncidence ≫ labelSum=labelSum (ι := Flag) := permutationMap_labelSum _ _
  have hP : planeIncidence ≫ labelSum=labelSum (ι := Flag) := permutationMap_labelSum _ _
  rw [hL,hP,add_neg_cancel]

abbrev forgetRep := forget₂ (Rep ℚ principalSix) (ModuleCat ℚ)

instance forgetRepPreservesBiproducts : PreservesBinaryBiproducts forgetRep :=
  preservesBinaryBiproducts_of_preservesBinaryProducts _

def scalarProductIso : forgetRep.obj (lineLabels ⊞ planeLabels) ≅
    ModuleCat.of ℚ (ℚ[Line] × ℚ[Plane]) :=
  forgetRep.mapBiprod lineLabels planeLabels ≪≫ ModuleCat.biprodIsoProd _ _

/-- The actual ordinary vertex chains split into their line and plane coefficients. -/
def vertexSplit : OrdinaryIncidenceChains.VertexChains ≃ₗ[ℚ] (ℚ[Line] × ℚ[Plane]) :=
  (Finsupp.sumFinsuppLEquivProdFinsupp ℚ).trans
    ((MonoidAlgebra.coeffLinearEquiv ℚ).symm.prodCongr (MonoidAlgebra.coeffLinearEquiv ℚ).symm)

def scalarVertexIso : forgetRep.obj (lineLabels ⊞ planeLabels) ≅
    ModuleCat.of ℚ OrdinaryIncidenceChains.VertexChains :=
  scalarProductIso ≪≫ vertexSplit.symm.toModuleIso

/-- The chosen scalar biproduct comparison has the literal first projection. -/
theorem scalarProductIso_fst : scalarProductIso.hom ≫
    ModuleCat.ofHom (LinearMap.fst ℚ ℚ[Line] ℚ[Plane]) = forgetRep.map (biprod.fst : lineLabels ⊞ planeLabels ⟶ _) := by
  have hp : (ModuleCat.biprodIsoProd (forgetRep.obj lineLabels) (forgetRep.obj planeLabels)).hom ≫
      ModuleCat.ofHom (LinearMap.fst ℚ ℚ[Line] ℚ[Plane])=biprod.fst := by
    rw [←ModuleCat.biprodIsoProd_inv_comp_fst,Iso.hom_inv_id_assoc]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun m => (forgetRep.mapBiprod lineLabels planeLabels).hom ≫ m) hp).trans
      (biprod.lift_fst _ _))

theorem scalarProductIso_snd : scalarProductIso.hom ≫
    ModuleCat.ofHom (LinearMap.snd ℚ ℚ[Line] ℚ[Plane]) = forgetRep.map (biprod.snd : lineLabels ⊞ planeLabels ⟶ _) := by
  have hp : (ModuleCat.biprodIsoProd (forgetRep.obj lineLabels) (forgetRep.obj planeLabels)).hom ≫
      ModuleCat.ofHom (LinearMap.snd ℚ ℚ[Line] ℚ[Plane])=biprod.snd := by
    rw [←ModuleCat.biprodIsoProd_inv_comp_snd,Iso.hom_inv_id_assoc]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun m => (forgetRep.mapBiprod lineLabels planeLabels).hom ≫ m) hp).trans
      (biprod.lift_snd _ _))

theorem scalarProductIso_fst_apply (c : (lineLabels ⊞ planeLabels : Rep ℚ principalSix)) :
    (scalarProductIso.hom c).1=(biprod.fst : lineLabels ⊞ planeLabels ⟶ lineLabels) c :=
  congrArg (fun f => f c) scalarProductIso_fst

theorem scalarProductIso_snd_apply (c : (lineLabels ⊞ planeLabels : Rep ℚ principalSix)) :
    (scalarProductIso.hom c).2=(biprod.snd : lineLabels ⊞ planeLabels ⟶ planeLabels) c :=
  congrArg (fun f => f c) scalarProductIso_snd

theorem scalarVertexIso_split (c : (lineLabels ⊞ planeLabels : Rep ℚ principalSix)) :
    vertexSplit (scalarVertexIso.hom c)=scalarProductIso.hom c :=
  vertexSplit.apply_symm_apply _

@[simp] theorem vertexSplit_single_line (L : Line) (r : ℚ) :
    vertexSplit (Finsupp.single (Sum.inl L) r)=(MonoidAlgebra.single L r,0) := by
  apply Prod.ext
  · apply (MonoidAlgebra.coeffLinearEquiv ℚ).injective
    change (Finsupp.sumFinsuppLEquivProdFinsupp ℚ (Finsupp.single (Sum.inl L) r)).1=Finsupp.single L r
    ext x
    simp only [Finsupp.fst_sumFinsuppLEquivProdFinsupp,Finsupp.single_apply,Sum.inl.injEq]
  · apply (MonoidAlgebra.coeffLinearEquiv ℚ).injective
    change (Finsupp.sumFinsuppLEquivProdFinsupp ℚ (Finsupp.single (Sum.inl L) r)).2=0
    ext x
    simp only [Finsupp.snd_sumFinsuppLEquivProdFinsupp,Finsupp.single_apply,Sum.inl_ne_inr,
      ↓reduceIte,Finsupp.zero_apply]

@[simp] theorem vertexSplit_single_plane (P : Plane) (r : ℚ) :
    vertexSplit (Finsupp.single (Sum.inr P) r)=(0,MonoidAlgebra.single P r) := by
  apply Prod.ext
  · apply (MonoidAlgebra.coeffLinearEquiv ℚ).injective
    change (Finsupp.sumFinsuppLEquivProdFinsupp ℚ (Finsupp.single (Sum.inr P) r)).1=0
    ext x
    simp only [Finsupp.fst_sumFinsuppLEquivProdFinsupp,Finsupp.single_apply,Sum.inr_ne_inl,
      ↓reduceIte,Finsupp.zero_apply]
  · apply (MonoidAlgebra.coeffLinearEquiv ℚ).injective
    change (Finsupp.sumFinsuppLEquivProdFinsupp ℚ (Finsupp.single (Sum.inr P) r)).2=Finsupp.single P r
    ext x
    simp only [Finsupp.snd_sumFinsuppLEquivProdFinsupp,Finsupp.single_apply,Sum.inr.injEq]

/-- The coefficient comparison retains the singleton incidence orientation exactly. -/
theorem scalarIncidence_single (F : Flag) (r : ℚ) :
    scalarVertexIso.hom (incidence (MonoidAlgebra.single F r))=
      Finsupp.single (Sum.inl F.val.1) r-Finsupp.single (Sum.inr F.val.2) r := by
  apply vertexSplit.injective
  rw [scalarVertexIso_split,map_sub,vertexSplit_single_line,vertexSplit_single_plane]
  apply Prod.ext
  · rw [scalarProductIso_fst_apply]
    change (incidence ≫ biprod.fst) (MonoidAlgebra.single F r)=MonoidAlgebra.single F.val.1 r-0
    rw [incidence,biprod.lift_fst,lineIncidence_single,sub_zero]
  · rw [scalarProductIso_snd_apply]
    change (incidence ≫ biprod.snd) (MonoidAlgebra.single F r)=0-MonoidAlgebra.single F.val.2 r
    rw [incidence,biprod.lift_snd]
    change -planeIncidence (MonoidAlgebra.single F r)=0-MonoidAlgebra.single F.val.2 r
    rw [planeIncidence_single,zero_sub]

/-- Flag coefficients are the literal ordinary incidence-edge coefficients. -/
def edgeCoefficients : ℚ[Flag] ≃ₗ[ℚ] OrdinaryIncidenceChains.EdgeChains :=
  MonoidAlgebra.coeffLinearEquiv ℚ

/-- The actual MV incidence is the negative of the fixed ordinary graph-boundary convention. -/
theorem scalarIncidence_boundary (c : ℚ[Flag]) : scalarVertexIso.hom (incidence c)=
    -OrdinaryIncidenceChains.boundary (edgeCoefficients c) := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp only [map_zero,neg_zero]
  | add c d hc hd => simp only [map_add,hc,hd,neg_add]
  | single F r =>
    rw [scalarIncidence_single]
    change _ = -BipartitePathChains.boundary OrdinaryIncidence.incidence (Finsupp.single F r)
    exact ((congrArg Neg.neg (BipartitePathChains.boundary_single OrdinaryIncidence.incidence
      (show OrdinaryIncidenceChains.Edge from F) r)).trans (neg_sub _ _)).symm

end TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
