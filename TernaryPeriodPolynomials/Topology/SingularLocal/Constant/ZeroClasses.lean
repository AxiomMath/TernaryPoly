module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Constant.Augmentation
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapAlgebra

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalConstant
open CategoryTheory Limits HomologicalComplex
open SingularLocalCap SingularLocalCap.Homology SingularLocalCompactCap.Algebra
open scoped Classical
open FreeActionLinearization CoveringSingularOrbits SingularLocalCoefficient SingularLocalHomology

/-- The canonical linear map from actual degree-zero chains to their actual homology classes. -/
def zeroClass (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) : K.X 0 ⟶ K.homology 0 :=
  K.liftCycles (𝟙 (K.X 0)) 0 (by simp) (by simp) ≫ K.homologyπ 0

/-- The canonical degree-zero class retains the actual underlying opcycle. -/
theorem zeroClass_opcycles (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) :
    zeroClass K ≫ K.homologyι 0 = K.pOpcycles 0 := by
  unfold zeroClass
  rw [Category.assoc, homology_π_ι, ← Category.assoc, liftCycles_i, Category.id_comp]

/-- The degree-zero class map agrees with the cap's exact cycle-representative convention. -/
theorem zeroClass_chainClass (K : ChainComplex (ModuleCat.{0} ℚ) ℕ)
    (x : Cycles (K.sc' 1 0 0)) :
    zeroClass K x.val = Descent.chainClass K 0 x := by
  apply (ModuleCat.mono_iff_injective (K.homologyι 0)).mp inferInstance
  change (zeroClass K ≫ K.homologyι 0) x.val = _
  rw [zeroClass_opcycles]
  exact (represented_opcycles K 1 0 0 (down_prev _) (down_next _) x).symm

/-- Degree-zero class formation is natural for genuine chain maps. -/
theorem zeroClass_natural {K L : ChainComplex (ModuleCat.{0} ℚ) ℕ} (f : K ⟶ L) :
    zeroClass K ≫ homologyMap f 0 = f.f 0 ≫ zeroClass L := by
  apply (cancel_mono (L.homologyι 0)).mp
  rw [Category.assoc, homologyι_naturality, ← Category.assoc, zeroClass_opcycles,
    Category.assoc, zeroClass_opcycles, p_opcyclesMap]

/-- Composing an actual degree-zero chain family with the class map is its canonical cycle lift. -/
theorem zeroClass_precompose (K : ChainComplex (ModuleCat.{0} ℚ) ℕ)
    {M : ModuleCat.{0} ℚ} (k : M ⟶ K.X 0) :
    k ≫ zeroClass K = K.liftCycles k 0 (by simp) (by simp) ≫ K.homologyπ 0 := by
  unfold zeroClass
  rw [← Category.assoc]
  congr 1
  apply (cancel_mono (K.iCycles 0)).mp
  simp only [Category.assoc, liftCycles_i, Category.comp_id]

/-- The actual ordinary singular H0 augmentation sends a coefficient on one vertex to itself. -/
theorem ordinary_zeroClass_generator (X : TopCat.{0}) (V : ModuleCat.{0} ℚ)
    (σ : SingularSimplex X 0) (v : V) :
    X.singularHomology₀ε V (zeroClass (ordinaryChains X V)
      (((TopCat.toSSet.obj X).ιChainComplex (R := V) σ) v)) = v := by
  have h : (TopCat.toSSet.obj X).ιChainComplex (R := V) σ ≫
      zeroClass (ordinaryChains X V) ≫ X.singularHomology₀ε V = 𝟙 V := by
    erw [← Category.assoc, zeroClass_precompose]
    exact (TopCat.toSSet.obj X).liftCycles_ιChainComplex_homologyπ_homology₀ε V σ
  exact congrArg (fun f => f v) h

/-- On every actual local zero-chain, the H0 augmentation is the literal finite sum of
canonical coefficient values. -/
theorem augmentation_zeroClass (X : TopCat.{0}) (V : ModuleCat.{0} ℚ)
    (c : (chains X V).X 0) :
    augmentation X V (zeroClass (chains X V) c) = coefficientSum X V 0 c := by
  have h : (zeroClass (chains X V) ≫ augmentation X V).hom = coefficientSum X V 0 := by
    apply DFinsupp.lhom_ext (M := fun σ : SingularSimplex X 0 =>
      FiberCoefficient (𝟙 X) (identityCover X) (constantRep V) (atVertex σ))
    intro σ v
    have hn := congrArg (fun f => f (DFinsupp.single (β := fun τ : SingularSimplex X 0 =>
      FiberCoefficient (𝟙 X) (identityCover X) (constantRep V) (atVertex τ)) σ v))
      (zeroClass_natural (ordinaryChainIso X V).hom)
    change (ordinaryHomologyIso X V 0).hom (zeroClass (chains X V) _) =
      zeroClass (ordinaryChains X V) (chainDegreeEquiv X V 0 _) at hn
    change X.singularHomology₀ε V ((ordinaryHomologyIso X V 0).hom (zeroClass (chains X V) _)) = _
    rw [hn, chainDegreeEquiv_single, ordinary_zeroClass_generator]
    exact (coefficientSum_single X V 0 σ v).symm
  exact LinearMap.congr_fun h c

/-- The actual H0 augmentation on the cycle representative is the coefficient sum. -/
theorem augmentation_chainClass (X : TopCat.{0}) (V : ModuleCat.{0} ℚ)
    (c : Cycles ((chains X V).sc' 1 0 0)) :
    augmentation X V (Descent.chainClass (chains X V) 0 c) = coefficientSum X V 0 c.val := by
  exact (congrArg (augmentation X V) (zeroClass_chainClass (chains X V) c).symm).trans
    (augmentation_zeroClass X V c.val)

end TernaryPoly.SingularLocalConstant
