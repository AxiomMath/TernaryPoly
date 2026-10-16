module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology.Coefficients
public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology.Coinvariants
public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality

@[expose] public section


/-!
# Coefficient naturality of the group-homology comparison

For a morphism `φ : V ⟶ W` of rational representations of `G`, the comparison of group homology with
the homology of the coinvariant singular chains of a free contractible `G`-space, and with the geometric
local-coefficient chains of a quotient covering, intertwines `groupHomology.map (MonoidHom.id G) φ`
with the literal coefficient chain map (`groupCoinvariantHomologyIso_natural`,
`groupLocalHomologyIso_natural`, `bordifiedGroupLocalHomologyIso_natural`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits HomologicalComplex

noncomputable section

namespace TernaryPeriodPolynomials.Argument.CoefficientNaturality

open TernaryPoly.SingularLocalHomology TernaryPoly.EquivariantSingularResolution
  TernaryPoly.FreeActionLinearization

section Bar

variable {G : Type} [Group G] {V W : Rep.{0} ℚ G}

/-- The coefficient morphism acts on coinvariant tensor complexes of any resolution complex. -/
def coinvTensorMap (φ : V ⟶ W) (P : ChainComplex (Rep.{0} ℚ G) ℕ) :
    P.coinvariantsTensorObj V ⟶ P.coinvariantsTensorObj W :=
  (NatTrans.mapHomologicalComplex ((Rep.coinvariantsTensor ℚ G).map φ)
    (ComplexShape.down ℕ)).app P

theorem coinvTensorMap_f (φ : V ⟶ W) (P : ChainComplex (Rep.{0} ℚ G) ℕ) (n : ℕ) :
    (coinvTensorMap φ P).f n = ((Rep.coinvariantsTensor ℚ G).map φ).app (P.X n) := rfl

/-- The free-module coinvariant description of the tensor is natural in the coefficients. -/
theorem finsuppToCoinvariantsTensorFree_natural (φ : V ⟶ W) (α : Type) [DecidableEq α] (x : α →₀ V) :
    DFunLike.coe (F := (α →₀ W.V) →ₗ[ℚ] (W.ρ.tprod (Representation.free ℚ G α)).Coinvariants)
      (Rep.finsuppToCoinvariantsTensorFree W α) (Finsupp.mapRange φ.hom (map_zero φ.hom) x) =
    (((Rep.coinvariantsTensor ℚ G).map φ).app (Rep.free ℚ G α))
      (DFunLike.coe (F := (α →₀ V.V) →ₗ[ℚ] (V.ρ.tprod (Representation.free ℚ G α)).Coinvariants)
        (Rep.finsuppToCoinvariantsTensorFree V α) x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [Finsupp.mapRange_add (fun _ _ => map_add _ _ _), map_add, hx, hy, map_add, map_add]
  | single i a =>
    rw [Finsupp.mapRange_single, Rep.finsuppToCoinvariantsTensorFree_single,
      Rep.finsuppToCoinvariantsTensorFree_single]
    rfl

/-- The inhomogeneous-to-bar isomorphism is natural in the coefficients. -/
theorem inhomogeneousChainsIso_natural (φ : V ⟶ W) [DecidableEq G] :
    groupHomology.chainsMap (MonoidHom.id G) φ ≫ (groupHomology.inhomogeneousChainsIso W).hom =
      (groupHomology.inhomogeneousChainsIso V).hom ≫ coinvTensorMap φ (Rep.barComplex ℚ G) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply groupHomology.inhomogeneousChains.ext
  intro g
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  have hc : (ModuleCat.Hom.hom ((groupHomology.chainsMap (MonoidHom.id G) φ).f n))
      ((Finsupp.lsingle (R := ℚ) g) a) = Finsupp.mapRange φ.hom (map_zero φ.hom) (Finsupp.single g (a : V.V)) := by
    erw [groupHomology.chainsMap_f_single]
    simp [Finsupp.mapRange_single]
  have key := finsuppToCoinvariantsTensorFree_natural φ (Fin n → G) (Finsupp.single g (a : V.V))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom, comp_f]
  rw [hc]
  exact key

end Bar

section Comparison

variable (G : Type) [Group G] (E : TopCat.{0}) [MulAction G E] [ContinuousConstSMul G E]
  [ContractibleSpace E] [IsCancelSMul G E] {V W : Rep.{0} ℚ G}

omit [ContractibleSpace E] [IsCancelSMul G E] in
theorem coinvariantCoefficientMap_eq (φ : V ⟶ W) :
    coinvariantCoefficientMap (E := E) φ = coinvTensorMap φ (equivariantChains G E) := rfl

/-- The inverse of the coinvariant resolution comparison is natural in the coefficients. -/
theorem coinvariantResolutionHomotopyEquiv_inv_natural (φ : V ⟶ W) :
    (coinvariantResolutionHomotopyEquiv G E V).inv ≫ coinvariantCoefficientMap (E := E) φ =
      coinvTensorMap φ (Rep.barComplex ℚ G) ≫ (coinvariantResolutionHomotopyEquiv G E W).inv := by
  apply HomologicalComplex.hom_ext
  intro n
  exact ((Rep.coinvariantsTensor ℚ G).map φ).naturality ((resolutionHomotopyEquiv G E).inv.f n)

/-- The comparison chain map from group homology is natural in the coefficients. -/
theorem comparisonMap_natural (φ : V ⟶ W) :
    groupHomology.chainsMap (MonoidHom.id G) φ ≫ comparisonMap G E W =
      comparisonMap G E V ≫ coinvariantCoefficientMap (E := E) φ := by
  classical
  dsimp only [comparisonMap]
  rw [← Category.assoc, inhomogeneousChainsIso_natural, Category.assoc,
    ← coinvariantResolutionHomotopyEquiv_inv_natural, ← Category.assoc]

/-- The group-homology comparison with coinvariant singular chains is natural in the coefficients. -/
theorem groupCoinvariantHomologyIso_natural (φ : V ⟶ W) (n : ℕ) :
    groupHomology.map (MonoidHom.id G) φ n ≫ (groupCoinvariantHomologyIso G E W n).hom =
      (groupCoinvariantHomologyIso G E V n).hom ≫
        homologyMap (coinvariantCoefficientMap (E := E) φ) n := by
  change homologyMap (groupHomology.chainsMap (MonoidHom.id G) φ) n ≫
      homologyMap (comparisonMap G E W) n =
    homologyMap (comparisonMap G E V) n ≫ homologyMap (coinvariantCoefficientMap (E := E) φ) n
  rw [← homologyMap_comp, ← homologyMap_comp, comparisonMap_natural]

end Comparison

section Geometric

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  [ContractibleSpace E] [IsCancelSMul G E] (p : E ⟶ B) (hp : IsQuotientCoveringMap p G)
  {V W : Rep.{0} ℚ G}

/-- The group-homology comparison with the geometric local-coefficient chains of a quotient covering
is natural in the coefficients. -/
theorem groupLocalHomologyIso_natural (φ : V ⟶ W) (n : ℕ) :
    groupHomology.map (MonoidHom.id G) φ n ≫ (groupLocalHomologyIso p hp W n).hom =
      (groupLocalHomologyIso p hp V n).hom ≫ homologyMap (localCoefficientMap p hp φ) n := by
  change groupHomology.map (MonoidHom.id G) φ n ≫ ((groupCoinvariantHomologyIso G E W n).hom ≫
      homologyMap (chainIso p hp W).hom n) =
    ((groupCoinvariantHomologyIso G E V n).hom ≫ homologyMap (chainIso p hp V).hom n) ≫
      homologyMap (localCoefficientMap p hp φ) n
  rw [← Category.assoc, groupCoinvariantHomologyIso_natural, Category.assoc, Category.assoc,
    ← homologyMap_comp, ← homologyMap_comp, chainIso_coefficient_natural]

end Geometric

/-- The bordified local-chain comparison of group homology is natural in the coefficient
representation of the principal-six group. -/
theorem bordifiedGroupLocalHomologyIso_natural
    {V W : Rep.{0} ℚ TernaryPoly.IntegralGL3Congruence.principalSix} (φ : V ⟶ W) (n : ℕ) :
    groupHomology.map (MonoidHom.id _) φ n ≫ (bordifiedGroupLocalHomologyIso W n).hom =
      (bordifiedGroupLocalHomologyIso V n).hom ≫
        homologyMap (localCoefficientMap bordifiedProjection
          bordifiedProjection_quotientCovering φ) n :=
  groupLocalHomologyIso_natural bordifiedProjection bordifiedProjection_quotientCovering φ n

end TernaryPeriodPolynomials.Argument.CoefficientNaturality
