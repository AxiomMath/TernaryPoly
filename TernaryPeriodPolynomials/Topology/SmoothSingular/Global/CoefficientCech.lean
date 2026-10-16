module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CechDomains
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.Coefficient
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set Function CategoryTheory AlgebraicTopology
open SymmetricSpaceCovering
open scoped Simplicial
variable {F : Type} [AddCommGroup F] [Module ℝ F]
  (ρ : Representation ℝ DeckGroup F) {ι : Type} (U : ι → Set OrbitSpace)

/-- Actual local-coefficient sections on every k-fold quotient intersection. -/
abbrev CoefficientCechTerms (k : ℕ) := ∀ t : Fin k → ι, coefficientSections ρ (cechDomain U t)

/-- Actual tuple restriction for the genuine coefficient sheaf. -/
def coefficientCechSelect {p q : ℕ} (f : Fin p → Fin q) :
    CoefficientCechTerms ρ U p →ₗ[ℝ] CoefficientCechTerms ρ U q :=
  LinearMap.pi (fun t => (coefficientRestriction ρ (cechDomain_select_subset U f t)).comp
    (LinearMap.proj (t ∘ f)))

theorem coefficientCechSelect_id (p : ℕ) :
    coefficientCechSelect ρ U (id : Fin p → Fin p) = LinearMap.id := by
  apply LinearMap.ext
  intro w
  funext t
  apply Subtype.ext
  apply LocallyConstant.ext
  intro x
  rfl

theorem coefficientCechSelect_comp {p q r : ℕ} (f : Fin p → Fin q) (g : Fin q → Fin r) :
    coefficientCechSelect ρ U (g ∘ f) =
      (coefficientCechSelect ρ U g).comp (coefficientCechSelect ρ U f) := by
  apply LinearMap.ext
  intro w
  funext t
  apply Subtype.ext
  apply LocallyConstant.ext
  intro x
  rfl

/-- The genuine coefficient Čech nerve, using literal coefficient-sheaf restrictions. -/
def coefficientCechCosimplicial : CosimplicialObject (ModuleCat ℝ) where
  obj k := ModuleCat.of ℝ (CoefficientCechTerms ρ U (k.len+1))
  map f := ModuleCat.ofHom (coefficientCechSelect ρ U f.toOrderHom)
  map_id k := ModuleCat.hom_ext (coefficientCechSelect_id ρ U (k.len+1))
  map_comp f g := ModuleCat.hom_ext (coefficientCechSelect_comp ρ U f.toOrderHom g.toOrderHom)

/-- The common actual coefficient Čech complex. -/
def coefficientCechComplex : CochainComplex (ModuleCat ℝ) ℕ :=
  (alternatingCofaceMapComplex (ModuleCat ℝ)).obj (coefficientCechCosimplicial ρ U)

/-- Its differential is literally the alternating sum of genuine coefficient restrictions. -/
theorem coefficientCechComplex_d (p : ℕ) :
    ((coefficientCechComplex ρ U).d p (p+1)).hom =
      ∑ i : Fin (p+2), (-1 : ℤ)^i.val • coefficientCechSelect ρ U i.succAbove := by
  have h := congrArg ModuleCat.Hom.hom
    (CochainComplex.of_d (fun p => (coefficientCechCosimplicial ρ U).obj ⦋p⦌)
      (AlternatingCofaceMapComplex.objD (coefficientCechCosimplicial ρ U)) p)
  refine h.trans ?_
  change (∑ i : Fin (p+2), (-1 : ℤ)^i.val •
    ModuleCat.ofHom (coefficientCechSelect ρ U i.succAbove)).hom = _
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul,ModuleCat.hom_ofHom]

end TernaryPoly.SmoothSingularGlobal
