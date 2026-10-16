module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CechDomains
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set Function CategoryTheory AlgebraicTopology
open SmoothLocalDeRham SmoothCoveringDeRham SymmetricSpaceCharts SymmetricSpaceCovering
open scoped Simplicial
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) {ι : Type*} (U : ι → Set OrbitSpace) (n : ℕ)

/-- Actual form Čech terms on all ordered k-tuples of cover members; k=0 is augmented. -/
abbrev FormCechTerms (k : ℕ) := ∀ t : Fin k → ι, EquivariantForm ρ (cechDomain U t) n

/-- A map of tuple positions acts by the true restriction of actual covering forms. -/
def formCechSelect {p q : ℕ} (f : Fin p → Fin q) :
    FormCechTerms ρ U n p →ₗ[ℝ] FormCechTerms ρ U n q where
  toFun w t := restrictEquivariant ρ (cechDomain_select_subset U f t) n (w (t ∘ f))
  map_add' w z := by
    funext t
    exact map_add (restrictEquivariant ρ (cechDomain_select_subset U f t) n) _ _
  map_smul' c w := by
    funext t
    exact map_smul (restrictEquivariant ρ (cechDomain_select_subset U f t) n) c (w (t ∘ f))

/-- The genuine Čech restriction for the identity tuple map is the identity. -/
theorem formCechSelect_id (p : ℕ) : formCechSelect ρ U n (id : Fin p → Fin p) = LinearMap.id := by
  apply LinearMap.ext
  intro w
  funext t
  exact LinearMap.congr_fun (restrictEquivariant_id ρ (cechDomain U t) n) (w t)

/-- Actual Čech tuple restrictions compose as their tuple maps do. -/
theorem formCechSelect_comp {p q r : ℕ} (f : Fin p → Fin q) (g : Fin q → Fin r) :
    formCechSelect ρ U n (g ∘ f) = (formCechSelect ρ U n g).comp (formCechSelect ρ U n f) := by
  apply LinearMap.ext
  intro w
  funext t
  exact (LinearMap.congr_fun (restrictEquivariant_comp ρ
    (cechDomain_select_subset U f (t ∘ g)) (cechDomain_select_subset U g t) n)
      (w (t ∘ (g ∘ f)))).symm

/-- The genuine cosimplicial object of local-coefficient smooth forms on the actual open cover. -/
def formCechCosimplicial : CosimplicialObject (ModuleCat ℝ) where
  obj k := ModuleCat.of ℝ (FormCechTerms ρ U n (k.len+1))
  map f := ModuleCat.ofHom (formCechSelect ρ U n f.toOrderHom)
  map_id k := by
    apply ModuleCat.hom_ext
    exact formCechSelect_id ρ U n (k.len+1)
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact formCechSelect_comp ρ U n f.toOrderHom g.toOrderHom

/-- The actual horizontal Čech complex, with the genuine alternating restriction differential. -/
def formCechComplex : CochainComplex (ModuleCat ℝ) ℕ :=
  (alternatingCofaceMapComplex (ModuleCat ℝ)).obj (formCechCosimplicial ρ U n)

/-- The Čech coboundary is the literal finite alternating sum of actual face restrictions. -/
theorem formCechComplex_d (k : ℕ) : (formCechComplex ρ U n).d k (k+1) =
    ∑ i : Fin (k+2), (-1 : ℤ)^i.val • ModuleCat.ofHom (formCechSelect ρ U n i.succAbove) := by
  exact CochainComplex.of_d (fun j => (formCechCosimplicial ρ U n).obj ⦋j⦌)
    (AlternatingCofaceMapComplex.objD (formCechCosimplicial ρ U n)) k

end TernaryPoly.SmoothSingularGlobal
