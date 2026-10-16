module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SingularPresheaf
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CechDomains
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.TotalFlip
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set Function CategoryTheory AlgebraicTopology
open SymmetricSpaceCovering
open scoped Simplicial

variable {F : Type} [AddCommGroup F] [Module ℝ F]
  (ρ : Representation ℝ DeckGroup F) {ι : Type} (U : ι → Set OrbitSpace)

/-- The actual equivariant singular Hom cochains on every k-fold quotient intersection. -/
abbrev SingularCechTerms (n k : ℕ) := ∀ t : Fin k → ι, (coveringCochains ρ (cechDomain U t)).X n

/-- Actual singular coboundary on each genuine intersection. -/
def singularCechColumnD (k n : ℕ) : SingularCechTerms ρ U n k →ₗ[ℝ]
    SingularCechTerms ρ U (n+1) k :=
  LinearMap.pi (fun t => ((coveringCochains ρ (cechDomain U t)).d n (n+1)).hom.comp
    (LinearMap.proj t))

/-- Intersectionwise actual singular coboundaries square to zero. -/
theorem singularCechColumnD_squared (k n : ℕ) (w : SingularCechTerms ρ U n k) :
    singularCechColumnD ρ U k (n+1) (singularCechColumnD ρ U k n w) = 0 := by
  funext t
  exact congrArg (fun f => f.hom (w t))
    ((coveringCochains ρ (cechDomain U t)).d_comp_d n (n+1) (n+1+1))

/-- The genuine singular cochain complex of all k-fold intersections. -/
def singularCechColumn (k : ℕ) : CochainComplex (ModuleCat ℝ) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of ℝ (SingularCechTerms ρ U n k))
    (fun n => ModuleCat.ofHom (singularCechColumnD ρ U k n)) (by
      intro n
      exact ModuleCat.hom_ext (LinearMap.ext (singularCechColumnD_squared ρ U k n)))

/-- Čech tuple maps act by the actual equivariant singular restriction maps. -/
def singularCechSelect {p q : ℕ} (f : Fin p → Fin q) (n : ℕ) :
    SingularCechTerms ρ U n p →ₗ[ℝ] SingularCechTerms ρ U n q :=
  LinearMap.pi (fun t => ((coveringCochainRestriction ρ (cechDomain_select_subset U f t)).f n).hom.comp
    (LinearMap.proj (t ∘ f)))

/-- The actual tuple identity acts as the identity on actual singular Čech cochains. -/
theorem singularCechSelect_id (p n : ℕ) :
    singularCechSelect ρ U (id : Fin p → Fin p) n = LinearMap.id := by
  apply LinearMap.ext
  intro w
  funext t
  exact congrArg (fun f => (f.f n).hom (w t))
    (cochainPullback_id (X := TopCat.of (CoverOpen (cechDomain U t))) (Rep.of ρ))

/-- Actual tuple restrictions compose as the tuple maps do. -/
theorem singularCechSelect_comp {p q r : ℕ} (f : Fin p → Fin q) (g : Fin q → Fin r) (n : ℕ) :
    singularCechSelect ρ U (g ∘ f) n =
      (singularCechSelect ρ U g n).comp (singularCechSelect ρ U f n) := by
  apply LinearMap.ext
  intro w
  funext t
  exact congrArg (fun k => (k.f n).hom (w (t ∘ (g ∘ f))))
    (cochainPullback_comp (coverInclusion (cechDomain_select_subset U g t))
      (coverInclusion_equivariant (cechDomain_select_subset U g t))
      (coverInclusion (cechDomain_select_subset U f (t ∘ g)))
      (coverInclusion_equivariant (cechDomain_select_subset U f (t ∘ g))) (Rep.of ρ))

/-- Tuple restriction intertwines the actual singular coboundary. -/
def singularCechSelectChainMap {p q : ℕ} (f : Fin p → Fin q) :
    singularCechColumn ρ U p ⟶ singularCechColumn ρ U q :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (singularCechSelect ρ U f n)) (by
    intro n
    simp only [singularCechColumn, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro w
    funext t
    exact congrArg (fun k => k.hom (w (t ∘ f)))
      ((coveringCochainRestriction ρ (cechDomain_select_subset U f t)).comm n (n+1)))

/-- The actual quotient Čech nerve valued in genuine equivariant singular Hom complexes. -/
def singularCechComplexCosimplicial : CosimplicialObject (CochainComplex (ModuleCat ℝ) ℕ) where
  obj k := singularCechColumn ρ U (k.len+1)
  map f := singularCechSelectChainMap ρ U f.toOrderHom
  map_id k := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact ModuleCat.hom_ext (singularCechSelect_id ρ U (k.len+1) n)
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact ModuleCat.hom_ext (singularCechSelect_comp ρ U f.toOrderHom g.toOrderHom n)

/-- The actual Čech–singular bicomplex, before the separate small-simplex row contraction. -/
def singularCechBicomplex : RealBicomplex :=
  (alternatingCofaceMapComplex (CochainComplex (ModuleCat ℝ) ℕ)).obj
    (singularCechComplexCosimplicial ρ U)

/-- Its vertical differential is the actual singular coboundary on intersections. -/
theorem singularCechBicomplex_vertical (p q : ℕ) :
    vertical (singularCechBicomplex ρ U) p q = singularCechColumnD ρ U (p+1) q := by
  change ((singularCechColumn ρ U (p+1)).d q (q+1)).hom = _
  simp only [singularCechColumn, CochainComplex.of_d, ModuleCat.hom_ofHom]
  rfl

/-- Its horizontal differential is the genuine alternating sum of actual restrictions. -/
theorem singularCechBicomplex_horizontal (p q : ℕ) :
    horizontal (singularCechBicomplex ρ U) p q =
      ∑ i : Fin (p+2), (-1 : ℤ)^i.val • singularCechSelect ρ U i.succAbove q := by
  have hd := congrArg (fun f => (f.f q).hom)
    (CochainComplex.of_d (fun p => (singularCechComplexCosimplicial ρ U).obj ⦋p⦌)
      (AlternatingCofaceMapComplex.objD (singularCechComplexCosimplicial ρ U)) p)
  refine hd.trans ?_
  change ((HomologicalComplex.Hom.fAddMonoidHom q)
    (∑ i : Fin (p+2), (-1 : ℤ)^i.val • singularCechSelectChainMap ρ U i.succAbove)).hom = _
  rw [map_sum]
  simp only [map_zsmul, HomologicalComplex.Hom.fAddMonoidHom_apply,
    ModuleCat.hom_sum, ModuleCat.hom_zsmul]
  rfl

end TernaryPoly.SmoothSingularGlobal
