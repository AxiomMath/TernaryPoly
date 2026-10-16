module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.Cech
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.TotalComparison

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set Function CategoryTheory AlgebraicTopology
open SmoothLocalDeRham SmoothCoveringDeRham SymmetricSpaceCharts SymmetricSpaceCovering
open scoped Simplicial Topology ContDiff Manifold

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) {ι : Type} (U : ι → Set OrbitSpace)
  (hU : ∀ i, IsOpen (U i))

/-- The actual de Rham differential acts independently on every Čech intersection. -/
def formCechColumnD (k n : ℕ) : FormCechTerms ρ U n k →ₗ[ℝ] FormCechTerms ρ U (n+1) k :=
  LinearMap.pi (fun t => (differential ρ (cechDomain_isOpen U hU t) n).comp
    (LinearMap.proj t))

/-- The true vertical differential squares to zero on each actual intersection. -/
theorem formCechColumnD_squared (k n : ℕ) (w : FormCechTerms ρ U n k) :
    formCechColumnD ρ U hU k (n+1) (formCechColumnD ρ U hU k n w) = 0 := by
  funext t
  exact differential_squared ρ (cechDomain_isOpen U hU t) n (w t)

/-- The actual de Rham cochain complex of all k-fold Čech intersections. -/
def formCechColumn (k : ℕ) : CochainComplex (ModuleCat ℝ) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of ℝ (FormCechTerms ρ U n k))
    (fun n => ModuleCat.ofHom (formCechColumnD ρ U hU k n)) (by
      intro n
      exact ModuleCat.hom_ext (LinearMap.ext (formCechColumnD_squared ρ U hU k n)))

/-- Actual tuple restriction is a map of the actual de Rham complexes. -/
def formCechSelectChainMap {p q : ℕ} (f : Fin p → Fin q) :
    formCechColumn ρ U hU p ⟶ formCechColumn ρ U hU q :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (formCechSelect ρ U n f)) (by
    intro n
    simp only [formCechColumn, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro w
    funext t
    exact (restrictEquivariant_d ρ (cechDomain_isOpen U hU (t ∘ f))
      (cechDomain_isOpen U hU t) (cechDomain_select_subset U f t) (w (t ∘ f))).symm)

/-- The genuine Čech nerve valued in actual local-coefficient de Rham complexes. -/
def formCechComplexCosimplicial : CosimplicialObject (CochainComplex (ModuleCat ℝ) ℕ) where
  obj k := formCechColumn ρ U hU (k.len+1)
  map f := formCechSelectChainMap ρ U hU f.toOrderHom
  map_id k := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact ModuleCat.hom_ext (formCechSelect_id ρ U n (k.len+1))
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact ModuleCat.hom_ext (formCechSelect_comp ρ U n f.toOrderHom g.toOrderHom)

/-- The actual Čech–de Rham bicomplex. Its differentials are the alternating restrictions
horizontally and the true exterior differential vertically. -/
def formCechBicomplex : RealBicomplex :=
  (alternatingCofaceMapComplex (CochainComplex (ModuleCat ℝ) ℕ)).obj
    (formCechComplexCosimplicial ρ U hU)

/-- The vertical bicomplex differential is the actual intersectionwise exterior derivative. -/
theorem formCechBicomplex_vertical (p q : ℕ) :
    vertical (formCechBicomplex ρ U hU) p q = formCechColumnD ρ U hU (p+1) q := by
  change ((formCechColumn ρ U hU (p+1)).d q (q+1)).hom = _
  simp only [formCechColumn, CochainComplex.of_d, ModuleCat.hom_ofHom]
  rfl

/-- The horizontal bicomplex differential is the actual alternating Čech restriction. -/
theorem formCechBicomplex_horizontal (p q : ℕ) :
    horizontal (formCechBicomplex ρ U hU) p q = formCechD ρ U q (p+1) := by
  have hd := congrArg (fun f => (f.f q).hom)
    (CochainComplex.of_d (fun p => (formCechComplexCosimplicial ρ U hU).obj ⦋p⦌)
      (AlternatingCofaceMapComplex.objD (formCechComplexCosimplicial ρ U hU)) p)
  refine hd.trans ?_
  change ((HomologicalComplex.Hom.fAddMonoidHom q)
    (∑ i : Fin (p+2), (-1 : ℤ)^i.val •
      formCechSelectChainMap ρ U hU i.succAbove)).hom = _
  rw [map_sum]
  simp only [map_zsmul, HomologicalComplex.Hom.fAddMonoidHom_apply,
    ModuleCat.hom_sum, ModuleCat.hom_zsmul]
  rfl

end TernaryPoly.SmoothSingularGlobal
