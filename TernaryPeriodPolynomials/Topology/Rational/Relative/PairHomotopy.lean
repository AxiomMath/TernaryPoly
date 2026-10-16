module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.ChainHomotopyMap
public import TernaryPeriodPolynomials.Topology.Singular.ChainHomotopyNaturalitySubspace

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalRelativeSingular
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology
open SingularChainHomotopyNaturality RationalSingularAugmentation
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- A genuine homotopy of topological pairs induces an actual relative chain homotopy,
in every degree and with arbitrary ambient spaces. -/
def relativePairHomotopy {f g : C(X,Y)} (S : Set X) (T : Set Y)
    (hf : Set.MapsTo f S T) (hg : Set.MapsTo g S T)
    (H : ContinuousMap.Homotopy f g) (hH : ∀ t x, x ∈ S → H (t,x) ∈ T) :
    Homotopy (relativeMap f S T hf) (relativeMap g S T hg) :=
  RelativeChainHomotopy.mapHomotopy (inclusion S) (inclusion T)
    (TopCat.Homotopy.singularChainComplexFunctorObjMap
      (f := TopCat.ofHom f) (g := TopCat.ofHom g) H (ModuleCat.of ℚ ℚ))
    (chainMap (subspaceMap f S T hf)) (chainMap (subspaceMap g S T hg))
    (inclusion_naturality f S T hf) (inclusion_naturality g S T hg)
    (subspace_singularChainHomotopy_relative_zero S T hf hg H hH)

/-- General homotopy invariance for the literal rational relative homology maps. -/
theorem relativeHomologyMap_eq_of_pairHomotopy {f g : C(X,Y)} (S : Set X) (T : Set Y)
    (hf : Set.MapsTo f S T) (hg : Set.MapsTo g S T)
    (H : ContinuousMap.Homotopy f g) (hH : ∀ t x, x ∈ S → H (t,x) ∈ T) (k : ℕ) :
    homologyMap (relativeMap f S T hf) k = homologyMap (relativeMap g S T hg) k :=
  (relativePairHomotopy S T hf hg H hH).homologyMap_eq k

/-- A continuous pair map whose entire image lies in the target subspace induces the zero
map of actual relative chain complexes. -/
theorem relativeMap_eq_zero_of_range (f : C(X,Y)) (S : Set X) (T : Set Y)
    (hf : Set.MapsTo f S T) (h : ∀ x, f x ∈ T) : relativeMap f S T hf = 0 := by
  apply (cancel_epi (cokernel.π (inclusion S))).mp
  simp only [relativeMap, cokernel.map, cokernel.π_desc, comp_zero]
  let g : C(X,T) := ⟨fun x => ⟨f x,h x⟩,f.continuous.subtype_mk _⟩
  have heq : chainMap f = chainMap g ≫ inclusion T := by
    rw [← RationalSingularAugmentation.chainMap_comp]
  rw [heq, Category.assoc, cokernel.condition, comp_zero]

/-- A pair-preserving homotopy to a map with image in the target subspace is an actual
nullhomotopy of the relative chain map. -/
def relativePairNullhomotopy {f g : C(X,Y)} (S : Set X) (T : Set Y)
    (hf : Set.MapsTo f S T) (hg : Set.MapsTo g S T)
    (H : ContinuousMap.Homotopy f g) (hH : ∀ t x, x ∈ S → H (t,x) ∈ T)
    (hgT : ∀ x, g x ∈ T) : Homotopy (relativeMap f S T hf) 0 :=
  (relativePairHomotopy S T hf hg H hH).trans
    (Homotopy.ofEq (relativeMap_eq_zero_of_range g S T hg hgT))

end TernaryPoly.RationalRelativeSingular
