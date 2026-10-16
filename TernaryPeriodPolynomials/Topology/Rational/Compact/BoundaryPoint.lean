module

public import TernaryPeriodPolynomials.SymmetricSpace.BoundaryNeighborhood.Trace
public import TernaryPeriodPolynomials.Topology.Rational.Compact.BoundaryClasses

@[expose] public section

noncomputable section
namespace TernaryPoly.RationalCompactBoundary
open CategoryTheory HomologicalComplex RationalRelativeSingular
open RationalLocalOrientation RationalManifoldCompact BoundaryNeighborhood
variable {X : Type} [TopologicalSpace X] [T2Space X] {A W : Set X}

/-- The literal relative-to-point map for an interior point of the compact pair. -/
def boundaryPointMap (A : Set X) (x : X) (hx : x ∉ A) :
    relativeChains A ⟶ RationalLocalChartHomology.localChains x :=
  relativeMap (ContinuousMap.id X) A {x}ᶜ (by
    intro y hy hxy
    change y = x at hxy
    exact hx (hxy ▸ hy))

/-- If a compact support contains the entire trace of a point, the ambient homotopy is a
literal homotopy of that support pair to the point pair. -/
def supportPointHomotopy (d : Deformation A W) (L : Set X) (x : X)
    (htrace : d.trace {x} ⊆ L) :
    Homotopy
      (supportPointMap L x (htrace (d.subset_trace {x} (Set.mem_singleton x))))
      (relativeMap d.endpoint Lᶜ {x}ᶜ (fun _ hy =>
        d.mapsTo_compl_trace {x} 1 (fun h => hy (htrace h)))) :=
  relativePairHomotopy Lᶜ {x}ᶜ _ _ d.ambientHomotopy
    (fun t _ hy => d.mapsTo_compl_trace {x} t (fun h => hy (htrace h)))

/-- Following support restriction by endpoint collapse and point restriction is homotopic
to the literal point restriction whenever the support contains the full point trace. -/
def collapsePointHomotopy (d : Deformation A W) (K L : Set X)
    (hcollapse : ∀ y ∈ Kᶜ, d.homotopy (1,y) ∈ A) (hKL : K ⊆ L)
    (x : X) (hx : x ∉ A) (htrace : d.trace {x} ⊆ L) :
    Homotopy
      (supportRestriction L K hKL ≫ fromNeighborhoodRelative d Kᶜ hcollapse ≫ boundaryPointMap A x hx)
      (supportPointMap L x (htrace (d.subset_trace {x} (Set.mem_singleton x)))) := by
  have hc : supportRestriction L K hKL ≫ fromNeighborhoodRelative d Kᶜ hcollapse ≫
      boundaryPointMap A x hx =
      relativeMap d.endpoint Lᶜ {x}ᶜ (fun _ hy =>
        d.mapsTo_compl_trace {x} 1 (fun h => hy (htrace h))) := by
    unfold supportRestriction fromNeighborhoodRelative boundaryPointMap
    erw [RationalRelativeSingular.relativeMap_comp, RationalRelativeSingular.relativeMap_comp]
    rfl
  exact (Homotopy.ofEq hc).trans (supportPointHomotopy d L x htrace).symm

end TernaryPoly.RationalCompactBoundary
