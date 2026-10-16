module

public import TernaryPeriodPolynomials.Topology.Rational.Compact.BoundaryRestriction
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapNaturality

@[expose] public section

noncomputable section
namespace TernaryPoly.RationalCompactBoundary
open CategoryTheory Limits HomologicalComplex RationalRelativeSingular
open RationalManifoldCompact RationalLocalOrientation BoundaryNeighborhood

variable {X : Type} [TopologicalSpace X]

/-- The literal identity pair map views a boundary-relative chain as supported on the interior. -/
def boundaryToSupport (A : Set X) : relativeChains A ⟶ supportChains Aᶜ :=
  relativeMap (ContinuousMap.id X) A (Aᶜ)ᶜ (fun _ hx h => h hx)

/-- The boundary-to-interior-support map retains the same ambient chain representative. -/
theorem boundaryToSupport_projection (A : Set X) :
    cokernel.π (inclusion A) ≫ boundaryToSupport A = cokernel.π (inclusion (Aᶜ)ᶜ) := by
  simp only [boundaryToSupport,relativeMap,cokernel.map,cokernel.π_desc,
    RationalSingularAugmentation.chainMap_id,Category.id_comp]

/-- Restricting the interior-supported boundary class to K is the actual relative quotient map. -/
theorem boundaryToSupport_restriction (A K : Set X) (hKA : K ⊆ Aᶜ) :
    boundaryToSupport A ≫ supportRestriction Aᶜ K hKA =
      toNeighborhoodRelative A Kᶜ (fun _ ha hk => hKA hk ha) := by
  unfold boundaryToSupport supportRestriction toNeighborhoodRelative
  erw [relativeMap_comp]
  rfl

variable {H : Type} [T2Space X] [TopologicalSpace H]
  (A : Set X) (hA : IsClosed A) [ChartedSpace H ↥Aᶜ]
  (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (o : Orientation (n+2) ↥Aᶜ)

/-- The same actual boundary class, viewed as interior-supported, restricts to each genuine
compact fundamental class through the literal support restriction map. -/
theorem boundaryToSupport_fundamental_restriction
    (c : (relativeChains A).homology (n+2))
    (hc : ∀ x (hx : x ∉ A), homologyMap (boundaryPointMap A x hx) (n+2) c =
      homologyMap (RationalRelativeExcision.pointExcisionMap x Aᶜ hx) (n+2)
        (o.generator ⟨x,hx⟩))
    (K : Set X) (hK : IsCompact K) (hKA : K ⊆ Aᶜ) :
    homologyMap (supportRestriction Aᶜ K hKA) (n+2)
      (homologyMap (boundaryToSupport A) (n+2) c) =
        interiorFundamentalClass A hA n e o K hK hKA := by
  change (homologyMap (boundaryToSupport A) (n+2) ≫
    homologyMap (supportRestriction Aᶜ K hKA) (n+2)) c = _
  rw [← homologyMap_comp,boundaryToSupport_restriction]
  exact restriction_eq_interiorFundamentalClass A hA n e o c hc K hK hKA

end TernaryPoly.RationalCompactBoundary
