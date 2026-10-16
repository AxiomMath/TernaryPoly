module

public import TernaryPeriodPolynomials.Topology.Rational.Compact.NeighborhoodContinuity
public import TernaryPeriodPolynomials.Topology.Rational.Local.ChartHomology

@[expose] public section

noncomputable section
namespace TernaryPoly.HalfSpaceBoundaryOrientation
open CategoryTheory Limits HomologicalComplex
open ContractibleSingularHomology RationalRelativeSingular RationalLocalChartHomology
open RationalCompactNeighborhood
open SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision

variable {X : Type} [TopologicalSpace X]

/-- The literal restriction from a relative pair to an omitted point. -/
def pointRestriction (S : Set X) (x : X) (hx : x ∉ S) : relativeChains S ⟶ localChains x :=
  relativeMap (ContinuousMap.id X) S {x}ᶜ (by
    intro y hy he
    change y = x at he
    exact hx (he ▸ hy))

/-- Actual point restriction commutes with the actual quotient projections. -/
theorem pointRestriction_projection (S : Set X) (x : X) (hx : x ∉ S) :
    cokernel.π (inclusion S) ≫ pointRestriction S x hx = cokernel.π (inclusion ({x}ᶜ : Set X)) := by
  simp [pointRestriction,relativeMap,cokernel.map,RationalSingularAugmentation.chainMap]

/-- Literal evaluation of the point-restriction projection square. -/
theorem pointRestriction_projection_apply (S : Set X) (x : X) (hx : x ∉ S)
    (n : ℕ) (a : (chains X).X n) :
    (pointRestriction S x hx).f n ((cokernel.π (inclusion S)).f n a) =
      (cokernel.π (inclusion ({x}ᶜ : Set X))).f n a :=
  congrArg (fun f => f a) (HomologicalComplex.congr_hom (pointRestriction_projection S x hx) n)

/-- An actual relative cycle remains a cycle under literal point restriction. -/
theorem pointRestriction_cycle (S : Set X) (x : X) (hx : x ∉ S)
    (n : ℕ) (a : (chains X).X n)
    (ha : (relativeChains S).d n (n-1) ((cokernel.π (inclusion S)).f n a) = 0) :
    (localChains x).d n (n-1) ((cokernel.π (inclusion ({x}ᶜ : Set X))).f n a) = 0 := by
  rw [← pointRestriction_projection_apply S x hx n a]
  have h := congrArg (fun f => f ((cokernel.π (inclusion S)).f n a))
    ((pointRestriction S x hx).comm n (n-1))
  change (localChains x).d n (n-1)
    ((pointRestriction S x hx).f n ((cokernel.π (inclusion S)).f n a)) =
      (pointRestriction S x hx).f (n-1)
        ((relativeChains S).d n (n-1) ((cokernel.π (inclusion S)).f n a)) at h
  rw [h,ha,map_zero]

/-- Literal point restriction retains the same absolute-chain representative. -/
theorem pointRestriction_cycleClass (S : Set X) (x : X) (hx : x ∉ S)
    (n : ℕ) (a : (chains X).X n)
    (ha : (relativeChains S).d n (n-1) ((cokernel.π (inclusion S)).f n a) = 0) :
    homologyMap (pointRestriction S x hx) n
      (cycleClass (relativeChains S) n ((cokernel.π (inclusion S)).f n a) ha) =
        cycleClass (localChains x) n ((cokernel.π (inclusion ({x}ᶜ : Set X))).f n a)
          (pointRestriction_cycle S x hx n a ha) := by
  have hz : (localChains x).d n (n-1)
      ((pointRestriction S x hx).f n ((cokernel.π (inclusion S)).f n a)) = 0 := by
    rw [pointRestriction_projection_apply]
    exact pointRestriction_cycle S x hx n a ha
  rw [cycleClass_naturality _ _ _ _ _ hz]
  congr 1
  exact pointRestriction_projection_apply S x hx n a

variable [T2Space X]

/-- If one literal local value of an actual relative class vanishes, its values vanish
throughout a neighborhood wherever the original pair allows point restriction.
The proof uses the finite compact carrier of an actual bounding-chain error. -/
theorem pointRestriction_zero_near (S : Set X) (x : X) (hx : x ∉ S)
    (n : ℕ) (c : (relativeChains S).homology n)
    (hc : homologyMap (pointRestriction S x hx) n c = 0) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ hy : y ∉ S, homologyMap (pointRestriction S y hy) n c = 0 := by
  obtain ⟨q,hq,rfl⟩ := exists_cycleClass (relativeChains S) n c
  obtain ⟨a,rfl⟩ := SingularLocalCap.RelativeAlgebra.projection_surjective (inclusion S) n q
  rw [pointRestriction_cycleClass] at hc
  obtain ⟨b,e,he⟩ :=
    (projected_cycleClass_eq_zero_iff {x} n a (pointRestriction_cycle S x hx n a hq)).mp hc
  obtain ⟨F,hF,hFx,haF⟩ := exists_compact_carrier ({x}ᶜ : Set X) n
    (a - (chains X).d (n+1) n b) ((inclusion_range_iff _ _ _).mp ⟨e,he⟩)
  refine ⟨Fᶜ,hF.isClosed.isOpen_compl,?_,?_⟩
  · intro hxF
    exact hFx hxF (Set.mem_singleton x)
  · intro y hyF hyS
    rw [pointRestriction_cycleClass]
    apply (projected_cycleClass_eq_zero_iff {y} n a (pointRestriction_cycle S y hyS n a hq)).mpr
    refine ⟨b,(inclusion_range_iff _ _ _).mpr ?_⟩
    have hFy : F ⊆ ({y}ᶜ : Set X) := by
      intro z hz hzy
      change z = y at hzy
      exact hyF (hzy ▸ hz)
    exact subChainSubmodule_mono (R := ℚ) (X := TopCat.of X) hFy n haF

end TernaryPoly.HalfSpaceBoundaryOrientation
