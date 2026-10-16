module

public import TernaryPeriodPolynomials.Topology.Euclidean.Finite.ConvexInduction

@[expose] public section

noncomputable section
namespace TernaryPoly.EuclideanFiniteConvex
open CategoryTheory Limits HomologicalComplex EuclideanConvexLocal EuclideanLocalHomology

variable (n : ℕ)
local notation "E" => EuclideanSpace ℝ (Fin (n+2))

/-- Every finite compact-convex union has exactly one actual top-degree class with
the fixed Euclidean local generator at every point, including for the empty union. -/
theorem finite_family_fundamental_class {ι : Type*} (s : Finset ι) (K : ι → Set E)
    (hK : ∀ i ∈ s, IsCompact (K i)) (hconv : ∀ i ∈ s, Convex ℝ (K i)) :
    ∃! c : (supportChains (⋃ i ∈ s, K i)).homology (n+2),
      ∀ (x : E) (hx : x ∈ ⋃ i ∈ s, K i),
        homologyMap (pointMap (⋃ i ∈ s, K i) x hx) (n+2) c = localGenerator n x := by
  obtain ⟨c, hc⟩ := (finite_family_data n s K hK hconv).exists_class
  refine ⟨c, hc, ?_⟩
  intro e he
  apply finite_family_detect n s K hK hconv e c
  intro x hx
  rw [he x hx, hc x hx]

/-- The canonical actual relative class of a finite compact-convex union. -/
def finiteFamilyGenerator {ι : Type*} (s : Finset ι) (K : ι → Set E)
    (hK : ∀ i ∈ s, IsCompact (K i)) (hconv : ∀ i ∈ s, Convex ℝ (K i)) :
    (supportChains (⋃ i ∈ s, K i)).homology (n+2) :=
  (finite_family_fundamental_class n s K hK hconv).choose

/-- The canonical finite-union class has the prescribed generator at every point. -/
theorem finiteFamilyGenerator_at_point {ι : Type*} (s : Finset ι) (K : ι → Set E)
    (hK : ∀ i ∈ s, IsCompact (K i)) (hconv : ∀ i ∈ s, Convex ℝ (K i))
    (x : E) (hx : x ∈ ⋃ i ∈ s, K i) :
    homologyMap (pointMap (⋃ i ∈ s, K i) x hx) (n+2)
      (finiteFamilyGenerator n s K hK hconv) = localGenerator n x :=
  (finite_family_fundamental_class n s K hK hconv).choose_spec.1 x hx

/-- All point values uniquely characterize the canonical finite-union class. -/
theorem finiteFamilyGenerator_unique {ι : Type*} (s : Finset ι) (K : ι → Set E)
    (hK : ∀ i ∈ s, IsCompact (K i)) (hconv : ∀ i ∈ s, Convex ℝ (K i))
    (c : (supportChains (⋃ i ∈ s, K i)).homology (n+2))
    (hc : ∀ (x : E) (hx : x ∈ ⋃ i ∈ s, K i),
      homologyMap (pointMap (⋃ i ∈ s, K i) x hx) (n+2) c = localGenerator n x) :
    c = finiteFamilyGenerator n s K hK hconv :=
  (finite_family_fundamental_class n s K hK hconv).choose_spec.2 c hc

/-- Literal support restrictions under inclusion of arbitrary finite compact-convex
unions preserve their canonical classes. The families can have different index types. -/
theorem finiteFamilyGenerator_restriction {ι κ : Type*} (s : Finset ι) (K : ι → Set E)
    (hK : ∀ i ∈ s, IsCompact (K i)) (hconvK : ∀ i ∈ s, Convex ℝ (K i))
    (t : Finset κ) (L : κ → Set E)
    (hL : ∀ j ∈ t, IsCompact (L j)) (hconvL : ∀ j ∈ t, Convex ℝ (L j))
    (h : (⋃ j ∈ t, L j) ⊆ ⋃ i ∈ s, K i) :
    homologyMap (supportRestriction (⋃ i ∈ s, K i) (⋃ j ∈ t, L j) h) (n+2)
      (finiteFamilyGenerator n s K hK hconvK) = finiteFamilyGenerator n t L hL hconvL := by
  apply finiteFamilyGenerator_unique n t L hL hconvL
  intro x hx
  rw [restriction_point_apply]
  exact finiteFamilyGenerator_at_point n s K hK hconvK x (h hx)

/-- The canonical class of an empty finite union is zero. -/
theorem finiteFamilyGenerator_eq_zero_of_empty {ι : Type*} (s : Finset ι) (K : ι → Set E)
    (hK : ∀ i ∈ s, IsCompact (K i)) (hconv : ∀ i ∈ s, Convex ℝ (K i))
    (he : (⋃ i ∈ s, K i) = ∅) : finiteFamilyGenerator n s K hK hconv = 0 := by
  apply (finite_family_eq_zero_iff n s K hK hconv _).mpr
  intro x hx
  rw [he] at hx
  exact False.elim hx

/-- The canonical class of a nonempty finite union is nonzero. -/
theorem finiteFamilyGenerator_ne_zero {ι : Type*} (s : Finset ι) (K : ι → Set E)
    (hK : ∀ i ∈ s, IsCompact (K i)) (hconv : ∀ i ∈ s, Convex ℝ (K i))
    (hne : (⋃ i ∈ s, K i).Nonempty) : finiteFamilyGenerator n s K hK hconv ≠ 0 := by
  intro he
  obtain ⟨x, hx⟩ := hne
  have h := finiteFamilyGenerator_at_point n s K hK hconv x hx
  rw [he, map_zero] at h
  exact localGenerator_ne_zero n x h.symm

end TernaryPoly.EuclideanFiniteConvex
