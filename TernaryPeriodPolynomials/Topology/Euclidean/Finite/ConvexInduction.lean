module

public import TernaryPeriodPolynomials.Topology.Euclidean.Finite.ConvexInductionData

@[expose] public section


noncomputable section
namespace TernaryPoly.EuclideanFiniteConvex
open CategoryTheory Limits HomologicalComplex EuclideanConvexLocal EuclideanLocalHomology

variable (n : ℕ)
local notation "E" => EuclideanSpace ℝ (Fin (n+2))

/-- Simultaneous finite-family induction proves upper-degree vanishing, local detection,
and existence of the actual canonical local class. The intersection step uses the
smaller family of compact convex intersections. -/
theorem finite_family_data {ι : Type*} (s : Finset ι) (K : ι → Set E)
    (hK : ∀ i ∈ s, IsCompact (K i)) (hconv : ∀ i ∈ s, Convex ℝ (K i)) :
    LocalFundamentalData n (⋃ i ∈ s, K i) := by
  classical
  induction s using Finset.induction_on generalizing K with
  | empty =>
    simpa using empty_data n
  | @insert i s hi ih =>
    have hKi := hK i (Finset.mem_insert_self i s)
    have hci := hconv i (Finset.mem_insert_self i s)
    have hKs : ∀ j ∈ s, IsCompact (K j) := fun j hj => hK j (Finset.mem_insert_of_mem hj)
    have hcs : ∀ j ∈ s, Convex ℝ (K j) := fun j hj => hconv j (Finset.mem_insert_of_mem hj)
    have hs := ih K hKs hcs
    have hinter := ih (fun j => K i ∩ K j)
      (fun j hj => hKi.inter (hKs j hj)) (fun j hj => hci.inter (hcs j hj))
    have heq : K i ∩ (⋃ j ∈ s, K j) = ⋃ j ∈ s, K i ∩ K j := by
      ext x
      simp
    rw [← heq] at hinter
    simpa using union_data n (K i) (⋃ j ∈ s, K j) (convex_data n (K i) hKi hci) hs hinter

/-- Actual relative homology supported on a finite compact-convex union vanishes
strictly above the ambient dimension. -/
theorem finite_family_above {ι : Type*} (s : Finset ι) (K : ι → Set E)
    (hK : ∀ i ∈ s, IsCompact (K i)) (hconv : ∀ i ∈ s, Convex ℝ (K i))
    (k : ℕ) (hk : n+2 < k) :
    IsZero ((supportChains (⋃ i ∈ s, K i)).homology k) :=
  (finite_family_data n s K hK hconv).above k hk

/-- Actual top-degree classes on a finite compact-convex union are detected by all
literal point restrictions. -/
theorem finite_family_detect {ι : Type*} (s : Finset ι) (K : ι → Set E)
    (hK : ∀ i ∈ s, IsCompact (K i)) (hconv : ∀ i ∈ s, Convex ℝ (K i))
    (c e : (supportChains (⋃ i ∈ s, K i)).homology (n+2))
    (hce : ∀ (x : E) (hx : x ∈ ⋃ i ∈ s, K i),
      homologyMap (pointMap (⋃ i ∈ s, K i) x hx) (n+2) c =
      homologyMap (pointMap (⋃ i ∈ s, K i) x hx) (n+2) e) : c = e :=
  (finite_family_data n s K hK hconv).detect c e hce

/-- A top-degree class on a finite compact-convex union vanishes exactly when all
its actual local values vanish. -/
theorem finite_family_eq_zero_iff {ι : Type*} (s : Finset ι) (K : ι → Set E)
    (hK : ∀ i ∈ s, IsCompact (K i)) (hconv : ∀ i ∈ s, Convex ℝ (K i))
    (c : (supportChains (⋃ i ∈ s, K i)).homology (n+2)) :
    c = 0 ↔ ∀ (x : E) (hx : x ∈ ⋃ i ∈ s, K i),
      homologyMap (pointMap (⋃ i ∈ s, K i) x hx) (n+2) c = 0 := by
  constructor
  · rintro rfl x hx
    exact map_zero _
  · intro hc
    apply finite_family_detect n s K hK hconv c 0
    intro x hx
    rw [map_zero, hc x hx]

end TernaryPoly.EuclideanFiniteConvex
