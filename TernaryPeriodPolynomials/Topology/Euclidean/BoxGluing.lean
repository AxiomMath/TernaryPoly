module

public import TernaryPeriodPolynomials.Topology.Euclidean.BoxTransport
public import TernaryPeriodPolynomials.Topology.OpenGluing.BasisGluingInduction

@[expose] public section


namespace TernaryPoly.EuclideanBoxBasis
open TopologicalSpace

/-- A precise Euclidean open-set induction principle with only local models, binary gluing,
and increasing-union continuity as hypotheses. -/
theorem euclidean_open_induction (m : ℕ) (P : Set (EuclideanSpace ℝ (Fin m)) → Prop)
    (hEmpty : P ∅)
    (hModel : ∀ s, IsOpen s → Nonempty (s ≃ₜ EuclideanSpace ℝ (Fin m)) → P s)
    (hGlue : ∀ b c, IsOpen b → IsOpen c → P b → P c → P (b ∩ c) → P (b ∪ c))
    (hIncreasing : ∀ s : ℕ → Set (EuclideanSpace ℝ (Fin m)),
      (∀ n, IsOpen (s n)) → Monotone s → (∀ n, P (s n)) → P (⋃ n, s n))
    (s : Set (EuclideanSpace ℝ (Fin m))) (hs : IsOpen s) : P s := by
  obtain ⟨B,hB,hInter,hHomeo⟩ := euclidean_basis m
  apply OpenBasisGluing.open_induction_of_open hB ?_ hEmpty hInter hGlue hIncreasing s hs
  intro b hb
  by_cases hne : b.Nonempty
  · exact hModel b (hB.isOpen hb) (hHomeo b hb hne)
  · simpa [Set.not_nonempty_iff_eq_empty.mp hne] using hEmpty

end TernaryPoly.EuclideanBoxBasis
