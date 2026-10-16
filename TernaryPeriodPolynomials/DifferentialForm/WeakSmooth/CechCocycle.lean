module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.SmoothGlobal
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CechOperators

@[expose] public section


/-! Literal intrinsic correction differences yield an actual smooth Čech cocycle. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
attribute [local irreducible] intrinsicSmoothCurrent intrinsicCurrentDifferential intrinsicCurrentRestriction

open Set PolynomialCoefficientMetric SymmetricSpaceCovering SmoothCoveringDeRham SmoothSingularGlobal

variable {ι : Type} (U : ι → Set OrbitSpace)

theorem cechDomain_entry_subset {k : ℕ} (t : Fin k → ι) (a : Fin k) :
    cechDomain U t ⊆ U (t a) := fun _ h => mem_iInter.mp h a

def intrinsicCechDifference (n : ℕ) (f : ∀ i, IntrinsicCurrent n 0 (U i))
    (t : Fin 2 → ι) : IntrinsicCurrent n 0 (cechDomain U t) :=
  intrinsicCurrentRestriction n 0 (cechDomain_entry_subset U t 1) (f (t 1)) -
    intrinsicCurrentRestriction n 0 (cechDomain_entry_subset U t 0) (f (t 0))

/-- The three alternating edge differences cancel in every abelian group. -/
theorem intrinsicCechDifference_sum_cancel {M : Type*} [AddCommGroup M] (r : Fin 3 → M) :
    (∑ i : Fin 3, (-1 : ℤ)^i.val • (r (i.succAbove 1) - r (i.succAbove 0))) = 0 := by
  simp only [Fin.sum_univ_three]
  change (1 : ℤ) • (r 2 - r 1) + (-1 : ℤ) • (r 2 - r 0) +
    (1 : ℤ) • (r 1 - r 0) = 0
  simp only [one_zsmul, neg_one_zsmul]
  abel

theorem intrinsicCechDifference_cocycle (n : ℕ) (hU : ∀ i, IsOpen (U i))
    (f : ∀ i, IntrinsicCurrent n 0 (U i)) (a : FormCechTerms (deckRepresentation n) U 0 2)
    (ha : ∀ t, intrinsicSmoothCurrent n 0 (cechDomain U t) (cechDomain_isOpen U hU t) (a t) =
      intrinsicCechDifference U n f t) :
    formCechD (deckRepresentation n) U 0 2 a = 0 := by
  funext t
  let S := intrinsicSmoothCurrent n 0 (cechDomain U t) (cechDomain_isOpen U hU t)
  let r (i : Fin 3) : IntrinsicCurrent n 0 (cechDomain U t) :=
    intrinsicCurrentRestriction n 0 (cechDomain_entry_subset U t i) (f (t i))
  have hr (i : Fin 3) :
      S (restrictEquivariant (deckRepresentation n) (cechDomain_select_subset U i.succAbove t) 0
          (a (t ∘ i.succAbove))) = r (i.succAbove 1) - r (i.succAbove 0) := by
    let R := intrinsicCurrentRestriction n 0 (cechDomain_select_subset U i.succAbove t)
    have hsub : R (intrinsicCechDifference U n f (t ∘ i.succAbove)) =
        r (i.succAbove 1) - r (i.succAbove 0) :=
      (map_sub R _ _).trans (congrArg₂ (fun x y : IntrinsicCurrent n 0 (cechDomain U t) => x - y)
        (intrinsicCurrentRestriction_trans n 0
          (cechDomain_entry_subset U (t ∘ i.succAbove) 1)
          (cechDomain_select_subset U i.succAbove t) (f (t (i.succAbove 1))))
        (intrinsicCurrentRestriction_trans n 0
          (cechDomain_entry_subset U (t ∘ i.succAbove) 0)
          (cechDomain_select_subset U i.succAbove t) (f (t (i.succAbove 0)))))
    exact (intrinsicSmoothCurrent_restriction n 0 (cechDomain_isOpen U hU (t ∘ i.succAbove))
      (cechDomain_isOpen U hU t) (cechDomain_select_subset U i.succAbove t) _).symm.trans
        ((congrArg R (ha (t ∘ i.succAbove))).trans hsub)
  have hs : S (formCechD (deckRepresentation n) U 0 2 a t) =
      ∑ i : Fin 3, (-1 : ℤ)^i.val • (r (i.succAbove 1) - r (i.succAbove 0)) := by
    apply (congrArg S (formCechD_apply (deckRepresentation n) U 0 2 a t)).trans
    apply (map_sum S _ _).trans
    apply Finset.sum_congr rfl
    intro i _
    exact (map_zsmul S _ _).trans (congrArg (fun z : IntrinsicCurrent n 0 (cechDomain U t) =>
      (-1 : ℤ)^i.val • z) (hr i))
  apply intrinsicSmoothCurrent_injective n 0 (cechDomain U t) (cechDomain_isOpen U hU t)
  exact (hs.trans (intrinsicCechDifference_sum_cancel r)).trans (map_zero S).symm

end TernaryPoly.PolynomialFormWeakSmooth
