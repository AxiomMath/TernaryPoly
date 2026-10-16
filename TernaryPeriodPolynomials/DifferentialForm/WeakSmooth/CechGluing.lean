module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.CechLocalForms
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.CechOverlap
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.CechCocycle
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CechPrimitiveDescent

@[expose] public section


/-! Genuine smooth global primitives from actual intrinsic local scalar-current corrections. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set PolynomialCoefficientMetric SymmetricSpaceCovering SmoothCoveringDeRham SmoothSingularGlobal

/-- Actual intrinsic local scalar corrections to genuine smooth local primitives descend by
actual smooth Čech contraction to a genuine global smooth equivariant primitive. -/
theorem global_primitive_of_local_intrinsic_corrections (n : ℕ) {ι : Type}
    (U : ι → Set OrbitSpace) (hU : ∀ i, IsOpen (U i)) (hcover : (⋃ i, U i) = univ)
    (omega : EquivariantForm (deckRepresentation n) univ 2) (T : IntrinsicCurrent n 1 univ)
    (v : ∀ i, EquivariantForm (deckRepresentation n) (U i) 1)
    (f : ∀ i, IntrinsicCurrent n 0 (U i))
    (hv : ∀ i, differential (deckRepresentation n) (hU i) 1 (v i) =
      restrictEquivariant (deckRepresentation n) (subset_univ _) 2 omega)
    (hf : ∀ i, intrinsicCurrentDifferential n 0 (U i) (f i) =
      intrinsicCurrentRestriction n 1 (subset_univ _) T -
        intrinsicSmoothCurrent n 1 (U i) (hU i) (v i)) :
    ∃ w : EquivariantForm (deckRepresentation n) univ 1,
      differential (deckRepresentation n) isOpen_univ 1 w = omega := by
  classical
  let h (t : Fin 2 → ι) := intrinsicCorrection_difference_smooth n (cechDomain U t)
    (cechDomain_isOpen U hU t) (intrinsicCurrentRestriction n 1 (subset_univ _) T)
    (intrinsicCurrentRestriction n 0 (cechLocal_entry_subset U t 0) (f (t 0)))
    (intrinsicCurrentRestriction n 0 (cechLocal_entry_subset U t 1) (f (t 1)))
    (restrictEquivariant (deckRepresentation n) (cechLocal_entry_subset U t 0) 1 (v (t 0)))
    (restrictEquivariant (deckRepresentation n) (cechLocal_entry_subset U t 1) 1 (v (t 1)))
    (intrinsicCorrection_restrict n (hU (t 0)) (cechDomain_isOpen U hU t)
      (cechLocal_entry_subset U t 0) T (f (t 0)) (v (t 0)) (hf (t 0)))
    (intrinsicCorrection_restrict n (hU (t 1)) (cechDomain_isOpen U hU t)
      (cechLocal_entry_subset U t 1) T (f (t 1)) (v (t 1)) (hf (t 1)))
  let a : FormCechTerms (deckRepresentation n) U 0 2 := fun t => (h t).choose
  have ha (t : Fin 2 → ι) :
      intrinsicSmoothCurrent n 0 (cechDomain U t) (cechDomain_isOpen U hU t) (a t) =
        intrinsicCechDifference U n f t := (h t).choose_spec.1
  have hav : formCechColumnD (deckRepresentation n) U hU 2 0 a =
      -formCechD (deckRepresentation n) U 1 1 (cechLocalFamily (deckRepresentation n) U 1 v) := by
    funext t
    exact (h t).choose_spec.2.trans ((neg_sub _ _).symm.trans
      (congrArg (fun z : EquivariantForm (deckRepresentation n) (cechDomain U t) 1 => -z)
        (cechLocalFamily_difference (deckRepresentation n) U 1 v t)).symm)
  exact global_primitive_of_cech_correction (deckRepresentation n) U hU
    (fun q hq => hcover ▸ hq) omega (cechLocalFamily (deckRepresentation n) U 1 v) a
    (intrinsicCechDifference_cocycle U n hU f a ha) hav
    (cechLocalFamily_primitive (deckRepresentation n) U hU omega v hv)

end TernaryPoly.PolynomialFormWeakSmooth
