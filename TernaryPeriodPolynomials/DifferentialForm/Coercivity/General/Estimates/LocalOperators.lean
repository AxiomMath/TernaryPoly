module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.LocalFriedrichs

@[expose] public section


/-! # General coercivity, Tier B: the exterior derivative and codifferential as first-order data

The exterior derivative and the codifferential, on forms supported in a compact subset `K` of the
positive coordinates, are the matrix first-order operators with the compactly supported coefficient
extensions of the coordinate library.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open Set MeasureTheory Filter Topology TernaryPoly TernaryPoly.SymmetricSpaceCharts
  TernaryPoly.PolynomialFormMetric TernaryPoly.PolynomialFormCoordinates
  TernaryPoly.CompactCoordinateIntegration TernaryPoly.SymmetricSpaceRiemannian
  TernaryPoly.SmoothLocalDeRham
open scoped ContDiff

variable {n : ℕ}

/-- The exterior derivative as first-order data over the compact set `K`. -/
def dDatum (k : ℕ) {K : Set Coordinates} (hK : IsCompact K) (hKpos : K ⊆ positiveCoordinates) :
    FODatum n k (k + 1) K :=
  let H := exists_differential_coefficient_extensions n k hK hKpos
  { D := fun g => extDeriv g
    Kι := Fin 5
    v := fun d => (Pi.single d 1 : Coordinates)
    A := H.choose
    B := fun _ _ _ _ => 0
    A_smooth := fun j i d => (H.choose_spec.choose_spec.2.2.1 j i d).1
    B_smooth := fun _ _ _ => contDiff_const
    A_compact := fun j i d => H.choose_spec.choose_spec.1.of_isClosed_subset (isClosed_tsupport _)
      (H.choose_spec.choose_spec.2.2.1 j i d).2
    B_compact := fun _ _ _ => HasCompactSupport.zero
    matrix := fun g hg hsg j => extDeriv_eq_extended_matrix n k K H.choose
      (fun x hx j i d => (H.choose_spec.choose_spec.2.2.2 x hx j i d).self_of_nhds) g hg hsg j
    smooth := fun _ hg _ => contDiffOn_univ.mp (smooth_extDeriv isOpen_univ hg.contDiffOn)
    tsupport_sub := fun g => tsupport_extDeriv_subset n k g
    loc := fun _ _ _ h => h.extDeriv_eq }

/-- The codifferential as first-order data over the compact set `K`. -/
def deltaDatum (k : ℕ) {K : Set Coordinates} (hK : IsCompact K) (hKpos : K ⊆ positiveCoordinates) :
    FODatum n (k + 1) k K :=
  let H := exists_adjoint_coefficient_extensions n k hK hKpos
  { D := fun g => localAdjoint n k g
    Kι := Index n k × Index n (k + 1) × Fin 5
    v := fun q => (Pi.single q.2.2 1 : Coordinates)
    A := fun i t q => H.choose i t q.1 q.2.1 q.2.2
    B := fun i t q => H.choose_spec.choose i t q.1 q.2.1 q.2.2
    A_smooth := fun i t q => (H.choose_spec.choose_spec.choose_spec.2.2.1 i t q.1 q.2.1 q.2.2).1
    B_smooth := fun i t q => (H.choose_spec.choose_spec.choose_spec.2.2.1 i t q.1 q.2.1 q.2.2).2.1
    A_compact := fun i t q => H.choose_spec.choose_spec.choose_spec.1.of_isClosed_subset
      (isClosed_tsupport _) (H.choose_spec.choose_spec.choose_spec.2.2.1 i t q.1 q.2.1 q.2.2).2.2.1
    B_compact := fun i t q => H.choose_spec.choose_spec.choose_spec.1.of_isClosed_subset
      (isClosed_tsupport _) (H.choose_spec.choose_spec.choose_spec.2.2.1 i t q.1 q.2.1 q.2.2).2.2.2
    matrix := fun g hg hsg j => by
      exact (localAdjoint_eq_extended_matrix n k K hKpos H.choose H.choose_spec.choose
        (fun x hx i t l j d => ⟨(H.choose_spec.choose_spec.choose_spec.2.2.2 x hx i t l j d).1.self_of_nhds,
          (H.choose_spec.choose_spec.choose_spec.2.2.2 x hx i t l j d).2.self_of_nhds⟩) g hg hsg j)
    smooth := fun _ hg hs => contDiff_localAdjoint n k hg.contDiffOn hs
    tsupport_sub := fun g => tsupport_localAdjoint n k g
    loc := fun _ _ _ h => localAdjoint_congr n k h }

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
