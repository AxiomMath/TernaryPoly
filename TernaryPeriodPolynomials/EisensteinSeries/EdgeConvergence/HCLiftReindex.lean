module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCLiftShift
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Smooth.NormPower
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.OrbitSmooth

@[expose] public section


/-!
# Adding a vertex to a family of plane sections

Original work by Claude Sonnet 5.5.

A family of plane sections with `k` vertices is also a family with `k + 1` vertices (the new vertex,
at position `0`, is ignored): `dropFirst`. Its cusp lift is again smooth (`hasSmoothCuspLift_dropFirst`).
This is used to absorb the determinant twist `exp (z τ(v))` of the orbit of the local vectors under
the real group `GL₂(ℝ)` into a new vertex `v`, with weight `τ(v) = -(1/3) log det v`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix
open scoped Matrix.Norms.Elementwise
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence.HCLift

/-- Smoothness of a function of a reindexed sub-tuple of a tuple of real matrices. -/
theorem smooth_comp_reindex {m n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (reindex : Fin m → Fin n) (function : (Fin m → RealGL3) → E) (smooth : Smooth function) :
    Smooth (fun x : Fin n → RealGL3 => function (fun i => x (reindex i))) := by
  have projection : ContDiff ℝ ⊤ (fun matrices : Fin n → Matrix (Fin 3) (Fin 3) ℝ =>
      fun i : Fin m => matrices (reindex i)) :=
    contDiff_pi.mpr (fun i => contDiff_apply ℝ _ (reindex i))
  have maps : Set.MapsTo (fun matrices : Fin n → Matrix (Fin 3) (Fin 3) ℝ =>
      fun i : Fin m => matrices (reindex i))
      {matrices | ∀ i, (matrices i).det ≠ 0} {matrices | ∀ i, (matrices i).det ≠ 0} := by
    intro matrices membership i
    exact membership (reindex i)
  apply (smooth.comp projection.contDiffOn maps).congr
  intro matrices membership
  rfl

/-- The family with one more vertex, at position `0`, on which it does not depend. -/
def dropFirst {arity : ℕ} (family : (Fin arity → RealGL3) → AdelicGL → ℂ) :
    (Fin (arity + 1) → RealGL3) → AdelicGL → ℂ :=
  fun vertices argument => family (fun i => vertices i.succ) argument

theorem hasSmoothCuspLift_dropFirst {degree arity : ℕ} (data : InducingData degree) (side : Side)
    (parameter : ℂ) (family : (Fin arity → RealGL3) → AdelicGL → ℂ)
    (lift : HasSmoothCuspLift data side parameter family) :
    HasSmoothCuspLift data side parameter (dropFirst family) := by
  intro argument
  obtain ⟨vectors, vectorsSmooth, equation⟩ := lift argument
  refine ⟨fun x => vectors (fun i => x i.succ), ?_, ?_⟩
  · exact smooth_comp_reindex (fun i : Fin (arity + 1) => i.succ)
      (fun x : Fin (arity + 1) → RealGL3 => (vectors x).val) vectorsSmooth
  · intro x binary
    have realization := equation (fun i => x i.succ) binary
    simp only [dropFirst]
    simpa only [Fin.succ_castSucc, Fin.succ_last] using realization

/-- The twist by the determinant of a vertex: `τ(v) = -(1/3) log det v`. -/
def determinantTwist (vertex : RealGL3) : ℝ := -(1 / 3) * Real.log vertex.val.det

theorem smooth_determinantTwist :
    Smooth (fun x : Fin 1 → RealGL3 => determinantTwist (x 0)) := by
  have logarithm : ContDiffOn ℝ ⊤ (fun matrices : SmoothJets.MatrixTuples 3 1 =>
      Real.log (matrices 0).det) (SmoothJets.domain 3 1) :=
    (SmoothNormPower.determinant_smooth (size := 3) (arity := 1) 0).contDiffOn.log
      (fun matrices membership => membership 0)
  apply ((contDiffOn_const (c := -(1 / 3 : ℝ))).mul logarithm).congr
  intro matrices membership
  have value : (invertibleMatrix (matrices 0)).val = matrices 0 :=
    PlaneEisensteinContinuation.OrbitSmooth.invertibleMatrix_val _ (membership 0)
  simp only [determinantTwist, value]

/-- The weight of the family with one more vertex: the weight of the old vertices plus the
determinant twist of the new one. -/
def extendedWeight {arity : ℕ} (weight : (Fin arity → RealGL3) → ℝ)
    (vertices : Fin (arity + 1) → RealGL3) : ℝ :=
  weight (fun i => vertices i.succ) + determinantTwist (vertices 0)

theorem smooth_extendedWeight {arity : ℕ} (weight : (Fin arity → RealGL3) → ℝ)
    (weightSmooth : Smooth weight) : Smooth (extendedWeight weight) :=
  (smooth_comp_reindex (fun i : Fin arity => i.succ) weight weightSmooth).add
    (smooth_comp_coordinate (0 : Fin (arity + 1))
      (fun x : Fin 1 → RealGL3 => determinantTwist (x 0)) smooth_determinantTwist)

end TernaryPeriodPolynomials.EdgeConvergence.HCLift
