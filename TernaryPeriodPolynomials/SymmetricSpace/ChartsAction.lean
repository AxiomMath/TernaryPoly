module

public import TernaryPeriodPolynomials.SymmetricSpace.ChartsHomeomorph
public import TernaryPeriodPolynomials.SymmetricSpace.PositiveAction

@[expose] public section


open Matrix
open scoped ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace TernaryPoly.SymmetricSpaceCharts
open SymmetricSpacePositive

section MatrixCalculus
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Entrywise finite sums prove smoothness of the actual matrix product. -/
theorem contDiff_matrix_mul {A B : E → Mat} (hA : ContDiff ℝ ∞ A)
    (hB : ContDiff ℝ ∞ B) : ContDiff ℝ ∞ (fun x => A x*B x) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  simp only [Matrix.mul_apply]
  apply ContDiff.sum
  intro k _
  exact (contDiff_pi.mp (contDiff_pi.mp hA i) k).mul
    (contDiff_pi.mp (contDiff_pi.mp hB k) j)

theorem contDiff_matrix_trace {A : E → Mat} (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (fun x => (A x).trace) := by
  change ContDiff ℝ ∞ (fun x => ∑ i,A x i i)
  exact ContDiff.sum fun i _ => contDiff_pi.mp (contDiff_pi.mp hA i) i

theorem contDiff_matrix_star {A : E → Mat} (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (fun x => star (A x)) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  simpa only [Matrix.star_apply,star_trivial] using
    (contDiff_pi.mp (contDiff_pi.mp hA j) i)

end MatrixCalculus

/-- Actual congruence in joint ambient matrix and five-coordinate variables. -/
def congruencePair (p : Mat × Coordinates) : Mat :=
  p.1*reconstruct p.2*star p.1

/-- The denominator in the actual normalized projective action. -/
def denominator (p : Mat × Coordinates) : ℝ := (congruencePair p).trace

/-- The rational trace-normalization formula, before restricting to invertible matrices. -/
def matrixCoordinateAction (p : Mat × Coordinates) : Coordinates :=
  extract (normalize (congruencePair p))

def regularPairs : Set (Mat × Coordinates) := {p | denominator p≠0}

theorem contDiff_congruencePair : ContDiff ℝ ∞ congruencePair := by
  exact contDiff_matrix_mul
    (contDiff_matrix_mul contDiff_fst (contDiff_reconstruct.comp contDiff_snd))
    (contDiff_matrix_star contDiff_fst)

theorem contDiff_denominator : ContDiff ℝ ∞ denominator :=
  contDiff_matrix_trace contDiff_congruencePair

theorem isOpen_regularPairs : IsOpen regularPairs :=
  isOpen_ne_fun contDiff_denominator.continuous continuous_const

/-- The actual projective formula is jointly smooth wherever its trace denominator is nonzero. -/
theorem contDiffOn_matrixCoordinateAction :
    ContDiffOn ℝ ∞ matrixCoordinateAction regularPairs := by
  apply contDiff_extract.comp_contDiffOn
  exact (contDiff_denominator.contDiffOn.inv (fun p hp => hp)).smul
    contDiff_congruencePair.contDiffOn

/-- Coordinate expression of the genuine normalized action of an invertible real matrix. -/
def coordinateAction (g : RealGL) (x : Coordinates) : Coordinates :=
  matrixCoordinateAction (g.val,x)

theorem coordinateAction_formula (g : RealGL) (x : Coordinates) :
    coordinateAction g x=extract (normalize (conjugate g (reconstruct x))) := rfl

/-- Positive definiteness proves the denominator positive for every actual group action. -/
theorem denominator_pos (g : RealGL) (x : Coordinates) (hx : x∈positiveCoordinates) :
    0<denominator (g.val,x) :=
  (conjugate_positive g (reconstruct x) hx).trace_pos

/-- Every actual GL3 action is smooth on the explicit open five-dimensional model. -/
theorem contDiffOn_coordinateAction (g : RealGL) :
    ContDiffOn ℝ ∞ (coordinateAction g) positiveCoordinates := by
  apply contDiffOn_matrixCoordinateAction.comp
    (show ContDiffOn ℝ ∞ (fun x : Coordinates => (g.val,x)) positiveCoordinates by fun_prop)
  intro x hx
  exact ne_of_gt (denominator_pos g x hx)

theorem coordinateAction_mem (g : RealGL) (x : Coordinates) (hx : x∈positiveCoordinates) :
    coordinateAction g x∈positiveCoordinates := by
  exact extract_mem (act g ⟨reconstruct x,reconstruct_mem x hx⟩)

/-- The smooth formula is literally the genuine action transported through the homeomorphism. -/
theorem chartHomeomorph_act (g : RealGL) (S : Space) :
    (chartHomeomorph (act g S)).val=coordinateAction g (chartHomeomorph S).val := by
  change extract (normalize (conjugate g S.val))=
    extract (normalize (conjugate g (reconstruct (extract S.val))))
  rw [reconstruct_extract S.val (Matrix.isHermitian_iff_isSymm.mp S.property.1.isHermitian)
    S.property.2]

/-- The coordinate action is a genuine homeomorphism of the explicit open domain. -/
def coordinateActionHomeomorph (g : RealGL) : PositiveCoordinates ≃ₜ PositiveCoordinates :=
  chartHomeomorph.symm.trans ((actionHomeomorph g).trans chartHomeomorph)

@[simp] theorem coordinateActionHomeomorph_apply (g : RealGL) (x : PositiveCoordinates) :
    (coordinateActionHomeomorph g x).val=coordinateAction g x.val := rfl

end TernaryPoly.SymmetricSpaceCharts
