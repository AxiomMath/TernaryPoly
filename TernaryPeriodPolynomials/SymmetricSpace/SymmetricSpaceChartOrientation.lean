module

public import TernaryPeriodPolynomials.SymmetricSpace.Orientation.Determinant
public import TernaryPeriodPolynomials.SymmetricSpace.ChartsBasic

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceChartOrientation
open Matrix
open SymmetricSpaceOrientation (Symmetric symmetricSubmodule congruence)
open SymmetricSpaceCharts (Coordinates extract reconstruct)

abbrev HomogeneousCoordinates := (Fin 5 ⊕ Unit) → ℝ

/-- Five literal matrix entries followed by the actual trace, in sum-type coordinates. -/
def traceCoordinates : Symmetric →ₗ[ℝ] HomogeneousCoordinates where
  toFun S := Sum.elim (extract S.val) (fun _ => S.val.trace)
  map_add' S T := by
    ext i
    rcases i with i | i
    · fin_cases i <;> rfl
    · exact Matrix.trace_add S.val T.val
  map_smul' r S := by
    ext i
    rcases i with i | i
    · fin_cases i <;> rfl
    · exact Matrix.trace_smul r S.val

/-- The last diagonal entry is trace minus the other two diagonal entries. -/
def fromTraceCoordinates : HomogeneousCoordinates →ₗ[ℝ] Symmetric where
  toFun z := ⟨!![z (.inl 0),z (.inl 1),z (.inl 2);
    z (.inl 1),z (.inl 3),z (.inl 4);
    z (.inl 2),z (.inl 4),z (.inr ())-z (.inl 0)-z (.inl 3)],by
      apply Matrix.IsSymm.ext
      intro i j
      fin_cases i <;> fin_cases j <;> rfl⟩
  map_add' z w := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    ring
  map_smul' r z := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    ring

@[simp] theorem traceCoordinates_from (z : HomogeneousCoordinates) :
    traceCoordinates (fromTraceCoordinates z)=z := by
  ext i
  rcases i with i | i
  · fin_cases i <;> rfl
  · cases i
    simp [traceCoordinates,fromTraceCoordinates,Matrix.trace,Fin.sum_univ_succ]

@[simp] theorem from_traceCoordinates (S : Symmetric) :
    fromTraceCoordinates (traceCoordinates S)=S := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  all_goals try (first | rfl | exact S.property.apply _ _)
  simp [fromTraceCoordinates,traceCoordinates,extract,Matrix.trace,Fin.sum_univ_succ]

/-- The actual six-dimensional linear coordinates compatible with trace-one charts. -/
def traceCoordinatesEquiv : Symmetric ≃ₗ[ℝ] HomogeneousCoordinates :=
  LinearEquiv.ofLinearMap traceCoordinates fromTraceCoordinates
    (by apply LinearMap.ext; intro z; exact traceCoordinates_from z)
    (by apply LinearMap.ext; intro S; exact from_traceCoordinates S)

/-- The affine chart is the literal homogeneous slice with trace coordinate one. -/
def affineLift (x : Coordinates) : HomogeneousCoordinates := Sum.elim x (fun _ => 1)

@[simp] theorem fromTraceCoordinates_affineLift (x : Coordinates) :
    (fromTraceCoordinates (affineLift x)).val=reconstruct x := rfl

@[simp] theorem traceCoordinates_inl (S : Symmetric) (i : Fin 5) :
    traceCoordinates S (.inl i)=extract S.val i := rfl

@[simp] theorem traceCoordinates_inr (S : Symmetric) :
    traceCoordinates S (.inr ())=S.val.trace := rfl

end TernaryPoly.SymmetricSpaceChartOrientation
