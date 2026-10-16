module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneGroup

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem realPlaneMatrix_binary_entry (element : RealPlaneGroup) (row column : Fin 2) :
    (realPlaneMatrix element).val row.castSucc column.castSucc = element.right.val row column := by
  rw [realPlaneMatrix_apply]
  fin_cases row <;> fin_cases column <;>
    simp [realPlaneRadicalMatrix, planeUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three]

theorem realPlaneMatrix_radical_entry (element : RealPlaneGroup) (row : Fin 2) :
    (realPlaneMatrix element).val row.castSucc 2 = element.left.toAdd row := by
  rw [realPlaneMatrix_apply]
  fin_cases row <;>
    simp [realPlaneRadicalMatrix, planeUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three]

theorem realPlaneMatrix_injective : Function.Injective realPlaneMatrix := by
  intro first second equality
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    funext row
    rw [← realPlaneMatrix_radical_entry, ← realPlaneMatrix_radical_entry, equality]
  · apply Units.ext
    funext row column
    rw [← realPlaneMatrix_binary_entry, ← realPlaneMatrix_binary_entry, equality]

def identityPlaneRealMatrix :
    flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)) →* RealGL3 :=
  (GeneralLinearGroup.map (algebraMap ℚ ℝ)).comp
    (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3))).subtype

theorem identityPlaneRealMatrix_lift
    (element : flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3))) :
    ∃ lift : RealPlaneGroup, realPlaneMatrix lift = identityPlaneRealMatrix element := by
  obtain ⟨first, second, matrix, equality⟩ := identityPlane_stabilizer_exists_blocks element
  refine ⟨⟨Multiplicative.ofAdd ![(first : ℝ), (second : ℝ)], GeneralLinearGroup.map (Int.castRingHom ℝ) matrix⟩, ?_⟩
  change planeUnipotent (first : ℝ) (second : ℝ) * planeLevi (GeneralLinearGroup.map (Int.castRingHom ℝ) matrix) 1 =
    GeneralLinearGroup.map (algebraMap ℚ ℝ) element.val
  rw [equality, map_mul, map_planeUnipotent, map_planeLevi_one, map_mul, map_planeUnipotent, map_planeLevi_one]
  have casts : GeneralLinearGroup.map (algebraMap ℚ ℝ) (GeneralLinearGroup.map (Int.castRingHom ℚ) matrix) =
      GeneralLinearGroup.map (Int.castRingHom ℝ) matrix := by
    apply Units.ext
    funext row column
    simp [GeneralLinearGroup.map_apply]
  rw [casts]
  simp

def identityPlaneRealGroup :
    flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)) →* RealPlaneGroup :=
  monoidHomLiftThroughInjective identityPlaneRealMatrix realPlaneMatrix realPlaneMatrix_injective identityPlaneRealMatrix_lift

theorem identityPlaneRealGroup_matrix
    (element : flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3))) :
    realPlaneMatrix (identityPlaneRealGroup element) = GeneralLinearGroup.map (algebraMap ℚ ℝ) element.val :=
  monoidHomLiftThroughInjective_spec identityPlaneRealMatrix realPlaneMatrix realPlaneMatrix_injective
    identityPlaneRealMatrix_lift element

def radicalLatticeReal : RadicalLattice →* RealPlaneRadical where
  toFun element := Multiplicative.ofAdd ![(element.toAdd.1 : ℝ), (element.toAdd.2 : ℝ)]
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext coordinate
    fin_cases coordinate <;> simp
  map_mul' first second := by
    apply Multiplicative.toAdd.injective
    funext coordinate
    fin_cases coordinate <;> simp

theorem identityPlaneRealGroup_radical (radical : RadicalLattice) :
    identityPlaneRealGroup (identityPlaneRadicalInclusion radical) = SemidirectProduct.inl (radicalLatticeReal radical) := by
  apply realPlaneMatrix_injective
  rw [identityPlaneRealGroup_matrix, realPlaneMatrix_inl]
  change GeneralLinearGroup.map (algebraMap ℚ ℝ)
    (planeUnipotent (radical.toAdd.1 : ℚ) (radical.toAdd.2 : ℚ)) =
      planeUnipotent (radical.toAdd.1 : ℝ) (radical.toAdd.2 : ℝ)
  rw [map_planeUnipotent]
  simp

theorem identityPlaneRealGroup_levi (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    identityPlaneRealGroup (identityPlaneLeviSection matrix) =
      SemidirectProduct.inr (GeneralLinearGroup.map (Int.castRingHom ℝ) matrix) := by
  apply realPlaneMatrix_injective
  rw [identityPlaneRealGroup_matrix, realPlaneMatrix_inr]
  change GeneralLinearGroup.map (algebraMap ℚ ℝ)
    (GeneralLinearGroup.map (Int.castRingHom ℚ) (planeLevi matrix 1)) = _
  rw [map_planeLevi_one, map_planeLevi_one]
  congr 1

end TernaryPeriodPolynomials.SphericalDetection.Helpers
