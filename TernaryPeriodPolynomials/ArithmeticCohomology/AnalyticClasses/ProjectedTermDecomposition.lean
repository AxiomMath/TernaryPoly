module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Good.LinePlaneSimplices
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.PlaneHomogeneousDecomposition
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.GenericEdgeTransfer

@[expose] public section


/-!
# The projected good-line term: canonical part plus transported edges

The projected term is the source on the Gram–Schmidt simplices of the two good-line
simplices `(1, γ, γ r')` and `(1, r, r γ)` moved by the good-line argument. Every vertex is of the
form `planeLevi B 1 · g(w)` with `|det B| = 1`, so (a) the source agrees with the
determinant-normalized source there, (b) the Gram–Schmidt vertices are positive multiples of points
of the real plane group, and (c) Codexiom's real-plane chain applied to the normalized source splits
the source on these simplices into the canonical binary relative cocycle and the coboundary of the
explicit total primitive. The coboundary parts of the two simplices combine into the four-edge
combination of the edge cochain `E(y₀, y₁) = K̂(π y₀, π y₁)` (`π` the real-plane point of the
Gram–Schmidt vertex).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- Vertices of the form `planeLevi B 1 · g(w)` with unimodular `B`. -/
def GoodLineForm (y : RealGL3) : Prop :=
  ∃ (B : BinaryRealGL) (w : ℝ × ℝ), |B.val.det| = 1 ∧
    y = planeLevi B 1 * standardGoodLineRealArgument w

theorem gsUpper_corner (w : ℝ × ℝ) : (gsUpper w).val 2 2 = gsRadius w := by
  rw [gsUpper_val]
  simp [gsUpperMatrix]

theorem planeLevi_mul_corner (B : BinaryRealGL) (p : RealGL3) :
    (planeLevi B 1 * p).val 2 2 = p.val 2 2 := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
  simp [planeLevi, planeBlock]

theorem GoodLineForm.gsVertex_mem {y : RealGL3} (form : GoodLineForm y) :
    gsVertex y ∈ planeParabolic ℝ := by
  obtain ⟨B, w, -, rfl⟩ := form
  exact gsVertex_plane_standard_mem (planeLevi_mem _ _) _

theorem GoodLineForm.corner_pos {y : RealGL3} (form : GoodLineForm y) :
    0 < (gsVertex y).val 2 2 := by
  obtain ⟨B, w, -, rfl⟩ := form
  rw [gsVertex_plane_standard (planeLevi_mem _ _), planeLevi_mul_corner, gsUpper_corner]
  exact gsRadius_pos w

theorem abs_det_standardGoodLineRealArgument (w : ℝ × ℝ) :
    |(standardGoodLineRealArgument w).val.det| = 1 := by
  rw [standardGoodLineRealArgument_val, Matrix.det_fin_three]
  simp

theorem GoodLineForm.abs_det {y : RealGL3} (form : GoodLineForm y) : |y.val.det| = 1 := by
  obtain ⟨B, w, unit, rfl⟩ := form
  rw [Units.val_mul, Matrix.det_mul, abs_mul, abs_det_standardGoodLineRealArgument, mul_one]
  have block : (planeLevi B 1).val.det = B.val.det := by
    simp [planeLevi, planeBlock, Matrix.det_fin_three, Matrix.det_fin_two]
  rw [block, unit]

theorem conjugateLevi_unimodular (γ : GeneralLinearGroup (Fin 2) ℤ) :
    |(binaryPivotSwap * GeneralLinearGroup.map (Int.castRingHom ℝ) γ * binaryPivotSwap :
      BinaryRealGL).val.det| = 1 := by
  have := abs_upperBlockDet_conjugateLevi γ
  rwa [goodLineConjugateRealLevi, upperBlockDet_planeLevi] at this

theorem goodLineForm_one (u : ℝ × ℝ) : GoodLineForm (standardGoodLineRealArgument u * 1) :=
  ⟨1, u, by simp, by rw [mul_one, show planeLevi (1 : BinaryRealGL) 1 = 1 from
    (planeLeviHom ℝ).map_one, one_mul]⟩

theorem goodLineForm_levi (u : ℝ × ℝ) (γ : GeneralLinearGroup (Fin 2) ℤ) :
    GoodLineForm (standardGoodLineRealArgument u * edgeLevi γ) :=
  ⟨_, goodLineLeviRealInput γ u, conjugateLevi_unimodular γ, standardGoodLineRealArgument_levi u γ⟩

theorem goodLineForm_radical (u : ℝ × ℝ) (r : RadicalLattice) :
    GoodLineForm (standardGoodLineRealArgument u * edgeRadical r) :=
  ⟨1, goodLineRadicalRealShift r u, by simp, by
    rw [show planeLevi (1 : BinaryRealGL) 1 = 1 from (planeLeviHom ℝ).map_one, one_mul]
    exact standardGoodLineRealArgument_radical u r⟩

theorem goodLineForm_leviRadical (u : ℝ × ℝ) (γ : GeneralLinearGroup (Fin 2) ℤ)
    (r : RadicalLattice) :
    GoodLineForm (standardGoodLineRealArgument u * (edgeLevi γ * edgeRadical r)) := by
  refine ⟨_, goodLineRadicalRealShift r (goodLineLeviRealInput γ u), conjugateLevi_unimodular γ, ?_⟩
  rw [← mul_assoc, standardGoodLineRealArgument_levi, mul_assoc,
    standardGoodLineRealArgument_radical]
  rfl

theorem goodLineForm_unimodular {y : RealGL3} (form : GoodLineForm y) :
    |(gsVertex y).val.det| = 1 := by
  rw [abs_det_gsVertex]
  exact form.abs_det

variable {n : ℕ} {index : Type} [Fintype index]

/-- The canonical value on a simplex of real-plane points. -/
def canonicalSimplexValue (data : InducingData n) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative)
    (Q : Fin 3 → RealPlaneGroup) : cuspidalTensorValues data.cusp (HomogeneousPoly n) :=
  (realPlaneCuspidalRep n data.cusp data.chi).ρ (Q 0)
    ((realPlaneLevelBinaryRelativeCycle n data.cusp data.chi trivial basis relative regular).val
      ((Q 0)⁻¹ * Q 1, (Q 1)⁻¹ * Q 2))

/-- The edge cochain of the explicit total primitive. -/
def totalPrimitiveEdge (data : InducingData n) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (primitive : RealPlaneRadical → realPlaneLevelCuspidalRep n data.cusp data.chi)
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative) :
    EdgeCochain data :=
  fun V => homogeneousOne (realPlaneCuspidalRep n data.cusp data.chi)
    (sourceTotalPrimitive data trivial basis primitive relative regular)
    (gsPlaneVertex (V 0)) (gsPlaneVertex (V 1))

/-- **The source on a Gram–Schmidt simplex of good-line vertices.** -/
theorem source_gsSimplex_split (data : InducingData n) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (source : SourceCochain n) (cocycle : IsSourceCocycle data .plane source)
    (primitive : RealPlaneRadical → realPlaneLevelCuspidalRep n data.cusp data.chi)
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (formula : relative.val = sourcePlaneLevelGroupCocycle data (normalizedSource source)
      (normalizedSource_cocycle data trivial source cocycle) -
      twoBoundaryCycle _ (realPlanePrimitiveExtension _ primitive))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative)
    (V : Fin 3 → RealGL3) (form : ∀ i, GoodLineForm (V i)) :
    sourcePlaneCuspidalValues data source cocycle (fun i => gsVertex (V i)) 1 =
      canonicalSimplexValue data trivial basis relative regular (fun i => gsPlaneVertex (V i)) +
        (totalPrimitiveEdge data trivial basis primitive relative regular ![V 1, V 2] -
          totalPrimitiveEdge data trivial basis primitive relative regular ![V 0, V 2] +
          totalPrimitiveEdge data trivial basis primitive relative regular ![V 0, V 1]) := by
  rw [sourcePlaneCuspidalValues_normalized data trivial source cocycle _
      (fun i => goodLineForm_unimodular (form i)),
    normalizedSource_gsVertex data trivial source cocycle V (fun i => (form i).gsVertex_mem)
      (fun i => (form i).corner_pos),
    sourcePlaneCuspidalValues_planeSimplex data trivial basis (normalizedSource source)
      (normalizedSource_cocycle data trivial source cocycle) primitive relative formula regular]
  rfl

/-- The canonical projected term. -/
def canonicalProjectedTerm (data : InducingData n) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative)
    (u : ℝ × ℝ) (γ : GeneralLinearGroup (Fin 2) ℤ) (r : RadicalLattice) :
    cuspidalTensorValues data.cusp (HomogeneousPoly n) :=
  cuspidalTensorMap data.cusp
    (realCoefficientComponent n data.chi (standardGoodLineRealArgument u)⁻¹)
    (canonicalSimplexValue data trivial basis relative regular
        (fun i => gsPlaneVertex (standardGoodLineRealArgument u *
          ![1, edgeLevi γ, edgeRadical r * edgeLevi γ] i)) -
      canonicalSimplexValue data trivial basis relative regular
        (fun i => gsPlaneVertex (standardGoodLineRealArgument u *
          ![1, edgeRadical r, edgeRadical r * edgeLevi γ] i)))

theorem goodLineForm_radicalLevi (u : ℝ × ℝ) (γ : GeneralLinearGroup (Fin 2) ℤ)
    (r : RadicalLattice) :
    GoodLineForm (standardGoodLineRealArgument u * (edgeRadical r * edgeLevi γ)) := by
  rw [edgeRadical_mul_edgeLevi]
  exact goodLineForm_leviRadical u γ _

theorem goodLineRealVertices_first (γ : GeneralLinearGroup (Fin 2) ℤ) (r : RadicalLattice) :
    goodLineRealVertices (goodLineLeviSection γ,
        goodLineRadicalInclusion (lowerLeviLatticeInput γ r)) =
      ![1, edgeLevi γ, edgeRadical r * edgeLevi γ] := by
  funext index
  fin_cases index
  · simp [goodLineRealVertices]
  · rfl
  · change GeneralLinearGroup.map (algebraMap ℚ ℝ)
      ((goodLineLeviSection γ).val * (goodLineRadicalInclusion (lowerLeviLatticeInput γ r)).val) = _
    rw [map_mul, edgeRadical_mul_edgeLevi]
    rfl

theorem goodLineRealVertices_second (γ : GeneralLinearGroup (Fin 2) ℤ) (r : RadicalLattice) :
    goodLineRealVertices (goodLineRadicalInclusion r, goodLineLeviSection γ) =
      ![1, edgeRadical r, edgeRadical r * edgeLevi γ] := by
  funext index
  fin_cases index
  · simp [goodLineRealVertices]
  · rfl
  · change GeneralLinearGroup.map (algebraMap ℚ ℝ)
      ((goodLineRadicalInclusion r).val * (goodLineLeviSection γ).val) = _
    rw [map_mul]
    rfl

/-- **The projected term splits into the canonical term and four transported edges.** -/
theorem goodLineIwasawaProjectedTerm_split (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (source : SourceCochain n) (cocycle : IsSourceCocycle data .plane source)
    (primitive : RealPlaneRadical → realPlaneLevelCuspidalRep n data.cusp data.chi)
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (formula : relative.val = sourcePlaneLevelGroupCocycle data (normalizedSource source)
      (normalizedSource_cocycle data trivial source cocycle) -
      twoBoundaryCycle _ (realPlanePrimitiveExtension _ primitive))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative)
    (u : ℝ × ℝ) (γ : GeneralLinearGroup (Fin 2) ℤ) (r : RadicalLattice) :
    goodLineIwasawaProjectedTerm data source cocycle u γ r =
      canonicalProjectedTerm data trivial basis relative regular u γ r +
        (edgeTransported data (totalPrimitiveEdge data trivial basis primitive relative regular) u
            (edgeLevi γ) (edgeRadical r * edgeLevi γ) -
          edgeTransported data (totalPrimitiveEdge data trivial basis primitive relative regular) u
            (edgeRadical r) (edgeRadical r * edgeLevi γ) +
          edgeTransported data (totalPrimitiveEdge data trivial basis primitive relative regular) u
            1 (edgeLevi γ) -
          edgeTransported data (totalPrimitiveEdge data trivial basis primitive relative regular) u
            1 (edgeRadical r)) := by
  have form1 (i : Fin 3) : GoodLineForm (standardGoodLineRealArgument u *
      ![1, edgeLevi γ, edgeRadical r * edgeLevi γ] i) := by
    fin_cases i
    · exact goodLineForm_one u
    · exact goodLineForm_levi u γ
    · exact goodLineForm_radicalLevi u γ r
  have form2 (i : Fin 3) : GoodLineForm (standardGoodLineRealArgument u *
      ![1, edgeRadical r, edgeRadical r * edgeLevi γ] i) := by
    fin_cases i
    · exact goodLineForm_one u
    · exact goodLineForm_radical u r
    · exact goodLineForm_radicalLevi u γ r
  have split1 := source_gsSimplex_split data trivial basis source cocycle primitive relative formula
    regular _ form1
  have split2 := source_gsSimplex_split data trivial basis source cocycle primitive relative formula
    regular _ form2
  unfold goodLineIwasawaProjectedTerm canonicalProjectedTerm
  rw [goodLineRealVertices_first, goodLineRealVertices_second, split1, split2]
  apply Subtype.ext
  funext A
  simp only [Submodule.coe_sub, Submodule.coe_add, Pi.sub_apply, Pi.add_apply,
    cuspidalTensorMap_val_apply, edgeTransported, map_add, map_sub]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  abel

end TernaryPeriodPolynomials.AnalyticClasses
