module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.Uniform
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.BadLineEdges

@[expose] public section


/-!
# The standard bad line: uniform form

The case `F = standardBadLine` of `Face/Uniform`: stabilizer `ℤ² ⋊ (ℤˣ × binaryArithmeticLevel)`
(`standardBadLineSemidirectEquiv`), whose radical fixes every complete flag over the line
(`binaryEdge_radical_mem`). `StandardBadLineMixedCuspidal` proves the same equivalence with the
explicit cusp subgroups `ℤˣ × binaryCuspLevel frame`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein Homogeneous Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Face

/-- The Levi `ℤˣ × binaryArithmeticLevel` of the standard line embeds in `GL₂(ℤ) × ℤˣ`. -/
def badLineLeviEmbedding :
    (ℤˣ × binaryArithmeticLevel) →* GeneralLinearGroup (Fin 2) ℤ × ℤˣ :=
  ((binaryArithmeticLevel.subtype).comp (MonoidHom.snd _ _)).prod (MonoidHom.fst _ _)

theorem badLineLeviEmbedding_injective : Function.Injective badLineLeviEmbedding := by
  rintro ⟨u, A⟩ ⟨u', A'⟩ h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  exact Prod.ext h2 (Subtype.ext h1)

/-- **The radical of the standard line fixes every complete flag over it.** -/
theorem badLine_radical_fixes (radical : Multiplicative (ℤ × ℤ)) (e : Edges)
    (he : endpoint .line e = standardBadLine) :
    (standardBadLineSemidirectEquiv (SemidirectProduct.inl radical)).val • e = e := by
  obtain ⟨frame, rfl⟩ := exists_binaryEdge e he
  exact MulAction.mem_stabilizer_iff.mp (binaryEdge_radical_mem frame radical).2

/-- **Standard bad line: locally inner iff mixed cuspidal**, for every degree. -/
theorem badLine_locallyInner_iff (degree : ℕ) (character : RankOneCharacter)
    (coordinate : H2 (fixedPointLevel rationalLevel standardBadLine)
      (rationalCoefficientComponent degree character)) :
    coordinate ∈ locallyInnerClasses degree character .line standardBadLine ↔
      ∃ radicalZero : faceH2Equiv integralBadLineSplitting.conjAct degree character
          standardBadLine standardBadLineSemidirectEquiv coordinate ∈
          (radicalRestrictionH2 integralBadLineSplitting.conjAct
            (faceRep integralBadLineSplitting.conjAct degree character standardBadLine
              standardBadLineSemidirectEquiv)).ker,
        ∀ e : Edges, endpoint .line e = standardBadLine →
          crossedPullbackH1 (faceCusp integralBadLineSplitting.conjAct standardBadLine
              standardBadLineSemidirectEquiv e).subtype
            (leviCrossedH1Representation integralBadLineSplitting.conjAct
              (faceRep integralBadLineSplitting.conjAct degree character standardBadLine
                standardBadLineSemidirectEquiv))
            (radicalKernelMixedMap integralBadLineSplitting.conjAct
              (faceRep integralBadLineSplitting.conjAct degree character standardBadLine
                standardBadLineSemidirectEquiv)
              ⟨faceH2Equiv integralBadLineSplitting.conjAct degree character standardBadLine
                standardBadLineSemidirectEquiv coordinate, radicalZero⟩) = 0 :=
  face_locallyInner_iff_uniform integralBadLineSplitting.conjAct degree character standardBadLine
    standardBadLineSemidirectEquiv (fun radical e he => badLine_radical_fixes radical e he)
    badLineLeviEmbedding badLineLeviEmbedding_injective coordinate

end TernaryPeriodPolynomials.Argument.FacePairingFull.Face
