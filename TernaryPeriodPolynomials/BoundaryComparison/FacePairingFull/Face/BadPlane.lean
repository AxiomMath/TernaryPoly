module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.Uniform
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.StabilizerSplitting
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.ParabolicFactorization

@[expose] public section


/-!
# The identity (bad) plane: stabilizer `ℤ² ⋊ GL₂(ℤ)` and its cusp subgroups

The stabilizer of the identity plane `⟨e₁, e₂⟩` in the arithmetic level is the split extension
`ℤ² ⋊ GL₂(ℤ)` (`SphericalDetection.identityPlaneSemidirectEquiv`). Its radical fixes every complete
flag over the plane, so `Face/Uniform` applies: a plane class at the identity plane is locally
inner (zero restriction to the stabilizer of every complete flag over it) if and only if it has
zero restriction to the radical and its mixed class vanishes on the cusp subgroup of every
rational cusp of `GL₂(ℤ)` (`badPlane_locallyInner_iff`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein Homogeneous Matrix GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (identityPlaneSemidirectEquiv identityPlaneSplitting RadicalLattice upperRadicalLattice
    identityPlaneRadicalInclusion)

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Face

/-- The identity plane `⟨e₁, e₂⟩`. -/
def badPlaneFlag : Flags .plane := QuotientGroup.mk (1 : RationalGL3)

/-- The split presentation of the stabilizer of the identity plane. -/
def badPlaneSemidirectEquiv :
    RadicalLattice ⋊[identityPlaneSplitting.conjAct] GeneralLinearGroup (Fin 2) ℤ ≃*
      ↥(fixedPointLevel rationalLevel badPlaneFlag) :=
  identityPlaneSemidirectEquiv

theorem badPlaneSemidirectEquiv_inl (radical : RadicalLattice) :
    (badPlaneSemidirectEquiv (SemidirectProduct.inl radical)).val =
      planeUnipotent (radical.toAdd.1 : ℚ) (radical.toAdd.2 : ℚ) := by
  change (identityPlaneRadicalInclusion radical * identityPlaneSplitting 1).val = _
  rw [map_one, mul_one]
  rfl

theorem planeUnipotent_inv (s t : ℚ) :
    (planeUnipotent s t)⁻¹ = planeUnipotent (-s) (-t) :=
  Units.ext rfl

/-- Conjugates of the plane radical by plane-parabolic elements lie in the Borel subgroup. -/
theorem planeUnipotent_conj_mem_borel (g : RationalGL3) (hg : g ∈ planeParabolic ℚ) (s t : ℚ) :
    g⁻¹ * planeUnipotent s t * g ∈ parabolic .plane ⊓ parabolic .line := by
  have hplane : g⁻¹ * planeUnipotent s t * g ∈ planeParabolic ℚ :=
    (planeParabolic ℚ).mul_mem ((planeParabolic ℚ).mul_mem ((planeParabolic ℚ).inv_mem hg)
      ⟨rfl, rfl⟩) hg
  refine ⟨hplane, ?_⟩
  have hcol : ∀ i, (planeUnipotent s t * g).val i 0 = g.val i 0 := by
    intro i
    have h20 : g.val 2 0 = 0 := hg.1
    fin_cases i <;> simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, planeUnipotent, h20]
  have key : ∀ i, (g⁻¹ * planeUnipotent s t * g).val i 0 = (1 : Matrix (Fin 3) (Fin 3) ℚ) i 0 := by
    intro i
    rw [mul_assoc, Units.val_mul, Matrix.mul_apply]
    simp only [hcol]
    rw [← Matrix.mul_apply, ← Units.val_mul, inv_mul_cancel]
    rfl
  change (g⁻¹ * planeUnipotent s t * g).val 1 0 = 0 ∧
    (g⁻¹ * planeUnipotent s t * g).val 2 0 = 0
  exact ⟨by rw [key]; rfl, by rw [key]; rfl⟩

/-- **The radical of the identity plane fixes every complete flag over it.** -/
theorem badPlane_radical_fixes (radical : RadicalLattice) (e : Edges)
    (he : endpoint .plane e = badPlaneFlag) :
    (badPlaneSemidirectEquiv (SemidirectProduct.inl radical)).val • e = e := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective e
  have hg : g ∈ planeParabolic ℚ := by
    have h := QuotientGroup.eq.mp he
    have h' : g⁻¹ ∈ parabolic .plane := by simpa using h
    have h'' : g ∈ parabolic .plane := by simpa using (parabolic .plane).inv_mem h'
    exact h''
  rw [badPlaneSemidirectEquiv_inl]
  change (QuotientGroup.mk (planeUnipotent (radical.toAdd.1 : ℚ) (radical.toAdd.2 : ℚ) * g) :
    Edges) = QuotientGroup.mk g
  apply QuotientGroup.eq.mpr
  have key := planeUnipotent_conj_mem_borel g hg (-(radical.toAdd.1 : ℚ)) (-(radical.toAdd.2 : ℚ))
  have hinv : (planeUnipotent (radical.toAdd.1 : ℚ) (radical.toAdd.2 : ℚ) * g)⁻¹ * g =
      g⁻¹ * planeUnipotent (-(radical.toAdd.1 : ℚ)) (-(radical.toAdd.2 : ℚ)) * g := by
    rw [_root_.mul_inv_rev, planeUnipotent_inv, mul_assoc]
  rw [hinv]
  exact key

/-- The Levi `GL₂(ℤ)` of the identity plane embeds in `GL₂(ℤ) × ℤˣ`. -/
def badPlaneLeviEmbedding : GeneralLinearGroup (Fin 2) ℤ →* GeneralLinearGroup (Fin 2) ℤ × ℤˣ :=
  (MonoidHom.id _).prod 1

theorem badPlaneLeviEmbedding_injective : Function.Injective badPlaneLeviEmbedding :=
  fun _ _ h => congrArg Prod.fst h

/-- **Identity plane: locally inner iff mixed cuspidal**, for every degree. -/
theorem badPlane_locallyInner_iff (degree : ℕ) (character : RankOneCharacter)
    (coordinate : H2 (fixedPointLevel rationalLevel badPlaneFlag)
      (rationalCoefficientComponent degree character)) :
    coordinate ∈ locallyInnerClasses degree character .plane badPlaneFlag ↔
      ∃ radicalZero : faceH2Equiv identityPlaneSplitting.conjAct degree character badPlaneFlag
          badPlaneSemidirectEquiv coordinate ∈
          (radicalRestrictionH2 identityPlaneSplitting.conjAct (faceRep identityPlaneSplitting.conjAct
            degree character badPlaneFlag badPlaneSemidirectEquiv)).ker,
        ∀ e : Edges, endpoint .plane e = badPlaneFlag →
          crossedPullbackH1 (faceCusp identityPlaneSplitting.conjAct badPlaneFlag
              badPlaneSemidirectEquiv e).subtype
            (leviCrossedH1Representation identityPlaneSplitting.conjAct
              (faceRep identityPlaneSplitting.conjAct degree character badPlaneFlag
                badPlaneSemidirectEquiv))
            (radicalKernelMixedMap identityPlaneSplitting.conjAct
              (faceRep identityPlaneSplitting.conjAct degree character badPlaneFlag
                badPlaneSemidirectEquiv)
              ⟨faceH2Equiv identityPlaneSplitting.conjAct degree character badPlaneFlag
                badPlaneSemidirectEquiv coordinate, radicalZero⟩) = 0 :=
  face_locallyInner_iff_uniform identityPlaneSplitting.conjAct degree character badPlaneFlag
    badPlaneSemidirectEquiv (fun radical e he => badPlane_radical_fixes radical e he)
    badPlaneLeviEmbedding badPlaneLeviEmbedding_injective coordinate

end TernaryPeriodPolynomials.Argument.FacePairingFull.Face
