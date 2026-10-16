module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.TransferOrthogonal
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Radical.PairDecomposition

@[expose] public section


/-!
# The canonical relative cocycle as a real good-line transfer integrand

The canonical binary relative cocycle of the real plane group is the pointwise canonical cochain
of the binary cocycle `B` attached to it, read pointwise in the adelic argument. Consequently the
canonical simplex value on real-plane points is the homogeneous pointwise canonical cochain of
`A ↦ B(A)`, and the canonical projected terms of the good-line simplices `(1, γ, r γ)`,
`(1, r, r γ)` and of the radical simplices `(1, r₁, r₁ r₂)` are transferred integrands of the
real good-line transfer, for the real stabilizer elements `γ ↦ (0, γ)` and
`(a, b) ↦ (3a, 3b)` of the integral Levi and the radical lattice.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ} {index : Type} [Fintype index]

/-! ### Integral stabilizer elements as real stabilizer elements -/

theorem abs_det_map_integral (γ : GeneralLinearGroup (Fin 2) ℤ) :
    |(GeneralLinearGroup.map (Int.castRingHom ℝ) γ : BinaryRealGL).val.det| = 1 := by
  have unit : IsUnit γ.val.det := (Matrix.isUnit_iff_isUnit_det _).mp γ.isUnit
  have image : (GeneralLinearGroup.map (Int.castRingHom ℝ) γ : BinaryRealGL).val.det =
      ((γ.val.det : ℤ) : ℝ) := by
    change ((Int.castRingHom ℝ).mapMatrix γ.val).det = _
    rw [← RingHom.map_det]
    rfl
  rw [image]
  rcases Int.isUnit_iff.mp unit with h | h <;> simp [h]

/-- The integral Levi element `γ` as an element of the real unimodular Levi. -/
def integralLevi (γ : GeneralLinearGroup (Fin 2) ℤ) : unimodularLevi :=
  ⟨GeneralLinearGroup.map (Int.castRingHom ℝ) γ, abs_det_map_integral γ⟩

/-- The real row vector of a radical lattice element: `(a, b) ↦ (3a, 3b)`. -/
def latticeVector (r : RadicalLattice) : Fin 2 → ℝ :=
  ![3 * (r.toAdd.1 : ℝ), 3 * (r.toAdd.2 : ℝ)]

theorem lineMatrix_integralLevi (γ : GeneralLinearGroup (Fin 2) ℤ) :
    lineMatrix (lineLeviElement (integralLevi γ)) = edgeLevi γ := by
  rw [lineMatrix_lineLeviElement]
  apply Units.ext
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [integralLevi, edgeLevi, arithmeticLevi, planeLevi, planeBlock,
      GeneralLinearGroup.map_apply]

theorem lineMatrix_latticeVector (r : RadicalLattice) :
    lineMatrix (lineRadicalElement (latticeVector r)) = edgeRadical r := by
  rw [lineMatrix_lineRadicalElement]
  apply Units.ext
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [lineRadicalMatrix, latticeVector, edgeRadical, lowerRadicalLattice,
      lowerPlaneUnipotent, GeneralLinearGroup.map_apply]

/-! ### The canonical simplex value -/

/-- The pointwise values `A ↦ B(A)` of the binary cocycle of the canonical relative cocycle. -/
def canonicalBinaryValues (data : InducingData n) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative) :
    BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1) :=
  fun A => (realPlaneLevelBinaryCocycle n data.cusp data.chi trivial basis relative regular A).val

theorem realPlaneCuspidalRep_val_of_trivial {cusp : CuspidalRepresentation}
    {character : RankOneCharacter} (trivial : character = trivialCharacter) (p : RealPlaneGroup)
    (values : cuspidalTensorValues cusp (HomogeneousPoly n)) :
    ((realPlaneCuspidalRep n cusp character).ρ p values).val =
      planeAmbientRepresentation n p values.val := by
  subst trivial
  rfl

theorem realCoefficientComponent_of_trivial {character : RankOneCharacter}
    (trivial : character = trivialCharacter) (g : RealGL3) :
    realCoefficientComponent n character g = realCoefficientComponent n trivialCharacter g := by
  rw [trivial]

/-- **The canonical relative cocycle is the pointwise canonical cochain of its binary cocycle.** -/
theorem canonicalRelative_val (data : InducingData n) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative)
    (p q : RealPlaneGroup) :
    ((realPlaneLevelBinaryRelativeCycle n data.cusp data.chi trivial basis relative regular).val
      (p, q)).val =
      pointCanonical (canonicalBinaryValues data trivial basis relative regular) p q := by
  funext h
  exact realPlaneLevelBinaryRelativeCycle_apply n data.cusp data.chi trivial basis relative regular
    p q h

/-- **The canonical simplex value is the homogeneous pointwise canonical cochain.** -/
theorem canonicalSimplexValue_val (data : InducingData n) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative)
    (Q : Fin 3 → RealPlaneGroup) (h : BinaryAdelicGL) :
    (canonicalSimplexValue data trivial basis relative regular Q).val h =
      planeHomogeneousCanonical (canonicalBinaryValues data trivial basis relative regular) Q
        h := by
  unfold canonicalSimplexValue planeHomogeneousCanonical
  refine (congrFun (realPlaneCuspidalRep_val_of_trivial trivial _ _) h).trans ?_
  rw [canonicalRelative_val]

/-! ### The canonical projected terms as transferred integrands -/

/-- The real stabilizer element of an integral Levi element. -/
abbrev leviPoint (γ : GeneralLinearGroup (Fin 2) ℤ) : LineGroup :=
  lineLeviElement (integralLevi γ)

/-- The real stabilizer element of a radical lattice element. -/
abbrev latticePoint (r : RadicalLattice) : LineGroup := lineRadicalElement (latticeVector r)

theorem lineMatrix_mixedFirst (γ : GeneralLinearGroup (Fin 2) ℤ) (r : RadicalLattice) (i : Fin 3) :
    lineMatrix (![1, leviPoint γ, latticePoint r * leviPoint γ] i) =
      ![1, edgeLevi γ, edgeRadical r * edgeLevi γ] i := by
  fin_cases i
  · exact map_one _
  · exact lineMatrix_integralLevi γ
  · change lineMatrix (latticePoint r * leviPoint γ) = edgeRadical r * edgeLevi γ
    rw [map_mul, lineMatrix_latticeVector, lineMatrix_integralLevi]

theorem lineMatrix_mixedSecond (γ : GeneralLinearGroup (Fin 2) ℤ) (r : RadicalLattice)
    (i : Fin 3) :
    lineMatrix (![1, latticePoint r, latticePoint r * leviPoint γ] i) =
      ![1, edgeRadical r, edgeRadical r * edgeLevi γ] i := by
  fin_cases i
  · exact map_one _
  · exact lineMatrix_latticeVector r
  · change lineMatrix (latticePoint r * leviPoint γ) = edgeRadical r * edgeLevi γ
    rw [map_mul, lineMatrix_latticeVector, lineMatrix_integralLevi]

theorem lineMatrix_radicalPair (r₁ r₂ : RadicalLattice) (i : Fin 3) :
    lineMatrix (![1, latticePoint r₁, latticePoint r₁ * latticePoint r₂] i) =
      ![1, edgeRadical r₁, edgeRadical r₁ * edgeRadical r₂] i := by
  fin_cases i
  · exact map_one _
  · exact lineMatrix_latticeVector r₁
  · change lineMatrix (latticePoint r₁ * latticePoint r₂) = edgeRadical r₁ * edgeRadical r₂
    rw [map_mul, lineMatrix_latticeVector, lineMatrix_latticeVector]

/-- **The canonical projected term is a difference of transferred integrands.** -/
theorem canonicalProjectedTerm_val (data : InducingData n) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative)
    (u : ℝ × ℝ) (γ : GeneralLinearGroup (Fin 2) ℤ) (r : RadicalLattice) (h : BinaryAdelicGL) :
    (canonicalProjectedTerm data trivial basis relative regular u γ r).val h =
      lineTransferIntegrand (canonicalBinaryValues data trivial basis relative regular)
          ![1, leviPoint γ, latticePoint r * leviPoint γ] u h -
        lineTransferIntegrand (canonicalBinaryValues data trivial basis relative regular)
          ![1, latticePoint r, latticePoint r * leviPoint γ] u h := by
  unfold canonicalProjectedTerm lineTransferIntegrand
  rw [cuspidalTensorMap_val_apply, realCoefficientComponent_of_trivial trivial]
  simp only [Submodule.coe_sub, Pi.sub_apply, map_sub, canonicalSimplexValue_val,
    lineMatrix_mixedFirst, lineMatrix_mixedSecond]

/-- The canonical projected term in relative form. -/
theorem canonicalProjectedTerm_val_relative (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative)
    (u : ℝ × ℝ) (γ : GeneralLinearGroup (Fin 2) ℤ) (r : RadicalLattice) (h : BinaryAdelicGL) :
    (canonicalProjectedTerm data trivial basis relative regular u γ r).val h =
      relativeIntegrand (canonicalBinaryValues data trivial basis relative regular) u
          (leviPoint γ) (latticePoint r * leviPoint γ) h -
        relativeIntegrand (canonicalBinaryValues data trivial basis relative regular) u
          (latticePoint r) (latticePoint r * leviPoint γ) h := by
  rw [canonicalProjectedTerm_val, lineTransferIntegrand_eq_relative,
    lineTransferIntegrand_eq_relative]

/-- **The canonical term of a radical simplex is a transferred integrand.** -/
theorem radicalCanonicalTerm_val (data : InducingData n) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative)
    (u : ℝ × ℝ) (r₁ r₂ : RadicalLattice) (h : BinaryAdelicGL) :
    (radicalCanonicalTerm data trivial basis relative regular u r₁ r₂).val h =
      lineTransferIntegrand (canonicalBinaryValues data trivial basis relative regular)
        ![1, latticePoint r₁, latticePoint r₁ * latticePoint r₂] u h := by
  unfold radicalCanonicalTerm lineTransferIntegrand
  rw [cuspidalTensorMap_val_apply, realCoefficientComponent_of_trivial trivial,
    canonicalSimplexValue_val]
  simp only [lineMatrix_radicalPair]

/-- The canonical term of a radical simplex in relative form. -/
theorem radicalCanonicalTerm_val_relative (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative)
    (u : ℝ × ℝ) (r₁ r₂ : RadicalLattice) (h : BinaryAdelicGL) :
    (radicalCanonicalTerm data trivial basis relative regular u r₁ r₂).val h =
      relativeIntegrand (canonicalBinaryValues data trivial basis relative regular) u
        (latticePoint r₁) (latticePoint r₁ * latticePoint r₂) h := by
  rw [radicalCanonicalTerm_val, lineTransferIntegrand_eq_relative]

end TernaryPeriodPolynomials.AnalyticClasses
