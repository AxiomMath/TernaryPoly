module

public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.BridgePart1
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.DifferentiablePotential
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.TangentCohomology

@[expose] public section


/-!
# Level-three port of the spherical holomorphic-detection chain, Part2

Mechanical port to the level-three group `{k ∈ GL₂(ℤ̂) : k₁₀ ≡ 0, k₁₁ ≡ 1 (mod 3)}` of
`SphericalDetection.BinaryDifferentiablePotential`, `SphericalDetection.BinaryTangentCohomology`.
`SphericalCusp` is replaced by `LevelThreeCusp`, `cuspSphericalValues` by `levelThreeValues`,
`cuspSphericalProjection` by `levelThreeProjection` and the level `GL₂(ℤ̂)` used for smoothness by
the principal congruence level of conductor three. Proofs are those of the original declarations
(source: the SphericalDetection development, AxiomProver); the port was generated and checked by AxiomCode (Claude Sonnet 5.5).
-/

noncomputable section

open TernaryPeriodPolynomials.SphericalDetection
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.MultiplicityOne

section CloneBinaryDifferentiablePotential

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

open scoped Matrix.Norms.Elementwise

variable {degree : ℕ} {index : Type} [Fintype index]

def binaryUpperPotential (cusp : CuspidalRepresentation) (spherical : LevelThreeCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (point : ℂ) : index → cusp.H :=
  (cycle (invertibleMatrix (binaryUpperSectionMatrix point)) : binaryHilbertFiniteValues cusp
    level).val

theorem binaryUpperPotential_coe (cusp : CuspidalRepresentation) (spherical : LevelThreeCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (point : UpperHalfPlane) :
    binaryUpperPotential cusp spherical basis level cycle point =
      (binarySymmetricPotential (binaryHilbertFiniteRep cusp spherical basis level) cycle point :
        binaryHilbertFiniteValues cusp level).val := by
  simp only [binaryUpperPotential, binaryUpperSectionMatrix_coe, invertibleMatrix_coe,
    binarySymmetricPotential]

theorem binaryUpperPotential_contDiffOn (cusp : CuspidalRepresentation) (spherical : LevelThreeCusp
    cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    {order : WithTop ℕ∞}
    (regular : ContDiffOn ℝ order (fun matrix : BinaryRealMatrix =>
      (cycle (invertibleMatrix matrix) : binaryHilbertFiniteValues cusp level).val)
      {matrix | matrix.det ≠ 0}) :
    ContDiffOn ℝ order (binaryUpperPotential cusp spherical basis level cycle)
      UpperHalfPlane.upperHalfPlaneSet :=
  regular.comp binaryUpperSectionMatrix_contDiffOn binaryUpperSectionMatrix_invertible

theorem binaryUpperPotential_affine (cusp : CuspidalRepresentation) (spherical : LevelThreeCusp
    cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (stabilizer_zero : ∀ matrix : BinaryRealGL,
      matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0)
    (point argument : UpperHalfPlane) :
    binaryUpperPotential cusp spherical basis level cycle
      ((point.re : ℂ) + (point.im : ℂ) * (argument : ℂ)) =
      (cycle (binarySymmetricSection point) : binaryHilbertFiniteValues cusp level).val +
        binaryHilbertOperator cusp basis (binarySymmetricSection point)
          (binaryUpperPotential cusp spherical basis level cycle argument) := by
  rw [← binarySymmetricSection_coe_smul point argument, binaryUpperPotential_coe,
    binaryUpperPotential_coe]
  exact congrArg Subtype.val (binarySymmetricPotential_affine _ cycle stabilizer_zero
    (binarySymmetricSection point) argument)

theorem binaryUpperPotential_exists_fderiv_ne_zero (cusp : CuspidalRepresentation)
    (spherical : LevelThreeCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (nonzero : groupCohomology.H1π (binaryHilbertFiniteRep cusp spherical basis level) cycle ≠ 0)
    (regular : DifferentiableOn ℝ (binaryUpperPotential cusp spherical basis level cycle)
      UpperHalfPlane.upperHalfPlaneSet)
    (stabilizer_zero : ∀ matrix : BinaryRealGL,
      matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0) :
    ∃ point : UpperHalfPlane,
      fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) (point : ℂ) ≠ 0 := by
  by_contra no_derivative
  have zero_derivative : Set.EqOn
      (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle)) 0
      UpperHalfPlane.upperHalfPlaneSet := by
    intro point member
    exact not_ne_iff.mp (fun nonzero => no_derivative ⟨⟨point, member⟩, nonzero⟩)
  have convex : Convex ℝ UpperHalfPlane.upperHalfPlaneSet :=
    (convex_Ioi (0 : ℝ)).linear_preimage Complex.imLm
  have constant {x y : ℂ} (x_mem : x ∈ UpperHalfPlane.upperHalfPlaneSet)
      (y_mem : y ∈ UpperHalfPlane.upperHalfPlaneSet) :
      binaryUpperPotential cusp spherical basis level cycle x =
        binaryUpperPotential cusp spherical basis level cycle y :=
    UpperHalfPlane.isOpen_upperHalfPlaneSet.is_const_of_fderiv_eq_zero
      convex.isPreconnected regular zero_derivative x_mem y_mem
  have basepoint : binaryUpperPotential cusp spherical basis level cycle (UpperHalfPlane.I : ℂ) = 0
    := by
    rw [binaryUpperPotential_coe, binarySymmetricPotential_basepoint _ cycle stabilizer_zero]
    rfl
  have cycle_zero : cycle = 0 := by
    apply groupCohomology.cocycles₁_ext
    intro matrix
    apply Subtype.ext
    have equal := constant (x := ((matrix • UpperHalfPlane.I : UpperHalfPlane) : ℂ))
      (y := (UpperHalfPlane.I : ℂ)) (matrix • UpperHalfPlane.I).im_pos UpperHalfPlane.I.im_pos
    rw [binaryUpperPotential_coe, binarySymmetricPotential_descent _ cycle stabilizer_zero,
      basepoint] at equal
    exact equal
  exact nonzero (by rw [cycle_zero, map_zero])

theorem binaryUpperPotential_fderiv_basepoint_ne_zero (cusp : CuspidalRepresentation)
    (spherical : LevelThreeCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (nonzero : groupCohomology.H1π (binaryHilbertFiniteRep cusp spherical basis level) cycle ≠ 0)
    (regular : DifferentiableOn ℝ (binaryUpperPotential cusp spherical basis level cycle)
      UpperHalfPlane.upperHalfPlaneSet)
    (stabilizer_zero : ∀ matrix : BinaryRealGL,
      matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0) :
    fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I ≠ 0 := by
  intro base_zero
  obtain ⟨point, derivative_nonzero⟩ := binaryUpperPotential_exists_fderiv_ne_zero
    cusp spherical basis level cycle nonzero regular stabilizer_zero
  let potential := binaryUpperPotential cusp spherical basis level cycle
  let affine : ℂ → ℂ := fun argument => (point.re : ℂ) + point.im • argument
  have affine_base : affine Complex.I = (point : ℂ) := by
    apply Complex.ext <;> simp [affine]
  have affine_derivative : HasFDerivAt affine (point.im • ContinuousLinearMap.id ℝ ℂ) Complex.I :=
    ((hasFDerivAt_id (𝕜 := ℝ) Complex.I).const_smul point.im).const_add (point.re : ℂ)
  have point_derivative : HasFDerivAt potential (fderiv ℝ potential (point : ℂ)) (point : ℂ) :=
    (regular.differentiableAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds
      point.im_pos)).hasFDerivAt
  have base_derivative : HasFDerivAt (𝕜 := ℝ) potential 0 Complex.I := by
    have differentiable := regular.differentiableAt
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds (show Complex.I ∈
        UpperHalfPlane.upperHalfPlaneSet by simp))
    simpa only [potential, base_zero] using differentiable.hasFDerivAt
  have at_affine : HasFDerivAt potential (fderiv ℝ potential (point : ℂ)) (affine Complex.I) :=
    affine_base.symm ▸ point_derivative
  have left_derivative := at_affine.comp Complex.I affine_derivative
  let action := (binaryHilbertOperator cusp basis (binarySymmetricSection point)).restrictScalars ℝ
  have right_derivative : HasFDerivAt (𝕜 := ℝ)
      (fun argument => (cycle (binarySymmetricSection point) : binaryHilbertFiniteValues cusp
        level).val +
        action (potential argument)) 0 Complex.I := by
    have derivative := (action.hasFDerivAt.comp Complex.I base_derivative).const_add
      (cycle (binarySymmetricSection point) : binaryHilbertFiniteValues cusp level).val
    rw [ContinuousLinearMap.comp_zero] at derivative
    exact derivative
  have equality : potential ∘ affine =ᶠ[nhds Complex.I]
      (fun argument => (cycle (binarySymmetricSection point) : binaryHilbertFiniteValues cusp
        level).val +
        action (potential argument)) := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds
      (show Complex.I ∈ UpperHalfPlane.upperHalfPlaneSet by simp)] with argument member
    exact binaryUpperPotential_affine cusp spherical basis level cycle stabilizer_zero point
      ⟨argument, member⟩
  have derivative_zero := left_derivative.unique (right_derivative.congr_of_eventuallyEq equality)
  apply derivative_nonzero
  apply ContinuousLinearMap.ext
  intro direction
  have scaled := congrArg (fun derivative : ℂ →L[ℝ] (index → cusp.H) => derivative direction)
    derivative_zero
  change fderiv ℝ potential (point : ℂ) (point.im • direction) = 0 at scaled
  rw [map_smul] at scaled
  exact (smul_eq_zero.mp scaled).resolve_left (ne_of_gt point.im_pos)

theorem cohomological_exists_symmetric_basepoint_differential (cusp : CuspidalRepresentation)
    (spherical : LevelThreeCusp cusp) (cohomological : Cohomological cusp degree)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1))) :
    ∃ (level : Subgroup BinaryFiniteGL)
      (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level)),
      IsOpen (level : Set BinaryFiniteGL) ∧ IsCompact (level : Set BinaryFiniteGL) ∧
      groupCohomology.H1π (binaryHilbertFiniteRep cusp spherical basis level) cycle ≠ 0 ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) (binaryUpperPotential cusp spherical basis level cycle)
        UpperHalfPlane.upperHalfPlaneSet ∧
      (∀ matrix : BinaryRealGL, matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0) ∧
      fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I ≠ 0 := by
  obtain ⟨level, cycle, level_open, level_compact, nonzero, regular, stabilizer_zero⟩ :=
    cohomological_exists_smooth_symmetricSpace_H1 cusp spherical cohomological basis
  have potential_regular := binaryUpperPotential_contDiffOn cusp spherical basis level cycle regular
  exact ⟨level, cycle, level_open, level_compact, nonzero, potential_regular, stabilizer_zero,
    binaryUpperPotential_fderiv_basepoint_ne_zero cusp spherical basis level cycle nonzero
      (potential_regular.differentiableOn (by simp)) stabilizer_zero⟩

end CloneBinaryDifferentiablePotential

section CloneBinaryTangentCohomology

open GeneralEisenstein GeneralEisenstein.Adelic

variable {degree : ℕ} {index : Type} [Fintype index]

theorem binaryUpperPotential_fderiv_equivariant (cusp : CuspidalRepresentation)
    (spherical : LevelThreeCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (regular : DifferentiableOn ℝ (binaryUpperPotential cusp spherical basis level cycle)
      UpperHalfPlane.upperHalfPlaneSet)
    (stabilizer_zero : ∀ matrix : BinaryRealGL,
      matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0)
    (matrix : BinaryRealGL) (point : UpperHalfPlane) :
    (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) ((matrix • point :
      UpperHalfPlane) : ℂ)).comp
        (UpperHalfPlane.smulFDeriv matrix point) =
      ((binaryHilbertOperator cusp basis matrix).restrictScalars ℝ).comp
        (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) (point : ℂ)) := by
  let potential := binaryUpperPotential cusp spherical basis level cycle
  let action := (binaryHilbertOperator cusp basis matrix).restrictScalars ℝ
  let orbit : ℂ → ℂ := fun argument => (matrix • UpperHalfPlane.ofComplex argument : UpperHalfPlane)
  have orbit_value : orbit point = ((matrix • point : UpperHalfPlane) : ℂ) := by
    simp only [orbit, UpperHalfPlane.ofComplex_apply]
  have orbit_derivative : HasFDerivAt orbit (UpperHalfPlane.smulFDeriv matrix point) (point : ℂ) :=
    (UpperHalfPlane.hasStrictFDerivAt_smul matrix point).hasFDerivAt
  have target_derivative := (regular.differentiableAt
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds (matrix • point).im_pos)).hasFDerivAt
  have at_orbit : HasFDerivAt potential
      (fderiv ℝ potential ((matrix • point : UpperHalfPlane) : ℂ)) (orbit point) :=
    orbit_value.symm ▸ target_derivative
  have left_derivative := at_orbit.comp (point : ℂ) orbit_derivative
  have source_derivative := (regular.differentiableAt
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds point.im_pos)).hasFDerivAt
  have right_derivative := (action.hasFDerivAt.comp (point : ℂ) source_derivative).const_add
    (cycle matrix : binaryHilbertFiniteValues cusp level).val
  have equality : potential ∘ orbit =ᶠ[nhds (point : ℂ)]
      (fun argument => (cycle matrix : binaryHilbertFiniteValues cusp level).val + action
        (potential argument)) := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds point.im_pos] with argument
      member
    have realization := congrArg Subtype.val (binarySymmetricPotential_affine _ cycle
      stabilizer_zero
      matrix (⟨argument, member⟩ : UpperHalfPlane))
    change (binarySymmetricPotential (binaryHilbertFiniteRep cusp spherical basis level) cycle
      (matrix • (⟨argument, member⟩ : UpperHalfPlane)) : binaryHilbertFiniteValues cusp level).val =
        (cycle matrix : binaryHilbertFiniteValues cusp level).val +
          binaryHilbertOperator cusp basis matrix
            (binarySymmetricPotential (binaryHilbertFiniteRep cusp spherical basis level) cycle
              (⟨argument, member⟩ : UpperHalfPlane) : binaryHilbertFiniteValues cusp
                level).val at realization
    rw [← binaryUpperPotential_coe, ← binaryUpperPotential_coe] at realization
    change potential (orbit argument) =
      (cycle matrix : binaryHilbertFiniteValues cusp level).val + action (potential argument)
    dsimp only [orbit]
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos member]
    exact realization
  exact left_derivative.unique (right_derivative.congr_of_eventuallyEq equality)

theorem binaryUpperPotential_fderiv_rotation (cusp : CuspidalRepresentation)
    (spherical : LevelThreeCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (regular : DifferentiableOn ℝ (binaryUpperPotential cusp spherical basis level cycle)
      UpperHalfPlane.upperHalfPlaneSet)
    (stabilizer_zero : ∀ matrix : BinaryRealGL,
      matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0)
    (angle : Circle) (direction : ℂ) :
    binaryHilbertOperator cusp basis (binaryRotations angle)
      (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I direction) =
        fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I
          (((angle : ℂ) ^ 2)⁻¹ * direction) := by
  have equivariant := binaryUpperPotential_fderiv_equivariant cusp spherical basis level cycle
    regular
    stabilizer_zero (binaryRotations angle) UpperHalfPlane.I
  rw [binaryRotations_smul_I] at equivariant
  have evaluated := congrArg (fun derivative : ℂ →L[ℝ] (index → cusp.H) => derivative direction)
    equivariant
  change fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I
      (UpperHalfPlane.smulFDeriv (binaryRotations angle) Complex.I direction) =
    binaryHilbertOperator cusp basis (binaryRotations angle)
      (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I
        direction) at evaluated
  rw [binaryRotations_smulFDeriv] at evaluated
  exact evaluated.symm

def binaryHolomorphicTangent (cusp : CuspidalRepresentation) (spherical : LevelThreeCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level)) : index
      → cusp.H :=
  fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I 1 -
    Complex.I • fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I Complex.I

theorem binaryHolomorphicTangent_rotation (cusp : CuspidalRepresentation)
    (spherical : LevelThreeCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (regular : DifferentiableOn ℝ (binaryUpperPotential cusp spherical basis level cycle)
      UpperHalfPlane.upperHalfPlaneSet)
    (stabilizer_zero : ∀ matrix : BinaryRealGL,
      matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0)
    (angle : Circle) :
    binaryHilbertOperator cusp basis (binaryRotations angle)
      (binaryHolomorphicTangent cusp spherical basis level cycle) =
        ((angle : ℂ) ^ 2)⁻¹ • binaryHolomorphicTangent cusp spherical basis level cycle :=
  holomorphicTangent_eigenvector
    (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I).toLinearMap
    (binaryHilbertOperator cusp basis (binaryRotations angle)).toLinearMap _
    (binaryUpperPotential_fderiv_rotation cusp spherical basis level cycle regular stabilizer_zero
      angle)

theorem binaryUpperPotential_fderiv_finiteLevel (cusp : CuspidalRepresentation)
    (spherical : LevelThreeCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (regular : DifferentiableOn ℝ (binaryUpperPotential cusp spherical basis level cycle)
      UpperHalfPlane.upperHalfPlaneSet)
    (element : level) (direction : ℂ) (position : index) :
    cusp.π (atFinite element.val)
      (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I direction
        position) =
        fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I direction
          position := by
  let potential := binaryUpperPotential cusp spherical basis level cycle
  let action := (binaryHilbertTranslation (index := index) cusp (atFinite
    element.val)).restrictScalars ℝ
  have fixed (argument : ℂ) : action (potential argument) = potential argument := by
    funext coordinate
    exact (cycle (invertibleMatrix (binaryUpperSectionMatrix argument)) :
      binaryHilbertFiniteValues cusp level).property element coordinate
  have derivative := (regular.differentiableAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds
    (show Complex.I ∈ UpperHalfPlane.upperHalfPlaneSet by simp))).hasFDerivAt
  have composed := action.hasFDerivAt.comp Complex.I derivative
  have same := (composed.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun argument => (fixed
    argument).symm))).unique derivative
  have evaluated := congrArg (fun map : ℂ →L[ℝ] (index → cusp.H) => map direction position) same
  exact evaluated

end CloneBinaryTangentCohomology

end TernaryPeriodPolynomials.MultiplicityOne
