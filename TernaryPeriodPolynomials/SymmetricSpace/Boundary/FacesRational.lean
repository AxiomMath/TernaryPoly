module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Full.Action
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Stabilizer.Coordinates
public import TernaryPeriodPolynomials.SymmetricSpace.Rational.GluingAction

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFaces
open Matrix OrdinaryIncidence OrdinaryFullAction RelativeStabilizerCoordinates
open SymmetricSpaceRationalAction SymmetricSpaceRationalGluing SymmetricSpaceBorelCorner
open SymmetricSpaceLineBordification

/-- The actual coordinate line in the existing rational incidence model. -/
def standardLine : Line := ⟨L0,finrank_L0,trivial⟩
/-- The actual coordinate plane in the existing rational incidence model. -/
def standardPlane : Plane := ⟨P0,finrank_P0,⟨standardLine,L0_le_P0⟩⟩

theorem standard_incident : incidence standardLine standardPlane :=
  GoodIncidenceConnected.line_lt_plane (fun _ => True) L0_le_P0

/-- The chart label is the frame's direct action on Q e₀, matching transition h⁻¹g. -/
def lineLabel (g : RationalGL) : Line := OrdinaryFullAction.lineAction g standardLine
/-- The chart plane label is the frame's direct action on Q e₀+Q e₁. -/
def planeLabel (g : RationalGL) : Plane := OrdinaryFullAction.planeAction g standardPlane

theorem rational_vector_apply (g : RationalGL) (v : ModThreeGoodAction.Space) :
    vectorAction g v=g.val.mulVec v := by
  change (GeneralLinearGroup.toLin g).toLinearEquiv v=_
  rw [LinearMap.GeneralLinearGroup.coe_toLinearEquiv,GeneralLinearGroup.toLin_apply]
  rfl

/-- Rational-coordinate version of the existing integral coordinate-stabilizer criterion. -/
theorem rational_coordinate_stabilizer (g : RationalGL) (s : Finset (Fin 3)) :
    subspaceAction g (coordinateSubspace s)=coordinateSubspace s ↔
      ∀ i,i∉s → ∀ j∈s,g.val i j=0 := by
  have heq : subspaceAction g (coordinateSubspace s)=coordinateSubspace s ↔
      subspaceAction g (coordinateSubspace s)≤coordinateSubspace s :=
    ⟨fun h => h.le,fun h => Submodule.eq_of_le_of_finrank_eq h
      (subspaceAction_finrank g (coordinateSubspace s))⟩
  rw [heq]
  constructor
  · intro h i hi j hj
    have hv : (Pi.single j (1 : ℚ) : ModThreeGoodAction.Space)∈coordinateSubspace s := by
      intro k hk
      have hkj : k≠j := by intro hh; subst k; exact hk hj
      simp [hkj]
    have hm := h (Submodule.mem_map_of_mem (f := (vectorAction g).toLinearMap) hv)
    have hz := hm i hi
    change vectorAction g (Pi.single j 1) i=0 at hz
    rw [rational_vector_apply,Matrix.mulVec_single_one] at hz
    exact hz
  · intro h v hv
    obtain ⟨w,hw,rfl⟩ := hv
    intro i hi
    rw [LinearEquiv.coe_coe,rational_vector_apply]
    change (∑ j : Fin 3,g.val i j*w j)=0
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j∈s
    · simp [h i hi j hj]
    · simp [hw j hj]

theorem rational_line_stabilizer (g : RationalGL) :
    subspaceAction g L0=L0 ↔ g.val 1 0=0 ∧ g.val 2 0=0 := by
  rw [L0,rational_coordinate_stabilizer]
  simp only [Finset.mem_singleton]
  constructor
  · intro h; exact ⟨h 1 (by decide) 0 rfl,h 2 (by decide) 0 rfl⟩
  · rintro ⟨h1,h2⟩ i hi j rfl
    fin_cases i <;> simp_all

theorem rational_plane_stabilizer (g : RationalGL) :
    subspaceAction g P0=P0 ↔ g.val 2 0=0 ∧ g.val 2 1=0 := by
  rw [P0,rational_coordinate_stabilizer]
  constructor
  · intro h; exact ⟨h 2 (by decide) 0 (by decide),h 2 (by decide) 1 (by decide)⟩
  · rintro ⟨h0,h1⟩ i hi j hj
    fin_cases i <;> fin_cases j <;> simp_all

theorem subspace_frame_eq_iff (g h : RationalGL) (L : ModThreeGoodAction.RationalSubspace) :
    subspaceAction g L=subspaceAction h L ↔ subspaceAction (h⁻¹*g) L=L := by
  constructor
  · intro he
    rw [subspaceAction_mul,he,←subspaceAction_mul,inv_mul_cancel,subspaceAction_one]
  · intro he
    have hh := congrArg (subspaceAction h) he
    rw [←subspaceAction_mul,mul_inv_cancel_left] at hh
    exact hh

/-- The direct frame convention is forced by the actual real transition matrix h⁻¹g. -/
theorem lineLabel_eq_iff (g h : RationalGL) :
    lineLabel g=lineLabel h ↔ changeMatrix g h∈lineStabilizer := by
  rw [Subtype.ext_iff]
  change subspaceAction g L0=subspaceAction h L0 ↔ _
  rw [subspace_frame_eq_iff,rational_line_stabilizer,mem_lineStabilizer_iff]
  change _ ↔ ((h⁻¹*g).val 1 0 : ℝ)=0 ∧ ((h⁻¹*g).val 2 0 : ℝ)=0
  norm_cast

theorem planeLabel_eq_iff (g h : RationalGL) :
    planeLabel g=planeLabel h ↔ changeMatrix g h∈planeStabilizer := by
  rw [Subtype.ext_iff]
  change subspaceAction g P0=subspaceAction h P0 ↔ _
  rw [subspace_frame_eq_iff,rational_plane_stabilizer,mem_planeStabilizer_iff]
  change _ ↔ ((h⁻¹*g).val 2 0 : ℝ)=0 ∧ ((h⁻¹*g).val 2 1 : ℝ)=0
  norm_cast

theorem lineAction_mul (a g : RationalGL) (L : Line) :
    OrdinaryFullAction.lineAction (a*g) L=
      OrdinaryFullAction.lineAction a (OrdinaryFullAction.lineAction g L) :=
  Subtype.ext (subspaceAction_mul a g L.val)

theorem planeAction_mul (a g : RationalGL) (P : Plane) :
    OrdinaryFullAction.planeAction (a*g) P=
      OrdinaryFullAction.planeAction a (OrdinaryFullAction.planeAction g P) :=
  Subtype.ext (subspaceAction_mul a g P.val)

@[simp] theorem lineLabel_one : lineLabel 1=standardLine := Subtype.ext (subspaceAction_one L0)
@[simp] theorem planeLabel_one : planeLabel 1=standardPlane := Subtype.ext (subspaceAction_one P0)

theorem labels_incident (g : RationalGL) : incidence (lineLabel g) (planeLabel g) :=
  (OrdinaryFullAction.incidence_action_iff g standardLine standardPlane).mpr standard_incident

end TernaryPoly.SymmetricSpaceBoundaryFaces
