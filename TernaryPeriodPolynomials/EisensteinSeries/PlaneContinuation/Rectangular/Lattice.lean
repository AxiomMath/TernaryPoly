module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Singular.Cuspidality

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RationalDiscreteness

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularLattice

noncomputable def rationalMap : Rectangular ℚ →+ Rectangular Adeles where
  toFun matrix := matrix.map rationalAdele
  map_zero' := by
    apply Matrix.ext
    intro row column
    exact map_zero rationalAdele
  map_add' first second := by
    apply Matrix.ext
    intro row column
    exact map_add rationalAdele _ _

noncomputable def lattice : AddSubgroup (Rectangular Adeles) := rationalMap.range

def window : Set (Rectangular Adeles) := {matrix | ∀ row column, matrix row column ∈ smallAdeles}

theorem window_open : IsOpen window := by
  have equality : window = ⋂ row : Fin 3, ⋂ column : Fin 2,
      {matrix : Rectangular Adeles | matrix row column ∈ smallAdeles} := by
    ext matrix
    simp [window]
  rw [equality]
  exact isOpen_iInter_of_finite (fun row => isOpen_iInter_of_finite (fun column =>
    smallAdeles_open.preimage ((continuous_apply column).comp (continuous_apply row))))

theorem rational_in_window (matrix : Rectangular ℚ) : rationalMap matrix ∈ window ↔ matrix = 0 := by
  constructor
  · intro membership
    ext row column
    exact (rational_mem_smallAdeles (matrix row column)).mp (membership row column)
  · rintro rfl
    rw [map_zero]
    intro row column
    exact zero_mem_smallAdeles

theorem lattice_window : (Subtype.val : lattice → Rectangular Adeles) ⁻¹' window = {0} := by
  ext point
  constructor
  · intro membership
    obtain ⟨matrix, equality⟩ := point.property
    have zeroMatrix : matrix = 0 := (rational_in_window matrix).mp (equality ▸ membership)
    apply Set.mem_singleton_iff.mpr
    apply Subtype.ext
    rw [← equality, zeroMatrix, map_zero]
    rfl
  · rintro rfl
    change (0 : Rectangular Adeles) ∈ window
    simpa only [map_zero] using (rational_in_window 0).mpr rfl

instance latticeDiscrete : DiscreteTopology lattice :=
  discreteTopology_iff_isOpen_singleton_zero.mpr
    (lattice_window ▸ window_open.preimage continuous_subtype_val)

theorem lattice_closed : IsClosed (lattice : Set (Rectangular Adeles)) :=
  AddSubgroup.isClosed_of_discreteTopology

theorem rationalMap_injective : Function.Injective rationalMap := by
  intro first second equality
  ext row column
  exact rationalAdele.injective (congrArg (fun matrix : Rectangular Adeles => matrix row column) equality)

theorem finite_in_compact (compact : Set (Rectangular Adeles)) (compactIs : IsCompact compact) :
    {matrix : Rectangular ℚ | rationalMap matrix ∈ compact}.Finite := by
  have closedEmbedding : Topology.IsClosedEmbedding (Subtype.val : lattice → Rectangular Adeles) :=
    lattice_closed.isClosedEmbedding_subtypeVal
  have finite := (closedEmbedding.isCompact_preimage compactIs).finite_of_discrete
  let intoLattice : Rectangular ℚ → lattice := fun matrix => ⟨rationalMap matrix, ⟨matrix, rfl⟩⟩
  have injective : Function.Injective intoLattice := by
    intro first second equality
    exact rationalMap_injective (congrArg Subtype.val equality)
  have liftedFinite : (intoLattice ⁻¹' ((Subtype.val : lattice → Rectangular Adeles) ⁻¹' compact)).Finite :=
    finite.preimage injective.injOn
  exact liftedFinite

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularLattice
