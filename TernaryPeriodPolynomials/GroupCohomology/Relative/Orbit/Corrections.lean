module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Orbit.Residues

@[expose] public section


noncomputable section
namespace TernaryPoly.RelativeOrbitCorrections
open ModThreeGoodAction RelativeOrbitCompletion RelativeOrbitResidues
open RelativeStabilizerCoordinates

/-- An integral sign representing each nonzero ternary residue. -/
def sign (a : ZMod 3) : ℤ := if a = 2 then -1 else 1

def lineMatrix (r : Row) : Matrix (Fin 3) (Fin 3) ℤ :=
  if r 1 = 0 then !![1,0,0;0,1,0;0,0,sign (r 2)] else
    !![1,0,0;0,OrdinaryCovectors.balanced (r 2),sign (r 1);0,-sign (r 1),0]
def lineInverse (r : Row) : Matrix (Fin 3) (Fin 3) ℤ :=
  if r 1 = 0 then !![1,0,0;0,1,0;0,0,sign (r 2)] else
    !![1,0,0;0,0,-sign (r 1);0,sign (r 1),OrdinaryCovectors.balanced (r 2)]

theorem lineMatrix_inverse : ∀ r : Row, lineMatrix r * lineInverse r = 1 ∧
    lineInverse r * lineMatrix r = 1 := by decide +kernel

def lineCorrection (r : Row) : IntegralGL :=
  ⟨lineMatrix r,lineInverse r,(lineMatrix_inverse r).1,(lineMatrix_inverse r).2⟩

def planeMatrix (r : Row) : Matrix (Fin 3) (Fin 3) ℤ := !![1,0,0;0,1,0;0,0,sign (r 2)]
theorem planeMatrix_inverse : ∀ r : Row, planeMatrix r * planeMatrix r = 1 := by decide +kernel
def planeCorrection (r : Row) : IntegralGL :=
  ⟨planeMatrix r,planeMatrix r,planeMatrix_inverse r,planeMatrix_inverse r⟩

def bgMatrix (r : Row) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1,0,0;0,1,0;0,-OrdinaryCovectors.balanced (r 1)*sign (r 2),sign (r 2)]
def bgInverse (r : Row) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1,0,0;0,1,0;0,OrdinaryCovectors.balanced (r 1),sign (r 2)]
theorem bgMatrix_inverse : ∀ r : Row, bgMatrix r * bgInverse r = 1 ∧
    bgInverse r * bgMatrix r = 1 := by decide +kernel
def bgCorrection (r : Row) : IntegralGL :=
  ⟨bgMatrix r,bgInverse r,(bgMatrix_inverse r).1,(bgMatrix_inverse r).2⟩

/-- A finite certificate on all ternary rows verifies the exact line-parabolic residue adjustment. -/
theorem line_row_correct : ∀ r : Row, r 0 = 0 → r ≠ 0 →
    Matrix.vecMul r ((lineMatrix r).map (Int.castRingHom (ZMod 3))) = ![0,0,1] := by decide +kernel

/-- Bad planes and bad-bad flags need only a diagonal integral sign correction. -/
theorem plane_row_correct : ∀ r : Row, r 0 = 0 → r 1 = 0 → r ≠ 0 →
    Matrix.vecMul r ((planeMatrix r).map (Int.castRingHom (ZMod 3))) = ![0,0,1] := by decide +kernel

/-- A finite certificate verifies the exact bad-Good flag-parabolic correction. -/
theorem bg_row_correct : ∀ r : Row, r 0 = 0 → r 2 ≠ 0 →
    Matrix.vecMul r ((bgMatrix r).map (Int.castRingHom (ZMod 3))) = ![0,0,1] := by decide +kernel

theorem line_stabilizes (r : Row) : Stabilizes (lineCorrection r) L0 := by
  rw [stabilizes_L0_iff]
  change (lineMatrix r) 1 0 = 0 ∧ (lineMatrix r) 2 0 = 0
  unfold lineMatrix
  split <;> exact ⟨rfl,rfl⟩

theorem plane_stabilizes_line (r : Row) : Stabilizes (planeCorrection r) L0 :=
  (stabilizes_L0_iff _).mpr ⟨rfl,rfl⟩
theorem plane_stabilizes_plane (r : Row) : Stabilizes (planeCorrection r) P0 :=
  (stabilizes_P0_iff _).mpr ⟨rfl,rfl⟩
theorem bg_stabilizes_line (r : Row) : Stabilizes (bgCorrection r) L0 :=
  (stabilizes_L0_iff _).mpr ⟨rfl,rfl⟩
theorem bg_stabilizes_plane (r : Row) : Stabilizes (bgCorrection r) P1 :=
  (stabilizes_P1_iff _).mpr ⟨rfl,rfl⟩

/-- Exchange the final two coordinates, preserving the first coordinate line. -/
def swap12 : IntegralGL := ⟨!![1,0,0;0,0,1;0,1,0],!![1,0,0;0,0,1;0,1,0],
  by decide +kernel,by decide +kernel⟩
theorem swap12_line : mapSpace swap12 L0 = L0 :=
  (stabilizes_L0_iff _).mpr ⟨rfl,rfl⟩
theorem swap12_plane : mapSpace swap12 P1 = P0 := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro v ⟨x,hx,rfl⟩
    apply (mem_P0 _).mpr
    change rationalRepresentation swap12 x 2 = 0
    rw [rationalRepresentation_apply]
    simpa [swap12,Matrix.mulVec,dotProduct,Fin.sum_univ_three,Matrix.GeneralLinearGroup.map_apply]
      using (mem_P1 x).mp hx
  · rw [mapSpace_finrank,finrank_P1,finrank_P0]

theorem flag_completion_P1 (L P : RationalSubspace) (hL : Module.finrank ℚ L = 1)
    (hP : Module.finrank ℚ P = 2) (hle : L ≤ P) :
    ∃ g : IntegralGL, mapSpace g L0 = L ∧ mapSpace g P1 = P := by
  obtain ⟨g,hgL,hgP⟩ := flag_completion L P hL hP hle
  exact ⟨g*swap12,by rw [mapSpace_mul,swap12_line,hgL],by rw [mapSpace_mul,swap12_plane,hgP]⟩

end TernaryPoly.RelativeOrbitCorrections
