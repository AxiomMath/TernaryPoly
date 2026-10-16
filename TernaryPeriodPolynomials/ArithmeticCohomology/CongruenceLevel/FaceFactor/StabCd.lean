module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Gamma6.Faces
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Farey.Cd

@[expose] public section


/-!
# The stabilizers of the lines and planes of `Γ(6)` have cohomological dimension `≤ 3`

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPoly.OrdinaryIncidence (Line Plane)

/-- The line group `gammaNQAt 6 h` is isomorphic to the stabilizer in `Γ(6)` of the line `lineOf h`. -/
def lineStabEquiv (h : SL(3, ℤ)) : ↥(gammaNQAt 6 h) ≃* ↥(MulAction.stabilizer Γ6 (lineOf h)) :=
  MulEquiv.ofBijective ((lineEmb h).codRestrict _ (fun p => by
      rw [← lineEmb_range]; exact ⟨p, rfl⟩))
    ⟨fun a b hab => lineEmb_injective h (congrArg Subtype.val hab), fun x => by
      have hx : (x : Γ6) ∈ (lineEmb h).range := by rw [lineEmb_range]; exact x.2
      obtain ⟨p, hp⟩ := hx
      exact ⟨p, Subtype.ext hp⟩⟩

/-- … and the plane group `gammaNPAt 6 h` to the stabilizer of the plane `planeOf h`. -/
def planeStabEquiv (h : SL(3, ℤ)) : ↥(gammaNPAt 6 h) ≃* ↥(MulAction.stabilizer Γ6 (planeOf h)) :=
  MulEquiv.ofBijective ((planeEmb h).codRestrict _ (fun p => by
      rw [← planeEmb_range]; exact ⟨p, rfl⟩))
    ⟨fun a b hab => planeEmb_injective h (congrArg Subtype.val hab), fun x => by
      have hx : (x : Γ6) ∈ (planeEmb h).range := by rw [planeEmb_range]; exact x.2
      obtain ⟨p, hp⟩ := hx
      exact ⟨p, Subtype.ext hp⟩⟩

variable {k : Type} [CommRing k] [Algebra ℚ k] [Invertible (2 : k)]

/-- **The stabilizer of every line of `Γ(6)` has cohomological dimension `≤ 3`.** -/
theorem cdLe_three_stab_line (ℓ : Line) : CdLe k ↥(MulAction.stabilizer Γ6 ℓ) 3 := by
  obtain ⟨h, rfl⟩ := exists_lineOf ℓ
  exact CdLe.of_mulEquiv (lineStabEquiv h) (cdLe_three_of_ext (k := k) (by norm_num : 3 ≤ 6) (lineFaceExt 6 h))

/-- **The stabilizer of every plane of `Γ(6)` has cohomological dimension `≤ 3`.** -/
theorem cdLe_three_stab_plane (P : Plane) : CdLe k ↥(MulAction.stabilizer Γ6 P) 3 := by
  obtain ⟨h, rfl⟩ := exists_planeOf P
  exact CdLe.of_mulEquiv (planeStabEquiv h) (cdLe_three_of_ext (k := k) (by norm_num : 3 ≤ 6) (faceExt 6 h))

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
