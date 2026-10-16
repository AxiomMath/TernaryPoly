module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.EdgeStabilizerPrimitives
public import TernaryPeriodPolynomials.Building.BoundaryApartments.Good.Apartments

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous Matrix

def lastColumnSign (sign : ℤˣ) : IntegralGL3 :=
  ⟨!![1,0,0;0,1,0;0,0,(sign : ℤ)], !![1,0,0;0,1,0;0,0,(sign⁻¹ : ℤˣ)], by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem lastColumnSign_parabolic (sign : ℤˣ) :
    GeneralLinearGroup.map (Int.castRingHom ℚ) (lastColumnSign sign) ∈
      parabolic .plane ⊓ parabolic .line := by
  exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

theorem secondColumn_plane_good (frame : IntegralGL3)
    (column_good : (frame.val 2 1 : ZMod 3) ≠ 0) :
    GoodFlag .plane (QuotientGroup.mk (GeneralLinearGroup.map (Int.castRingHom ℚ) frame)) := by
  refine ⟨fun index => frame.val index 1, ?_, column_good⟩
  refine ⟨GeneralLinearGroup.map (Int.castRingHom ℚ) frame, rfl, Pi.single 1 1, rfl, ?_⟩
  ext index
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem nonzero_modThree_sign (residue : ZMod 3) (nonzero : residue ≠ 0) :
    ∃ sign : ℤˣ, residue * ((sign : ℤ) : ZMod 3) = 1 := by
  have alternatives : residue = 0 ∨ residue = 1 ∨ residue = -1 := by
    exact (by decide : ∀ value : ZMod 3, value = 0 ∨ value = 1 ∨ value = -1) residue
  rcases alternatives with zero | positive | negative
  · exact (nonzero zero).elim
  · exact ⟨1, by simp [positive]⟩
  · exact ⟨-1, by simp [negative]⟩

theorem bad_integral_edge_in_standard_orbit (frame : IntegralGL3)
    (plane_bad : ¬GoodFlag .plane
      (QuotientGroup.mk (GeneralLinearGroup.map (Int.castRingHom ℚ) frame))) :
    ∃ matrix : rationalLevel, matrix.val • standardBadEdge =
      (QuotientGroup.mk (GeneralLinearGroup.map (Int.castRingHom ℚ) frame) : Edges) := by
  have first_zero : (frame.val 2 0 : ZMod 3) = 0 := by
    by_contra nonzero
    exact plane_bad (firstColumn_good frame nonzero .plane)
  have second_zero : (frame.val 2 1 : ZMod 3) = 0 := by
    by_contra nonzero
    exact plane_bad (secondColumn_plane_good frame nonzero)
  have last_nonzero : (frame.val 2 2 : ZMod 3) ≠ 0 := by
    intro zero
    have inverse_identity := congrArg (fun entries : Matrix (Fin 3) (Fin 3) (ZMod 3) =>
      entries 2 2) (reductionThree frame).mul_inv
    change ∑ index : Fin 3, (frame.val 2 index : ZMod 3) *
      (reductionThree frame).inv index 2 = 1 at inverse_identity
    simp only [Fin.sum_univ_three, first_zero, second_zero, zero, zero_mul, add_zero]
      at inverse_identity
    exact zero_ne_one inverse_identity
  obtain ⟨sign, normalized⟩ := nonzero_modThree_sign (frame.val 2 2) last_nonzero
  have frame_arithmetic : frame * lastColumnSign sign ∈ arithmeticLevel := by
    change lastRow ᵥ* (reductionThree (frame * lastColumnSign sign)).val = lastRow
    ext index
    fin_cases index <;>
      simp [lastRow, reductionThree, lastColumnSign, Matrix.single_vecMul,
        Matrix.mul_apply, Fin.sum_univ_three, first_zero, second_zero, normalized]
  refine ⟨integralImage (frame * lastColumnSign sign) frame_arithmetic, ?_⟩
  change (QuotientGroup.mk
    (GeneralLinearGroup.map (Int.castRingHom ℚ) (frame * lastColumnSign sign) * 1) : Edges) = _
  rw [mul_one, map_mul]
  exact QuotientGroup.mk_mul_of_mem _ (lastColumnSign_parabolic sign)

theorem edge_orbits_of_integral_frames
    (integral_frames : ∀ edge : Edges, ∃ frame : IntegralGL3,
      (QuotientGroup.mk (GeneralLinearGroup.map (Int.castRingHom ℚ) frame) : Edges) = edge)
    (edge : Edges) :
    GoodFlag .plane (endpoint .plane edge) ∨ GoodFlag .line (endpoint .line edge) ∨
      ∃ matrix : rationalLevel, matrix.val • standardBadEdge = edge := by
  classical
  by_cases plane_good : GoodFlag .plane (endpoint .plane edge)
  · exact Or.inl plane_good
  · obtain ⟨frame, rfl⟩ := integral_frames edge
    exact Or.inr (Or.inr (bad_integral_edge_in_standard_orbit frame plane_good))

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
