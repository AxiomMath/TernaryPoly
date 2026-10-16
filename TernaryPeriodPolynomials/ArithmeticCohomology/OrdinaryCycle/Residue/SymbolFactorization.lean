module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Plane.EdgeParabolic
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.SymbolAbsent

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryResidueSymbol
open OrdinaryPlaneEdge OrdinaryResidueParabolic SinglePole
open OrdinaryApartmentPresentation OrdinaryApartmentFrames

/-- An integral apartment whose last two columns lie in a=0 has the expected binary residue evaluation. -/
theorem factorization_frame_parabolic (n : ℕ) (F : OrdinaryFullCoefficient.ResidueHom n (-1))
    (g : ModThreeGoodAction.IntegralGL) (h1 : g.val 0 1 = 0) (h2 : g.val 0 2 = 0) :
    zeroCoordinate n (F.val (frameCycle g)) = restriction n F (binaryProject (frameCycle g)) := by
  obtain ⟨C,lam,u,hg⟩ := integral_block_decomposition g h1 h2
  have hp : binaryProject (frameCycle g) =
      BinaryModularSymbol.action (BinaryModularSymbol.integral C) BinaryModularSymbol.reference := by
    rw [←mul_one g,←OrdinaryFullAction.frameCycle_equivariant,←binaryCone_reference]
    exact binaryProject_action_binaryCone (OrdinaryFullAction.integral g) lam u
      (BinaryModularSymbol.integral C) hg BinaryModularSymbol.reference
  rw [hp,restriction_equivariant,OrdinaryFullCoefficient.hom_frame]
  change SinglePoleCoordinate.coordinateTuple n
    (residueAction n (-1) (OrdinaryFullAction.integral g)
      (OrdinaryFullCoefficient.reference (residueAction n (-1)) F)) 0 = _
  rw [coordinateTuple_action n (OrdinaryFullAction.integral g) lam u (BinaryModularSymbol.integral C) hg,
    coefficient_action]
  congr 1
  change zeroCoordinate n (F.val (frameCycle 1)) = zeroCoordinate n (F.val (binaryCone BinaryModularSymbol.reference))
  rw [binaryCone_reference]

theorem mul_cycle_first_row (g : ModThreeGoodAction.IntegralGL) (j : Fin 3) :
    (g * ReferenceCoefficientMatrices.c).val 0 j =
      g.val 0 ((![1,2,0] : Fin 3 → Fin 3) j) :=
  congrFun (mul_c_column g j) 0

/-- Every actual integral apartment satisfies the literal plane-edge factorization. -/
theorem factorization_frame (n : ℕ) (F : OrdinaryFullCoefficient.ResidueHom n (-1))
    (g : ModThreeGoodAction.IntegralGL) :
    zeroCoordinate n (F.val (frameCycle g)) = restriction n F (binaryProject (frameCycle g)) := by
  by_cases hg : FrameFirstRowCoordinate g
  · obtain ⟨i,hi⟩ := hg
    fin_cases i
    · exact factorization_frame_parabolic n F g (hi 1 (by decide)) (hi 2 (by decide))
    · have h := factorization_frame_parabolic n F (g * ReferenceCoefficientMatrices.c)
        (by simp only [mul_cycle_first_row]; exact hi 2 (by decide))
        (by simp only [mul_cycle_first_row]; exact hi 0 (by decide))
      simpa only [OrdinaryFullAction.frameCycle_cyclic] using h
    · have h := factorization_frame_parabolic n F ((g * ReferenceCoefficientMatrices.c) * ReferenceCoefficientMatrices.c)
        (by simp only [mul_cycle_first_row]; exact hi 0 (by decide))
        (by simp only [mul_cycle_first_row]; exact hi 1 (by decide))
      simpa only [OrdinaryFullAction.frameCycle_cyclic] using h
  · rw [coordinate_frame_zero n F g hg,project_frame_zero g hg,map_zero]

/-- Actual full integral apartment spanning proves factorization on every incidence cycle. -/
theorem restriction_factorization (n : ℕ) (F : OrdinaryFullCoefficient.ResidueHom n (-1))
    (c : OrdinaryIncidenceChains.Cycles) :
    zeroCoordinate n (F.val c) = restriction n F (binaryProject c) := by
  have he : (zeroCoordinate n).comp F.val = (restriction n F).comp binaryProject := by
    apply cycle_functional_ext
    intro g
    exact factorization_frame n F g
  exact LinearMap.congr_fun he c

/-- The factorization refers to the constructed actual binary modular-symbol functional. -/
theorem toBinaryHom_factorization (n : ℕ) (F : OrdinaryFullCoefficient.ResidueHom n (-1))
    (c : OrdinaryIncidenceChains.Cycles) :
    SinglePoleCoordinate.coordinateTuple n (F.val c) 0 = (toBinaryHom n F).val (binaryProject c) :=
  restriction_factorization n F c

end TernaryPoly.OrdinaryResidueSymbol
