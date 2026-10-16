module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.ModThreeFlags

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

theorem edgeStabilizer_standard : edgeStabilizer (QuotientGroup.mk (1 : RationalGL3)) = standardBorel := by
  ext g
  constructor
  · rintro ⟨level,fixes⟩
    refine ⟨level,?_⟩
    change g ∈ parabolic .plane ⊓ parabolic .line
    have fixed : (QuotientGroup.mk (g*1) : Edges) = QuotientGroup.mk 1 := fixes
    rw [mul_one] at fixed
    have member := QuotientGroup.eq.mp fixed.symm
    simpa only [inv_one,one_mul] using member
  · rintro ⟨level,borel⟩
    change g ∈ parabolic .plane ⊓ parabolic .line at borel
    refine ⟨level,?_⟩
    change (QuotientGroup.mk (g*1) : Edges) = QuotientGroup.mk 1
    rw [mul_one]
    apply Eq.symm
    apply QuotientGroup.eq.mpr
    simpa only [inv_one,one_mul] using borel

theorem normalizedBadLine_primitive_at_standard_orbit (n : ℕ) (positive : 0 < n)
    (f : HomogeneousPoly n) (solution : SymmetricSolution f)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (normalized : NormalizedBadLine f c) (edge : Edges)
    (orbit : ∃ transport : rationalLevel, edge = transport.val • QuotientGroup.mk 1) :
    ∃ primitive : cochains (edgeStabilizer edge) (rationalCoefficientComponent n trivialCharacter) 1,
      ∀ vertices, (differentialOne (edgeStabilizer edge)
        (rationalCoefficientComponent n trivialCharacter) primitive).val vertices = c.val.val vertices := by
  obtain ⟨transport,edge_eq⟩ := orbit
  obtain ⟨primitive,primitive_eq⟩ := normalizedBadLine_standardBorel_primitive n positive f solution c normalized
  apply cocycle_primitive_transport rationalLevel standardBorel (edgeStabilizer edge)
    (rationalCoefficientComponent n trivialCharacter) c transport _ primitive primitive_eq
  intro element
  rw [← edgeStabilizer_standard]
  refine ⟨rationalLevel.mul_mem
    (rationalLevel.mul_mem (rationalLevel.inv_mem transport.property) element.property.1)
      transport.property,?_⟩
  have fixes : element.val • edge = edge := element.property.2
  change (transport.val⁻¹*element.val*transport.val) • (QuotientGroup.mk 1 : Edges) = QuotientGroup.mk 1
  rw [mul_smul,mul_smul,← edge_eq,fixes,edge_eq,inv_smul_smul]

theorem normalizedPathClass_all_flag_primitives (n : ℕ) (positive : 0 < n)
    (f : HomogeneousPoly n) (solution : SymmetricSolution f)
    (F : EdgeChains →ₗ[ℂ] HomogeneousPoly n) (functional : IsPolynomialFunctional f F)
    (paths : rationalLevel → EdgeChains)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (path_family : IsPathFamily paths) (realization : RealizesPathClass F paths c)
    (normalized : NormalizedBadLine f c) (edge : Edges) :
    ∃ primitive : cochains (edgeStabilizer edge) (rationalCoefficientComponent n trivialCharacter) 1,
      ∀ vertices, (differentialOne (edgeStabilizer edge)
        (rationalCoefficientComponent n trivialCharacter) primitive).val vertices = c.val.val vertices := by
  rcases rational_flag_orbit_cases edge with standard | good_plane
  · exact normalizedBadLine_primitive_at_standard_orbit n positive f solution c normalized edge standard
  · exact pathClass_primitive_at_plane_orbit f F functional paths c path_family realization edge good_plane

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
