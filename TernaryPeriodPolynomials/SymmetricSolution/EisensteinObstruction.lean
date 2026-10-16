module

public import TernaryPeriodPolynomials.SymmetricSolution.EisensteinObstruction.Inputs
public import TernaryPeriodPolynomials.SymmetricSolution.EisensteinObstruction.Recognition

@[expose] public section


/-! The complete Eisenstein obstruction argument.
-/

noncomputable section
namespace TernaryPeriodPolynomials
open GeneralEisenstein

/-- The four parent statements, together with the proved bridge and
holomorphy results, supply the existing paper assembly. -/
theorem eisensteinInputs : EisensteinInputs where
  bridge := TernaryPeriodPolynomials.PolynomialBoundaryBridge.polynomial_boundary_bridge
  recognition := boundary_cuspidal_recognition
  holomorphy := TernaryPeriodPolynomials.EisensteinHolomorphy.eisenstein_holomorphy
  graph := general_eisenstein_graph
  projection := boundary_projection_good_cusps
  detection := eisenstein_bad_plane_detection

/-- The paper's literal Bernoulli obstruction vanishes for every symmetric
positive-degree homogeneous solution, given the four parent statements. -/
theorem bernoulli_obstruction_vanishes (n : ℕ) (hn : 0 < n)
    (f : HomogeneousPoly n) (hf : SymmetricSolution f) : bernoulliObstruction f = 0 :=
  bernoulli_obstruction_vanishes_of_challenges eisensteinInputs n hn f hf

/-- The three recognition children and the proved Hecke descent. -/
theorem recognitionPieces : CuspidalRecognitionPieces where
  hecke := TernaryPeriodPolynomials.BoundaryHeckeDescent.boundary_hecke_descent
  span := inner_bad_line_cuspidal_span
  projectors := cuspidal_associate_projector
  recovery := cuspidal_finite_spectral_recovery

/-- The away-three algebra statement and proved Hecke stability. -/
theorem projectionPieces : GoodProjectionPieces where
  stability := TernaryPeriodPolynomials.AwayThreeHeckeGoodCusps.away_three_hecke_good_cusps
  algebra := associate_projector_away_three_algebra

/-- The spherical detection statement and the four accepted local inputs. -/
theorem detectionPieces : BadPlaneDetectionPieces where
  representative := TernaryPeriodPolynomials.BadPlaneSameConstituentRepresentative.bad_plane_same_constituent_representative
  sphericity := TernaryPeriodPolynomials.BadPlaneSupportSphericity.bad_plane_support_sphericity
  parity := TernaryPeriodPolynomials.LevelOneCohomologicalParity.level_one_cohomological_parity
  localEntry := TernaryPeriodPolynomials.LocalThreeBadPlaneEntry.local_three_bad_plane_entry
  globalDetection := spherical_standard_good_cusp_detection

/-- The parent statements follow alternatively from their exact child statements. -/
theorem eisensteinInputsFromChildren : EisensteinInputs where
  bridge := TernaryPeriodPolynomials.PolynomialBoundaryBridge.polynomial_boundary_bridge
  recognition := boundary_cuspidal_recognition_of_pieces recognitionPieces
  holomorphy := TernaryPeriodPolynomials.EisensteinHolomorphy.eisenstein_holomorphy
  graph := general_eisenstein_graph
  projection := boundary_projection_good_cusps_of_pieces projectionPieces
  detection := eisenstein_bad_plane_detection_of_pieces detectionPieces

/-- The same obstruction conclusion through six child/graph statements. -/
theorem bernoulli_obstruction_vanishes_from_children (n : ℕ) (hn : 0 < n)
    (f : HomogeneousPoly n) (hf : SymmetricSolution f) : bernoulliObstruction f = 0 :=
  bernoulli_obstruction_vanishes_of_challenges eisensteinInputsFromChildren n hn f hf

end TernaryPeriodPolynomials
