module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Coefficients
public import TernaryPeriodPolynomials.BoundaryComparison.LevelTransfer
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.GroupEquivCohomology

@[expose] public section


/-!
# L2 for the model: the level `H²` is the `Γ/Γ(6)`-invariants of the `Γ(6)` `H²`

Worker L's level transfer (`Statements.LevelTransfer.levelTransfer`, degree two, in the homogeneous-cochain
model) applied to `S = rationalLevel` and `N = N6`, the image of `Γ(6)` in `GL₃(ℚ)`
(`levelSixTransfer`, for every complex representation of `GL₃(ℚ)`, in particular `E`, `E*` and their
function representations on flags). `N6` is normalized by the level (`N6_normalized`), of finite index
(`N6_finite_quotient`), and `H² N6` is the whole-group `H²` of the abstract group `Γ(6)` (`n6H2Equiv`),
the object of the geometric side after the bridge to Mathlib's `groupCohomology`.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein TernaryPoly.IntegralGL3Congruence

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

/-- The image of `Γ(6)` in `GL₃(ℚ)`. -/
def N6 : Subgroup RationalGL3 :=
  principalSix.map (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ))

theorem intMap_injective :
    Function.Injective (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) : IntegralGL3 →* RationalGL3) := by
  intro a b h
  apply Units.ext
  ext i j
  have := congrArg (fun g : RationalGL3 => g.val i j) h
  simpa [Matrix.GeneralLinearGroup.map] using this

theorem rationalLevel_eq_map :
    rationalLevel = arithmeticLevel.map (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ)) := by
  ext g
  constructor
  · rintro ⟨γ, rfl⟩
    exact ⟨γ.1, γ.2, rfl⟩
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨⟨γ, hγ⟩, rfl⟩

theorem N6_le_rationalLevel : N6 ≤ rationalLevel := by
  rw [rationalLevel_eq_map]
  exact Subgroup.map_mono principalSix_le_arithmeticLevel

theorem N6_normalized : ∀ s ∈ rationalLevel, ∀ n ∈ N6, s⁻¹ * n * s ∈ N6 := by
  intro s hs n hn
  rw [rationalLevel_eq_map] at hs
  obtain ⟨g, _, rfl⟩ := hs
  obtain ⟨d, hd, rfl⟩ := hn
  refine ⟨g⁻¹ * d * g, ?_, by simp⟩
  have := (principal_normal 6).conj_mem d hd g⁻¹
  simpa using this

theorem N6_finite_quotient : Finite (rationalLevel ⧸ N6.subgroupOf rationalLevel) := by
  have hidx : (N6.subgroupOf rationalLevel).index ≠ 0 := by
    change N6.relIndex rationalLevel ≠ 0
    rw [N6, rationalLevel_eq_map, Subgroup.relIndex_map_map_of_injective _ _ intMap_injective]
    intro h
    have h2 := Subgroup.relIndex_dvd_index_of_normal (H := principalSix) (K := arithmeticLevel)
    rw [h] at h2
    have := zero_dvd_iff.mp h2
    exact (principal_finiteIndex 6).index_ne_zero this
  have : (N6.subgroupOf rationalLevel).FiniteIndex := ⟨hidx⟩
  infer_instance

instance : Fintype (rationalLevel ⧸ N6.subgroupOf rationalLevel) :=
  @Fintype.ofFinite _ N6_finite_quotient

open TernaryPeriodPolynomials.Argument.Statements.LevelTransfer in
/-- **L2 for the model level.** For any complex representation `ρ` of `GL₃(ℚ)` (in particular
`E`, `E*`, and their function representations on flags), the cohomology `H²` of the model level is
the `rationalLevel / Γ(6)`-invariants of the `H²` of the image of `Γ(6)`. -/
def levelSixTransfer {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ RationalGL3 V) :
    GeneralEisenstein.Homogeneous.H2 rationalLevel ρ ≃ₗ[ℂ] invariants ρ N6_normalized :=
  levelTransfer ρ N6_le_rationalLevel N6_normalized

/-- `Γ(6) ≃ N6`. -/
def sixEquivN6 : principalSix ≃* N6 :=
  Subgroup.equivMapOfInjective principalSix _ intMap_injective

/-- The coefficient system restricted to `Γ(6)`, as a representation of the abstract group `Γ(6)`. -/
def sixRep {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ RationalGL3 V) :
    Representation ℂ principalSix V :=
  (ρ.comp N6.subtype).comp sixEquivN6.toMonoidHom

open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers in
/-- `H²(N6, ρ)` in the ambient-vertex model is the whole-group `H²` of the abstract group `Γ(6)`. -/
def n6H2Equiv {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ RationalGL3 V) :
    GeneralEisenstein.Homogeneous.H2 N6 ρ ≃ₗ[ℂ]
      GeneralEisenstein.Homogeneous.H2 (⊤ : Subgroup principalSix) (sixRep ρ) :=
  (ambientResolutionH2Equiv N6 ρ).trans (fullGroupEquivH2 sixEquivN6 (ρ.comp N6.subtype))

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
