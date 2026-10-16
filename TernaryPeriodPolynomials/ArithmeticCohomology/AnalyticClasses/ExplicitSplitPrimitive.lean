module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Split.CocycleDescent
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.CentralGroupH2

@[expose] public section


/-!
# An explicit primitive for relative two-cocycles of a split extension

Let `E = N ⋊ L` be a split extension and `d` a two-cocycle of `E` vanishing on pairs of radical
elements. Suppose every edge one-cocycle `r ↦ d(s l, r') - d(r, s l)` is the coboundary of a given
vector `potential l` (with `potential 1 = 0`), and that a central element `z` of `L` acts on the
radical invariants by a scalar `λ ≠ 1`. Then `d = δ K` for the explicit one-cochain

`K e = (λ - 1)⁻¹ (d₂(s z, s π e) - d₂(s π e, s z)) - d₁(n(e), s π e) - potential (π e)`,

where `d₁ = d + δ(potential ∘ π)`, `d₂ = d₁ + δ(e ↦ d₁(n(e), s π e))` and `n(e)` is the radical
coordinate of `e`. This is the constructive form of the edge-injectivity argument: no choice is
made, so analytic properties of `K` can be read off from those of `d` and of the potentials.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {N E L : Type} [Group N] [Group E] [Group L]
variable {extension : GroupExtension N E L}

/-- The first correction `d + δ(potential ∘ π)`. -/
def potentialCorrected (representation : Rep ℂ E)
    (cycle : relativeTwoCocycles extension.inl representation) (potential : L → representation)
    (potential_one : potential 1 = 0) : relativeTwoCocycles extension.inl representation :=
  cycle + relativeBoundaryOfRestriction extension.inl representation
    (fun element => potential (extension.rightHom element)) 0 (by
      intro radical
      change potential (extension.rightHom (extension.inl radical)) = 0
      rw [extension.rightHom_inl, potential_one])

theorem potentialCorrected_apply (representation : Rep ℂ E)
    (cycle : relativeTwoCocycles extension.inl representation) (potential : L → representation)
    (potential_one : potential 1 = 0) (first second : E) :
    (potentialCorrected representation cycle potential potential_one).val (first, second) =
      cycle.val (first, second) +
        (representation.ρ first (potential (extension.rightHom second)) -
          potential (extension.rightHom (first * second)) +
            potential (extension.rightHom first)) := rfl

theorem potentialCorrected_val (representation : Rep ℂ E)
    (cycle : relativeTwoCocycles extension.inl representation) (potential : L → representation)
    (potential_one : potential 1 = 0) :
    (potentialCorrected representation cycle potential potential_one).val =
      cycle.val + twoBoundaryCycle representation
        (fun element => potential (extension.rightHom element)) := rfl

theorem potentialCorrected_edge (splitting : extension.Splitting) (representation : Rep ℂ E)
    (cycle : relativeTwoCocycles extension.inl representation) (potential : L → representation)
    (potential_one : potential 1 = 0)
    (boundary : ∀ levi,
      oneBoundaryCycle (Rep.res extension.inl representation) (potential levi) =
        splitEdgeCycle splitting representation levi cycle) (levi : L) :
    splitEdgeCycle splitting representation levi
      (potentialCorrected representation cycle potential potential_one) = 0 := by
  unfold potentialCorrected
  rw [(splitEdgeCycle splitting representation levi).map_add, splitEdgeCycle_relativeBoundary,
    map_zero, sub_zero, zero_sub, splitting.rightHom_splitting, boundary, add_neg_cancel]

/-- The second correction, killing the mixed values `d₁(n, s l)`. -/
def mixedCorrected (splitting : extension.Splitting) (representation : Rep ℂ E)
    (cycle : relativeTwoCocycles extension.inl representation) :
    relativeTwoCocycles extension.inl representation :=
  cycle + relativeBoundaryOfRestriction extension.inl representation
    (splitMixedPrimitive splitting representation cycle) 0
    (splitMixedPrimitive_inl splitting representation cycle)

theorem mixedCorrected_val (splitting : extension.Splitting) (representation : Rep ℂ E)
    (cycle : relativeTwoCocycles extension.inl representation) :
    (mixedCorrected splitting representation cycle).val =
      cycle.val + twoBoundaryCycle representation
        (splitMixedPrimitive splitting representation cycle) := rfl

theorem mixedCorrected_edge (splitting : extension.Splitting) (representation : Rep ℂ E)
    (cycle : relativeTwoCocycles extension.inl representation)
    (zero : ∀ levi, splitEdgeCycle splitting representation levi cycle = 0) (levi : L) :
    splitEdgeCycle splitting representation levi
      (mixedCorrected splitting representation cycle) = 0 := by
  unfold mixedCorrected
  rw [(splitEdgeCycle splitting representation levi).map_add, zero, zero_add]
  rw [splitEdgeCycle_relativeBoundary, map_zero, sub_zero]
  apply groupCohomology.cocycles₁_ext
  intro radical
  change 0 - (representation.ρ (extension.inl radical)
    (splitMixedPrimitive splitting representation cycle (splitting levi)) -
      splitMixedPrimitive splitting representation cycle (splitting levi)) = 0
  rw [splitMixedPrimitive_splitting, map_zero, sub_self, sub_self]

theorem mixedCorrected_mixed (splitting : extension.Splitting) (representation : Rep ℂ E)
    (cycle : relativeTwoCocycles extension.inl representation) (radical : N) (levi : L) :
    (mixedCorrected splitting representation cycle).val
      (extension.inl radical, splitting levi) = 0 := by
  change cycle.val (extension.inl radical, splitting levi) +
    twoBoundaryCycle representation (splitMixedPrimitive splitting representation cycle)
      (extension.inl radical, splitting levi) = 0
  rw [twoBoundaryCycle_apply, splitMixedPrimitive_inl, splitMixedPrimitive_splitting,
    splitMixedPrimitive_pair, map_zero]
  abel

theorem mixedCorrected_left_zero (splitting : extension.Splitting) (representation : Rep ℂ E)
    (cycle : relativeTwoCocycles extension.inl representation) (radical : N) (element : E) :
    (mixedCorrected splitting representation cycle).val (extension.inl radical, element) = 0 :=
  relativeTwoCocycle_radical_left splitting representation _
    (mixedCorrected_mixed splitting representation cycle) radical element

theorem mixedCorrected_right_zero (splitting : extension.Splitting) (representation : Rep ℂ E)
    (cycle : relativeTwoCocycles extension.inl representation)
    (zero : ∀ levi, splitEdgeCycle splitting representation levi cycle = 0)
    (element : E) (radical : N) :
    (mixedCorrected splitting representation cycle).val (element, extension.inl radical) = 0 :=
  relativeTwoCocycle_radical_right splitting representation _
    (mixedCorrected_edge splitting representation cycle zero)
    (mixedCorrected_mixed splitting representation cycle) element radical

/-- The inflation of a coboundary on `L` is the coboundary of the inflated cochain. -/
theorem splitInflatedCocycle_twoBoundary (splitting : extension.Splitting)
    (representation : Rep ℂ E)
    (primitive : L → splitInvariantRepresentation splitting representation) :
    splitInflatedCocycle splitting representation
        (twoBoundaryCycle (splitInvariantRepresentation splitting representation) primitive) =
      twoBoundaryCycle representation
        (fun element => (primitive (extension.rightHom element)).val) := by
  apply Subtype.ext
  funext pair
  obtain ⟨first, second⟩ := pair
  change splitInflatedCocycle splitting representation
      (twoBoundaryCycle (splitInvariantRepresentation splitting representation) primitive)
        (first, second) =
    twoBoundaryCycle representation
      (fun element => (primitive (extension.rightHom element)).val) (first, second)
  rw [splitInflatedCocycle_apply, twoBoundaryCycle_apply, twoBoundaryCycle_apply]
  obtain ⟨radical, levi, rfl⟩ := split_exists_pair splitting first
  simp only [map_mul, extension.rightHom_inl, splitting.rightHom_splitting, one_mul]
  have invariant : representation.ρ (extension.inl radical)
      (representation.ρ (splitting levi) (primitive (extension.rightHom second)).val) =
      representation.ρ (splitting levi) (primitive (extension.rightHom second)).val :=
    (Representation.mem_invariants _ _).mp
      ((splitInvariantRepresentation splitting representation).ρ levi
        (primitive (extension.rightHom second))).property radical
  rw [Module.End.mul_apply, invariant]
  rfl

/-- The descended cocycle on `L` of the doubly corrected cocycle. -/
def explicitDescended (splitting : extension.Splitting) (representation : Rep ℂ E)
    (cycle : relativeTwoCocycles extension.inl representation) (potential : L → representation)
    (potential_one : potential 1 = 0)
    (boundary : ∀ levi,
      oneBoundaryCycle (Rep.res extension.inl representation) (potential levi) =
        splitEdgeCycle splitting representation levi cycle) :
    groupCohomology.cocycles₂ (splitInvariantRepresentation splitting representation) :=
  splitDescendedCocycle splitting representation
    (mixedCorrected splitting representation
      (potentialCorrected representation cycle potential potential_one)).val
    (mixedCorrected_left_zero splitting representation _)
    (mixedCorrected_right_zero splitting representation _
      (potentialCorrected_edge splitting representation cycle potential potential_one boundary))

/-- The invariant-valued part of the explicit primitive, on `L`. -/
def explicitLeviPrimitive (splitting : extension.Splitting) (representation : Rep ℂ E)
    (cycle : relativeTwoCocycles extension.inl representation) (potential : L → representation)
    (potential_one : potential 1 = 0)
    (boundary : ∀ levi,
      oneBoundaryCycle (Rep.res extension.inl representation) (potential levi) =
        splitEdgeCycle splitting representation levi cycle) (central : L) (scalar : ℂ) :
    L → splitInvariantRepresentation splitting representation :=
  (scalar - 1)⁻¹ • centralTwoCocycleHomotopy (splitInvariantRepresentation splitting representation)
    central (explicitDescended splitting representation cycle potential potential_one boundary)

/-- **The explicit primitive.** -/
def explicitSplitPrimitive (splitting : extension.Splitting) (representation : Rep ℂ E)
    (cycle : relativeTwoCocycles extension.inl representation) (potential : L → representation)
    (potential_one : potential 1 = 0)
    (boundary : ∀ levi,
      oneBoundaryCycle (Rep.res extension.inl representation) (potential levi) =
        splitEdgeCycle splitting representation levi cycle) (central : L) (scalar : ℂ) :
    E → representation :=
  fun element =>
    (explicitLeviPrimitive splitting representation cycle potential potential_one boundary central
        scalar (extension.rightHom element)).val -
      splitMixedPrimitive splitting representation
        (potentialCorrected representation cycle potential potential_one) element -
      potential (extension.rightHom element)

theorem twoBoundaryCycle_sub_sub (representation : Rep ℂ E) (a b c : E → representation) :
    twoBoundaryCycle representation (a - b - c) =
      twoBoundaryCycle representation a - twoBoundaryCycle representation b -
        twoBoundaryCycle representation c := by
  apply Subtype.ext
  funext pair
  change twoBoundaryCycle representation (a - b - c) pair =
    twoBoundaryCycle representation a pair - twoBoundaryCycle representation b pair -
      twoBoundaryCycle representation c pair
  rw [twoBoundaryCycle_apply, twoBoundaryCycle_apply, twoBoundaryCycle_apply,
    twoBoundaryCycle_apply]
  simp only [Pi.sub_apply, map_sub]
  abel

/-- **A relative cocycle with pointwise-exact edges and a nontrivial central scalar on the radical
invariants is the coboundary of the explicit primitive.** -/
theorem relativeTwoCocycle_eq_explicitBoundary (splitting : extension.Splitting)
    (representation : Rep ℂ E)
    (cycle : relativeTwoCocycles extension.inl representation) (potential : L → representation)
    (potential_one : potential 1 = 0)
    (boundary : ∀ levi,
      oneBoundaryCycle (Rep.res extension.inl representation) (potential levi) =
        splitEdgeCycle splitting representation levi cycle)
    (central : L) (commutes : ∀ element, central * element = element * central) (scalar : ℂ)
    (nontrivial : scalar ≠ 1)
    (action : ∀ vector,
      (splitInvariantRepresentation splitting representation).ρ central vector =
        scalar • vector) :
    cycle.val = twoBoundaryCycle representation
      (explicitSplitPrimitive splitting representation cycle potential potential_one boundary
        central scalar) := by
  have descended_boundary :
      twoBoundaryCycle (splitInvariantRepresentation splitting representation)
          (explicitLeviPrimitive splitting representation cycle potential potential_one boundary
            central scalar) =
        explicitDescended splitting representation cycle potential potential_one boundary := by
    apply Subtype.ext
    funext pair
    change (splitInvariantRepresentation splitting representation).ρ pair.1
        ((scalar - 1)⁻¹ • centralTwoCocycleHomotopy _ central
          (explicitDescended splitting representation cycle potential potential_one boundary)
            pair.2) -
      (scalar - 1)⁻¹ • centralTwoCocycleHomotopy _ central
          (explicitDescended splitting representation cycle potential potential_one boundary)
            (pair.1 * pair.2) +
        (scalar - 1)⁻¹ • centralTwoCocycleHomotopy _ central
          (explicitDescended splitting representation cycle potential potential_one boundary)
            pair.1 =
      explicitDescended splitting representation cycle potential potential_one boundary
        (pair.1, pair.2)
    rw [map_smul, ← smul_sub, ← smul_add]
    change (scalar - 1)⁻¹ • twoBoundaryCycle _ (centralTwoCocycleHomotopy _ central
        (explicitDescended splitting representation cycle potential potential_one boundary))
          (pair.1, pair.2) = _
    rw [centralTwoCocycleHomotopy_boundary _ central commutes, action]
    have difference (vector : splitInvariantRepresentation splitting representation) :
        scalar • vector - vector = (scalar - 1) • vector := by rw [sub_smul, one_smul]
    rw [difference, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr nontrivial), one_smul]
  have second_val :
      (mixedCorrected splitting representation
        (potentialCorrected representation cycle potential potential_one)).val =
      twoBoundaryCycle representation (fun element =>
        (explicitLeviPrimitive splitting representation cycle potential potential_one boundary
          central scalar (extension.rightHom element)).val) := by
    rw [← splitInflatedCocycle_twoBoundary, descended_boundary, explicitDescended,
      splitInflated_descended]
  rw [mixedCorrected_val, potentialCorrected_val] at second_val
  have unfolded :
      explicitSplitPrimitive splitting representation cycle potential potential_one boundary
          central scalar =
        (fun element =>
          (explicitLeviPrimitive splitting representation cycle potential potential_one boundary
            central scalar (extension.rightHom element)).val) -
          splitMixedPrimitive splitting representation
            (potentialCorrected representation cycle potential potential_one) -
          (fun element => potential (extension.rightHom element)) := rfl
  rw [unfolded, twoBoundaryCycle_sub_sub, ← second_val]
  abel

end TernaryPeriodPolynomials.AnalyticClasses
