module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.Boundary

@[expose] public section


/-!
# The full rank-two Borel--Serre boundary cochain model

The rational Tits building for GL_3 is the bipartite graph of rational lines,
planes, and incident line-plane flags. Its equivariant cohomology is computed
by the total complex C^p(Γ, C^q(building,E)), q=0,1. The boundary is equivariantly
homotopy equivalent to this building. At the non-neat level we use rational
(or complex) equivariant cohomology, equivalently neat-cover cohomology with
finite-quotient invariants. The edge coordinate and its incoming differential
are retained below; the full boundary is not replaced by maximal strata.
-/

noncomputable section
namespace GeneralEisenstein
open Homogeneous

/-- Complete rational flags: the stabilizer is the upper triangular Borel. -/
abbrev Edges := RationalGL3 ⧸ (parabolic .plane ⊓ parabolic .line)

/-- Forgetting one endpoint of a complete flag. -/
def endpoint (s : Side) : Edges → Flags s :=
  Quotient.map' id (by
    intro a b h
    rw [QuotientGroup.leftRel_apply] at h ⊢
    cases s with
    | plane => exact h.1
    | line => exact h.2)

@[simp] theorem endpoint_smul (s : Side) (g : RationalGL3) (e : Edges) :
    endpoint s (g • e) = g • endpoint s e := by
  induction e using Quotient.inductionOn with
  | h q => rfl

abbrev MaximalCycles (n : ℕ) (χ : RankOneCharacter) (s : Side) :=
  cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) s)

instance (n : ℕ) (χ : RankOneCharacter) (s : Side) : AddCommGroup (MaximalCycles n χ s) :=
  cocyclesAddCommGroup rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) s)

abbrev MaximalCochains (n : ℕ) (χ : RankOneCharacter) (s : Side) (k : ℕ) :=
  cochains rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) s) k

abbrev EdgeCochains (n : ℕ) (χ : RankOneCharacter) (k : ℕ) :=
  cochains rationalLevel (functionRepresentation (rationalCoefficientComponent n χ) Edges) k

/-- Degree two: two maximal-stratum two-cocycles and a complete-flag one-cochain. -/
abbrev BoundaryDegreeTwo (n : ℕ) (χ : RankOneCharacter) :=
  (MaximalCycles n χ .plane × MaximalCycles n χ .line) × EdgeCochains n χ 1

/-- The remaining total-cocycle equation is incidence(a)=d(b). -/
def boundaryCompatibility (n : ℕ) (χ : RankOneCharacter) :
    BoundaryDegreeTwo n χ →ₗ[ℂ] ((Fin 3 → RationalGL3) → Edges → HomogeneousPoly n) where
  toFun z x e := z.1.1.val.val x (endpoint .plane e) - z.1.2.val.val x (endpoint .line e) -
    (z.2.val ![x 1,x 2] e - z.2.val ![x 0,x 2] e + z.2.val ![x 0,x 1] e)
  map_add' a b := by
    funext x e
    change
      (a.1.1.val.val x (endpoint .plane e) + b.1.1.val.val x (endpoint .plane e)) -
      (a.1.2.val.val x (endpoint .line e) + b.1.2.val.val x (endpoint .line e)) -
      ((a.2.val ![x 1,x 2] e + b.2.val ![x 1,x 2] e) -
       (a.2.val ![x 0,x 2] e + b.2.val ![x 0,x 2] e) +
       (a.2.val ![x 0,x 1] e + b.2.val ![x 0,x 1] e)) =
      (a.1.1.val.val x (endpoint .plane e) - a.1.2.val.val x (endpoint .line e) -
        (a.2.val ![x 1,x 2] e - a.2.val ![x 0,x 2] e + a.2.val ![x 0,x 1] e)) +
      (b.1.1.val.val x (endpoint .plane e) - b.1.2.val.val x (endpoint .line e) -
        (b.2.val ![x 1,x 2] e - b.2.val ![x 0,x 2] e + b.2.val ![x 0,x 1] e))
    abel
  map_smul' c a := by
    funext x e
    change
      c • a.1.1.val.val x (endpoint .plane e) - c • a.1.2.val.val x (endpoint .line e) -
      (c • a.2.val ![x 1,x 2] e - c • a.2.val ![x 0,x 2] e + c • a.2.val ![x 0,x 1] e) =
      c • (a.1.1.val.val x (endpoint .plane e) - a.1.2.val.val x (endpoint .line e) -
        (a.2.val ![x 1,x 2] e - a.2.val ![x 0,x 2] e + a.2.val ![x 0,x 1] e))
    simp only [smul_sub, smul_add]

/-- All total two-cocycles, including their complete-flag coordinates. -/
def fullBoundaryCycles (n : ℕ) (χ : RankOneCharacter) :
    Submodule ℂ (BoundaryDegreeTwo n χ) := LinearMap.ker (boundaryCompatibility n χ)

instance (n : ℕ) (χ : RankOneCharacter) : AddCommGroup (fullBoundaryCycles n χ) :=
  @Submodule.addCommGroup ℂ (BoundaryDegreeTwo n χ) inferInstance inferInstance inferInstance
    (fullBoundaryCycles n χ)

/-- The entire incoming total differential. No cocycle representative is
identified unless it differs by d(u_P,u_Q,v)=(du_P,du_Q,Ju-dv). -/
def IsBoundaryCoboundary (n : ℕ) (χ : RankOneCharacter)
    (z : fullBoundaryCycles n χ) : Prop :=
  ∃ (uP : MaximalCochains n χ .plane 1) (uQ : MaximalCochains n χ .line 1)
    (v : EdgeCochains n χ 0),
    z.val.1.1.val = differentialOne _ _ uP ∧
    z.val.1.2.val = differentialOne _ _ uQ ∧
    ∀ x e, z.val.2.val x e =
      uP.val x (endpoint .plane e) - uQ.val x (endpoint .line e) -
      (v.val ![x 1] e - v.val ![x 0] e)

/-- Incidence pulls a pair of cochains back to complete flags. -/
def incidenceCochain (n : ℕ) (χ : RankOneCharacter) (k : ℕ)
    (uP : MaximalCochains n χ .plane k) (uQ : MaximalCochains n χ .line k) :
    EdgeCochains n χ k :=
  ⟨fun x e => uP.val x (endpoint .plane e) - uQ.val x (endpoint .line e), by
    intro γ x
    funext e
    have hp := congrFun (uP.property γ x) (endpoint .plane e)
    have hq := congrFun (uQ.property γ x) (endpoint .line e)
    change uP.val (fun i => γ.val * x i) (endpoint .plane e) -
      uQ.val (fun i => γ.val * x i) (endpoint .line e) = _
    rw [hp,hq]
    change rationalCoefficientComponent n χ γ.val
      (uP.val x (γ.val⁻¹ • endpoint .plane e)) -
      rationalCoefficientComponent n χ γ.val
        (uQ.val x (γ.val⁻¹ • endpoint .line e)) =
      rationalCoefficientComponent n χ γ.val
        (uP.val x (endpoint .plane (γ.val⁻¹ • e)) -
         uQ.val x (endpoint .line (γ.val⁻¹ • e)))
    rw [endpoint_smul,endpoint_smul,map_sub]⟩

/-- Every total incoming differential really is a cocycle; there is no
unproved restriction on the zero- or one-cochains quantified in the quotient. -/
def fullBoundaryDifferential (n : ℕ) (χ : RankOneCharacter)
    (uP : MaximalCochains n χ .plane 1) (uQ : MaximalCochains n χ .line 1)
    (v : EdgeCochains n χ 0) : fullBoundaryCycles n χ :=
  ⟨((boundaryMap rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane) uP,
     boundaryMap rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line) uQ),
    incidenceCochain n χ 1 uP uQ -
      differentialZero rationalLevel (functionRepresentation (rationalCoefficientComponent n χ) Edges) v), by
    funext x e
    change
      (uP.val ![x 1,x 2] (endpoint .plane e) - uP.val ![x 0,x 2] (endpoint .plane e) +
        uP.val ![x 0,x 1] (endpoint .plane e)) -
      (uQ.val ![x 1,x 2] (endpoint .line e) - uQ.val ![x 0,x 2] (endpoint .line e) +
        uQ.val ![x 0,x 1] (endpoint .line e)) -
      ((uP.val ![x 1,x 2] (endpoint .plane e) - uQ.val ![x 1,x 2] (endpoint .line e) -
         (v.val ![x 2] e - v.val ![x 1] e)) -
       (uP.val ![x 0,x 2] (endpoint .plane e) - uQ.val ![x 0,x 2] (endpoint .line e) -
         (v.val ![x 2] e - v.val ![x 0] e)) +
       (uP.val ![x 0,x 1] (endpoint .plane e) - uQ.val ![x 0,x 1] (endpoint .line e) -
         (v.val ![x 1] e - v.val ![x 0] e))) = 0
    abel⟩

theorem fullBoundaryDifferential_is_coboundary (n : ℕ) (χ : RankOneCharacter)
    (uP : MaximalCochains n χ .plane 1) (uQ : MaximalCochains n χ .line 1)
    (v : EdgeCochains n χ 0) :
    IsBoundaryCoboundary n χ (fullBoundaryDifferential n χ uP uQ v) :=
  ⟨uP,uQ,v,rfl,rfl,fun _ _ => rfl⟩

/-- The span of all literal incoming boundaries. The set itself is linear;
taking its span is a construction that requires no choice of representatives. -/
def fullBoundaryRelations (n : ℕ) (χ : RankOneCharacter) :
    Submodule ℂ (fullBoundaryCycles n χ) :=
  Submodule.span ℂ {z | IsBoundaryCoboundary n χ z}

/-- Degree-two equivariant cohomology of the whole rational boundary building. -/
abbrev FullBoundaryH2 (n : ℕ) (χ : RankOneCharacter) :=
  @HasQuotient.Quotient (fullBoundaryCycles n χ) (Submodule ℂ (fullBoundaryCycles n χ))
    (@Submodule.hasQuotient ℂ (fullBoundaryCycles n χ) inferInstance inferInstance inferInstance)
    (fullBoundaryRelations n χ)

def fullBoundaryClass (n : ℕ) (χ : RankOneCharacter) :
    fullBoundaryCycles n χ →ₗ[ℂ] FullBoundaryH2 n χ :=
  @Submodule.mkQ ℂ (fullBoundaryCycles n χ) inferInstance inferInstance inferInstance
    (fullBoundaryRelations n χ)

/-- Pullback from global cohomology has constant maximal coordinates and zero
edge coordinate; it is the map from the augmentation of the building complex. -/
def globalBoundaryCocycle (n : ℕ) (χ : RankOneCharacter)
    (c : cocycles rationalLevel (rationalCoefficientComponent n χ)) :
    fullBoundaryCycles n χ :=
  ⟨((restrictionCocycle n χ .plane c, restrictionCocycle n χ .line c),0), by
    funext x e
    change c.val.val x - c.val.val x - (0 - 0 + 0) = 0
    simp⟩

/-- The boundary restriction is constrained on every global representative. -/
def RealizesFullRestriction (n : ℕ) (χ : RankOneCharacter)
    (r : WholeGlobalH2 n χ →ₗ[ℂ] FullBoundaryH2 n χ) : Prop :=
  ∀ c, r (classOf rationalLevel (rationalCoefficientComponent n χ) c) =
    fullBoundaryClass n χ (globalBoundaryCocycle n χ c)

/-- Maximal-stratum coordinates are induced by forgetting only the edge coordinate. -/
def RealizesBoundaryCoordinates (n : ℕ) (χ : RankOneCharacter)
    (q : FullBoundaryH2 n χ →ₗ[ℂ] BoundaryCoordinates n χ) : Prop :=
  ∀ c, q (fullBoundaryClass n χ c) =
    (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane) c.val.1.1,
     classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line) c.val.1.2)

end GeneralEisenstein

end
