module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Dual.Transport

@[expose] public section


/-!
# The dual coefficient system in the boundary-building cochain model

`dualRep ρ = ρ ∘ φ` is the dual coefficient system (`E*` after the fixed change of coefficient
coordinates, `Definitions` of `Proofs/AxiomCodeDuality`). This file extends the boundary model of
`Definitions/Boundary`, `Definitions/ManuscriptBoundary` (`StratumH2`, `restrictionCocycle`,
`globalCoordinates`, `InnerBoundary`) from the representations
`rationalCoefficientComponent n χ` to an arbitrary representation, so that the paper's
statements about `E*` (`ar:eq:dualconstantterms`) can be stated literally for `ρ* = dualRep ρ`:

* `StratumH2Rep ρ side`, `restrictionCocycleRep`, `globalCoordinatesRep`, `InnerBoundaryRep`,
  with `InnerBoundaryRep (rationalCoefficientComponent n χ) = InnerBoundary n χ` by `Iff.rfl`;
* `phiCocycle`: the global cocycle `x ↦ c(φ x)` of `E*` attached to a global cocycle `c` of `E`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Dual

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- The dual coefficient system `ρ ∘ φ`. -/
def dualRep (ρ : Representation ℂ RationalGL3 V) : Representation ℂ RationalGL3 V :=
  ρ.comp dualInvolution

/-- Degree-two cohomology of the maximal stratum of `side` with coefficients `ρ`. -/
abbrev StratumH2Rep (ρ : Representation ℂ RationalGL3 V) (side : Side) :=
  H2 rationalLevel (flagRepresentation ρ side)

/-- Pulling a global cocycle back to a maximal stratum (literally constant on flags). -/
def restrictionCocycleRep (ρ : Representation ℂ RationalGL3 V) (side : Side)
    (c : cocycles rationalLevel ρ) : cocycles rationalLevel (flagRepresentation ρ side) :=
  ⟨⟨fun x _ => c.val.val x, by
    intro γ x
    funext f
    exact c.val.property γ x⟩, by
    funext x f
    exact congrFun c.property x⟩

/-- The maximal coordinates of a global cocycle. -/
def globalCoordinatesRep (ρ : Representation ℂ RationalGL3 V) (c : cocycles rationalLevel ρ) :
    StratumH2Rep ρ .plane × StratumH2Rep ρ .line :=
  (classOf rationalLevel (flagRepresentation ρ .plane) (restrictionCocycleRep ρ .plane c),
   classOf rationalLevel (flagRepresentation ρ .line) (restrictionCocycleRep ρ .line c))

/-- Inner (mixed cuspidal) classes: zero restriction to every complete flag. -/
def InnerBoundaryRep (ρ : Representation ℂ RationalGL3 V) (side : Side)
    (a : StratumH2Rep ρ side) : Prop :=
  ∃ z : cocycles rationalLevel (flagRepresentation ρ side),
    classOf rationalLevel (flagRepresentation ρ side) z = a ∧
    ∃ u : cochains rationalLevel (functionRepresentation ρ Edges) 1, ∀ x e,
      z.val.val x (endpoint side e) =
        (differentialOne rationalLevel (functionRepresentation ρ Edges) u).val x e

theorem innerBoundaryRep_iff (n : ℕ) (χ : RankOneCharacter) (side : Side)
    (a : StratumH2 n χ side) :
    InnerBoundaryRep (rationalCoefficientComponent n χ) side a ↔ InnerBoundary n χ side a :=
  Iff.rfl

/-- The subspace of inner classes. -/
def innerClassesRep (ρ : Representation ℂ RationalGL3 V) (side : Side) :
    Submodule ℂ (StratumH2Rep ρ side) where
  carrier := {a | InnerBoundaryRep ρ side a}
  zero_mem' := ⟨0, map_zero _, 0, fun x e => by
    rw [map_zero]
    rfl⟩
  add_mem' := by
    rintro a b ⟨z, hz, u, hu⟩ ⟨z', hz', u', hu'⟩
    refine ⟨z + z', by rw [map_add, hz, hz'], u + u', fun x e => ?_⟩
    have e1 : (z + z').val.val x (endpoint side e) =
        z.val.val x (endpoint side e) + z'.val.val x (endpoint side e) := rfl
    have e2 : (differentialOne rationalLevel (functionRepresentation ρ Edges) (u + u')).val x e =
        (differentialOne rationalLevel (functionRepresentation ρ Edges) u).val x e +
        (differentialOne rationalLevel (functionRepresentation ρ Edges) u').val x e := by
      rw [map_add]
      rfl
    rw [e1, e2, hu x e, hu' x e]
  smul_mem' := by
    rintro c a ⟨z, hz, u, hu⟩
    refine ⟨c • z, by rw [map_smul, hz], c • u, fun x e => ?_⟩
    have e1 : (c • z).val.val x (endpoint side e) = c • z.val.val x (endpoint side e) := rfl
    have e2 : (differentialOne rationalLevel (functionRepresentation ρ Edges) (c • u)).val x e =
        c • (differentialOne rationalLevel (functionRepresentation ρ Edges) u).val x e := by
      rw [map_smul]
      rfl
    rw [e1, e2, hu x e]

/-- The restriction of global cocycles to a maximal stratum is linear. -/
def restrictionCocycleRepLinear (ρ : Representation ℂ RationalGL3 V) (side : Side) :
    cocycles rationalLevel ρ →ₗ[ℂ] cocycles rationalLevel (flagRepresentation ρ side) where
  toFun := restrictionCocycleRep ρ side
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `globalCoordinatesRep` is linear. -/
def globalCoordinatesRepLinear (ρ : Representation ℂ RationalGL3 V) :
    cocycles rationalLevel ρ →ₗ[ℂ] StratumH2Rep ρ .plane × StratumH2Rep ρ .line :=
  LinearMap.prod
    ((classOf rationalLevel (flagRepresentation ρ .plane)).comp
      (restrictionCocycleRepLinear ρ .plane))
    ((classOf rationalLevel (flagRepresentation ρ .line)).comp
      (restrictionCocycleRepLinear ρ .line))

theorem globalCoordinatesRepLinear_apply (ρ : Representation ℂ RationalGL3 V)
    (c : cocycles rationalLevel ρ) :
    globalCoordinatesRepLinear ρ c = globalCoordinatesRep ρ c := rfl

/-- **The dual global cocycle.** A global cocycle `c` of `E` gives the global cocycle
`x ↦ c(φ x)` of `E* = ρ ∘ φ`. -/
def phiCocycle (ρ : Representation ℂ RationalGL3 V) :
    cocycles rationalLevel ρ →ₗ[ℂ] cocycles rationalLevel (dualRep ρ) where
  toFun c := ⟨⟨fun x => c.val.val (fun i => dualInvolution (x i)), by
    intro γ x
    have hlevel : dualInvolution γ.val ∈ rationalLevel :=
      dualInvolution_mem_rationalLevel γ.property
    have h := c.val.property ⟨dualInvolution γ.val, hlevel⟩ (fun i => dualInvolution (x i))
    have hv : (fun i => dualInvolution (γ.val * x i)) =
        fun i => dualInvolution γ.val * dualInvolution (x i) := by
      funext i
      exact map_mul dualInvolution _ _
    change c.val.val (fun i => dualInvolution (γ.val * x i)) =
      ρ (dualInvolution γ.val) (c.val.val (fun i => dualInvolution (x i)))
    rw [hv]
    exact h⟩, by
    funext x
    have h := congrFun c.property (fun i => dualInvolution (x i))
    change c.val.val (fun i => dualInvolution ((![x 1, x 2, x 3] : Fin 3 → RationalGL3) i)) -
        c.val.val (fun i => dualInvolution ((![x 0, x 2, x 3] : Fin 3 → RationalGL3) i)) +
        c.val.val (fun i => dualInvolution ((![x 0, x 1, x 3] : Fin 3 → RationalGL3) i)) -
        c.val.val (fun i => dualInvolution ((![x 0, x 1, x 2] : Fin 3 → RationalGL3) i)) = 0
    rw [phi_vec3, phi_vec3, phi_vec3, phi_vec3]
    exact h⟩
  map_add' c c' := rfl
  map_smul' a c := rfl

end TernaryPeriodPolynomials.Argument.FacePairingFull.Dual
