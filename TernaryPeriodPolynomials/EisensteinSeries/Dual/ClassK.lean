module

public import TernaryPeriodPolynomials.EisensteinSeries.Dual.PhiClass
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.FormClass
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.CuspRestriction
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.Values
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.GammaNSeries
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.GramBridge
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Dual.ConstantTerms

@[expose] public section


open CategoryTheory

/-!
# The comparison of the `Γ(N)` dual class `ȷ̃^* x ∈ H²(Γ(N), E^∨)` with the rational cocycle model of `E*`

Formalized by Claude Sonnet 5.5.

And the boundary-building cochain model of `FacePairingFull/Dual/ConstantTerms`, where `E* = E ∘ φ` (`dualRep`) and global classes live in `H2 rationalLevel`.

* `dualPrincipal N = φ⁻¹(Γ ∩ Γ(N))`, a normal finite-index subgroup of the level group (`φ` preserves it);
* `dualPsi`: `φ(Γ(N)) → Γ(N)`, `m ↦ ȷ(φ(m))`, with `dualRhoC (ψ m) = E*(m)` (`dualRep_dualPsi`); `dualClassM`: `H²(Γ(N), E^∨) → H²(φ(Γ(N)), E*)`, the pullback along `ψ` followed by the inverse bridge;
* **`dualClassK`** = `trToLevel ∘ dualClassM : H²(Γ(N), E^∨) → H²(Γ, E*)` (the level descent / corestriction to `K†`, the exact analogue of the `classK` for `E`);
* **`dualClassK_jPullC`**: `dualClassK (ȷ̃^* x) = φ^*(classK x)` (naturality of the transfer, `PhiClass.trH2_phiH2`, and of the bridge, `PhiClass.bridge_phiH2`);
* `classOf_phiCocycle_dualClassK`: a global cocycle `c` representing `classK x` has `phiCocycle c` representing `dualClassK (ȷ̃^* x)`;
* **`dual_model_of_gammaN`** / `dual_model_of_cusps`: for `x` locally inner at every plane (equivalently mixed cuspidal at every plane cusp), the maximal coordinates of `phiCocycle c` are inner (`r_B = 0`), `r_Q^∨ = ȷ`-transport of `r_P`,
  and `r_P^∨ = T^∨ r_Q^∨` for `T^∨ = (ȷ-transport) ∘ T ∘ (ȷ-transport)⁻¹`, `T` the map of `line_constant_term_comparison`;
* `dualFormClassK`, `dualFormClassK_eq`, `cxGen_dualSeriesClass`, `dualClassK_cxGen_dualSeries`: the same for the actual dual series `ȷ̃^* ℰ_P(ω_f)` (`dualSeriesClass_gammaN`).

NOT proved (the adelic lift): the `dual_constant_terms` is a statement for EVERY inner line class `η` of `E*` in `H2 rationalLevel`; here only the classes in the image of `dualClassK` (dual series of `Γ(N)` classes) are covered, and the identification of the plane
coordinate with the cusp-form seed classes is S6/the constant-term package (`PlaneLocallyInner`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinDual

open GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Argument.LevelTransfer
  TernaryPeriodPolynomials.Argument.SeedC3S4c

/-! ## Comparison of the Γ(N) dual coefficient system with the model's `E*` -/

open scoped MatrixGroups
open GeneralEisenstein TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.Argument.FormClassK TernaryPeriodPolynomials.Argument.FacePairingFull.Dual
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.EisensteinClass

/-- The coefficient system `E_n` of the model. -/
abbrev rhoE (n : ℕ) := rationalCoefficientComponent n trivialCharacter

section DualPrincipal

variable (N : ℕ)

/-- `φ(Γ ∩ Γ(N)) = φ⁻¹(Γ ∩ Γ(N))`: the principal subgroup of the dual coefficient system `E* = E ∘ φ` (a normal finite-index subgroup of the level group). -/
def dualPrincipal : Subgroup RationalGL3 := (levelPrincipal N).comap dualInvolution

theorem dualPrincipal_iff : ∀ x : RationalGL3, x ∈ dualPrincipal N ↔ dualInvolution x ∈ levelPrincipal N := fun _ => Iff.rfl

theorem mem_rationalLevel_iff (x : RationalGL3) : x ∈ rationalLevel ↔ dualInvolution x ∈ rationalLevel :=
  ⟨dualInvolution_mem_rationalLevel, fun h => by
    simpa [dualInvolution_involutive] using dualInvolution_mem_rationalLevel h⟩

theorem dualPrincipal_le : dualPrincipal N ≤ rationalLevel := fun x hx =>
  (mem_rationalLevel_iff x).2 (levelPrincipal_le N hx)

theorem dualPrincipal_norm : ∀ s ∈ rationalLevel, ∀ m ∈ dualPrincipal N, s⁻¹ * m * s ∈ dualPrincipal N := by
  intro s hs m hm
  show dualInvolution (s⁻¹ * m * s) ∈ levelPrincipal N
  rw [map_mul, map_mul, map_inv]
  exact levelPrincipal_norm N _ ((mem_rationalLevel_iff s).1 hs) _ hm

/-- The bijection `Γ/φ(Γ(N)) ≃ Γ/(Γ ∩ Γ(N))` induced by `φ`. -/
def dualQuotEquiv : (rationalLevel ⧸ (dualPrincipal N).subgroupOf rationalLevel) ≃
    (rationalLevel ⧸ (levelPrincipal N).subgroupOf rationalLevel) :=
  quotEquiv dualInvolution dualInvolution_involutive (levelPrincipal N) (dualPrincipal N) rationalLevel
    (dualPrincipal_iff N) mem_rationalLevel_iff

variable [NeZero N]

instance dualPrincipal_finiteRelIndex : (dualPrincipal N).IsFiniteRelIndex rationalLevel := by
  have : Finite (rationalLevel ⧸ (dualPrincipal N).subgroupOf rationalLevel) :=
    Finite.of_equiv _ (dualQuotEquiv N).symm
  rw [Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero]
  exact Nat.pos_iff_ne_zero.mp Nat.card_pos

end DualPrincipal

/-- `E* = E ∘ φ` by definition. -/
theorem dualRep_phi {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ RationalGL3 V) (g : RationalGL3) :
    dualRep ρ g = ρ (dualInvolution g) := rfl

section Comparison

variable (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (hN : 3 ≤ N) (n : ℕ)

/-- `α = φ` as a homomorphism `φ(Γ(N)) → Γ ∩ Γ(N)`. -/
abbrev phiSub : dualPrincipal N →* levelPrincipal N :=
  alphaSub dualInvolution (levelPrincipal N) (dualPrincipal N) (dualPrincipal_iff N)

/-- The group homomorphism `ψ : φ(Γ(N)) → Γ(N)`, `m ↦ ȷ(φ(m))` (via `Γ(N) ≅ Γ ∩ Γ(N)`). -/
def dualPsi : dualPrincipal N →* gammaN N :=
  (jN N).comp ((principalEquiv N h3 hN).symm.toMonoidHom.comp (phiSub N))

omit [NeZero N] in
theorem jN_jN (g : gammaN N) : jN N (jN N g) = g := Subtype.ext (jmath_jmath g.1)

omit [NeZero N] in
theorem dualRep_dualPsi (m : dualPrincipal N) :
    ((dualRep (rhoE n)).comp (dualPrincipal N).subtype) m = dualRhoC N n (dualPsi N h3 hN m) := by
  have h1 : dualRhoC N n (dualPsi N h3 hN m) = gammaRhoC (gammaN N) n ((principalEquiv N h3 hN).symm (phiSub N m)) := by
    change gammaRhoC (gammaN N) n (jN N (jN N ((principalEquiv N h3 hN).symm (phiSub N m)))) = _
    rw [jN_jN]
  rw [h1, ← rho_principalEquiv N h3 hN n, MulEquiv.apply_symm_apply]
  rfl

/-- The identity intertwiner over `ψ`. -/
def dualPsiCoeff : Rep.res (dualPsi N h3 hN) (Rep.of (dualRhoC N n)) ⟶
    Rep.of ((dualRep (rhoE n)).comp (dualPrincipal N).subtype) :=
  resMorK (dualPsi N h3 hN) ((dualRep (rhoE n)).comp (dualPrincipal N).subtype) (dualRhoC N n) (dualRep_dualPsi N h3 hN n)

/-- **The comparison map to the principal dual subgroup**: `H²(Γ(N), E^∨) → H²(φ(Γ(N)), E*)` in the homogeneous model, pullback along `m ↦ ȷ(φ(m))` followed by the bridge. -/
def dualClassM : groupCohomology.H2 (Rep.of (dualRhoC N n)) →ₗ[ℂ] H2 (dualPrincipal N) (dualRep (rhoE n)) :=
  (bridge (dualRep (rhoE n)) (dualPrincipal N)).symm.toLinearMap ∘ₗ
    (groupCohomology.map (dualPsi N h3 hN) (dualPsiCoeff N h3 hN n) 2).hom

/-- **The comparison map to the rational cocycle model**: the transfer to the level group `Γ = rationalLevel` of `dualClassM`.  `H²(Γ(N), E^∨) → H²(Γ, E*)`. -/
def dualClassK : groupCohomology.H2 (Rep.of (dualRhoC N n)) →ₗ[ℂ] H2 rationalLevel (dualRep (rhoE n)) :=
  trToLevel (dualRep (rhoE n)) (dualPrincipal N) (dualPrincipal_le N) (dualPrincipal_norm N) ∘ₗ dualClassM N h3 hN n

theorem map_map_eq {G H1 H2 K : Type} [Group G] [Group H1] [Group H2] [Group K]
    {A : Rep ℂ K} {B1 : Rep ℂ H1} {B2 : Rep ℂ H2} {C : Rep ℂ G}
    (f1 : H1 →* K) (g1 : G →* H1) (f2 : H2 →* K) (g2 : G →* H2)
    (φ1 : Rep.res f1 A ⟶ B1) (ψ1 : Rep.res g1 B1 ⟶ C) (φ2 : Rep.res f2 A ⟶ B2) (ψ2 : Rep.res g2 B2 ⟶ C)
    (hfg : f1.comp g1 = f2.comp g2)
    (hlin : ((Rep.resFunctor g1).map φ1 ≫ ψ1).hom.toLinearMap = ((Rep.resFunctor g2).map φ2 ≫ ψ2).hom.toLinearMap)
    (x : groupCohomology.H2 A) :
    (groupCohomology.map g1 ψ1 2).hom ((groupCohomology.map f1 φ1 2).hom x) =
      (groupCohomology.map g2 ψ2 2).hom ((groupCohomology.map f2 φ2 2).hom x) := by
  have h1 := congrArg (fun m => m.hom x) (groupCohomology.map_comp f1 g1 φ1 ψ1 2).symm
  have h2 := congrArg (fun m => m.hom x) (groupCohomology.map_comp f2 g2 φ2 ψ2 2).symm
  have h3 := congrArg (fun m => m.hom x) (groupCohomology.map_congr hfg hlin 2)
  exact h1.trans (h3.trans h2.symm)

omit [NeZero N] in
theorem dualClassM_jPullC (x : groupCohomology.H2 (gammaRep (gammaN N) n)) :
    dualClassM N h3 hN n (jPullC N n x) =
      phiH2 dualInvolution (rhoE n) (dualRep (rhoE n)) (dualRep_phi _) (levelPrincipal N) (dualPrincipal N) (dualPrincipal_iff N)
        (classPrincipal N h3 n hN x) := by
  unfold dualClassM
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_eq]
  rw [bridge_phiH2]
  have hb : bridge (rhoE n) (levelPrincipal N) (classPrincipal N h3 n hN x) = (principalIso N h3 n hN).hom.hom x := by
    unfold classPrincipal
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [hb]
  refine map_map_eq (jN N) (dualPsi N h3 hN) (principalEquiv N h3 hN).symm.toMonoidHom (phiSub N) _ _ _ _ ?_ ?_ x
  · ext m
    simp [dualPsi, jN_jN]
  · ext v
    rfl

end Comparison

/-! ## The dual class in the model: representatives and constant terms -/

section StarClasses

open TernaryPeriodPolynomials.Argument.FacePairingFull.Dual
open TernaryPeriodPolynomials.Duality

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- The class-level transport of `transportCocycles`. -/
def transportH2 {X X' : Type} [MulAction RationalGL3 X] [MulAction RationalGL3 X']
    (ρ ρ' : Representation ℂ RationalGL3 V) (hρ : ∀ g, ρ' g = ρ (dualInvolution g))
    (m : X' → X) (hm : ∀ (g : RationalGL3) F, m (g • F) = dualInvolution g • m F) :
    H2 rationalLevel (functionRepresentation ρ X) →ₗ[ℂ] H2 rationalLevel (functionRepresentation ρ' X') :=
  Submodule.mapQ _ _ (transportCocycles ρ ρ' hρ m hm) (by
    rintro _ ⟨u, rfl⟩
    exact ⟨transportCochains ρ ρ' hρ m hm 1 u, (transportCocycles_boundaryMap ρ ρ' hρ m hm u).symm⟩)

theorem transportH2_classOf {X X' : Type} [MulAction RationalGL3 X] [MulAction RationalGL3 X']
    (ρ ρ' : Representation ℂ RationalGL3 V) (hρ : ∀ g, ρ' g = ρ (dualInvolution g))
    (m : X' → X) (hm : ∀ (g : RationalGL3) F, m (g • F) = dualInvolution g • m F)
    (z : cocycles rationalLevel (functionRepresentation ρ X)) :
    transportH2 ρ ρ' hρ m hm (classOf rationalLevel (functionRepresentation ρ X) z) =
      classOf rationalLevel (functionRepresentation ρ' X') (transportCocycles ρ ρ' hρ m hm z) := rfl

variable (ρ : Representation ℂ RationalGL3 V)

/-- Plane classes of `E` to line classes of `E*`. -/
def toLineStarH : StratumH2Rep ρ .plane →ₗ[ℂ] StratumH2Rep (dualRep ρ) .line :=
  transportH2 ρ (dualRep ρ) (fun _ => rfl) dualFlag dualFlag_smul

/-- Line classes of `E` to plane classes of `E*`. -/
def toPlaneStarH : StratumH2Rep ρ .line →ₗ[ℂ] StratumH2Rep (dualRep ρ) .plane :=
  transportH2 ρ (dualRep ρ) (fun _ => rfl) dualPlaneFlag dualPlaneFlag_smul

/-- Line classes of `E*` to plane classes of `E`. -/
def fromLineStarH : StratumH2Rep (dualRep ρ) .line →ₗ[ℂ] StratumH2Rep ρ .plane :=
  transportH2 (dualRep ρ) ρ (dualRep_dualRep_apply ρ) dualPlaneFlag dualPlaneFlag_smul

theorem fromLineStarH_toLineStarH (a : StratumH2Rep ρ .plane) : fromLineStarH ρ (toLineStarH ρ a) = a := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  exact congrArg (classOf rationalLevel (flagRepresentation ρ .plane)) (fromLineStar_toLineStar ρ z)

theorem toLineStarH_classOf (z : cocycles rationalLevel (flagRepresentation ρ .plane)) :
    toLineStarH ρ (classOf rationalLevel (flagRepresentation ρ .plane) z) =
      classOf rationalLevel (flagRepresentation (dualRep ρ) .line) (toLineStar ρ z) := rfl

theorem toPlaneStarH_classOf (z : cocycles rationalLevel (flagRepresentation ρ .line)) :
    toPlaneStarH ρ (classOf rationalLevel (flagRepresentation ρ .line) z) =
      classOf rationalLevel (flagRepresentation (dualRep ρ) .plane) (toPlaneStar ρ z) := rfl

theorem innerBoundaryRep_toLineStarH (a : StratumH2Rep ρ .plane) (h : InnerBoundaryRep ρ .plane a) :
    InnerBoundaryRep (dualRep ρ) .line (toLineStarH ρ a) := by
  obtain ⟨z, hz, u, hu⟩ := h
  refine ⟨toLineStar ρ z, ?_, toEdgeStar ρ u,
    edgeExact_transport ρ (dualRep ρ) (fun _ => rfl) dualFlag dualFlag_smul (endpoint .plane) (endpoint .line)
      (fun e => (endpoint_plane_dualEdge e).symm) z u hu⟩
  rw [← hz]
  rfl

theorem innerBoundaryRep_toPlaneStarH (a : StratumH2Rep ρ .line) (h : InnerBoundaryRep ρ .line a) :
    InnerBoundaryRep (dualRep ρ) .plane (toPlaneStarH ρ a) := by
  obtain ⟨z, hz, u, hu⟩ := h
  refine ⟨toPlaneStar ρ z, ?_, toEdgeStar ρ u,
    edgeExact_transport ρ (dualRep ρ) (fun _ => rfl) dualPlaneFlag dualPlaneFlag_smul (endpoint .line) (endpoint .plane)
      (fun e => (endpoint_line_dualEdge e).symm) z u hu⟩
  rw [← hz]
  rfl

/-- The class of the `φ`-transport of a global cocycle is the `φ`-transport of its class. -/
theorem classOf_phiCocycle (c : cocycles rationalLevel ρ) :
    classOf rationalLevel (dualRep ρ) (phiCocycle ρ c) =
      phiH2 dualInvolution ρ (dualRep ρ) (dualRep_phi ρ) rationalLevel rationalLevel mem_rationalLevel_iff
        (classOf rationalLevel ρ c) := rfl

/-- The maximal coordinates of the `φ`-transport of a global cocycle are the `ȷ`-transports of its coordinates. -/
theorem globalCoordinatesRep_phiCocycle (c : cocycles rationalLevel ρ) :
    globalCoordinatesRep (dualRep ρ) (phiCocycle ρ c) =
      (toPlaneStarH ρ (globalCoordinatesRep ρ c).2, toLineStarH ρ (globalCoordinatesRep ρ c).1) := rfl

end StarClasses

section Constants

open TernaryPeriodPolynomials.Argument.FacePairingFull.Dual TernaryPeriodPolynomials.Argument

variable (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (hN : 3 ≤ N) (n : ℕ)

/-- **`dualClassK` carries `ȷ̃^*x` to the `φ`-transport of the `K†`-corestriction of `x`** (naturality of the transfer, the bridge and the principal-subgroup identification). -/
theorem dualClassK_jPullC (x : groupCohomology.H2 (gammaRep (gammaN N) n)) :
    dualClassK N h3 hN n (jPullC N n x) =
      phiH2 dualInvolution (rhoE n) (dualRep (rhoE n)) (dualRep_phi _) rationalLevel rationalLevel mem_rationalLevel_iff
        (classK N h3 hN n x) := by
  unfold dualClassK
  rw [LinearMap.comp_apply, dualClassM_jPullC]
  exact trH2_phiH2 dualInvolution dualInvolution_involutive (rhoE n) (dualRep (rhoE n)) (dualRep_phi _)
    (levelPrincipal N) (dualPrincipal N) rationalLevel (dualPrincipal_iff N) mem_rationalLevel_iff
    (levelPrincipal_le N) (levelPrincipal_norm N) (dualPrincipal_le N) (dualPrincipal_norm N) _

/-- **Representatives**: a global cocycle `c` representing `classK x` has `φ`-transport `phiCocycle c` representing `dualClassK (ȷ̃^* x)`. -/
theorem classOf_phiCocycle_dualClassK (x : groupCohomology.H2 (gammaRep (gammaN N) n))
    (c : cocycles rationalLevel (rhoE n)) (hc : classOf rationalLevel (rhoE n) c = classK N h3 hN n x) :
    classOf rationalLevel (dualRep (rhoE n)) (phiCocycle (rhoE n) c) = dualClassK N h3 hN n (jPullC N n x) := by
  rw [classOf_phiCocycle, hc, dualClassK_jPullC]

/-- **The model statement `ar:eq:dualconstantterms` for the dual of a `Γ(N)` class that is locally inner at every plane** (`4 ≤ n`).

If the class `x ∈ H²(Γ(N), E_n)_ℂ` (e.g. the complexified `ℰ_P`) is locally inner at every rational plane, then for every global cocycle `c` of `E` representing its `K†`-corestriction, the `φ`-transport
`c' = phiCocycle c` represents the model class `dualClassK (ȷ̃^* x)` of `ȷ̃^* x ∈ H²(Γ(N), E^∨)`, both maximal coordinates of `c'` are inner (`r_B = 0`), `r_Q^∨ c'` is the `ȷ`-transport of `r_P c`, and `r_P^∨ c' = T^∨ r_Q^∨ c'`
where `T^∨ = (ȷ-transport) ∘ T ∘ (ȷ-transport)⁻¹` for the canonical map `T` of `line_constant_term_comparison`. -/
theorem dual_model_of_gammaN (hn : 4 ≤ n) (x : groupCohomology.H2 (gammaRep (gammaN N) n))
    (hx : PlaneLocallyInner N h3 hN n x) :
    ∃ T : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line,
      BadPlaneInjectivity.IsUniquenessMap n trivialCharacter T ∧
      ∀ c : cocycles rationalLevel (rhoE n), classOf rationalLevel (rhoE n) c = classK N h3 hN n x →
        classOf rationalLevel (dualRep (rhoE n)) (phiCocycle (rhoE n) c) = dualClassK N h3 hN n (jPullC N n x) ∧
        InnerBoundaryRep (dualRep (rhoE n)) .plane (globalCoordinatesRep (dualRep (rhoE n)) (phiCocycle (rhoE n) c)).1 ∧
        InnerBoundaryRep (dualRep (rhoE n)) .line (globalCoordinatesRep (dualRep (rhoE n)) (phiCocycle (rhoE n) c)).2 ∧
        (globalCoordinatesRep (dualRep (rhoE n)) (phiCocycle (rhoE n) c)).2 =
          toLineStarH (rhoE n) (globalCoordinates n trivialCharacter c).1 ∧
        (globalCoordinatesRep (dualRep (rhoE n)) (phiCocycle (rhoE n) c)).1 =
          toPlaneStarH (rhoE n) (T (fromLineStarH (rhoE n)
            (globalCoordinatesRep (dualRep (rhoE n)) (phiCocycle (rhoE n) c)).2)) := by
  obtain ⟨T, hT, -, hcl⟩ := classK_line_eq_T N h3 hN n hn x hx
  refine ⟨T, hT, fun c hc => ?_⟩
  obtain ⟨hP, hL, hTc⟩ := hcl c hc
  have hcoord : globalCoordinatesRep (dualRep (rhoE n)) (phiCocycle (rhoE n) c) =
      (toPlaneStarH (rhoE n) (globalCoordinates n trivialCharacter c).2,
        toLineStarH (rhoE n) (globalCoordinates n trivialCharacter c).1) :=
    globalCoordinatesRep_phiCocycle (rhoE n) c
  have hc1 := congrArg Prod.fst hcoord
  have hc2 := congrArg Prod.snd hcoord
  refine ⟨classOf_phiCocycle_dualClassK N h3 hN n x c hc, ?_, ?_, hc2, ?_⟩
  · rw [hc1]
    exact innerBoundaryRep_toPlaneStarH (rhoE n) _ hL
  · rw [hc2]
    exact innerBoundaryRep_toLineStarH (rhoE n) _ hP
  · have hF : fromLineStarH (rhoE n) (globalCoordinatesRep (dualRep (rhoE n)) (phiCocycle (rhoE n) c)).2 =
        (globalCoordinates n trivialCharacter c).1 :=
      (congrArg (fromLineStarH (rhoE n)) hc2).trans (fromLineStarH_toLineStarH _ _)
    exact hc1.trans (congrArg (toPlaneStarH (rhoE n)) (hTc.trans (congrArg T hF.symm)))

end Constants

section Series

open TernaryPeriodPolynomials.Argument.FacePairingFull.Dual TernaryPeriodPolynomials.Argument
open TernaryPeriodPolynomials.Argument.Statements.EisensteinClass

variable (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (hN : 3 ≤ N) (n : ℕ)

/-- **The model class of the dual series at `Γ(N)`**: the comparison map applied to the complexified `ȷ̃^* ℰ_P(ω_f)`. -/
def dualFormClassK (hn : 4 ≤ n) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    H2 rationalLevel (dualRep (rhoE n)) :=
  dualClassK N h3 hN n (jPullC N n (eisensteinClassC_gammaN N n f hn))

/-- The complexified real dual series class `ℰ_Q^∨ = ȷ̃^* ℰ_P` is `jPullC` of the complexified class of `ℰ_P`. -/
theorem cxGen_dualSeriesClass (hn : 4 ≤ n) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    cxGen (dualRhoN N n) (dualRhoC N n) (fun _ _ => rfl) (dualSeriesClass_gammaN N n f hn) =
      jPullC N n (eisensteinClassC_gammaN N n f hn) := by
  rw [dualSeriesClass_gammaN_eq, cxGen_jPull, cxGen_eq_complexify]
  rfl

/-- **`ȷ̃^*ℰ_P` in the model is the `φ`-transport of the model form class `formClassK`** (the class whose coordinates the target `constant_terms` describes). -/
theorem dualFormClassK_eq (hn : 4 ≤ n) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    dualFormClassK N h3 hN n hn f =
      phiH2 dualInvolution (rhoE n) (dualRep (rhoE n)) (dualRep_phi _) rationalLevel rationalLevel mem_rationalLevel_iff
        (FormClassK.formClassK N h3 hN n hn f) :=
  dualClassK_jPullC N h3 hN n _

/-- The model class of the real dual series, via complexification. -/
theorem dualClassK_cxGen_dualSeries (hn : 4 ≤ n) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    dualClassK N h3 hN n (cxGen (dualRhoN N n) (dualRhoC N n) (fun _ _ => rfl) (dualSeriesClass_gammaN N n f hn)) =
      dualFormClassK N h3 hN n hn f := by
  rw [cxGen_dualSeriesClass]
  rfl

/-- **The model statement in the cusp-by-cusp form delivered by the `Γ(N)` constant-term package**: if the restriction of `x` to every plane cusp `h⁻¹Ph` is mixed cuspidal, the model dual statement of
`dual_model_of_gammaN` holds for `ȷ̃^* x`. -/
theorem dual_model_of_cusps (hn : 4 ≤ n) (x : groupCohomology.H2 (gammaRep (gammaN N) n))
    (hx : ∀ h : SL(3, ℤ), FormClassK.resAtC N h n x ∈ SeedC3S4c.faceLocallyInner N h n) :
    ∃ T : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line,
      BadPlaneInjectivity.IsUniquenessMap n trivialCharacter T ∧
      ∀ c : cocycles rationalLevel (rhoE n), classOf rationalLevel (rhoE n) c = FormClassK.classK N h3 hN n x →
        classOf rationalLevel (dualRep (rhoE n)) (phiCocycle (rhoE n) c) = dualClassK N h3 hN n (jPullC N n x) ∧
        InnerBoundaryRep (dualRep (rhoE n)) .plane (globalCoordinatesRep (dualRep (rhoE n)) (phiCocycle (rhoE n) c)).1 ∧
        InnerBoundaryRep (dualRep (rhoE n)) .line (globalCoordinatesRep (dualRep (rhoE n)) (phiCocycle (rhoE n) c)).2 ∧
        (globalCoordinatesRep (dualRep (rhoE n)) (phiCocycle (rhoE n) c)).2 =
          toLineStarH (rhoE n) (globalCoordinates n trivialCharacter c).1 ∧
        (globalCoordinatesRep (dualRep (rhoE n)) (phiCocycle (rhoE n) c)).1 =
          toPlaneStarH (rhoE n) (T (fromLineStarH (rhoE n)
            (globalCoordinatesRep (dualRep (rhoE n)) (phiCocycle (rhoE n) c)).2)) :=
  dual_model_of_gammaN N h3 hN n hn x ((FormClassK.planeLocallyInner_iff_cusps N n h3 hN x).2 hx)

end Series

end TernaryPeriodPolynomials.Argument.EisensteinDual
