module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelTransfer.Transfer
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelTransfer.Bridge

@[expose] public section


/-!
# Link L2 of the model comparison: level group versus `Γ(6)`

Formalized by Claude Sonnet 5.5.

**Statement.**  In the homogeneous-cochain model of `GeneralEisenstein.Homogeneous`
(`TernaryPeriodPolynomials/ArithmeticCohomology/Defs/HomogeneousCohomology.lean`: equivariant cochains on ambient vertices
`G^{k+1}`, `H2 Γ ρ = cocycles / boundaries`), let `N ≤ S` be subgroups of `G` with `N` normalized by `S`
and `N` of finite index in `S` (`Fintype (S ⧸ N.subgroupOf S)`), and `ρ` any `ℂ`-linear representation of
`G`.  Then restriction of cochains induces a linear isomorphism
`H²(S, ρ) ≃ H²(N, ρ)^{S/N}` onto the `S`-invariant classes (`resH2Equiv`), where `s ∈ S` acts on `N`-cochains
by `(s • f)(x) = ρ(s) f(s⁻¹ x)` (`actFun`, descended to `actH2`).  For `N = S ⊓ M`, `M` normal in the ambient
group (e.g. `M = Γ(6)` inside `GL₃`), the normalization hypothesis holds (`normalizes_inf`).

**Proof.**  The `S`-equivariant cochains are exactly the `S`-fixed `N`-cochains (`isEq_iff_fixed`); the
averaging operator `|S/N|⁻¹ ∑_{q ∈ S/N} q • (-)` projects the `N`-cochains onto them (`isEq_avg`, `actFun_avg`,
`avg_of_isEq_S`) and commutes with the differentials (`avg_rd1`, `avg_rd2`).  Injectivity: a cocycle of `S` that is a
coboundary of an `N`-cochain `c` is the coboundary of `avg c` (`resH2_injective`).  Image: a class invariant under
`S` is the class of its average (`mem_range_resH2_iff`).

**Compatibility.**  The isomorphism is the restriction map itself, hence compatible with restriction between
such subgroups (`resH2_comp`), and with every cochain-level construction given by a `ρ`-independent formula
(cup products into degree four, the trace): these act on the same underlying functions on `G^{k+1}` for `S` and `N`.

**Bridge to Mathlib**.  `bridge ρ Γ : H2 Γ ρ ≃ₗ[ℂ]
groupCohomology.H2 (Rep.of (ρ.comp Γ.subtype))` for an arbitrary group `G`, subgroup `Γ` and
`ρ : Representation ℂ G V`; the class of a homogeneous cocycle `F` goes to the class of the inhomogeneous
cocycle `(a, b) ↦ F(1, a, ab)` (`bridge_mk`, `bridgeCocycle_apply`).  It is natural in the subgroup
(`bridge_res`: model restriction `resH2` versus `groupCohomology.map` of the inclusion) and in
conjugation (`bridge_conj`: Mathlib's map for `γ ↦ gγg⁻¹` with intertwiner `ρ(g⁻¹)` is inverse to the model
action `actH2Conj` by `(g • F)(x) = ρ(g)F(g⁻¹x)`; proved with the prism identity `prism_identity`).
Consequently the level transfer holds on Mathlib's `groupCohomology` itself: the image of
`H²(S, ρ|S) → H²(N, ρ|N)` is exactly the classes fixed by Mathlib's conjugation action of `S`
(`mem_range_resMathlib_iff`).

**Scope.**  Only degree two is available, because the model defines only `cochains` in degrees `1, 2` and the
differentials `differentialOne`, `differentialTwo` (cocycles are the kernel of the latter into all functions on
`G⁴`).  This is exactly the degree used by the face pairing.  The actual bridge from the model to Mathlib's
`groupCohomology.H2`, including restriction and conjugation compatibility, is exported above.
The comparison with the geometric `H²(Γ(6), V)` of the original library
(links L1, L3), and the degree-three and cup/trace comparisons, are not addressed here.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.LevelTransfer

open GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.LevelTransfer

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
  {N S : Subgroup G} [Fintype (S ⧸ N.subgroupOf S)]

/-- The `S`-invariant classes of `H²(N, ρ)` (`S` normalizes `N`). -/
abbrev invariants (hnorm : ∀ s ∈ S, ∀ n ∈ N, s⁻¹ * n * s ∈ N) : Submodule ℂ (H2 N ρ) :=
  invariantsH2 ρ hnorm

/-- **Level transfer, degree two**: restriction `H²(S, ρ) ≃ H²(N, ρ)^{S/N}`. -/
def levelTransfer (hNS : N ≤ S) (hnorm : ∀ s ∈ S, ∀ n ∈ N, s⁻¹ * n * s ∈ N) :
    H2 S ρ ≃ₗ[ℂ] invariants ρ hnorm :=
  resH2Equiv ρ hNS hnorm

/-- The isomorphism is the restriction map. -/
theorem levelTransfer_apply (hNS : N ≤ S) (hnorm : ∀ s ∈ S, ∀ n ∈ N, s⁻¹ * n * s ∈ N)
    (x : H2 S ρ) : ((levelTransfer ρ hNS hnorm x : invariants ρ hnorm) : H2 N ρ) = resH2 ρ hNS x :=
  rfl

/-- Restriction is injective. -/
theorem res_injective (hNS : N ≤ S) (hnorm : ∀ s ∈ S, ∀ n ∈ N, s⁻¹ * n * s ∈ N) :
    Function.Injective (resH2 ρ hNS) :=
  resH2_injective ρ hNS hnorm

/-- The image of restriction is exactly the `S`-invariant classes. -/
theorem mem_range_res_iff (hNS : N ≤ S) (hnorm : ∀ s ∈ S, ∀ n ∈ N, s⁻¹ * n * s ∈ N)
    (x : H2 N ρ) :
    x ∈ LinearMap.range (resH2 ρ hNS) ↔ ∀ (s : G) (hs : s ∈ S), actH2 ρ s (hnorm s hs) x = x :=
  mem_range_resH2_iff ρ hNS hnorm x

/-- For a normal subgroup `M` of the ambient group, `S ⊓ M` is normalized by `S`. -/
theorem normalizes_inf' (M : Subgroup G) [M.Normal] (S : Subgroup G) :
    ∀ s ∈ S, ∀ n ∈ S ⊓ M, s⁻¹ * n * s ∈ S ⊓ M :=
  normalizes_inf M S

/-! ### The bridge to Mathlib's group cohomology -/

/-- **Bridge** `H²_{hom}(Γ, ρ) ≃ H²(Γ, ρ|Γ)` (Mathlib), `F ↦ [(a, b) ↦ F(1, a, ab)]`. -/
def bridge (Γ : Subgroup G) : H2 Γ ρ ≃ₗ[ℂ] groupCohomology.H2 (Rep.of (ρ.comp Γ.subtype)) :=
  _root_.TernaryPeriodPolynomials.Argument.LevelTransfer.bridge ρ Γ

/-- Naturality in the subgroup. -/
theorem bridge_res {Γ Γ' : Subgroup G} (h : Γ' ≤ Γ) (x : H2 Γ ρ) :
    (groupCohomology.map (Subgroup.inclusion h) (_root_.TernaryPeriodPolynomials.Argument.LevelTransfer.resRep ρ h) 2).hom (bridge ρ Γ x) =
      bridge ρ Γ' (resH2 ρ h x) :=
  _root_.TernaryPeriodPolynomials.Argument.LevelTransfer.bridge_res ρ h x

/-- Naturality in conjugation. -/
theorem bridge_conj {Δ Δ' : Subgroup G} (g : G) (hg : _root_.TernaryPeriodPolynomials.Argument.LevelTransfer.IsConj Δ Δ' g) (x : H2 Δ ρ) :
    (groupCohomology.map (_root_.TernaryPeriodPolynomials.Argument.LevelTransfer.conjHom g hg) (_root_.TernaryPeriodPolynomials.Argument.LevelTransfer.conjRep ρ g hg) 2).hom
        (bridge ρ Δ' (_root_.TernaryPeriodPolynomials.Argument.LevelTransfer.actH2Conj ρ g hg x)) = bridge ρ Δ x :=
  _root_.TernaryPeriodPolynomials.Argument.LevelTransfer.bridge_conj ρ g hg x

/-- **Level transfer on Mathlib's `groupCohomology`** (degree two). -/
theorem mem_range_resMathlib_iff (hNS : N ≤ S) (hnorm : ∀ s ∈ S, ∀ n ∈ N, s⁻¹ * n * s ∈ N)
    (y : groupCohomology.H2 (Rep.of (ρ.comp N.subtype))) :
    y ∈ LinearMap.range (_root_.TernaryPeriodPolynomials.Argument.LevelTransfer.resMathlib ρ hNS) ↔
      ∀ (s : G) (hs : s ∈ S), _root_.TernaryPeriodPolynomials.Argument.LevelTransfer.conjAct ρ hnorm hs y = y :=
  _root_.TernaryPeriodPolynomials.Argument.LevelTransfer.mem_range_resMathlib_iff ρ hNS hnorm y

end TernaryPeriodPolynomials.Argument.Statements.LevelTransfer
