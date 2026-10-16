module

public import TernaryPeriodPolynomials.GroupCohomology.SingularComparison.Conjugation

@[expose] public section


/-!
# Link W2: homogeneous chains modulo null chains versus Mathlib's group homology

Formalized by Claude Sonnet 5.5.

**Setting.**  `G` is a group, `Λ ≤ G` a subgroup, `Chains G n = ((Fin (n+1) → G) →₀ ℂ)` the homogeneous
chains of `TernaryPeriodPolynomials.BoundaryDuality.ChainCalculus`, `NullChains Λ n` the span of
the differences `γ·x - x` (`γ ∈ Λ`), `BdryChains Λ n = NullChains Λ n ⊔ range ∂`.

**Statement.**  Let `Zhom Λ j = {c ∈ Chains G (j+1) | ∂c ∈ NullChains Λ j}` (the homogeneous `(j+1)`-cycles
modulo `Λ`-null chains).  There is a `ℂ`-linear map
`bridgeClass Λ j : Zhom Λ j → groupHomology (Rep.res Λ.subtype (Rep.trivial ℂ G ℂ)) (j+1)`
to Mathlib's group homology `H_{j+1}(Λ, ℂ)` (the restriction of the trivial representation of `G` is the trivial
representation of `Λ`) such that

* it is surjective (`bridgeClass_surjective`);
* its kernel is exactly `BdryChains Λ (j+1)`, i.e. two cycles have the same class iff their difference is a
  boundary modulo `Λ`-null chains (`bridgeClass_eq_zero_iff`, `bridgeClass_eq_iff`).  Hence it induces a linear
  isomorphism from `Zhom Λ j / (BdryChains Λ (j+1))` onto `H_{j+1}(Λ, ℂ)`; the quotient type is not formed,
  only the class map with its surjectivity and kernel, which is what the comparison uses;
* it is natural in the subgroup: for `Λ' ≤ Λ`, Mathlib's corestriction
  `groupHomology.map (Subgroup.inclusion h) _ (j+1)` carries the class of `c` modulo `Λ'` to the class of the same
  chain modulo `Λ` (`bridgeClass_natural`);
* it is natural in conjugation: for `g ∈ G` with `g Λ g⁻¹ ≤ Λ'`, the map induced by `γ ↦ gγg⁻¹ : Λ → Λ'` carries
  the class of `c` to the class of the left translate `leftTranslate g (j+1) c`
  (`bridgeClass_conj`), the very operation used for the translated cells of the face pairing;
* it is compatible with the boundary map: the identification of the coinvariant complex of the standard
  resolution with chains modulo null chains commutes with `∂` (`sigma_d`, used in the proof; the connecting
  data is therefore the chain-level `homogeneousBoundary`, with no sign or normalisation).

Degree three (the corner stabilisers) is `j = 2`; degrees two and four are `j = 1` and `j = 3`.

**Proof.**  The standard resolution `Rep.standardComplex` is a projective resolution, so group homology is the
homology of its `Λ`-coinvariants (Mathlib `groupHomologyIso`).
The coinvariants of the permutation module on `G^{n+1}` are chains modulo null chains (`ker_eq_null`), whence a
covering `sigma : Chains G n → (coinvariant complex)_n` with kernel `NullChains`; the homology of a short complex
covered in this way is a quotient of the covering cycles (`coverClass_surjective`, `coverClass_eq_zero_iff`).
Naturality is checked on the chain maps (`chains_incl_comm_gen`, `chains_conj_comm_gen`), the latter using that right
translation acts trivially on homology (`homologyMap_FNrt`, via the explicit homotopy `rtHomotopy`).

**Scope.**  Only trivial coefficients `ℂ`.  The Kronecker pairing with cohomology, and the corestriction
`Λ → Γ(6)` of the averaging operator in Mathlib homology, are not part of this file.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.HomologyBridge

open TernaryPeriodPolynomials.BoundaryDuality.TraceChains (NullChains)
open TernaryPeriodPolynomials.BoundaryDuality.ChainCalculus (Chains BdryChains leftTranslate)

variable {G : Type} [Group G]

/-- The trivial representation of `G` on `ℂ`; its restriction to `Λ` is the trivial representation of `Λ`. -/
abbrev triv : Rep ℂ G := _root_.TernaryPeriodPolynomials.Argument.HomologyBridge.triv

/-- Homogeneous `(j+1)`-cycles modulo `Λ`-null chains: `{c | ∂c ∈ NullChains Λ j}`. -/
abbrev Zhom (Λ : Subgroup G) (j : ℕ) : Submodule ℂ (Chains G (j + 1)) :=
  _root_.TernaryPeriodPolynomials.Argument.HomologyBridge.Zhom Λ j

theorem mem_Zhom (Λ : Subgroup G) (j : ℕ) (c : Chains G (j + 1)) :
    c ∈ Zhom Λ j ↔
      TernaryPeriodPolynomials.TopVanishing.homogeneousBoundary (j + 1) c ∈ NullChains Λ j :=
  _root_.TernaryPeriodPolynomials.Argument.HomologyBridge.mem_Zhom Λ j c

/-- The class of a homogeneous cycle modulo `Λ`-null chains in Mathlib's group homology `H_{j+1}(Λ, ℂ)`. -/
def bridgeClass (Λ : Subgroup G) (j : ℕ) :
    Zhom Λ j →ₗ[ℂ] groupHomology (Rep.res Λ.subtype (triv (G := G))) (j + 1) :=
  _root_.TernaryPeriodPolynomials.Argument.HomologyBridge.bridgeClass Λ j

/-- Every class of `H_{j+1}(Λ, ℂ)` is represented by a homogeneous cycle modulo `Λ`-null chains. -/
theorem bridgeClass_surjective (Λ : Subgroup G) (j : ℕ) : Function.Surjective (bridgeClass Λ j) :=
  _root_.TernaryPeriodPolynomials.Argument.HomologyBridge.bridgeClass_surjective Λ j

/-- The kernel of the class map: boundaries modulo `Λ`-null chains. -/
theorem bridgeClass_eq_zero_iff (Λ : Subgroup G) (j : ℕ) (c : Zhom Λ j) :
    bridgeClass Λ j c = 0 ↔ (c : Chains G (j + 1)) ∈ BdryChains Λ (j + 1) :=
  _root_.TernaryPeriodPolynomials.Argument.HomologyBridge.bridgeClass_eq_zero_iff Λ j c

/-- Two cycles have the same class iff their difference is a boundary modulo `Λ`-null chains. -/
theorem bridgeClass_eq_iff (Λ : Subgroup G) (j : ℕ) (c d : Zhom Λ j) :
    bridgeClass Λ j c = bridgeClass Λ j d ↔ (c : Chains G (j + 1)) - d ∈ BdryChains Λ (j + 1) :=
  _root_.TernaryPeriodPolynomials.Argument.HomologyBridge.bridgeClass_eq_iff Λ j c d

/-- The identity intertwiner of the trivial representations for `Λ' ≤ Λ`. -/
abbrev phiInc {Λ' Λ : Subgroup G} (h : Λ' ≤ Λ) :=
  _root_.TernaryPeriodPolynomials.Argument.HomologyBridge.phiInc h

/-- **Naturality in the subgroup**: corestriction `H_{j+1}(Λ') → H_{j+1}(Λ)` keeps the underlying chain. -/
theorem bridgeClass_natural {Λ' Λ : Subgroup G} (h : Λ' ≤ Λ) (j : ℕ) (c : Zhom Λ' j) :
    (groupHomology.map (Subgroup.inclusion h) (phiInc h) (j + 1)).hom (bridgeClass Λ' j c) =
      bridgeClass Λ j ⟨c.1, _root_.TernaryPeriodPolynomials.Argument.HomologyBridge.Zhom_mono h j c.2⟩ :=
  _root_.TernaryPeriodPolynomials.Argument.HomologyBridge.bridgeClass_natural h j c

/-- Conjugation `γ ↦ gγg⁻¹ : Λ → Λ'` for `g Λ g⁻¹ ≤ Λ'`. -/
abbrev conjIncl {Λ Λ' : Subgroup G} (g : G) (hg : ∀ γ ∈ Λ, g * γ * g⁻¹ ∈ Λ') : Λ →* Λ' :=
  _root_.TernaryPeriodPolynomials.Argument.HomologyBridge.conjIncl g hg

/-- The identity intertwiner of the trivial representations for conjugation. -/
abbrev phiConj {Λ Λ' : Subgroup G} (g : G) (hg : ∀ γ ∈ Λ, g * γ * g⁻¹ ∈ Λ') :=
  _root_.TernaryPeriodPolynomials.Argument.HomologyBridge.phiConj g hg

/-- Left translation preserves cycles modulo null chains, from `Λ` to `Λ'`. -/
theorem leftTranslate_mem_Zhom {Λ Λ' : Subgroup G} (g : G) (hg : ∀ γ ∈ Λ, g * γ * g⁻¹ ∈ Λ') (j : ℕ)
    {c : Chains G (j + 1)} (hc : c ∈ Zhom Λ j) : leftTranslate g (j + 1) c ∈ Zhom Λ' j :=
  _root_.TernaryPeriodPolynomials.Argument.HomologyBridge.Zhom_leftTranslate g hg j hc

/-- **Naturality in conjugation**: Mathlib's map for `γ ↦ gγg⁻¹` sends the class of `c` to the class of its
left translate `g·c`. -/
theorem bridgeClass_conj {Λ Λ' : Subgroup G} (g : G) (hg : ∀ γ ∈ Λ, g * γ * g⁻¹ ∈ Λ') (j : ℕ)
    (c : Zhom Λ j) :
    (groupHomology.map (conjIncl g hg) (phiConj g hg) (j + 1)).hom (bridgeClass Λ j c) =
      bridgeClass Λ' j ⟨leftTranslate g (j + 1) c.1, leftTranslate_mem_Zhom g hg j c.2⟩ :=
  _root_.TernaryPeriodPolynomials.Argument.HomologyBridge.bridgeClass_conj g hg j c

end TernaryPeriodPolynomials.Argument.Statements.HomologyBridge
