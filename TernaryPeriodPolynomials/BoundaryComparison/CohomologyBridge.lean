module

public import TernaryPeriodPolynomials.GroupCohomology.SingularComparison.Kronecker
public import TernaryPeriodPolynomials.BoundaryComparison.HomologyBridge

@[expose] public section


/-!
# Link W2, cohomology half: invariant homogeneous cochains versus Mathlib's group cohomology

Formalized by Claude Sonnet 5.5.

**Setting.**  `G` a group, `Λ ≤ G` a subgroup.  `Inv Λ n` is the space of `Λ`-invariant functions
`(Fin (n+1) → G) → ℂ` (the equivariant cochains of the homogeneous resolution on ambient vertices),
`dInv Λ n : Inv Λ n → Inv Λ (n+1)` the coboundary `(δF)(x) = ∑ (-1)^i F(x ∘ succAbove i)` (`dInv_apply`, which is
`F(∂x)` in terms of `homogeneousBoundary`), and `cohCycles Λ j = {F ∈ Inv Λ (j+1) | δF = 0}`.  Degree three
(the three-cochains of the face pairing, functions on `G⁴`) is `j = 2`.

**Statement.**  There is a `ℂ`-linear class map `cohClass Λ j : cohCycles Λ j → groupCohomology (Rep.trivial ℂ Λ ℂ) (j+1)`
(Mathlib's `H^{j+1}(Λ, ℂ)`) which is

* surjective (`cohClass_surjective`);
* with kernel exactly the coboundaries of invariant cochains (`cohClass_eq_zero_iff`), so it induces an
  isomorphism `cohCycles Λ j / δ Inv Λ j ≅ H^{j+1}(Λ, ℂ)` (the quotient type is not formed);
* natural in the subgroup: for `Λ' ≤ Λ`, Mathlib's restriction `groupCohomology.map (Subgroup.inclusion h) _ (j+1)` carries
  the class of `F` to the class of the same function, `Λ'`-invariant (`cohClass_res`).

**Kronecker pairing.**  Mathlib has none.  `kron Λ j : H^{j+1}(Λ, ℂ) →ₗ Dual (H_{j+1}(Λ, ℂ))` is the unique bilinear form with
`kron (cohClass F) (bridgeClass c) = ∑ c(x) F(x)` (`kron_class`), where `bridgeClass` is the homology bridge of
`Exports/HomologyBridge`; it is well defined because invariant functions kill null chains and cocycles kill
boundaries.  It satisfies the adjunction between Mathlib's cohomology restriction and homology corestriction for
`Λ' ≤ Λ` (`kron_res_cor`).

**Proof.**  The cochain map `Θ : Hom(Res std, ℂ) → inhomogeneousCochains`, `F ↦ (y ↦ F(1, y₁, y₁y₂, …))` (`Theta_apply`),
is a quasi-isomorphism because the bar resolution of `Λ` and the restricted standard resolution of `G` are projective
resolutions of the same representation and `Θ` is induced by a chain map over the identity, hence a homotopy
equivalence (`isIso_Theta`, `isIso_homologyMap_yMap_res`); `Hom_Λ(Res std_n, ℂ) ≃ Inv Λ n` (`homEquiv`).

**Scope.**  Trivial coefficients `ℂ`.  Conjugation naturality of the cohomology class map (the analogue of
`bridgeClass_conj`) is NOT proved; the homology side is.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.CohomologyBridge

open TernaryPeriodPolynomials.Argument.HomologyBridge

variable {G : Type} [Group G]

/-- `Λ`-invariant functions on `(n+1)`-tuples of ambient vertices. -/
abbrev Inv' (Λ : Subgroup G) (n : ℕ) := Inv Λ n

/-- Invariant `(j+1)`-cochains with zero coboundary. -/
abbrev cohCycles' (Λ : Subgroup G) (j : ℕ) := cohCycles Λ j

/-- Mathlib's `H^{j+1}(Λ, ℂ)` with trivial coefficients. -/
abbrev CohL' (Λ : Subgroup G) (j : ℕ) := CohL Λ j

/-- Mathlib's `H_{j+1}(Λ, ℂ)` with trivial coefficients. -/
abbrev HomL' (Λ : Subgroup G) (j : ℕ) := HomL Λ j

/-- The coboundary is `F(∂ x)`. -/
theorem dInv_apply' (Λ : Subgroup G) (i : ℕ) (F : Inv Λ i) (x : Fin (i + 2) → G) :
    (dInv Λ i F).1 x = Finsupp.linearCombination ℂ F.1
      (TernaryPeriodPolynomials.TopVanishing.homogeneousBoundary (i + 1)
        (Finsupp.single x (1 : ℂ))) :=
  dInv_apply Λ i F x

/-- The class of an invariant cocycle in Mathlib's `H^{j+1}(Λ, ℂ)`. -/
def cohClass' (Λ : Subgroup G) (j : ℕ) : cohCycles' Λ j →ₗ[ℂ] CohL' Λ j :=
  cohClass Λ j

theorem cohClass_surjective' (Λ : Subgroup G) (j : ℕ) : Function.Surjective (cohClass' Λ j) :=
  cohClass_surjective Λ j

theorem cohClass_eq_zero_iff' (Λ : Subgroup G) (j : ℕ) (F : cohCycles' Λ j) :
    cohClass' Λ j F = 0 ↔ (F : Inv Λ (j + 1)) ∈ LinearMap.range (dInv Λ j) :=
  cohClass_eq_zero_iff Λ j F

/-- Naturality in the subgroup: Mathlib's restriction keeps the function. -/
theorem cohClass_res' {Λ' Λ : Subgroup G} (h : Λ' ≤ Λ) (j : ℕ) (F : cohCycles' Λ j) :
    (groupCohomology.map (Subgroup.inclusion h) (phiCoh h) (j + 1)).hom (cohClass' Λ j F) =
      cohClass' Λ' j ⟨restrInv h (j + 1) F.1, restrInv_mem_cohCycles h j F⟩ :=
  cohClass_res h j F

/-- The Kronecker pairing between Mathlib's cohomology and homology, through the two bridges. -/
def kron' (Λ : Subgroup G) (j : ℕ) : CohL' Λ j →ₗ[ℂ] Module.Dual ℂ (HomL' Λ j) := kron Λ j

/-- **Kronecker compatibility**: `⟨[F], [c]⟩ = ∑ c(x) F(x)`. -/
theorem kron_class' (Λ : Subgroup G) (j : ℕ) (F : cohCycles' Λ j) (c : Zhom Λ j) :
    kron' Λ j (cohClass' Λ j F) (bridgeClass Λ j c) = Finsupp.linearCombination ℂ F.1.1 c.1 :=
  kron_class Λ j F c

/-- Restriction in cohomology is adjoint to corestriction in homology. -/
theorem kron_res_cor' {Λ' Λ : Subgroup G} (h : Λ' ≤ Λ) (j : ℕ) (α : CohL' Λ j) (β : HomL' Λ' j) :
    kron' Λ' j ((groupCohomology.map (Subgroup.inclusion h) (phiCoh h) (j + 1)).hom α) β =
      kron' Λ j α ((groupHomology.map (Subgroup.inclusion h) (phiInc h) (j + 1)).hom β) :=
  kron_res_cor h j α β

end TernaryPeriodPolynomials.Argument.Statements.CohomologyBridge
