module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Singular.Transfer

@[expose] public section


/-!
# Finite covers: restriction and induction for `compactForget`

For quotient coverings `p : E ⟶ B` (group `G`) and `p' : E ⟶ B'` (group `H`, `φ : H →* G` with
finite-index range, compatible actions) and a base map `π : B' ⟶ B` with `p' ≫ π = p`:
* `compactForget_zero_of_res`: if preimages of compact sets under `π` are compact, vanishing of
  `compactForget p' (Rep.res φ V) 2` implies vanishing of `compactForget p V 2` (transfer);
* `compactForget_zero_res_of_ind`: vanishing of `compactForget p (indRep φ V) 2` implies vanishing of
  `compactForget p' (Rep.res φ V) 2` (Shapiro).
Both reduce, through `compactForget_two_eq_zero_iff_funVanish`, to the function-model lemmas of
`Singular/Transfer`, the only topological input being how compact supports correspond.

Formalized by Claude Sonnet 5.5.
-/


open CategoryTheory TopologicalSpace

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly.CompactInteriorRelativeBoundary TernaryPoly.EquivariantSingularSmall

section Cover

variable {G H : Type} [Group G] [Group H] (φ : H →* G)
  {E B B' : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E] [MulAction H E]
  [ContinuousConstSMul H E] (hact : ∀ (h : H) (x : E), h • x = φ h • x)
  (p : E ⟶ B) [Fact (IsQuotientCoveringMap p G)]
  (p' : E ⟶ B') [Fact (IsQuotientCoveringMap p' H)] (π : B' ⟶ B) (hπ : p' ≫ π = p)

include hπ in
theorem preimage_compl_eq (K : Set B) : p' ⁻¹' (π ⁻¹' K)ᶜ = p ⁻¹' Kᶜ := by
  ext x
  have : π (p' x) = p x := congrArg (fun f => f x) (congrArg (fun f => f.hom) hπ)
  simp [this]

include hact hπ in
/-- **Restriction to a finite-index subgroup detects vanishing upstairs.**  If the actual
compact-to-ordinary map of the finite-index cover `p'` with coefficients `Res V` vanishes in degree
two and preimages of compact sets under the base map `π` are compact, then the map for `p` with
coefficients `V` vanishes. -/
theorem compactForget_zero_of_res [Finite (G ⧸ φ.range)]
    (hproper : ∀ K : Compacts B, IsCompact (π ⁻¹' (K : Set B))) (V : Rep.{0} ℚ G)
    (h : compactForget p' (Rep.res φ V) 2 = 0) : compactForget p V 2 = 0 := by
  rw [compactForget_two_eq_zero_iff_funVanish] at h ⊢
  intro K
  have := h ⟨π ⁻¹' (K : Set B), hproper K⟩
  have e := preimage_compl_eq p p' π hπ (K : Set B)
  change FunVanish (G := H) (E := E) (Rep.res φ V) (p' ⁻¹' (π ⁻¹' (K : Set B))ᶜ) at this
  rw [e] at this
  exact funVanish_of_res φ hact _ this

include hact hπ in
/-- **Shapiro for the covering**: vanishing for the induced coefficients on the base of the larger
group gives vanishing for the finite-index subgroup's cover. -/
theorem compactForget_zero_res_of_ind (V : Rep.{0} ℚ G)
    (h : compactForget p (indRep φ V) 2 = 0) : compactForget p' (Rep.res φ V) 2 = 0 := by
  rw [compactForget_two_eq_zero_iff_funVanish] at h ⊢
  intro K'
  have hK : IsCompact (π '' (K' : Set B')) := K'.isCompact.image π.hom.continuous
  have := h ⟨π '' (K' : Set B'), hK⟩
  change FunVanish (G := G) (E := E) (indRep φ V) (p ⁻¹' (π '' (K' : Set B'))ᶜ) at this
  refine funVanish_res_of_ind φ hact _ _ (preimage_invariant p _) ?_ this
  intro x hx hx'
  apply hx
  refine ⟨p' x, hx', ?_⟩
  exact congrArg (fun f => f x) (congrArg (fun f => f.hom) hπ)

end Cover

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
