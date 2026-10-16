module

public import Mathlib

@[expose] public section


/-!
# Permutation modules of a free `Q`-set are coinduced from the kernel

Formalized by Claude Sonnet 5.5.

For a surjection `π : G →* Q` and a free `Q`-set `X ≃ Q × I`, the permutation module `Fun(X, A)` of `G` (acting through `π`) is isomorphic to the module
`Coind_{ker π}^G (Fun(I, A))` with trivial action of the kernel (`permCoindIso`); by Shapiro's lemma its cohomology in degrees above the cohomological dimension
of the kernel vanishes (`isZero_perm`).  `CdLe k G d` is the vanishing of the cohomology of `G` with every trivial coefficient module in degrees above `d`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open CategoryTheory CategoryTheory.Limits

universe u

variable {k : Type} [CommRing k] {G Q : Type} [Group G] [Group Q] (π : G →* Q)
  (X : Type) [MulAction Q X] (A : Type) [AddCommGroup A] [Module k A]

/-- The permutation representation of `G` on the functions `X → A`, through `π : G →* Q` and an action of `Q` on `X`:
`(g · F)(x) = F ((π g)⁻¹ x)`. -/
def permRep : Representation k G (X → A) where
  toFun g :=
    { toFun := fun F x => F ((π g)⁻¹ • x)
      map_add' := fun F F' => rfl
      map_smul' := fun c F => rfl }
  map_one' := by
    ext F x
    simp
  map_mul' g h := by
    ext F x
    simp [mul_smul, mul_inv_rev]

theorem permRep_apply (g : G) (F : X → A) (x : X) : permRep (k := k) π X A g F x = F ((π g)⁻¹ • x) := rfl

variable {I : Type} (e : X ≃ Q × I) (he : ∀ (q : Q) (x : X), e (q • x) = (q * (e x).1, (e x).2))
  (hπ : Function.Surjective π)

/-- The function on `G` attached to `F : X → A`: `r ↦ (i ↦ F (e⁻¹ ((π r)⁻¹, i)))`. -/
def permToCoind (F : X → A) : G → (I → A) := fun r i => F (e.symm ((π r)⁻¹, i))

omit [MulAction Q X] [AddCommGroup A] in
theorem permToCoind_mem (F : X → A) (s : π.ker) (r : G) :
    permToCoind π X A e F ((Subgroup.subtype π.ker s) * r) = permToCoind π X A e F r := by
  funext i
  have : π (s.1 * r) = π r := by rw [map_mul, MonoidHom.mem_ker.mp s.2, one_mul]
  simp [permToCoind, this]

omit [AddCommGroup A] in
include he in
theorem he_symm (q q' : Q) (i : I) : q • e.symm (q', i) = e.symm (q * q', i) := by
  apply e.injective
  rw [he, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- **The permutation module of a free `Q`-set is coinduced from the kernel**: `Fun(X, A) ≅ Coind_{ker π}^G (Fun(I, A))` as `G`-modules. -/
def permCoindEquiv :
    (X → A) ≃ₗ[k] ↥(Representation.coindV (k := k) (π.ker.subtype) (Representation.trivial k π.ker (I → A))) where
  toFun F := ⟨permToCoind π X A e F, fun s r => by
    simpa using permToCoind_mem π X A e F s r⟩
  map_add' F F' := by
    apply Subtype.ext
    funext r i
    rfl
  map_smul' c F := by
    apply Subtype.ext
    funext r i
    rfl
  invFun f x := f.1 (Function.surjInv hπ (e x).1⁻¹) (e x).2
  left_inv F := by
    funext x
    have h1 : π (Function.surjInv hπ (e x).1⁻¹) = (e x).1⁻¹ := Function.surjInv_eq hπ _
    simp only [permToCoind, h1, inv_inv]
    have : ((e x).1, (e x).2) = e x := rfl
    rw [this, Equiv.symm_apply_apply]
  right_inv f := by
    apply Subtype.ext
    funext r i
    have h1 : π (Function.surjInv hπ (π r)) = π r := Function.surjInv_eq hπ _
    have hs : r = (r * (Function.surjInv hπ (π r))⁻¹) * Function.surjInv hπ (π r) := by group
    have hk : r * (Function.surjInv hπ (π r))⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
    have hmem := f.2 ⟨_, hk⟩ (Function.surjInv hπ (π r))
    have hmem' : f.1 r = f.1 (Function.surjInv hπ (π r)) := by
      have := hmem
      simp only [Representation.trivial_apply, Subgroup.coe_subtype] at this
      rw [← hs] at this
      rw [this]
    simp only [permToCoind]
    rw [Equiv.apply_symm_apply]
    simp only [inv_inv]
    rw [hmem']

include he in
theorem permCoindEquiv_comm (g : G) (F : X → A) :
    permCoindEquiv π X A e hπ (permRep (k := k) π X A g F) =
      (Representation.coind (k := k) (π.ker.subtype) (Representation.trivial k π.ker (I → A))) g
        (permCoindEquiv π X A e hπ F) := by
  apply Subtype.ext
  funext r i
  change F ((π g)⁻¹ • e.symm ((π r)⁻¹, i)) = F (e.symm ((π (r * g))⁻¹, i))
  rw [he_symm X e he, map_mul, mul_inv_rev]

/-- **The permutation module is isomorphic, as a `G`-representation, to the module coinduced from the kernel of `π`.** -/
def permCoindIso :
    Rep.of (permRep (k := k) π X A) ≅
      Rep.coind π.ker.subtype (Rep.trivial k π.ker (I → A)) :=
  Rep.mkIso (Representation.Equiv.mk (permCoindEquiv π X A e hπ) (fun g => by
    apply LinearMap.ext
    intro F
    exact permCoindEquiv_comm π X A e he hπ g F))

/-- Vanishing of the cohomology of the permutation module of a free `Q`-set in degrees above the cohomological dimension of the kernel. -/
def CdLe (k : Type) [CommRing k] (G : Type) [Group G] (d : ℕ) : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Module k A] (n : ℕ), d < n → IsZero (groupCohomology (Rep.trivial k G A) n)

include he hπ in
theorem isZero_perm {d : ℕ} (hS : CdLe k π.ker d) (n : ℕ) (hn : d < n) :
    IsZero (groupCohomology (Rep.of (permRep (k := k) π X A)) n) := by
  have h1 : groupCohomology (Rep.of (permRep (k := k) π X A)) n ≅
      groupCohomology (Rep.coind π.ker.subtype (Rep.trivial k π.ker (I → A))) n :=
    (groupCohomology.functor k G n).mapIso (permCoindIso π X A e he hπ)
  exact ((hS (I → A) n hn).of_iso (groupCohomology.coindIso (Rep.trivial k π.ker (I → A)) n)).of_iso h1

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
