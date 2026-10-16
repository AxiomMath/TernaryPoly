module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.PermCoind
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.TreeSES

@[expose] public section


/-!
# The antisymmetric edge functions are a retract of all edge functions

Formalized by Claude Sonnet 5.5.

Over a ring with `2` invertible, `Anti(E, A)` is a `G`-equivariant direct summand of `Fun(E, A)` (`antiIncl`, `antiProj`), so its cohomology vanishes wherever that of `Fun(E, A)` does (`isZero_anti`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open CategoryTheory CategoryTheory.Limits
section Retract

variable {k : Type} [CommRing k] {G Q : Type} [Group G] [Group Q] (π : G →* Q) (T : TreeData Q)
  (A : Type) [AddCommGroup A] [Module k A]

/-- The inclusion of the antisymmetric edge functions into all edge functions. -/
def antiIncl : Rep.of (antiRep (k := k) π T A) ⟶ Rep.of (permRep (k := k) π T.Et A) :=
  Rep.ofHom
    { toLinearMap := (T.antiSub k A).subtype
      isIntertwining' := fun g => by
        ext F e
        rfl }

variable [Invertible (2 : k)]

/-- The antisymmetrisation `F ↦ (F - F ∘ swap) / 2`. -/
def antiProj : Rep.of (permRep (k := k) π T.Et A) ⟶ Rep.of (antiRep (k := k) π T A) :=
  Rep.ofHom
    { toFun := fun F => ⟨fun e => (⅟2 : k) • (F e - F (T.swap e)), fun e => by
        simp only [T.swap_swap]
        rw [← smul_neg, neg_sub]⟩
      map_add' := fun F F' => by
        apply Subtype.ext
        funext e
        simp only [Pi.add_apply, Submodule.coe_add]
        rw [← smul_add]
        congr 1
        abel
      map_smul' := fun c F => by
        apply Subtype.ext
        funext e
        show (⅟2 : k) • (c • F e - c • F (T.swap e)) = c • ((⅟2 : k) • (F e - F (T.swap e)))
        module
      isIntertwining' := fun g => by
        ext F e
        show (⅟2 : k) • (F ((π g)⁻¹ • e) - F ((π g)⁻¹ • T.swap e)) =
          (⅟2 : k) • (F ((π g)⁻¹ • e) - F (T.swap ((π g)⁻¹ • e)))
        rw [T.swap_smul] }

theorem antiIncl_antiProj : antiIncl (k := k) π T A ≫ antiProj (k := k) π T A = 𝟙 _ := by
  apply Rep.hom_ext
  ext F e
  show (⅟2 : k) • (F.1 e - F.1 (T.swap e)) = F.1 e
  rw [F.2 e, sub_neg_eq_add]
  calc (⅟2 : k) • (F.1 e + F.1 e) = ((⅟2 : k) * 2) • F.1 e := by module
    _ = F.1 e := by rw [invOf_mul_self, one_smul]

/-- The cohomology of the antisymmetric edge functions vanishes wherever that of all edge functions does. -/
theorem isZero_anti {n : ℕ} (h : IsZero (groupCohomology (Rep.of (permRep (k := k) π T.Et A)) n)) :
    IsZero (groupCohomology (Rep.of (antiRep (k := k) π T A)) n) := by
  have hc : (groupCohomology.functor k G n).map (antiIncl (k := k) π T A) ≫
      (groupCohomology.functor k G n).map (antiProj (k := k) π T A) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, antiIncl_antiProj, CategoryTheory.Functor.map_id]
  have hmono : Mono ((groupCohomology.functor k G n).map (antiIncl (k := k) π T A)) := mono_of_mono_fac hc
  exact @IsZero.of_mono _ _ _ _ _ ((groupCohomology.functor k G n).map (antiIncl (k := k) π T A)) hmono h

end Retract
end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
