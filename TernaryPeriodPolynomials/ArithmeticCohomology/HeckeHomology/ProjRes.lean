module

public import Mathlib

@[expose] public section


/-!
# Restriction along an injective group homomorphism preserves projective representations

Formalized by Claude Sonnet 5.5.

Mathlib proves that restriction to a subgroup preserves projective objects by showing that coinduction along
`Subgroup.subtype` preserves epimorphisms.  The same proof works for any injective `f : H →* G`
(`coind_preservesEpi_of_injective`), giving `projective_res_of_injective`, and the corollary
`projective_res_bar` that every term of the bar resolution of `P`, restricted along an injective `S →* P`, is projective.
-/

open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeHomology

/-- Coinduction along an injective homomorphism preserves epimorphisms. -/
theorem coind_preservesEpi_of_injective {H G : Type} [Group H] [Group G] (f : H →* G)
    (hf : Function.Injective f) :
    (Rep.coindFunctor ℚ f).PreservesEpimorphisms where
  preserves {X Y} p := (Rep.epi_iff_surjective _).2 fun y => by
    let := QuotientGroup.rightRel f.range
    choose! s hs using (Rep.epi_iff_surjective p).1 ‹_›
    choose! i hi using Quotient.mk'_surjective (α := G)
    have hmem (g : G) : g * (i (Quotient.mk' g))⁻¹ ∈ f.range :=
      QuotientGroup.rightRel_apply.1 (Quotient.eq'.1 (hi (Quotient.mk' g)))
    choose γ hγf using hmem
    have hmk (s : H) (g : G) : Quotient.mk' (f s * g) = (Quotient.mk' g : Quotient (QuotientGroup.rightRel f.range)) :=
      Quotient.eq'.2 (QuotientGroup.rightRel_apply.2 (by simp))
    have hγ (s : H) (g : G) : γ (f s * g) = s * γ g := by
      apply hf
      rw [hγf, map_mul, hγf, hmk]
      simp [mul_assoc]
    let x (g : G) : X := X.ρ (γ g) (s (y.1 (i (Quotient.mk' g))))
    refine ⟨⟨x, fun _ _ => ?_⟩, Subtype.ext <| funext fun g => ?_⟩
    · simp [x, ← Module.End.mul_apply, ← map_mul, hmk, hγ]
    · simp only [Rep.coindFunctor_obj, Rep.coindFunctor_map, Rep.hom_ofHom,
        Representation.coindMap_coe_apply_apply, Rep.hom_comm_apply, x]
      simp_all [← y.2 (γ g)]

/-- Restriction along an injective homomorphism preserves projective representations. -/
theorem projective_res_of_injective {H G : Type} [Group H] [Group G] (f : H →* G)
    (hf : Function.Injective f) (F : Rep.{0} ℚ G) [Projective F] :
    Projective (Rep.res f F) := by
  have := coind_preservesEpi_of_injective f hf
  have := (Rep.resFunctor (k := ℚ) f).preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    (Rep.resCoindAdjunction ℚ f)
  exact Functor.PreservesProjectiveObjects.projective_obj (F := Rep.resFunctor f) (inferInstance)

/-- Terms of the bar resolution, restricted along an injective homomorphism, are projective. -/
theorem projective_res_bar {S P : Type} [Group S] [Group P] (f : S →* P)
    (hf : Function.Injective f) (j : ℕ) :
    Projective ((Rep.resFunctor f).obj ((Rep.barResolution ℚ P).complex.X j)) := by
  have : Projective ((Rep.barResolution ℚ P).complex.X j) := (Rep.barResolution ℚ P).projective j
  exact projective_res_of_injective f hf _

end TernaryPeriodPolynomials.Argument.HeckeHomology

end
