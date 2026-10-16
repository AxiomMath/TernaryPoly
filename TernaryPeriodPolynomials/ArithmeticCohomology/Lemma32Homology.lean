module

public import TernaryPeriodPolynomials.BoundaryComparison.FiberModel

@[expose] public section


/-!
# Lemma 3.2 (`prop:26-model`) with Borel-Serre duality composed in

Formalized by Claude Sonnet 5.5.

> **Lemma 3.2.** The group `H₃(K, E_{n,t})`, with the right coefficient action defined above, is
> represented by precisely the functions `F : 𝒮 → V_n` such that `F(rh) = χ_t(h) F(r) ∣ h` and
> `F(r) + F(rA²) ∣ A + F(rA) ∣ A² = 0` for every `r ∈ 𝒮` and every signed permutation matrix `h`.
> ... The coordinate `F(ℓ)` is the value on the identity apartment of the corresponding ordinary
> Steinberg functional.
>
> *Proof.* Rational Borel-Serre duality gives `H³(K,E*) ≅ (St ⊗ E*)_K`, `H₃(K,E) ≅ Hom_K(St,E)` ...

`Statements.FiberModel.lemma_3_2` is the second half (functions `F` against `Hom_K(St, E)`) and
`Statements.FiberModel.H3_K_equiv` the first half (`H₃(K,E)` against `Hom_K(St, E)`); this module composes
them into the single statement of the lemma: an equivalence between `H₃(K, E_{n,t})`
(Mathlib `groupHomology` of the `K`-representation `E_{n,t}`) and the space of functions `F`, such that
the duality functional of a class has the stated value on every apartment and `F(ℓ)` on the identity
apartment.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.FiberModel

open TernaryPoly TernaryPoly.ModThreeGoodAction
open TernaryPeriodPolynomials.Argument.FiberModel

/-- **Lemma 3.2 (`prop:26-model`), complete form.**  For `t ∈ {0,1}` and every `n` there is a `ℚ`-linear
equivalence `e` of `H₃(K, E_{n,t})` onto the space of functions `F : 𝒮 → V_n` satisfying
`eq:fiber-signed` and `eq:fiber-norm`, such that the Steinberg functional `Φ = H3_K_equiv z` attached to
a class `z` by Borel-Serre duality takes the apartment of `g ∈ GL₃(ℤ)` to `g · F(ℓ g)` for `F = e z`
and, in particular, the identity apartment to `F(ℓ)`. -/
theorem lemma_3_2_homology (t : Fin 2) (n : ℕ) :
    ∃ e : groupHomology (EK n t) 3 ≃ₗ[ℚ] fiberFunctions t n, ∀ z,
      (∀ g : IntegralGL,
        (H3_K_equiv n t z).1 (apartment g) = coeff n t g ((e z).1 (ellMul g))) ∧
      (H3_K_equiv n t z).1 identityApartment = (e z).1 ell := by
  obtain ⟨e0, he0⟩ := lemma_3_2 t n
  refine ⟨(H3_K_equiv n t).trans e0.symm, fun z => ?_⟩
  have hz : e0 (e0.symm (H3_K_equiv n t z)) = H3_K_equiv n t z := e0.apply_symm_apply _
  obtain ⟨h1, h2⟩ := he0 (e0.symm (H3_K_equiv n t z))
  rw [hz] at h1 h2
  exact ⟨h1, h2⟩

end TernaryPeriodPolynomials.Argument.Statements.FiberModel
