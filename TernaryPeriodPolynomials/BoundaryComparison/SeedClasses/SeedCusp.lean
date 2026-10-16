module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.SeedConj
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.RadicalEichlerClass

@[expose] public section


/-!
# The class of the seed of a cusp form

Paper: Lemma C.3 (`ar:lem:seed`).

For a cusp form `f` of weight `n + 3` for a determinant-one group `Λ_P ⊂ GL₂(ℝ)` and a plane
parabolic group `G` (`PlaneData`) whose Levi block lands in `Λ_P`, the seed `ω_h`,
`h = f ∘ ofComplex`, has a zig-zag datum for the moment primitives `momentPrim` of `h(z)z^j`
(normalized by `G_j(i) = 0`, `RadicalEichlerPackage`), hence a class in `H²(G, E_n)`, and the
cochain is the closed form of `toPoly_cochain`. The same holds for the antiholomorphic seed.

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial UpperHalfPlane ModularForm
open scoped UpperHalfPlane
open CategoryTheory groupCohomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3

section Cusp

variable (Λ : Subgroup (GL (Fin 2) ℝ)) [Λ.HasDetOne] (n : ℕ) (f : CuspForm Λ ((n + 3 : ℕ) : ℤ))

/-- The extension `h = f ∘ ofComplex` of a cusp form to `ℂ`. -/
def cuspH : ℂ → ℂ := fun z => f (ofComplex z)

omit [Λ.HasDetOne] in
theorem cuspH_holo : DifferentiableOn ℂ (cuspH Λ n f) Psi.upperSet :=
  UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo f)

/-- The moment primitives `G_j` of `h(z) z^j` normalized by `G_j(i) = 0` (a fixed choice from
`seed_radical_class_eq_eichler_class`). -/
def momentPrim : ℕ → ℂ → ℂ := Classical.choose (seed_radical_class_eq_eichler_class Λ n f)

theorem momentPrim_spec : RadicalEichlerPackage Λ n f (momentPrim Λ n f) :=
  Classical.choose_spec (seed_radical_class_eq_eichler_class Λ n f)

theorem momentPrim_zero (j : ℕ) : momentPrim Λ n f j Complex.I = 0 :=
  (momentPrim_spec Λ n f).1 j

theorem momentPrim_hasDerivAt (j : ℕ) (z : ℂ) (hz : 0 < z.im) :
    HasDerivAt (momentPrim Λ n f j) (cuspH Λ n f z * z ^ j) z :=
  (momentPrim_spec Λ n f).2.1 j z hz

variable {Λ n f}

theorem cuspH_mod {G : Type} [Group G] (D : PlaneData G) (hΛ : ∀ g, (D.lam g : GL (Fin 2) ℝ) ∈ Λ)
    (g : G) (z : ℂ) (hz : 0 < z.im) :
    cuspH Λ n f (mob (D.lam g) z) = dnm (D.lam g) z ^ (n + 3) * cuspH Λ n f z :=
  modular_of_slashInvariant Λ (n + 3) f (D.lam g) (hΛ g) z hz

variable {G : Type} [Group G] (D : PlaneData G) (hΛ : ∀ g, (D.lam g : GL (Fin 2) ℝ) ∈ Λ)

/-- **The zig-zag datum of the seed of a cusp form.** -/
def cuspSeedDatum :=
  D.seedDatum (cuspH Λ n f) n (momentPrim Λ n f) (cuspH_holo Λ n f)
    (momentPrim_hasDerivAt Λ n f) (cuspH_mod D hΛ)

/-- The seed `ω_h` of a cusp form, as a closed `ρ`-equivariant 2-form on the face. -/
def cuspSeedInv :=
  D.seedInv (cuspH Λ n f) n (momentPrim Λ n f) (cuspH_holo Λ n f)
    (momentPrim_hasDerivAt Λ n f) (cuspH_mod D hΛ)

/-- **The class of the seed of a cusp form** in `H²(G, E_n)`. -/
def cuspSeedClass : H2 (Rep.of (D.rhoR n)) :=
  D.seedClass (cuspH Λ n f) n (momentPrim Λ n f) (cuspH_holo Λ n f)
    (momentPrim_hasDerivAt Λ n f) (cuspH_mod D hΛ)

/-- **The class of the antiholomorphic seed of a cusp form** in `H²(G, E_n)`. -/
def cuspSeedConjClass : H2 (Rep.of (D.rhoR n)) :=
  D.seedConjClass (cuspH Λ n f) n (momentPrim Λ n f) (cuspH_holo Λ n f)
    (momentPrim_hasDerivAt Λ n f) (cuspH_mod D hΛ)

/-- The de Rham class of the seed is `cuspSeedClass`. -/
theorem deRhamClass_cuspSeed :
    ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty D.action (D.rhoR n)
      (cuspSeedInv D hΛ (f := f)) = cuspSeedClass D hΛ (f := f) :=
  D.deRhamClass_seedInv (cuspH Λ n f) n (momentPrim Λ n f) (cuspH_holo Λ n f)
    (momentPrim_hasDerivAt Λ n f) (cuspH_mod D hΛ)

/-- The zig-zag cochain of the seed of a cusp form. -/
def cuspSeedCochain (g k : G) : Coef n :=
  ZigZag.cochain (ZigZag.laws isOpen_faceSet convex_faceSet faceSet_nonempty D.action (D.rhoR n))
    (cuspSeedDatum D hΛ (f := f)) g k

/-- The zig-zag cochain of the seed of a cusp form is a 2-cocycle. -/
theorem cuspSeedCochain_cocycle (g h j : G) :
    cuspSeedCochain D hΛ (f := f) (g * h) j + cuspSeedCochain D hΛ (f := f) g h =
      D.rhoR n g (cuspSeedCochain D hΛ (f := f) h j) +
        cuspSeedCochain D hΛ (f := f) g (h * j) :=
  ZigZag.cochain_isCocycle _ _ g h j

/-- **The closed-form cocycle of the seed of a cusp form.** -/
theorem toPoly_cuspSeedCochain (g k : G) :
    Coef.toPoly (cuspSeedCochain D hΛ (f := f) g k) =
      D.seedCocycleFormula n (momentPrim Λ n f) g k :=
  D.toPoly_cochain (cuspH Λ n f) n (momentPrim Λ n f) (cuspH_holo Λ n f)
    (momentPrim_hasDerivAt Λ n f) (momentPrim_zero Λ n f) (cuspH_mod D hΛ) g k

/-- The antiholomorphic seed `conj ω_h` of a cusp form, as a closed equivariant 2-form. -/
def cuspSeedConjInv :=
  D.seedConjInv (cuspH Λ n f) n (momentPrim Λ n f) (cuspH_holo Λ n f)
    (momentPrim_hasDerivAt Λ n f) (cuspH_mod D hΛ)

/-- The de Rham class of the antiholomorphic seed is `cuspSeedConjClass`. -/
theorem deRhamClass_cuspSeedConj :
    ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty D.action (D.rhoR n)
      (cuspSeedConjInv D hΛ (f := f)) = cuspSeedConjClass D hΛ (f := f) :=
  D.deRhamClass_seedConjInv (cuspH Λ n f) n (momentPrim Λ n f) (cuspH_holo Λ n f)
    (momentPrim_hasDerivAt Λ n f) (cuspH_mod D hΛ)

/-- **The closed-form cocycle of the antiholomorphic seed**: the conjugate of the holomorphic
one. -/
theorem toPoly_cuspSeedConjCochain (g k : G) :
    Coef.toPoly (ZigZag.cochain (ZigZag.laws isOpen_faceSet convex_faceSet faceSet_nonempty
      D.action (D.rhoR n)) (D.seedConjDatum (cuspH Λ n f) n (momentPrim Λ n f)
        (cuspH_holo Λ n f) (momentPrim_hasDerivAt Λ n f) (cuspH_mod D hΛ)) g k) =
      MvPolynomial.map (starRingEnd ℂ) (D.seedCocycleFormula n (momentPrim Λ n f) g k) :=
  D.toPoly_cochain_conj (cuspH Λ n f) n (momentPrim Λ n f) (cuspH_holo Λ n f)
    (momentPrim_hasDerivAt Λ n f) (momentPrim_zero Λ n f) (cuspH_mod D hΛ) g k

/-- The zig-zag cochain of the antiholomorphic seed of a cusp form. -/
def cuspSeedConjCochain (g k : G) : Coef n :=
  ZigZag.cochain (ZigZag.laws isOpen_faceSet convex_faceSet faceSet_nonempty D.action (D.rhoR n))
    (D.seedConjDatum (cuspH Λ n f) n (momentPrim Λ n f) (cuspH_holo Λ n f)
      (momentPrim_hasDerivAt Λ n f) (cuspH_mod D hΛ)) g k

/-- The cochain of the antiholomorphic seed is the coefficientwise conjugate. -/
theorem cuspSeedConjCochain_eq (g k : G) :
    cuspSeedConjCochain D hΛ (f := f) g k = Coef.conjCoef (cuspSeedCochain D hΛ (f := f) g k) :=
  D.cochain_seedConj (cuspH Λ n f) n (momentPrim Λ n f) (cuspH_holo Λ n f)
    (momentPrim_hasDerivAt Λ n f) (cuspH_mod D hΛ) g k

/-- The cochain of the antiholomorphic seed is a 2-cocycle. -/
theorem cuspSeedConjCochain_cocycle (g h j : G) :
    cuspSeedConjCochain D hΛ (f := f) (g * h) j + cuspSeedConjCochain D hΛ (f := f) g h =
      D.rhoR n g (cuspSeedConjCochain D hΛ (f := f) h j) +
        cuspSeedConjCochain D hΛ (f := f) g (h * j) :=
  ZigZag.cochain_isCocycle _ _ g h j

end Cusp

end TernaryPeriodPolynomials.Argument.SeedC3
