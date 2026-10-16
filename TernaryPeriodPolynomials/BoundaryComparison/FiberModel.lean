module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Top.BoundaryComparisonApartment
public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.Instances
public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.Gamma2Presentation
public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.Gamma2Cusps
public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.KLevel
public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.KLevelGeneric
public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.EquivS1
public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.HeckeCosets
public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.HeckeHom
public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.NeatDualityK
public import TernaryPeriodPolynomials.Topology.DualityEquivariance.EpsNaturality

@[expose] public section


/-!
# Lemma 3.2 (`prop:26-model`) and Lemma 4.3 (`lem:three-seed`): the fiber model

Lemma 3.2 of the paper says that
`H₃(K, E_{n,t})` "is represented by precisely the functions `F : 𝒮 → V_n`" with
`F(rh) = χ_t(h) F(r) ∣ h` for the signed permutation matrices `h` (`eq:fiber-signed`) and
`F(r) + F(rA²) ∣ A + F(rA) ∣ A² = 0` (`eq:fiber-norm`), and that "the coordinate `F(ℓ)` is the value
on the identity apartment of the corresponding ordinary Steinberg functional".  Lemma 4.3 says that
such an `F` is uniquely determined by its seeds `P = F(1,0,0)`, `Q = F(1,1,0)`, `f = F(1,1,1)`, that
`eq:fiber-norm` holds if and only if the seeds satisfy an explicit list (including `eq:mixed1`,
`eq:mixed2`), and that seeds with these properties extend uniquely, for polynomial or
rational-function coefficients.

**What is proved here.**

* `lemma_3_2`, `lemma_3_2_iff`, `lemma_3_2_unique`: for `t ∈ {0,1}` and every `n`, a `ℚ`-linear
  equivalence between the `ℚ`-space of functions `F : 𝒮 → V_n` satisfying `eq:fiber-signed` and
  `eq:fiber-norm` literally (`TernaryPeriodPolynomials.Argument.FiberModel.IsFiberFunction`: all signed permutation matrices
  `h = Dπ`, covectors multiplied modulo three, direct substitution `∣`) and the `K`-equivariant
  linear maps `St → E_{n,t}`, where `St` is the ordinary incidence cycle module
  `TernaryPoly.OrdinaryIncidenceChains.Cycles` (the first homology of the rational Tits graph) and
  `E_{n,t}` is `V_n` with the left action `g · f(x) = det(g)^{-t} f(g⁻¹ x)` of `GL₃(ℤ)`
  (`TernaryPeriodPolynomials.Argument.FiberModel.coeff`).  Under it `F` corresponds to the unique equivariant functional taking the
  apartment of the ordered basis given by the columns of `g ∈ GL₃(ℤ)` to `g · F(ℓ g)`; in particular
  `F(ℓ)` is the value on the identity apartment (`identityApartment_eq`).  Both inclusions of
  "precisely" are proved, and `F` is determined by its functional.
* `lemma_4_3_polynomial`, `lemma_4_3_rational`: uniqueness from seeds, norm criterion, and unique
  extension, with polynomial and with rational-function coefficients.
* `H3_neat_iso`, `H3_neat_evaluation`, `H3_neat_coefficients`: the library's duality
  `H₃(Γ(6), W) ≅ Hom_{Γ(6)}(St, W)` for the neat group `Γ(6)`, with identity-apartment evaluation.
* `gamma2_relations`, `gamma2_presentation`, `gamma2_free_product`, `cusp_orbits`, `cusp_widths`: the
  presentation `Γ₂ ≅ 𝔖₃ * C₂` of `eq:Gamma-presentation` and the two cusp orbits of widths one and three.

* `H3_K_descent_surjective`, `H3_K_descent_ker`, `H3_K_descent_conj`, `H3_K_descent_idem`: the
  passage from `Γ(6)` to `K` on group homology, in Mathlib's `groupHomology` and unconditionally: the
  corestriction `H₃(Γ(6), E) → H₃(K, E)` is surjective, its kernel is the kernel of the averaging
  operator over `K/Γ(6)` of the conjugation action `c_g = H₃(conj g, ρ g)`, it is invariant under
  `c_g`, and the averaging operator is idempotent.  (These are instances of the general
  `Proofs/TernaryPeriodPolynomials.Argument.GroupHomology/NormalDescent.lean`, which compares Mathlib's `groupHomologyIso` for the bar
  resolution of `K` and of its restriction to `Γ(6)`.)
* `H3_K_equiv_of_neat_equivariance` (helper, stated with an explicit hypothesis): if the neat-level
  duality is `K`-equivariant (`NeatDualityEquivariant`: it intertwines `c_g` with
  `Φ ↦ ρ(g) ∘ Φ ∘ g⁻¹`), then `H₃(K, E_{n,t}) ≃ Hom_K(St, E_{n,t})`. For the arithmetic group `K`
  and the rational coefficients `E_{n,t}` this hypothesis IS proved
  (`neatDualityEquivariant_of_capEps` with `DualityEquivariance.capEps`), giving the unconditional
  `H3_K_equiv`.

* `hecke_cosets_ternary`, `hecke_cosets_binary`, `hecke_block_form`, `hecke_fibres`,
  `hecke_lattice_indices`, `hecke_transfer_sum_formal`, `hecke_transfer_hom`, `threeNR_lattice`: the
  unnumbered lattice and Hecke identities of Appendix A.3 ("The Hecke transfer") and of the paper: the `p² + p + 1` (resp. `p + 1`) matrices form a complete irredundant set of coset
  representatives; the block decomposition `(λ 0; u C)` and the fibre counts `p, p, 1`; the lattice indices
  `e_t` and weights `e_t λ² = p, p, p²`; the formal sum; `T₃(p,1)|_res = p T₂(p) + p² I` in the Hom model of
  the library with determinant exponent `+1`; the lattice fixing a covector contains `3N_R` and `3ℤ²` is
  Zariski dense.

**`K`-level duality.** `H3_K_equiv`: `H₃(K, E_{n,t}) ≃ Hom_K(St, E_{n,t})` (rational Borel-Serre
duality for the group `K` with torsion, first display of the proof of Lemma 3.2), unconditional.  The
`K`-equivariance of the library's neat-level duality is `neatDualityEquivariant_of_capEps` (S3, the
Mayer-Vietoris edge map, `S1` and the assembly); its last input, the compatibility of the cap
product with the fibrewise coefficient reindexing of the conjugation-twisted covering, is `TernaryPeriodPolynomials.Argument.DualityEquivariance.capEps`
.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.FiberModel

open TernaryPoly TernaryPoly.ModThreeGoodAction
open TernaryPeriodPolynomials.Argument.FiberModel

/-- The Steinberg module of the ordinary (full) rational Tits building: the cycles of its edge
chains, with the `K`-action `OrdinaryIncidenceChains.complex.cyclesAction`. -/
abbrev St : Type := OrdinaryIncidenceChains.Cycles

/-- The `K`-equivariant linear maps `St → E_{n,t}` for the left action of `K ⊆ GL₃(ℤ)` on
`E_{n,t} = Sym^n ⊗ det^{-t}` (`coeff`). -/
def HomK (t : Fin 2) (n : ℕ) : Submodule ℚ (St →ₗ[ℚ] V n) := homK (coeff n t)

theorem mem_HomK {t : Fin 2} {n : ℕ} {Φ : St →ₗ[ℚ] V n} :
    Φ ∈ HomK t n ↔ ∀ (k : K) (z : St),
      Φ (OrdinaryIncidenceChains.complex.cyclesAction k z) = coeff n t k.val (Φ z) := Iff.rfl

/-- The covector `ℓ = (1,1,1) ∈ 𝒮`. -/
def ell : Covectors := ⟨![1, 1, 1], by decide⟩

/-- The apartment of the ordered basis formed by the columns of `g ∈ GL₃(ℤ)`. -/
abbrev apartment (g : IntegralGL) : St := OrdinaryApartmentPresentation.frameCycle g

/-- The identity apartment: the apartment of `(e₁, e₂, e₃)`. -/
abbrev identityApartment : St := apartment 1

/-- The identity apartment is the included reference apartment of the Good building. -/
theorem identityApartment_eq : identityApartment =
    OrdinaryIncidenceChains.cycleInclusion GoodUnimodularOrbit.referenceApartment :=
  OrdinaryFiberComparison.frameCycle_one

/-- The residue of the first row of `g` modulo three: the covector `ℓ g`. -/
def ellMul (g : IntegralGL) : Covectors := rowS g

theorem ellMul_one : ellMul 1 = ell := by
  apply Subtype.ext
  funext i
  fin_cases i <;> rfl

/-- The value of the left action on a polynomial, as the paper's `det(g)^{-t} f(g⁻¹ x)`. -/
theorem coeff_apply (n : ℕ) (t : Fin 2) (g : IntegralGL) (f : V n) :
    ((coeff n t g f : V n) : MvPolynomial (Fin 3) ℚ) =
      ((g⁻¹.val.det : ℤ) : ℚ) ^ (t : ℕ) • bar g⁻¹.val f := by
  have h := coeff_inv_apply n t g⁻¹ f
  rwa [inv_inv] at h


/-- **Lemma 3.2 (`prop:26-model`).**  For `t ∈ {0,1}` and every `n`, the functions `F : 𝒮 → V_n`
satisfying `eq:fiber-signed` and `eq:fiber-norm` are in `ℚ`-linear bijection with the
`K`-equivariant linear maps `St → E_{n,t}`: `F` corresponds to the functional `Φ_F` with
`Φ_F(apartment of g) = g · F(ℓ g)` for every `g ∈ GL₃(ℤ)`, and in particular `Φ_F` takes the identity
apartment to `F(ℓ)`. -/
theorem lemma_3_2 (t : Fin 2) (n : ℕ) :
    ∃ e : fiberFunctions t n ≃ₗ[ℚ] HomK t n, ∀ F : fiberFunctions t n,
      (∀ g : IntegralGL, (e F).1 (apartment g) = coeff n t g (F.1 (ellMul g))) ∧
        (e F).1 identityApartment = F.1 ell := by
  refine ⟨fiberEquiv (coeff n t), fun F => ⟨fun g => fiberEquiv_frame F g, ?_⟩⟩
  have h := fiberEquiv_frame F 1
  rw [map_one, Module.End.one_apply] at h
  exact h.trans (congrArg F.1 ellMul_one)

/-- **Lemma 3.2, "represented by precisely the functions".**  A linear map `Φ : St → V_n` is
`K`-equivariant for `E_{n,t}` if and only if there is a function `F : 𝒮 → V_n` satisfying
`eq:fiber-signed` and `eq:fiber-norm` with `Φ(apartment of g) = g · F(ℓ g)` for all `g ∈ GL₃(ℤ)`. -/
theorem lemma_3_2_iff (t : Fin 2) (n : ℕ) (Φ : St →ₗ[ℚ] V n) :
    Φ ∈ HomK t n ↔ ∃ F : Covectors → V n, IsFiberFunction t n F ∧
      ∀ g : IntegralGL, Φ (apartment g) = coeff n t g (F (ellMul g)) := by
  constructor
  · intro h
    refine ⟨((fiberEquiv (coeff n t)).symm ⟨Φ, h⟩).1,
      mem_fiberFunctions.mp ((fiberEquiv (coeff n t)).symm ⟨Φ, h⟩).2, fun g => ?_⟩
    have h1 := fiberEquiv_frame ((fiberEquiv (coeff n t)).symm ⟨Φ, h⟩) g
    rw [LinearEquiv.apply_symm_apply] at h1
    exact h1
  · rintro ⟨F, hF, hΦ⟩
    have hF' : F ∈ fiberFunctions t n := mem_fiberFunctions.mpr hF
    have he : Φ = (fiberEquiv (coeff n t) ⟨F, hF'⟩).1 := by
      apply OrdinaryApartmentPresentation.cycle_functional_ext
      intro g
      rw [hΦ g]
      exact (fiberEquiv_frame ⟨F, hF'⟩ g).symm
    rw [he]
    exact (fiberEquiv (coeff n t) ⟨F, hF'⟩).2

/-- **Lemma 3.2, uniqueness.**  Two functions `F, F' : 𝒮 → V_n` representing the same functional
on the apartments are equal; in particular `F` is determined by its functional. -/
theorem lemma_3_2_unique (t : Fin 2) (n : ℕ) (Φ : St →ₗ[ℚ] V n) (F F' : Covectors → V n)
    (hF : ∀ g : IntegralGL, Φ (apartment g) = coeff n t g (F (ellMul g)))
    (hF' : ∀ g : IntegralGL, Φ (apartment g) = coeff n t g (F' (ellMul g))) : F = F' := by
  funext r
  obtain ⟨g, rfl⟩ := act_surjective r
  have h1 : F (rowS g) = coeff n t g⁻¹ (Φ (apartment g)) := by
    rw [hF g, rho_inv_cancel']
    rfl
  have h2 : F' (rowS g) = coeff n t g⁻¹ (Φ (apartment g)) := by
    rw [hF' g, rho_inv_cancel']
    rfl
  rw [h1, h2]


/-! ### Lemma 4.3 (`lem:three-seed`): the three seeds of a fiber function -/

/-- The covector `(1,0,0)`, whose fiber value is the seed `P`. -/
abbrev covP : Covectors := rep 0

/-- The covector `(1,1,0)`, whose fiber value is the seed `Q`. -/
abbrev covQ : Covectors := rep 1

/-- The covector `(1,1,1) = ℓ`, whose fiber value is the seed `f`. -/
abbrev covF : Covectors := rep 2

theorem covP_val : covP.1 = ![1, 0, 0] := rfl
theorem covQ_val : covQ.1 = ![1, 1, 0] := rfl
theorem covF_val : covF.1 = ![1, 1, 1] := rfl
theorem covF_eq_ell : covF = ell := rfl

/-- **Lemma 4.3 (`lem:three-seed`), polynomial coefficients.**  For functions
`F : 𝒮 → ℚ[x,y,z]` with `F(rh) = χ₁(h) F(r) ∣ h` for all signed permutation matrices `h = Dπ`
(`eq:fiber-signed`, `PolySigned`):

* `F` is uniquely determined by its seeds `P = F(1,0,0)`, `Q = F(1,1,0)`, `f = F(1,1,1)`;
* `F` satisfies `F(r) + F(rA²) ∣ A + F(rA) ∣ A² = 0` (`eq:fiber-norm`, `PolyNorm`) if and only if
  the seeds satisfy the list of the lemma (`PolySeeds`, including `eq:mixed1`, `eq:mixed2`);
* conversely, seeds with these properties extend to a function with `eq:fiber-signed` and
  `eq:fiber-norm`, uniquely among the functions satisfying `eq:fiber-signed` with these seeds. -/
theorem lemma_4_3_polynomial :
    (∀ F F' : Covectors → MvPolynomial (Fin 3) ℚ, PolySigned F → PolySigned F' →
      F covP = F' covP → F covQ = F' covQ → F covF = F' covF → F = F') ∧
    (∀ F : Covectors → MvPolynomial (Fin 3) ℚ, PolySigned F →
      (PolyNorm F ↔ PolySeeds (F covF) (F covP) (F covQ))) ∧
    (∀ f P Q : MvPolynomial (Fin 3) ℚ, PolySeeds f P Q →
      ∃! F : Covectors → MvPolynomial (Fin 3) ℚ,
        PolySigned F ∧ PolyNorm F ∧ F covP = P ∧ F covQ = Q ∧ F covF = f) := by
  refine ⟨fun F F' hF hF' h0 h1 h2 => ?_, fun F hF => ?_, fun f P Q h => ?_⟩
  · exact lemma43_unique isTwist_poly ((polySigned_iff F).mp hF) ((polySigned_iff F').mp hF') h0 h1 h2
  · rw [polyNorm_iff, polySeeds_iff]
    exact lemma43_iff isTwist_poly ((polySigned_iff F).mp hF)
  · obtain ⟨F, ⟨h1, h2, h3, h4, h5⟩, hu⟩ := lemma43_extension isTwist_poly ((polySeeds_iff f P Q).mp h)
    exact ⟨F, ⟨(polySigned_iff F).mpr h1, (polyNorm_iff F).mpr h2, h3, h4, h5⟩,
      fun F' ⟨a, b, c, d, e⟩ => hu F' ⟨(polySigned_iff F').mp a, (polyNorm_iff F').mp b, c, d, e⟩⟩

/-- **Lemma 4.3 (`lem:three-seed`), rational-function coefficients.**  The same three statements for
functions `F : 𝒮 → ℚ(x,y,z)` with values in the field of rational functions, where `x ∣ h`
(`TernaryPeriodPolynomials.Argument.FiberModel.slash`) is the extension of the substitution `f(x) ↦ f(h x)` to rational functions and
the list of the lemma (`SeedList`) is written with the same explicit integer matrices as
`PolySeeds`.  By `seedList_frac_embed_iff` the list for seeds that are polynomials is the
polynomial list of `lemma_4_3_polynomial`. -/
theorem lemma_4_3_rational :
    (∀ F F' : Covectors → RatFun, PaperSigned fracRho0 F → PaperSigned fracRho0 F' →
      F covP = F' covP → F covQ = F' covQ → F covF = F' covF → F = F') ∧
    (∀ F : Covectors → RatFun, PaperSigned fracRho0 F →
      (PaperNorm fracRho0 F ↔ SeedList fracRho0 (F covF) (F covP) (F covQ))) ∧
    (∀ f P Q : RatFun, SeedList fracRho0 f P Q →
      ∃! F : Covectors → RatFun,
        PaperSigned fracRho0 F ∧ PaperNorm fracRho0 F ∧ F covP = P ∧ F covQ = Q ∧ F covF = f) :=
  ⟨fun _ _ hF hF' h0 h1 h2 => lemma43_unique isTwist_frac hF hF' h0 h1 h2,
    fun _ hF => lemma43_iff isTwist_frac hF,
    fun _ _ _ h => lemma43_extension isTwist_frac h⟩


/-! ### The available comparison with group homology (neat level)

The library identifies group homology with equivariant functionals on the Steinberg module only for
the neat principal congruence subgroup `Γ(6)` (`IntegralGL3Congruence.principalSix`), by an
isomorphism built from the bordified symmetric space, relative cap product, and the Mayer-Vietoris
comparison (`OrdinaryTopBoundaryComparison.groupOrdinaryIso`).  This is the `Γ'` instance of the
Borel-Serre duality `H₃(Γ', E) ≅ Hom_{Γ'}(St, E)` used in the proof of Lemma 3.2.  The passage from
`Γ' = Γ(6)` to the group `K` of Lemma 3.2 is split in two: on group homology it is the unconditional
`H3_K_descent_*` below (coinvariants of the finite quotient `K/Γ'`); on `Hom` it is the averaging
(invariants).  The equivariance of the isomorphism for the action of `K/Γ'` is proved for the
arithmetic group `K` and the rational coefficients `E_{n,t}` (`neatDualityEquivariant_of_capEps` with
`DualityEquivariance.capEps`), so `H₃(K, E_{n,t}) ≅ Hom_K(St, E_{n,t})` holds unconditionally
(`H3_K_equiv`); the generic-group form `H3_level_equiv_of_neat_equivariance` keeps its explicit
hypothesis. -/

/-- The neat-level duality: for every rational representation `W` of `Γ(6)`, the group homology
`H₃(Γ(6), W)` (Mathlib's `groupHomology`) is isomorphic to the space of `Γ(6)`-equivariant linear
maps from the Steinberg module (the ordinary incidence cycles) to `W`. -/
def H3_neat_iso (W : Rep.{0} ℚ IntegralGL3Congruence.principalSix) :
    groupHomology W 3 ≅ OrdinaryTopBoundaryComparison.ordinaryFunctionals W :=
  OrdinaryTopBoundaryComparison.groupOrdinaryIso W

open CategoryTheory in
/-- Under the neat-level duality, evaluation of the corresponding Steinberg functional on the
identity apartment is `OrdinaryTopBoundaryComparison.groupApartmentEvaluation`. -/
theorem H3_neat_evaluation (W : Rep.{0} ℚ IntegralGL3Congruence.principalSix) :
    OrdinaryTopBoundaryComparison.groupApartmentEvaluation W =
      (H3_neat_iso W).hom ≫ OrdinaryTopBoundaryComparison.identityApartmentEvaluation W := rfl

/-- The coefficient module `E_{n,t}` restricted to `Γ(6)`. -/
abbrev neatCoefficients (n : ℕ) (t : Fin 2) : Rep.{0} ℚ IntegralGL3Congruence.principalSix :=
  Rep.res IntegralGL3Congruence.principalSix.subtype (Rep.of (coeff n t))

/-- `H₃(Γ(6), E_{n,t}) ≅ Hom_{Γ(6)}(St, E_{n,t})`, the neat-level instance of Lemma 3.2. -/
def H3_neat_coefficients (n : ℕ) (t : Fin 2) :
    groupHomology (neatCoefficients n t) 3 ≅
      OrdinaryTopBoundaryComparison.ordinaryFunctionals (neatCoefficients n t) :=
  H3_neat_iso _


/-! ### From `Γ(6)` to `K` on group homology -/

section KLevel

open TernaryPeriodPolynomials.Argument.FiberModel TernaryPeriodPolynomials.Argument.GroupHomology IntegralGL3Congruence

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- The corestriction `H₃(Γ(6), E_{n,t}) → H₃(K, E_{n,t})` (Mathlib's `groupHomology.map` for the
inclusion `Γ(6) ≤ K`) is surjective. -/
theorem H3_K_descent_surjective (n : ℕ) (t : Fin 2) :
    Function.Surjective (corN principalSixInK (EK n t) 3) :=
  corN_surjective card_ne_zero

/-- The kernel of the corestriction is the kernel of the averaging operator over `K/Γ(6)` of the
conjugation action `c_g = H₃(conj g, ρ g)`. -/
theorem H3_K_descent_ker (n : ℕ) (t : Fin 2)
    (z : groupHomology (Rep.res principalSixInK.subtype (EK n t)) 3) :
    corN principalSixInK (EK n t) 3 z = 0 ↔ avgN principalSixInK (EK n t) 3 z = 0 :=
  corN_eq_zero_iff card_ne_zero z

/-- The corestriction is invariant under the conjugation action of `K`. -/
theorem H3_K_descent_conj (n : ℕ) (t : Fin 2) (g : KT)
    (z : groupHomology (Rep.res principalSixInK.subtype (EK n t)) 3) :
    corN principalSixInK (EK n t) 3 (cAct principalSixInK (EK n t) 3 g z) =
      corN principalSixInK (EK n t) 3 z :=
  corN_cAct g z

/-- The averaging operator over `K/Γ(6)` is idempotent. -/
theorem H3_K_descent_idem (n : ℕ) (t : Fin 2)
    (z : groupHomology (Rep.res principalSixInK.subtype (EK n t)) 3) :
    avgN principalSixInK (EK n t) 3 (avgN principalSixInK (EK n t) 3 z) =
      avgN principalSixInK (EK n t) 3 z :=
  avgN_idem card_ne_zero z

/-- **CONDITIONAL** form of Lemma 3.2 (first display of its proof): `H₃(K, E_{n,t}) ≃ Hom_K(St,
E_{n,t})`, assuming that the library's neat-level duality `H₃(Γ(6), E) ≅ Hom_{Γ(6)}(St, E)` is
`K`-equivariant (`NeatDualityEquivariant`).  This helper keeps the hypothesis explicit; for the
arithmetic `K` and `E_{n,t}` it is discharged by `neatDualityEquivariant_of_capEps` and
`DualityEquivariance.capEps`, see `H3_K_equiv`. -/
def H3_K_equiv_of_neat_equivariance (n : ℕ) (t : Fin 2) (h : NeatDualityEquivariant n t) :
    groupHomology (EK n t) 3 ≃ₗ[ℚ] homK (coeff n t) :=
  kEquivOfEquivariance h

open TernaryPeriodPolynomials.Argument.FiberModel in
/-- **Lemma 3.2, first display of the proof (unconditional).**  `H₃(K, E_{n,t}) ≃ Hom_K(St, E_{n,t})`
in Mathlib's `groupHomology`: the conditional equivalence `H3_K_equiv_of_neat_equivariance` with its
hypothesis discharged by `neatDualityEquivariant_of_capEps`. -/
def H3_K_equiv (n : ℕ) (t : Fin 2) :
    groupHomology (EK n t) 3 ≃ₗ[ℚ] homK (coeff n t) :=
  H3_K_equiv_of_neat_equivariance n t
    (neatDualityEquivariant_of_capEps n t (fun k => TernaryPeriodPolynomials.Argument.DualityEquivariance.capEps k (Rep.of (coeff n t))))

open TernaryPeriodPolynomials.Argument.FiberModel in
/-- **CONDITIONAL, generic coefficients.**  For any group `Kp` with a normal finite index subgroup `N`
identified with `Γ(6)` (`e : N ≃* Γ(6)`), a representation `σ` of `Kp` on the Steinberg module extending
the library's action of `Γ(6)`, and any `ℚ`-representation `M` of `Kp`: if the neat-level duality is
`Kp`-equivariant (`NeatDualityEquivariantGen`), then `H₃(Kp, M) ≃ Hom_{Kp}(St, M)`. -/
def H3_level_equiv_of_neat_equivariance {Kp : Type} [Group Kp] (N : Subgroup Kp) [N.Normal]
    [N.FiniteIndex] (e : N ≃* IntegralGL3Congruence.principalSix)
    (σ : Representation ℚ Kp OrdinaryIncidenceChains.Cycles) (M : Rep.{0} ℚ Kp)
    (hσ : ∀ n : N, σ n = SymmetricSpaceBoundaryIncidenceHomology.ordinaryCyclesRep.ρ (e n))
    (h : NeatDualityEquivariantGen N e σ M) :
    groupHomology M 3 ≃ₗ[ℚ] homKGen σ M :=
  kEquivGeneric hσ h

open TernaryPeriodPolynomials.Argument.FiberModel TernaryPoly.EquivariantSingularResolution CategoryTheory in
/-- **Item (i), upstairs half.**  For a group `G` acting continuously on a contractible space `E`, a
normal finite index subgroup `N` acting freely, and `A : Rep ℚ G`: the library's comparison
`H_n(N, Res A) ≅ H_n((Sing(E) ⊗ A)_N)` intertwines Mathlib's conjugation action
`c_g = groupHomology.map (conj g) (ρ g)` with the diagonal action of `g` on `(Sing(E) ⊗ A)_N`. -/
theorem S1_upstairs_conj {G : Type} [Group G] (E : TopCat.{0}) [MulAction G E]
    [ContinuousConstSMul G E] [ContractibleSpace E] (N : Subgroup G) [N.Normal]
    [IsCancelSMul N E] (A : Rep.{0} ℚ G) (n : ℕ) (g : G) :
    groupHomology.map (conjN N g) (conjRep N A g) n ≫
        (TernaryPoly.SingularLocalHomology.groupCoinvariantHomologyIso N E (Rep.res N.subtype A) n).hom =
      (TernaryPoly.SingularLocalHomology.groupCoinvariantHomologyIso N E (Rep.res N.subtype A) n).hom ≫
        HomologicalComplex.homologyMap (GY N (Ygeo E A) g) n :=
  groupCoinvariantHomologyIso_conj E N A n g

end KLevel

/-! ### The Hecke transfer for `diag(1,1,p)` (Appendix A.3)

`p` is a prime, matrices are integral, `GL₃(ℤ) = GL (Fin 3) ℤ`.  The cosets are `m · GL₃(ℤ)`, i.e. the
index-`p` sublattices `m ℤ³` (classified by the normalized annihilating covector modulo `p`). -/

section Hecke

open TernaryPeriodPolynomials.Argument.FiberModel Matrix

/-- **Representatives of the double coset of `diag(1,1,p)`** (ternary, `p² + p + 1` of them): they lie in
`GL₃(ℤ) diag(1,1,p) GL₃(ℤ)`, define pairwise distinct cosets `m GL₃(ℤ)`, and every element of the double
coset lies in one of them. -/
theorem hecke_cosets_ternary (p : ℕ) [Fact p.Prime] :
    (∀ i : HeckeIdx p, repT p i ∈ DC3 p) ∧
      (∀ (i j : HeckeIdx p) (γ : GL (Fin 3) ℤ),
        repT p i = repT p j * (γ : Matrix (Fin 3) (Fin 3) ℤ) → i = j) ∧
      (∀ g ∈ DC3 p, ∃ (i : HeckeIdx p) (γ : GL (Fin 3) ℤ),
        g = repT p i * (γ : Matrix (Fin 3) (Fin 3) ℤ)) :=
  ⟨repT_mem p, fun i j γ h => repT_inj p i j γ h, fun g hg => repT_complete p g hg⟩

/-- The same for the `p + 1` binary blocks `C_c = (1 0; c p)`, `C_∞ = diag(p, 1)` of
`GL₂(ℤ) diag(1,p) GL₂(ℤ)`. -/
theorem hecke_cosets_binary (p : ℕ) [Fact p.Prime] :
    (∀ i : HeckeIdx2 p, repB p i ∈ DC2 p) ∧
      (∀ (i j : HeckeIdx2 p) (γ : GL (Fin 2) ℤ),
        repB p i = repB p j * (γ : Matrix (Fin 2) (Fin 2) ℤ) → i = j) ∧
      (∀ g ∈ DC2 p, ∃ (i : HeckeIdx2 p) (γ : GL (Fin 2) ℤ),
        g = repB p i * (γ : Matrix (Fin 2) (Fin 2) ℤ)) :=
  ⟨repB_mem p, fun i j γ h => repB_inj p i j γ h, fun g hg => repB_complete p g hg⟩

/-- Every representative is `(λ 0; u C)` with first row `(λ, 0, 0)` (it preserves `H = {a = 0}`):
the first family has `λ = 1`, `u = (0, b)`, `C = C_c`; the second `λ = 1`, `u = (a, 0)`, `C = C_∞`; the
last `λ = p`, `u = 0`, `C = I`. -/
theorem hecke_block_form (p : ℕ) (i : HeckeIdx p) :
    repT p i = blockM (lamOf p i) (uOf p i) (cOf p i) ∧
      repT p i 0 0 = lamOf p i ∧ repT p i 0 1 = 0 ∧ repT p i 0 2 = 0 :=
  ⟨repT_block p i, repT_first_row p i⟩

/-- Exactly `p` representatives lie above each of `C_0, …, C_{p-1}` and above `C_∞`, and exactly one
(`diag(p,1,1)`) above `I`. -/
theorem hecke_fibres (p : ℕ) [Fact p.Prime] :
    (∀ c : Fin p, (Finset.univ.filter (fun i : HeckeIdx p => cOf p i = repB p (.inl c))).card = p) ∧
      (Finset.univ.filter (fun i : HeckeIdx p => cOf p i = repB p (.inr ()))).card = p ∧
      (Finset.univ.filter (fun i : HeckeIdx p => cOf p i = 1)).card = 1 :=
  ⟨fun c => fibre_card_c p c, fibre_card_inf p, fibre_card_one p⟩

/-- `U_t = ℤ² ∩ (C/λ)ℤ²`, `e_t = [ℤ² : U_t]`: `e_t = p` for `λ = 1`, `C ∈ {C_c, C_∞}`; `e_t = 1` for
`λ = p`, `C = I`; the radical quotient `ℤ²/U_t` is represented by `(0, b)` (resp. `(a, 0)`), and
`e_t λ² = p, p, p²`. -/
theorem hecke_lattice_indices (p : ℕ) [Fact p.Prime] :
    (∀ c : Fin p, eIdx 1 (repB p (.inl c)) = p) ∧ eIdx 1 (repB p (.inr ())) = p ∧
      eIdx (p : ℤ) 1 = 1 ∧
      (∀ (c : Fin p) (v : Fin 2 → ℤ), ∃! b : Fin p, v - ![0, (b : ℤ)] ∈ latU 1 (repB p (.inl c))) ∧
      (∀ v : Fin 2 → ℤ, ∃! a : Fin p, v - ![(a : ℤ), 0] ∈ latU 1 (repB p (.inr ()))) ∧
      (∀ c : Fin p, eIdx 1 (repB p (.inl c)) * 1 ^ 2 = p) ∧
        eIdx 1 (repB p (.inr ())) * 1 ^ 2 = p ∧ eIdx (p : ℤ) 1 * p ^ 2 = p ^ 2 :=
  ⟨eIdx_c p, eIdx_inf p, eIdx_one p, quotient_reps_c p, quotient_reps_inf p, (weights p).1,
    (weights p).2.1, (weights p).2.2⟩

/-- The transfer sum as a formal combination of binary blocks:
`∑_i λ_i² [C_i] = p (∑_c [C_c] + [C_∞]) + p² [I]`. -/
theorem hecke_transfer_sum_formal (p : ℕ) :
    ∑ i : HeckeIdx p, (lamOf p i) ^ 2 • Finsupp.single (cOf p i) (1 : ℤ) =
      (p : ℤ) • (∑ c : Fin p, Finsupp.single (repB p (.inl c)) (1 : ℤ) +
        Finsupp.single (repB p (.inr ())) (1 : ℤ)) +
      (p : ℤ) ^ 2 • Finsupp.single (1 : Matrix (Fin 2) (Fin 2) ℤ) (1 : ℤ) :=
  transfer_sum_formal p

open TernaryPoly TernaryPoly.OrdinaryResidueSymbol TernaryPoly.OrdinaryResidueParabolic
  TernaryPoly.SinglePole in
/-- **`T₃(p,1)|_res = p T₂(p) + p² I`** for the library's Hom-model Hecke correspondences, with the
paper's determinant exponent `+1 = -1 + 2` on both sides: `T₃ = OrdinaryHomHecke.rationalHecke`
of `diag(p,1,1)` on `Hom_G(St, R_n ⊗ det)`, `T₂ = BinaryRationalHecke.rationalHecke` of `diag(p,1)` on
`Hom_{GL₂(ℤ)}(St₂, Sym^{n+1} ⊗ det)`, residue coordinate on the plane cone `toBinaryHom`.  The elements
of the exponent-`+1` Hom spaces are the same functionals as `F` and its residue coordinate
(`det = ±1` on the integral groups; `mem_lift_ternary`, `mem_lift_binary`). -/
theorem hecke_transfer_hom (n p : ℕ) [Fact p.Prime]
    (F : OrdinaryFullCoefficient.ResidueHom n (-1)) (c : BinaryModularSymbol.St) :
    zeroCoordinate n
        ((OrdinaryHomHecke.rationalHecke (OrdinaryHeckeCosets.primeDiagonal p)
          (residueAction n (-1 + 2))
          (⟨F.val, mem_lift_ternary n (-1) F⟩ : OrdinaryFullCoefficient.ResidueHom n (-1 + 2))).val
          (OrdinaryPlaneEdge.binaryCone c)) =
      (p : ℚ) • (BinaryRationalHecke.rationalHecke (BinaryRationalHeckePrime.primeDiagonal p)
          (BinaryModularSymbolCoefficients.homogeneousAction (n + 1) (-1 + 2))
          (⟨(toBinaryHom n F).val, mem_lift_binary (n + 1) (-1) (toBinaryHom n F)⟩ :
            BinaryModularSymbol.Hom
              (BinaryModularSymbolCoefficients.homogeneousAction (n + 1) (-1 + 2)))).val c +
        (p : ℚ) ^ 2 • (toBinaryHom n F).val c :=
  hecke_transfer_lifted n p F c

/-- The lattice fixing a covector `ℓ` modulo three contains `3 N_R` (for the radicals `N_P`, `N_Q`
of the two maximal parabolics), and `3ℤ²` is Zariski dense. -/
theorem threeNR_lattice :
    (∀ (x y : ℤ) (ℓ : Fin 3 → ZMod 3),
      ℓ ᵥ* (radP (3 * x) (3 * y)).map (Int.castRingHom (ZMod 3)) = ℓ ∧
        ℓ ᵥ* (radQ (3 * x) (3 * y)).map (Int.castRingHom (ZMod 3)) = ℓ) ∧
      (∀ P : MvPolynomial (Fin 2) ℚ,
        (∀ a b : ℤ, MvPolynomial.eval ![(3 * a : ℚ), 3 * b] P = 0) → P = 0) :=
  ⟨threeNR_fixes_covector, threeLattice_zariskiDense⟩

end Hecke

/-! ### The binary group `Γ₂` (`eq:Gamma-presentation`) and its cusps

`Γ₂ = {g ∈ GL₂(ℤ) : (0,1) g = (0,1) (mod 3)}` (`TernaryPeriodPolynomials.Argument.FiberModel.Gamma2`) is the free product of
`⟨A₀, B₀⟩ ≅ 𝔖₃` and `⟨R₀⟩ ≅ C₂`, where `U₀ = (1 0; 3 1)`, `T = (1 1; 0 1)`,
`A₀ = U₀ T⁻¹ = (1 -1; 3 -2)`, `R₀ = diag(-1, 1)`, `B₀ = U₀ R₀ = (-1 0; -3 1)`. -/

open TernaryPeriodPolynomials.Argument.FiberModel in
/-- The relations of the paper: `A₀³ = 1`, `B₀² = R₀² = 1`, `B₀ A₀ B₀ = A₀⁻¹`,
`R₀ U₀ R₀ = U₀⁻¹`, `R₀ A₀ R₀ = U₀⁻¹ A₀⁻¹ U₀`, `A₀ = U₀ T⁻¹`, `B₀ = U₀ R₀`. -/
theorem gamma2_relations :
    A0 ^ 3 = 1 ∧ B0 ^ 2 = 1 ∧ R0 ^ 2 = 1 ∧ B0 * A0 * B0 = A0⁻¹ ∧ R0 * U0 * R0 = U0⁻¹ ∧
      R0 * A0 * R0 = U0⁻¹ * A0⁻¹ * U0 ∧ A0 = U0 * Tm⁻¹ ∧ B0 = U0 * R0 :=
  ⟨A0_cube, B0_sq, R0_sq, B0_A0, R0_U0, R0_A0, A0_eq, B0_eq⟩

open TernaryPeriodPolynomials.Argument.FiberModel in
/-- **`eq:Gamma-presentation`.**  The natural map from the free product of `⟨A₀, B₀⟩` and `⟨R₀⟩` to
`Γ₂` is bijective, `⟨A₀, B₀⟩ ≅ 𝔖₃` (a three-cycle goes to `A₀`, a transposition to `B₀`) and
`⟨R₀⟩ ≅ C₂`. -/
theorem gamma2_presentation :
    Function.Bijective
      (Monoid.CoprodI.lift (fun i : Fin 2 => (Gamma2Factor i).subtype)) ∧
    Nonempty (Equiv.Perm (Fin 3) ≃* ↥(Gamma2Factor 0)) ∧
    Nonempty (Multiplicative (ZMod 2) ≃* ↥(Gamma2Factor 1)) :=
  ⟨lift_bijective, ⟨factor0Equiv⟩, ⟨factor1Equiv⟩⟩

open TernaryPeriodPolynomials.Argument.FiberModel in
/-- **`Γ₂ ≅ 𝔖₃ * C₂`.**  An isomorphism of `Γ₂` with the free product of `𝔖₃ = Equiv.Perm (Fin 3)`
and `C₂ = Multiplicative (ZMod 2)` (the factors are `Fac 0` and `Fac 1`), sending the three-cycle to
`A₀`, a transposition to `B₀` and the generator of `C₂` to `R₀`. -/
theorem gamma2_free_product : Nonempty (↥Gamma2 ≃* Monoid.CoprodI Fac) :=
  ⟨freeProductToGamma2.symm.trans freeProductCongr.symm⟩

open TernaryPeriodPolynomials.Argument.FiberModel in
/-- **Cusp orbits (two orbits).**  `Γ₁(3) = Γ₂ ∩ SL₂(ℤ)` acts on the rational lines of `ℚ²`
(`lineImage`); every rational line is in the orbit of `ℚ e₁` or of `ℚ e₂`, and no element of `Γ₂` (a
fortiori of `Γ₁(3)`) takes `ℚ e₁` to `ℚ e₂`. -/
theorem cusp_orbits :
    (∀ L : Submodule ℚ (Fin 2 → ℚ), IsRatLine L →
      (∃ g ∈ Gamma1_3, lineImage g (lineE 0) = L) ∨ (∃ g ∈ Gamma1_3, lineImage g (lineE 1) = L)) ∧
    ¬ ∃ g ∈ Gamma2, lineImage g (lineE 0) = lineE 1 :=
  ⟨cusp_orbits_exhaustive, cusp_orbits_distinct⟩

open TernaryPeriodPolynomials.Argument.FiberModel in
/-- **Cusp widths one and three.**  The unipotent determinant-one matrices fixing `ℚ e₁` are the
translations `T^k = (1 k; 0 1)`, all in `Γ₁(3)`: width one.  The unipotent determinant-one matrices
fixing `ℚ e₂` are the lower unipotents `(1 0; k 1)`, and such a matrix lies in `Γ₁(3)` exactly for
`k = 3m`, `(1 0; 3m 1) = U₀^m`: width three. -/
theorem cusp_widths :
    (∀ k : ℤ, tk k ∈ Gamma1_3 ∧ lineImage (tk k) (lineE 0) = lineE 0) ∧
    (∀ g : GL2Z, g.val.det = 1 → g.val 0 0 + g.val 1 1 = 2 →
      lineImage g (lineE 0) = lineE 0 → ∃ k : ℤ, g = tk k) ∧
    (∀ m : ℤ, uk m ∈ Gamma1_3 ∧ lineImage (uk m) (lineE 1) = lineE 1) ∧
    (∀ g : GL2Z, g.val.det = 1 → g.val 0 0 + g.val 1 1 = 2 →
      lineImage g (lineE 1) = lineE 1 → ∃ k : ℤ, g.val = !![1, 0; k, 1]) ∧
    (∀ k : ℤ, mkSL 1 0 k 1 (by ring) ∈ Gamma1_3 ↔ 3 ∣ k) ∧
    (∀ g ∈ Gamma1_3, g.val 0 0 + g.val 1 1 = 2 → lineImage g (lineE 1) = lineE 1 →
      ∃ m : ℤ, g = uk m) :=
  ⟨fun k => ⟨tk_mem_Gamma1_3 k, tk_fix_e1 k⟩, fun g hd ht hf => stab_e1 g hd ht hf,
    fun m => ⟨uk_mem_Gamma1_3 m, uk_fix_e2 m⟩, fun g hd ht hf => stab_e2 g hd ht hf,
    fun k => lower_mem_Gamma1_3_iff k, fun g hg ht hf => stab_e2_Gamma1_3 g hg ht hf⟩

end TernaryPeriodPolynomials.Argument.Statements.FiberModel
