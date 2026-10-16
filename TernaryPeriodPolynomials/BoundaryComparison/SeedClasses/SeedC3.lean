module

public import Mathlib.NumberTheory.ModularForms.Basic
public import TernaryPeriodPolynomials.BoundaryComparison.StokesComparison
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.ParabolicEquivariance
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.BinaryComparison
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.RadicalPoincare
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.RadicalEichlerClass
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.EichlerLevelOne
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.ZigZagMain
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.SeedCusp
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.PlaneOfSubgroup
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.GammaNPlane
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.ReflectionDescent
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.ReflectionLevel
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Level.Seed
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.ESLevelOne
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Level3ES
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Seed.SpanEq
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.GammaNSeed

@[expose] public section


/-!
# Lemma C.3 (`ar:lem:seed`): literal exports

The target `seed_closed_equivariant` carries the closedness, the radical-translation clause, the Levi
transformation law and the potential of the seed. The statements below add the remaining literal
clauses of the lemma that are proved in the library's model.

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial UpperHalfPlane ModularForm
open scoped UpperHalfPlane MatrixGroups Pointwise

namespace TernaryPeriodPolynomials.Argument.Statements.SeedC3

open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3

/-- **Lemma C.3, equivariance for `Γ_P` with coefficients `E`.** For a cusp form `f` of weight
`k = n + 3` for a group `Λ_P` of determinant-one binary matrices, `h = f ∘ ofComplex`, and every
parabolic element `g = [[γ, w], [0, 1]]` with `γ ∈ Λ_P`, `w ∈ ℝ²`, the seed satisfies
`g^* ω_h = ρ(g) ω_h` with the literal action `ρ(g)q(𝐗) = det(g)⁻¹ q(g⁻¹𝐗)`. -/
theorem seed_equivariant_cuspForm (Λ : Subgroup (GL (Fin 2) ℝ)) [Λ.HasDetOne] (n : ℕ)
    (f : CuspForm Λ ((n + 3 : ℕ) : ℤ)) (γ : GL (Fin 2) ℝ) (hγ : γ ∈ Λ) (w : Fin 2 → ℝ)
    (p : Fin 5 → ℝ) (hp : 0 < p 3) (i j : Fin 5) :
    formPullback (parabolicMap (γ : Matrix (Fin 2) (Fin 2) ℝ) w)
        (seedForm n (fun z => f (ofComplex z))) p i j =
      rho (parabolicMatrix (γ : Matrix (Fin 2) (Fin 2) ℝ) w)
        (seedForm n (fun z => f (ofComplex z)) p i j) :=
  seed_parabolic_equivariant Λ n f γ hγ w p hp i j

/-- **Lemma C.3, the radical cochain is a cocycle.** The radical cochain
`(ω_h(e₁, ∂_x), ω_h(e₂, ∂_x)) = h(τ)𝓑ⁿ(1, -τ)` of the seed is a Lie cocycle of the radical
`⟨e₁, e₂⟩` acting by `ν₁ = -Z∂_X`, `ν₂ = -Z∂_Y` on `ℂ[X, Y, Z]`, at every point. -/
theorem seed_radical_cocycle (n : ℕ) (h : ℂ → ℂ) (p : Fin 5 → ℝ) :
    IsRadicalCocycle (seedForm n h p 0 2) (seedForm n h p 1 2) :=
  seedRadical_isCocycle n h p

/-- **Lemma C.3, the radical class.** The potential-modulo-`Z` class of the radical cochain of the
seed is `-(h(τ)/(n+1)) (τY - X)^{n+1}`; the scalar `-1/(n+1)` is nonzero. Exact pairs
`(ν₁ e, ν₂ e)` have zero class. -/
theorem seed_radical_class (n : ℕ) (h : ℂ → ℂ) (p : Fin 5 → ℝ) :
    radicalContraction n (seedForm n h p 0 2) (seedForm n h p 1 2) =
      -(C (((n : ℂ) + 1)⁻¹ * h (seedTau p)) * (C (seedTau p) * X 1 - X 0) ^ (n + 1)) :=
  seedRadical_contraction n h p

theorem radical_class_coboundary (n : ℕ) (e : MvPolynomial (Fin 3) ℂ) :
    radicalContraction n (radicalOpX e) (radicalOpY e) = 0 :=
  radicalContraction_coboundary n e

/-- **The radical cohomology is the binary forms (injectivity).** A closed homogeneous pair of
degree `n` has zero potential-modulo-`Z` class iff it is exact, `(a, b) = (ν₁ e, ν₂ e)`. -/
theorem radical_class_eq_zero_iff (n : ℕ) (a b : MvPolynomial (Fin 3) ℂ)
    (hab : IsRadicalCocycle a b) (ha : a.IsHomogeneous n) (hb : b.IsHomogeneous n) :
    radicalContraction n a b = 0 ↔
      ∃ e : MvPolynomial (Fin 3) ℂ, e.IsHomogeneous n ∧ a = radicalOpX e ∧ b = radicalOpY e :=
  radicalContraction_eq_zero_iff n a b hab ha hb

/-- **The radical cohomology is the binary forms (surjectivity).** Every homogeneous potential of
degree `n + 1` is the potential of a closed homogeneous pair of degree `n` (its gradient). -/
theorem radical_class_surjective (n : ℕ) (Q : MvPolynomial (Fin 3) ℂ)
    (hQ : Q.IsHomogeneous (n + 1)) :
    ∃ a b : MvPolynomial (Fin 3) ℂ, IsRadicalCocycle a b ∧ a.IsHomogeneous n ∧
      b.IsHomogeneous n ∧ radicalContraction n a b = setZ Q :=
  exists_cocycle_with_contraction n Q hQ

/-- **Lemma C.3, comparison with the binary cusp-form class (level one).** The radical class of the
seed of `f ∈ S_{n+3}(SL₂(ℤ))`, evaluated at `(x, y, 0)`, is `-(n+1)⁻¹` times the library's
Eichler--Shimura period integrand, and `-(n+1)⁻¹ ·` the library's Eichler integral is a primitive
of it on the upper half-plane. -/
theorem seed_radical_class_eq_binary (n : ℕ) (f : TernaryPoly.BinaryCuspPeriod.Forms (n + 1))
    (p : Fin 5 → ℝ) (hp : 0 < p 3) (x y : ℂ) :
    eval ![x, y, 0] (radicalContraction n (seedForm n (fun z => f (ofComplex z)) p 0 2)
        (seedForm n (fun z => f (ofComplex z)) p 1 2)) =
        -(((n : ℂ) + 1)⁻¹ * TernaryPoly.BinaryCuspPeriod.periodIntegrand f x y (seedTau p)) ∧
      HasDerivAt (fun z => -(((n : ℂ) + 1)⁻¹ * TernaryPoly.BinaryCuspPeriod.eichlerIntegral f x y z))
        (eval ![x, y, 0] (radicalContraction n (seedForm n (fun z => f (ofComplex z)) p 0 2)
          (seedForm n (fun z => f (ofComplex z)) p 1 2))) (seedTau p) :=
  ⟨seedRadical_eval_eq_periodIntegrand n f p x y, seedRadical_primitive n f p hp x y⟩

/-- **Lemma C.3, radical class = Eichler--Shimura class, class level, any `Λ_P`.** For every
group `Λ_P` of determinant-one binary matrices and every cusp form `f` of weight `n + 3` for it:
the Eichler cocycle is a homogeneous binary-form-valued 1-cocycle, the radical cocycle of the seed
is `-(n+1)⁻¹` times it, and the radical cocycle is the period cocycle of the primitive of the
radical class of `ω_h` at every plane point. See `RadicalEichlerPackage`. -/
theorem seed_radical_class_eq_eichler_class (Λ : Subgroup (GL (Fin 2) ℝ)) [Λ.HasDetOne] (n : ℕ)
    (f : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    ∃ G : ℕ → ℂ → ℂ, RadicalEichlerPackage Λ n f G :=
  _root_.TernaryPeriodPolynomials.Argument.SeedC3.seed_radical_class_eq_eichler_class Λ n f

/-- The paper's `Λ_P`: the principal congruence subgroup `Γ(N) ⊂ SL₂(ℤ)` (`3 ∣ N`, neat)
embedded in `GL₂(ℝ)`. -/
theorem seed_radical_class_eq_eichler_class_principal (N n : ℕ)
    (f : CuspForm ((CongruenceSubgroup.Gamma N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
      ((n + 3 : ℕ) : ℤ)) :
    ∃ G : ℕ → ℂ → ℂ, RadicalEichlerPackage _ n f G :=
  _root_.TernaryPeriodPolynomials.Argument.SeedC3.seed_radical_class_eq_eichler_class _ n f

/-- A rational (indeed real) conjugate of the principal congruence subgroup. -/
theorem seed_radical_class_eq_eichler_class_conjugate (N n : ℕ) (g : ConjAct (GL (Fin 2) ℝ))
    (f : CuspForm (g • ((CongruenceSubgroup.Gamma N : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ))) ((n + 3 : ℕ) : ℤ)) :
    ∃ G : ℕ → ℂ → ℂ, RadicalEichlerPackage _ n f G :=
  _root_.TernaryPeriodPolynomials.Argument.SeedC3.seed_radical_class_eq_eichler_class _ n f

/-- **Agreement with the library's level-one cocycle.** For `g ∈ SL₂(ℤ)`, the library's
transformation constants of its Eichler integral equal the general Eichler cocycle up to the
coboundary of `κ(v) = eichlerIntegral f v₀ v₁ i`. -/
theorem slConstant_eq_eichlerCocycle_add (n : ℕ) (f : TernaryPoly.BinaryCuspPeriod.Forms (n + 1))
    (G : ℕ → ℂ → ℂ) (hG0 : ∀ j, G j Complex.I = 0)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (G j) (f (ofComplex z) * z ^ j) z)
    (g : SL(2, ℤ)) (v : Fin 2 → ℂ) :
    TernaryPoly.BinaryCuspSymbol.slConstant f g v =
      eval v (eichlerCocycle n G (g : GL (Fin 2) ℝ)) +
        TernaryPoly.BinaryCuspPeriod.eichlerIntegral f (v 0) (v 1) Complex.I -
          TernaryPoly.BinaryCuspPeriod.eichlerIntegral f
            (TernaryPoly.BinaryCuspSymbol.slCoordinates g⁻¹ v 0)
            (TernaryPoly.BinaryCuspSymbol.slCoordinates g⁻¹ v 1) Complex.I :=
  _root_.TernaryPeriodPolynomials.Argument.SeedC3.slConstant_eq_eichlerCocycle_add n f G hG0 hG g v

/-- **Agreement with the library's level-one cocycle, inside `Sym^{n+1}`.** The library's
`slConstant` equals the Eichler cocycle plus the coboundary of a homogeneous binary form
`P` of degree `n + 1`, as an identity of polynomials in `v`. -/
theorem slConstant_eq_eichlerCocycle_add_coboundary (n : ℕ)
    (f : TernaryPoly.BinaryCuspPeriod.Forms (n + 1)) (G : ℕ → ℂ → ℂ)
    (hG0 : ∀ j, G j Complex.I = 0)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (G j) (f (ofComplex z) * z ^ j) z) :
    ∃ P : MvPolynomial (Fin 2) ℂ, P.IsHomogeneous (n + 1) ∧
      ∀ (g : SL(2, ℤ)) (v : Fin 2 → ℂ), TernaryPoly.BinaryCuspSymbol.slConstant f g v =
        eval v (eichlerCocycle n G (g : GL (Fin 2) ℝ) + P -
          bind₁ (invCoordPoly (g : GL (Fin 2) ℝ)) P) :=
  _root_.TernaryPeriodPolynomials.Argument.SeedC3.slConstant_eq_eichlerCocycle_add_coboundary
    n f G hG0 hG

/-- **S4a: the de Rham class map of a group acting on a convex open set.** For a group `G` acting
by smooth maps on a nonempty convex open set `s` of a finite-dimensional real normed space, and a
finite-dimensional real representation `ρ`, the class in `H²(G, F)` of a closed `ρ`-equivariant
2-form `ω` (`dω = 0`, `g^*ω = ρ(g)ω`) is the class of the zig-zag cocycle of ANY data
`(η, θ_g)` with `dη = ω`, `dθ_g = g^*η − ρ(g)η`; it is linear in `ω`
(`SeedC3.ZigZag.deRhamClass`). -/
theorem deRham_class_eq_of_datum {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [CompleteSpace F] {s : Set E} {G : Type} [Group G] (hs : IsOpen s) (hc : Convex ℝ s)
    (hne : s.Nonempty) (A : SeedC3.ZigZag.Action G s) (ρ : Representation ℝ G F)
    (om : SeedC3.ZigZag.invClosed hs A ρ)
    (D : SeedC3.ZigZag.Datum (TernaryPoly.SmoothLocalDeRham.d hs 0)
      (TernaryPoly.SmoothLocalDeRham.d hs 1) (fun g => SeedC3.ZigZag.pullForm hs A g 1)
      (fun g => SeedC3.ZigZag.twForm (SeedC3.ZigZag.repCLM ρ g) 1)
      (om : TernaryPoly.SmoothLocalDeRham.Form (F := F) s 2)) :
    SeedC3.ZigZag.deRhamClass hs hc hne A ρ om =
      SeedC3.ZigZag.zigzagClass (SeedC3.ZigZag.laws hs hc hne A ρ) D :=
  SeedC3.ZigZag.deRhamClass_eq hs hc hne A ρ om D

/-! ### S4b: the class of the seed in `H²(Γ_P, E_n)` (zig-zag, face model)

Conventions. `Γ_P` is any group `G` with `PlaneData` (`λ : G →* SL₂`, `w`, `[[λ_g, w_g], [0, 1]]`;
`PlaneData.ofSubgroup` for subgroups of `GL₃(ℝ)`), acting on the convex face
`e(P) = ℝ² × ℍ` by `act`; the coefficients `E_n` are the degree-`n` forms in `X, Y, Z` with the
REAL representation `ρ(g) q(𝐗) = det(g)⁻¹ q(g⁻¹𝐗)` (`PlaneData.rhoR`); the group cohomology is
Mathlib's `groupCohomology.H2` of `Rep.of ρ` (inhomogeneous cocycles,
`c(gh, j) + c(g, h) = g • c(h, j) + c(g, hj)`); the cochain of the data `(η, θ_g)` with
`dη = ω_h`, `dθ_g = g^*η − ρ(g)η` is `c(g, k) = k^*θ_g + ρ(g)θ_k − θ_{gk}`. -/

/-- **S4b, (1): `dη = ω_h`.** The primitive `η = Ψ dτ` of the seed on the face: the coefficients of
`dη` on the coordinate basis `(∂_{u₁}, ∂_{u₂}, ∂_x, ∂_y)` are the `seedForm`. -/
theorem seed_primitive_d_eta (h : ℂ → ℂ) (n : ℕ) (hh : DifferentiableOn ℂ h SeedC3.Psi.upperSet)
    {x : SeedC3.Face} (hx : x ∈ SeedC3.faceSet) (i j : Fin 4) :
    SeedC3.Coef.toPoly ((TernaryPoly.SmoothLocalDeRham.d SeedC3.isOpen_faceSet 1
        (SeedC3.Psi.etaForm h hh n) : TernaryPoly.SmoothLocalDeRham.RawForm SeedC3.Face
          (SeedC3.Coef n) 2) x ![Pi.single i 1, Pi.single j 1]) =
      seedForm n h (SeedC3.Psi.ptOf x) i.castSucc j.castSucc :=
  SeedC3.PlaneData.toPoly_d_etaForm h n hh hx i j

/-- **S4b, (2): `dθ_g = g^*η − ρ(g)η`.** -/
theorem seed_primitive_defect {G : Type} [Group G] (D : SeedC3.PlaneData G) (h : ℂ → ℂ) (n : ℕ)
    (Gm : ℕ → ℂ → ℂ) (hh : DifferentiableOn ℂ h SeedC3.Psi.upperSet)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (Gm j) (h z * z ^ j) z)
    (hmod : ∀ g : G, ∀ z : ℂ, 0 < z.im →
      h (SeedC3.mob (D.lam g) z) = SeedC3.dnm (D.lam g) z ^ (n + 3) * h z) (g : G) :
    TernaryPoly.SmoothLocalDeRham.d SeedC3.isOpen_faceSet 0 (D.thetaForm h n Gm g hG) =
      SeedC3.ZigZag.pullForm SeedC3.isOpen_faceSet D.action g 1 (SeedC3.Psi.etaForm h hh n) -
        SeedC3.ZigZag.twForm (SeedC3.ZigZag.repCLM (D.rhoR n) g) 1 (SeedC3.Psi.etaForm h hh n) :=
  D.dTheta_eq h n Gm hh hG hmod g

/-- **S4b, (1): the class of the seed of a cusp form** in Mathlib's `groupCohomology.H2` of the
real representation `E_n` of `Γ_P`: the de Rham class (zig-zag) of the closed equivariant form
`ω_h = dη`. -/
theorem seed_deRham_class {G : Type} [Group G] (Λ : Subgroup (GL (Fin 2) ℝ)) [Λ.HasDetOne]
    (n : ℕ) (f : CuspForm Λ ((n + 3 : ℕ) : ℤ)) (D : SeedC3.PlaneData G)
    (hΛ : ∀ g, (D.lam g : GL (Fin 2) ℝ) ∈ Λ) :
    SeedC3.ZigZag.deRhamClass SeedC3.isOpen_faceSet SeedC3.convex_faceSet
      SeedC3.faceSet_nonempty D.action (D.rhoR n) (SeedC3.cuspSeedInv D hΛ (f := f)) =
      SeedC3.cuspSeedClass D hΛ (f := f) :=
  SeedC3.deRhamClass_cuspSeed D hΛ

/-- **S4b, (2): the explicit cocycle.** With the moment primitives `G_j = momentPrim` normalized
by `G_j(i) = 0`, the zig-zag cochain of the seed of a cusp form is, for all `g, k ∈ Γ_P`,
`c(g, k) = (n+1)⁻¹ · (ρ([[λ_g, w_g], [0, 1]]) − ρ([[λ_g, 0], [0, 1]])) ε_{λ_k} / Z`,
where `ε_γ` is the Eichler cocycle (`eichlerCocycle`, the binary form
`∑_j C(n+1,j)(−1)^{n+1−j} G_j(γ i) Y^j X^{n+1−j}`) viewed in `ℂ[X, Y, Z]` and `/Z` is exact
division. -/
theorem seed_cocycle_formula {G : Type} [Group G] (Λ : Subgroup (GL (Fin 2) ℝ)) [Λ.HasDetOne]
    (n : ℕ) (f : CuspForm Λ ((n + 3 : ℕ) : ℤ)) (D : SeedC3.PlaneData G)
    (hΛ : ∀ g, (D.lam g : GL (Fin 2) ℝ) ∈ Λ) (g k : G) :
    SeedC3.Coef.toPoly (SeedC3.cuspSeedCochain D hΛ (f := f) g k) =
      C (((n : ℂ) + 1)⁻¹) *
        SeedC3.ddiv (rho (D.plm g) (rename Fin.castSucc
            (eichlerCocycle n (SeedC3.momentPrim Λ n f) (D.lam k))) -
          rho (parabolicMatrix (D.lamM g) 0) (rename Fin.castSucc
            (eichlerCocycle n (SeedC3.momentPrim Λ n f) (D.lam k)))) :=
  SeedC3.toPoly_cuspSeedCochain D hΛ g k

/-- The zig-zag cochain of the seed is a Mathlib 2-cocycle (`IsCocycle₂` convention). -/
theorem seed_cochain_isCocycle {G : Type} [Group G] (Λ : Subgroup (GL (Fin 2) ℝ)) [Λ.HasDetOne]
    (n : ℕ) (f : CuspForm Λ ((n + 3 : ℕ) : ℤ)) (D : SeedC3.PlaneData G)
    (hΛ : ∀ g, (D.lam g : GL (Fin 2) ℝ) ∈ Λ) (g k j : G) :
    SeedC3.cuspSeedCochain D hΛ (f := f) (g * k) j + SeedC3.cuspSeedCochain D hΛ (f := f) g k =
      D.rhoR n g (SeedC3.cuspSeedCochain D hΛ (f := f) k j) +
        SeedC3.cuspSeedCochain D hΛ (f := f) g (k * j) :=
  SeedC3.ZigZag.cochain_isCocycle _ _ g k j

/-- **S4b: the antiholomorphic seed.** Its class is the class of the datum `(conj η, conj θ_g)`
and its cocycle is the complex conjugate (coefficientwise) of the holomorphic one. -/
theorem seed_conj_deRham_class {G : Type} [Group G] (Λ : Subgroup (GL (Fin 2) ℝ))
    [Λ.HasDetOne] (n : ℕ) (f : CuspForm Λ ((n + 3 : ℕ) : ℤ)) (D : SeedC3.PlaneData G)
    (hΛ : ∀ g, (D.lam g : GL (Fin 2) ℝ) ∈ Λ) :
    SeedC3.ZigZag.deRhamClass SeedC3.isOpen_faceSet SeedC3.convex_faceSet
      SeedC3.faceSet_nonempty D.action (D.rhoR n) (SeedC3.cuspSeedConjInv D hΛ (f := f)) =
      SeedC3.cuspSeedConjClass D hΛ (f := f) :=
  SeedC3.deRhamClass_cuspSeedConj D hΛ

theorem seed_conj_cocycle_formula {G : Type} [Group G] (Λ : Subgroup (GL (Fin 2) ℝ))
    [Λ.HasDetOne] (n : ℕ) (f : CuspForm Λ ((n + 3 : ℕ) : ℤ)) (D : SeedC3.PlaneData G)
    (hΛ : ∀ g, (D.lam g : GL (Fin 2) ℝ) ∈ Λ) (g k : G) :
    SeedC3.Coef.toPoly (SeedC3.ZigZag.cochain (SeedC3.ZigZag.laws SeedC3.isOpen_faceSet
      SeedC3.convex_faceSet SeedC3.faceSet_nonempty D.action (D.rhoR n))
        (D.seedConjDatum (SeedC3.cuspH Λ n f) n (SeedC3.momentPrim Λ n f)
          (SeedC3.cuspH_holo Λ n f) (SeedC3.momentPrim_hasDerivAt Λ n f)
          (SeedC3.cuspH_mod D hΛ)) g k) =
      MvPolynomial.map (starRingEnd ℂ) (D.seedCocycleFormula n (SeedC3.momentPrim Λ n f) g k) :=
  SeedC3.toPoly_cuspSeedConjCochain D hΛ g k

/-- **The plane parabolic group inside `GL₃(ℝ)`.** A subgroup of determinant-one matrices with
last row `(0, 0, 1)` is a `PlaneData` group whose `ρ` is the literal `ρ(g) q(𝐗) = det(g)⁻¹ q(g⁻¹𝐗)`
on the matrix `g` itself. -/
theorem planeData_ofSubgroup_plm (Γ : Subgroup (GL (Fin 3) ℝ))
    (hshape : ∀ g ∈ Γ, SeedC3.IsPlaneShape (g : Matrix (Fin 3) (Fin 3) ℝ))
    (hdet : ∀ g ∈ Γ, (g : Matrix (Fin 3) (Fin 3) ℝ).det = 1) (g : Γ) :
    (SeedC3.PlaneData.ofSubgroup Γ hshape hdet).plm g = (g.1 : Matrix (Fin 3) (Fin 3) ℝ) :=
  SeedC3.PlaneData.ofSubgroup_plm Γ hshape hdet g

/-! ### Lemma C.3 at the paper's level `Γ_P = Γ(N) ∩ P(ℤ)`, `Λ_P = Γ₂(N)` -/

/-- **S4b at level `Γ(N)`: the class of the seed.** For `h ∈ S_{n+3}(Γ₂(N))`, the seed `ω_h` is a
closed, `ρ`-equivariant two-form on the face for `Γ_P = Γ(N) ∩ P(ℤ)` (with `ρ(γ)` the literal action
of the real matrix of `γ`, `gammaNPlaneData_plm`), and its de Rham class in
`H²(Γ_P, E_n)` is the class of the zig-zag datum. -/
theorem seed_gammaN_deRham_class (N n : ℕ)
    (f : CuspForm (ConvergenceC4.leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    SeedC3.ZigZag.deRhamClass SeedC3.isOpen_faceSet SeedC3.convex_faceSet
      SeedC3.faceSet_nonempty (SeedC3.gammaNPlaneData N).action
      ((SeedC3.gammaNPlaneData N).rhoR n)
      (SeedC3.cuspSeedInv (SeedC3.gammaNPlaneData N) (SeedC3.gammaNPlaneData_lam_mem N) (f := f)) =
      SeedC3.cuspSeedClass (SeedC3.gammaNPlaneData N) (SeedC3.gammaNPlaneData_lam_mem N)
        (f := f) :=
  SeedC3.deRhamClass_cuspSeed _ _

/-- **S4b at level `Γ(N)`: the explicit cocycle**, as in `seed_cocycle_formula`, for
`Γ_P = Γ(N) ∩ P(ℤ)` (the coefficient matrix `plm γ` is `realMat γ`). -/
theorem seed_gammaN_cocycle_formula (N n : ℕ)
    (f : CuspForm (ConvergenceC4.leviGroup N) ((n + 3 : ℕ) : ℤ))
    (g k : ↥(SeedC3.gammaNP N)) :
    SeedC3.Coef.toPoly (SeedC3.cuspSeedCochain (SeedC3.gammaNPlaneData N)
        (SeedC3.gammaNPlaneData_lam_mem N) (f := f) g k) =
      C (((n : ℂ) + 1)⁻¹) *
        SeedC3.ddiv (rho (ConvergenceC4.realMat g.1) (rename Fin.castSucc
            (eichlerCocycle n (SeedC3.momentPrim _ n f) ((SeedC3.gammaNPlaneData N).lam k))) -
          rho (parabolicMatrix ((SeedC3.gammaNPlaneData N).lamM g) 0) (rename Fin.castSucc
            (eichlerCocycle n (SeedC3.momentPrim _ n f) ((SeedC3.gammaNPlaneData N).lam k)))) := by
  rw [SeedC3.toPoly_cuspSeedCochain, SeedC3.PlaneData.seedCocycleFormula,
    SeedC3.gammaNPlaneData_plm]

/-! ### The finite reflection (det −1 elements, full level)

The reflection `r = diag(−1, 1, 1)` of `GL₃(ℤ)` acts on the face by `(u₁, u₂, x, y) ↦
(−u₁, u₂, −x, y)`, `τ ↦ −τ̄` (antiholomorphic), and on the coefficients by `ρ(r) q = −q(−X, Y, Z)`.
With `h^*(z) = conj (h (−conj z))` (the cusp form `f^*`), one has
`r^* ω_h = (−1)^{n+1} ρ(r) ω̄_{h^*}`. The `ε`-isotypic projection of the seed is
`ω_f + ε (−1)^{n+1} ω̄_{f^*}`. -/

/-- **The reflection acts on the seed by the conjugate seed** (coefficient-matrix model):
`r^* ω_h = (−1)^n · \overline{ω_{h^*}}(−X, Y, Z)`, i.e. `(−1)^{n+1} ρ(r) \overline{ω_{h^*}}`. -/
theorem seed_reflection_pullback (n : ℕ) (h hs : ℂ → ℂ) (p : Fin 5 → ℝ)
    (hhs : hs (seedTau p) = (starRingEnd ℂ) (h (-(starRingEnd ℂ) (seedTau p)))) (i j : Fin 5) :
    formPullback SeedC3.reflMap5 (seedForm n h) p i j =
      C ((-1 : ℂ) ^ n) * bind₁ (![-X 0, X 1, X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ)
        (MvPolynomial.map (starRingEnd ℂ) (seedForm n hs p i j)) :=
  SeedC3.refl_pullback n h hs p hhs i j

/-- **The reflection acts on the seed form of the face by the conjugate seed**
(`r^* ω_h = (−1)^{n+1} ρ(r) ω̄_{h^*}`, as closed forms with values in `E_n`). -/
theorem seed_reflection_form (n : ℕ) (h hs : ℂ → ℂ)
    (hh : DifferentiableOn ℂ h SeedC3.Psi.upperSet)
    (hhs : DifferentiableOn ℂ hs SeedC3.Psi.upperSet)
    (hrel : ∀ z : ℂ, 0 < z.im → hs z = (starRingEnd ℂ) (h (-(starRingEnd ℂ) z))) :
    SeedC3.ZigZag.pullForm SeedC3.isOpen_faceSet SeedC3.reflAction SeedC3.reflGen 2
        (TernaryPoly.SmoothLocalDeRham.d SeedC3.isOpen_faceSet 1 (SeedC3.Psi.etaForm h hh n)) =
      ((-1 : ℝ) ^ (n + 1)) • SeedC3.ZigZag.twForm
        ((SeedC3.reflCoefCLM n).comp (SeedC3.conjCLM n)) 2
        (TernaryPoly.SmoothLocalDeRham.d SeedC3.isOpen_faceSet 1 (SeedC3.Psi.etaForm hs hhs n)) :=
  SeedC3.pullForm_refl_seed n h hs hh hhs hrel

/-- **Level one: the `ε`-isotypic seed.** For a level-one cusp form `f`, a plane group `D` with Levi
block in `SL₂(ℤ)` and `ε = ±1`, the form `ω_f + ε (−1)^{n+1} ω̄_{f^*}` is closed and `ρ`-equivariant
for `Λ₀⁺`, and the reflection acts on it by `ε ρ(r)`: it is equivariant for `Λ₀ = Λ₀⁺ ⋊ ⟨r⟩` with
the coefficients twisted by `ε` on the determinant `−1` coset (`ε = 1`: the untwisted `E_n`).
Its class is `[ω_f] + ε (−1)^{n+1} [ω̄_{f^*}]`. -/
theorem seed_reflection_isotypic_levelOne {G : Type} [Group G] (D : SeedC3.PlaneData G)
    (hΛ : ∀ g, (D.lam g : GL (Fin 2) ℝ) ∈ TernaryPeriodPolynomials.Argument.SeedC3S4c.Lvl1) (n : ℕ)
    (f : CuspForm TernaryPeriodPolynomials.Argument.SeedC3S4c.Lvl1 ((n + 3 : ℕ) : ℤ)) {ε : ℝ} (hε : ε * ε = 1) :
    SeedC3.ZigZag.pullForm SeedC3.isOpen_faceSet SeedC3.reflAction SeedC3.reflGen 2
        ((TernaryPeriodPolynomials.Argument.SeedC3S4c.reflSeedInv D hΛ f ε :
          SeedC3.ZigZag.invClosed SeedC3.isOpen_faceSet D.action (D.rhoR n)) :
            TernaryPoly.SmoothLocalDeRham.Form (F := SeedC3.Coef n) SeedC3.faceSet 2) =
      ε • SeedC3.ZigZag.twForm (SeedC3.reflCoefCLM n) 2
        ((TernaryPeriodPolynomials.Argument.SeedC3S4c.reflSeedInv D hΛ f ε :
          SeedC3.ZigZag.invClosed SeedC3.isOpen_faceSet D.action (D.rhoR n)) :
            TernaryPoly.SmoothLocalDeRham.Form (F := SeedC3.Coef n) SeedC3.faceSet 2) ∧
    SeedC3.ZigZag.deRhamClass SeedC3.isOpen_faceSet SeedC3.convex_faceSet
        SeedC3.faceSet_nonempty D.action (D.rhoR n) (TernaryPeriodPolynomials.Argument.SeedC3S4c.reflSeedInv D hΛ f ε) =
      SeedC3.cuspSeedClass D hΛ (f := f) +
        (ε * (-1 : ℝ) ^ (n + 1)) • SeedC3.cuspSeedConjClass D hΛ
          (f := TernaryPeriodPolynomials.Argument.SeedC3S4c.fStar f) :=
  ⟨TernaryPeriodPolynomials.Argument.SeedC3S4c.pullForm_refl_reflSeed D hΛ f hε,
    TernaryPeriodPolynomials.Argument.SeedC3S4c.deRhamClass_reflSeedInv D hΛ f ε⟩

/-- **Level `Γ(N)`: the `ε`-isotypic seed.** The same statement for `Γ_P = Γ(N) ∩ P(ℤ)`,
`Λ_P = Γ₂(N)`, which is normalized by `J`. -/
theorem seed_reflection_isotypic_gammaN (N n : ℕ)
    (f : CuspForm (ConvergenceC4.leviGroup N) ((n + 3 : ℕ) : ℤ)) {ε : ℝ} (hε : ε * ε = 1) :
    SeedC3.ZigZag.pullForm SeedC3.isOpen_faceSet SeedC3.reflAction SeedC3.reflGen 2
        ((TernaryPeriodPolynomials.Argument.SeedC3S4c.reflSeedInvGen _ (TernaryPeriodPolynomials.Argument.SeedC3S4c.leviGroup_J_stable N) f
          (SeedC3.gammaNPlaneData N) (SeedC3.gammaNPlaneData_lam_mem N) ε :
          SeedC3.ZigZag.invClosed SeedC3.isOpen_faceSet (SeedC3.gammaNPlaneData N).action
            ((SeedC3.gammaNPlaneData N).rhoR n)) :
            TernaryPoly.SmoothLocalDeRham.Form (F := SeedC3.Coef n) SeedC3.faceSet 2) =
      ε • SeedC3.ZigZag.twForm (SeedC3.reflCoefCLM n) 2
        ((TernaryPeriodPolynomials.Argument.SeedC3S4c.reflSeedInvGen _ (TernaryPeriodPolynomials.Argument.SeedC3S4c.leviGroup_J_stable N) f
          (SeedC3.gammaNPlaneData N) (SeedC3.gammaNPlaneData_lam_mem N) ε :
          SeedC3.ZigZag.invClosed SeedC3.isOpen_faceSet (SeedC3.gammaNPlaneData N).action
            ((SeedC3.gammaNPlaneData N).rhoR n)) :
            TernaryPoly.SmoothLocalDeRham.Form (F := SeedC3.Coef n) SeedC3.faceSet 2) :=
  TernaryPeriodPolynomials.Argument.SeedC3S4c.pullForm_refl_reflSeedGen _ (TernaryPeriodPolynomials.Argument.SeedC3S4c.leviGroup_J_stable N) f
    (SeedC3.gammaNPlaneData N) (SeedC3.gammaNPlaneData_lam_mem N) hε

open TernaryPeriodPolynomials.SphericalDetection.Helpers in
/-- **The edge of the `ε`-isotypic seed at level one**, in the binary coordinates of
`H¹(SL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)`: `(n+1)⁻¹ ((−1)^{n+1} [c_f] − ε [R c_f])`, where `c_f` is the
library's holomorphic period cocycle and `R` its parity reflection. -/
theorem seed_reflection_edge (n : ℕ) (f : CuspForm TernaryPeriodPolynomials.Argument.SeedC3S4c.Lvl1 ((n + 3 : ℕ) : ℤ))
    (ε : ℝ) (hw : ((n + 3 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 2) :
    (TernaryPeriodPolynomials.Argument.SeedC3S4c.plusLeviCohomologyIso n).hom (TernaryPeriodPolynomials.Argument.SeedC3S4c.plusEdgeS n
        (relativeTwoCocycleClass TernaryPeriodPolynomials.Argument.SeedC3S4c.plusExtensionS.inl
          (TernaryPeriodPolynomials.Argument.SeedC3S4c.plusRep n)
          (TernaryPeriodPolynomials.Argument.SeedC3S4c.seedRelCocycle f + (((ε * (-1 : ℝ) ^ (n + 1) : ℝ) : ℂ)) •
            TernaryPeriodPolynomials.Argument.SeedC3S4c.seedConjRelCocycle (TernaryPeriodPolynomials.Argument.SeedC3S4c.fStar f)))) =
      (((n : ℂ) + 1)⁻¹) • (((-1 : ℂ) ^ (n + 1)) • TernaryPeriodPolynomials.Argument.SeedC3S4c.periodClass f hw -
        (ε : ℂ) • TernaryPeriodPolynomials.Argument.SeedC3S4c.periodClassRefl f hw) :=
  TernaryPeriodPolynomials.Argument.SeedC3S4c.edge_reflSeed f ε hw

/-! ### Eichler--Shimura spanning (the spanning clause of Lemma C.3)

The spanning clause is reduced to the proposition `ESSpan Λ n` (every parabolic class of
`H¹(Λ, Sym^{n+1} ⊗ det⁻¹)` is a combination of holomorphic and antiholomorphic period classes of
cusp forms of weight `n + 3` for `Λ`). It is a hypothesis in the theorems of this file, never an
axiom. It is **proved** for `Λ = SL₂(ℤ)` (`eichler_shimura_spanning_levelOne`), `Λ = Γ₁(3)`
(`eichler_shimura_spanning_levelThree`) and, unconditionally, for every principal congruence
subgroup `Λ = Γ₂(N)`, `N > 0`: `Statements.EichlerShimura.eichler_shimura_spanning_gammaN`
(`TernaryPeriodPolynomials.Argument.ESFoundations.ESFinal.esSpan_gamma`). The conditional statements below for `Γ₂(N)` and for
the paper's plane group `Γ(N) ∩ P(ℤ)` therefore hold unconditionally as
`Statements.EichlerShimura.seed_span_gammaN`, `seed_span_iff_gammaN` and `seed_gammaP_span`.

Scope of the statements below: they concern the ALGEBRAIC group `H²(ℤ² ⋊ Λ, E_n)` (resp.
`H²(Γ(N) ∩ P(ℤ), E_n)`): the radical-kernel condition together with the parabolic-edge condition on
the Hochschild--Serre edge. They are not by themselves the geometric equality with the
paper's mixed cuspidal group `𝒞_P(E)`; for one plane cusp and `N ≥ 3` that comparison (the
literal definition of `𝒞_P(E)` through restrictions at all rational cusps of the binary Levi) is in
`TernaryPeriodPolynomials.Argument.SeedC3S4c.MixedCuspidal`. -/

open TernaryPeriodPolynomials.SphericalDetection.Helpers in
/-- **The edge of the seed on `ℤ² ⋊ Λ` for every `Λ ⊆ SL₂(ℤ)` (unconditional).** For a cusp form
`f` of weight `n + 3` for the image of `Λ` in `GL₂(ℝ)`, the `(1,1)` Hochschild–Serre edge of the
class of the seed `ω_f` (relative 2-cocycle `levelRel f` on `ℤ² ⋊ Λ`), in the binary coordinates
of `H¹(Λ, Sym^{n+1} ⊗ det⁻¹)`, is `(n+1)⁻¹` times the class of the holomorphic period cocycle
`m ↦ ε_f(m)` (D's Eichler cocycle of the normalized moment primitives). -/
theorem seed_level_edge (Λ : Subgroup SL(2, ℤ)) (n : ℕ)
    (f : CuspForm (TernaryPeriodPolynomials.Argument.SeedC3S4c.LamGL Λ) ((n + 3 : ℕ) : ℤ)) :
    TernaryPeriodPolynomials.Argument.SeedC3S4c.levelEdge Λ n
        (relativeTwoCocycleClass (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelExt Λ).inl
          (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelRep Λ n) (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelRel f)) =
      (((n : ℂ) + 1)⁻¹) • groupCohomology.H1π (TernaryPeriodPolynomials.Argument.SeedC3S4c.binRep Λ n)
        (TernaryPeriodPolynomials.Argument.SeedC3S4c.holCocycle f) :=
  TernaryPeriodPolynomials.Argument.SeedC3S4c.levelSeedEdge f

open TernaryPeriodPolynomials.SphericalDetection.Helpers in
/-- **The edge of the antiholomorphic seed on `ℤ² ⋊ Λ` (unconditional).** Same as
`seed_level_edge` for `\overline{ω_f}` and the conjugate period cocycle. -/
theorem seed_level_conj_edge (Λ : Subgroup SL(2, ℤ)) (n : ℕ)
    (f : CuspForm (TernaryPeriodPolynomials.Argument.SeedC3S4c.LamGL Λ) ((n + 3 : ℕ) : ℤ)) :
    TernaryPeriodPolynomials.Argument.SeedC3S4c.levelEdge Λ n
        (relativeTwoCocycleClass (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelExt Λ).inl
          (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelRep Λ n) (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelConjRel f)) =
      (((n : ℂ) + 1)⁻¹) • groupCohomology.H1π (TernaryPeriodPolynomials.Argument.SeedC3S4c.binRep Λ n)
        (TernaryPeriodPolynomials.Argument.SeedC3S4c.antiholCocycle f) :=
  TernaryPeriodPolynomials.Argument.SeedC3S4c.levelSeedConjEdge f

/-- **The complexified de Rham class of the seed is the class of the relative cocycle
(unconditional).** -/
theorem seed_level_class (Λ : Subgroup SL(2, ℤ)) (n : ℕ)
    (f : CuspForm (TernaryPeriodPolynomials.Argument.SeedC3S4c.LamGL Λ) ((n + 3 : ℕ) : ℤ)) :
    TernaryPeriodPolynomials.Argument.SeedC3S4c.complexifyL Λ n (SeedC3.cuspSeedClass (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelPlaneData Λ)
        (TernaryPeriodPolynomials.Argument.SeedC3S4c.level_hΛ Λ) (f := f)) =
      (TernaryPeriodPolynomials.SphericalDetection.Helpers.relativeTwoCocycleClass
        (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelExt Λ).inl (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelRep Λ n)
        (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelRel f)).val :=
  TernaryPeriodPolynomials.Argument.SeedC3S4c.complexifyL_cuspSeedClass f

open TernaryPeriodPolynomials.SphericalDetection.Helpers in
/-- **The Hochschild–Serre edge of `ℤ² ⋊ Λ` is injective on classes with zero radical
restriction, for every subgroup `Λ ⊆ SL₂(ℤ)` (unconditional).** -/
theorem seed_level_edge_injective (Λ : Subgroup SL(2, ℤ)) (n : ℕ) :
    Function.Injective (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelEdge Λ n) :=
  TernaryPeriodPolynomials.Argument.SeedC3S4c.levelEdge_injective_binary Λ n

open TernaryPeriodPolynomials.SphericalDetection.Helpers in
/-- **Lemma C.3, spanning clause, CONDITIONAL on `ESSpan Λ n`.** Assume the Eichler–Shimura
spanning proposition `ESSpan Λ n` for `Λ ⊆ SL₂(ℤ)` (a hypothesis, not an axiom; it is proved for
`SL₂(ℤ)`, `Γ₁(3)` and every `Γ₂(N)`, see the section header above). A class
`y ∈ H²(ℤ² ⋊ Λ, E_n)` that restricts to zero on the radical lattice and whose Hochschild–Serre
edge is a parabolic class of `H¹(Λ, Sym^{n+1} ⊗ det⁻¹)` (an algebraic condition on the edge, not
the geometric `𝒞_P(E)`) lies in the span of the complexified de Rham classes of the seeds `ω_f` and
`\overline{ω_f}`, `f ∈ S_{n+3}(Λ)`. The converse inclusion (seeds are parabolic) is
not part of this statement. -/
theorem seed_span_of_eichlerShimura (Λ : Subgroup SL(2, ℤ)) (n : ℕ)
    (hES : TernaryPeriodPolynomials.Argument.SeedC3S4c.ESSpan Λ n) (y : groupCohomology.H2 (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelRep Λ n))
    (hy : twoCohomologyRestriction (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelExt Λ).inl
      (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelRep Λ n) y = 0)
    (hpar : TernaryPeriodPolynomials.Argument.SeedC3S4c.levelEdge Λ n ⟨y, hy⟩ ∈ TernaryPeriodPolynomials.Argument.SeedC3S4c.parabolicH1 Λ n) :
    y ∈ TernaryPeriodPolynomials.Argument.SeedC3S4c.seedSpan Λ n :=
  TernaryPeriodPolynomials.Argument.SeedC3S4c.seed_span_conditional Λ n hES y hy hpar

open TernaryPeriodPolynomials.SphericalDetection.Helpers in
/-- **Lemma C.3, spanning clause at the paper's level `Λ_P = Γ₂(N)`, stated with the
hypothesis `ESSpan (Γ₂(N)) n`** (a hypothesis, not an axiom; the hypothesis is discharged for every
`N > 0` by `Statements.EichlerShimura.eichler_shimura_spanning_gammaN`, giving the unconditional
`Statements.EichlerShimura.seed_span_gammaN`; at the full group `ℤ² ⋊ Γ₂(N)`, radical `ℤ²`, not the
paper's `Γ(N) ∩ P(ℤ)`, for which see `seed_gammaP_span_conditional`): the
specialization of
`seed_span_of_eichlerShimura` to the principal congruence subgroup, whose image in `GL₂(ℝ)` is
`ConvergenceC4.leviGroup N`. -/
theorem seed_span_gammaN_of_eichlerShimura (N n : ℕ)
    (hES : TernaryPeriodPolynomials.Argument.SeedC3S4c.ESSpan (CongruenceSubgroup.Gamma N) n)
    (y : groupCohomology.H2 (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelRep (CongruenceSubgroup.Gamma N) n))
    (hy : twoCohomologyRestriction (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelExt (CongruenceSubgroup.Gamma N)).inl
      (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelRep (CongruenceSubgroup.Gamma N) n) y = 0)
    (hpar : TernaryPeriodPolynomials.Argument.SeedC3S4c.levelEdge (CongruenceSubgroup.Gamma N) n ⟨y, hy⟩ ∈
      TernaryPeriodPolynomials.Argument.SeedC3S4c.parabolicH1 (CongruenceSubgroup.Gamma N) n) :
    y ∈ TernaryPeriodPolynomials.Argument.SeedC3S4c.seedSpan (CongruenceSubgroup.Gamma N) n :=
  TernaryPeriodPolynomials.Argument.SeedC3S4c.seed_span_conditional _ n hES y hy hpar

/-- **Eichler–Shimura spanning at level one (unconditional).** Every parabolic class of
`H¹(SL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)` is a combination of holomorphic and antiholomorphic period classes
of cusp forms of weight `n + 3` for `SL₂(ℤ)`. Proved from the library's level-one dimension count
`dim H¹ = 2 dim S + 1`, the boundary functional and injectivity of the period map; nothing
assumed. -/
theorem eichler_shimura_spanning_levelOne (n : ℕ) :
    TernaryPeriodPolynomials.Argument.SeedC3S4c.ESSpan (⊤ : Subgroup SL(2, ℤ)) n :=
  TernaryPeriodPolynomials.Argument.SeedC3S4c.esSpan_top n

open TernaryPeriodPolynomials.SphericalDetection.Helpers in
/-- **Lemma C.3, spanning clause at level one (unconditional).** For `Λ = SL₂(ℤ)` (as the subgroup
`⊤`): a class of `H²(ℤ² ⋊ SL₂(ℤ), E_n)` with zero radical restriction and parabolic edge lies in
the span of the complexified de Rham classes of the seeds `ω_f`, `\overline{ω_f}`,
`f ∈ S_{n+3}(SL₂(ℤ))`. -/
theorem seed_span_levelOne (n : ℕ) (y : groupCohomology.H2
      (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelRep (⊤ : Subgroup SL(2, ℤ)) n))
    (hy : twoCohomologyRestriction (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelExt (⊤ : Subgroup SL(2, ℤ))).inl
      (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelRep (⊤ : Subgroup SL(2, ℤ)) n) y = 0)
    (hpar : TernaryPeriodPolynomials.Argument.SeedC3S4c.levelEdge (⊤ : Subgroup SL(2, ℤ)) n ⟨y, hy⟩ ∈
      TernaryPeriodPolynomials.Argument.SeedC3S4c.parabolicH1 (⊤ : Subgroup SL(2, ℤ)) n) :
    y ∈ TernaryPeriodPolynomials.Argument.SeedC3S4c.seedSpan (⊤ : Subgroup SL(2, ℤ)) n :=
  TernaryPeriodPolynomials.Argument.SeedC3S4c.seed_span_conditional _ n (TernaryPeriodPolynomials.Argument.SeedC3S4c.esSpan_top n) y hy hpar

/-- **Eichler–Shimura spanning at level three (unconditional).** Every parabolic class of
`H¹(Γ₁(3), Sym^{n+1} ⊗ det⁻¹)`, `Γ₁(3) = Gamma1 3` the Levi block of the level-three plane cusp, is
a combination of holomorphic and antiholomorphic period classes of cusp forms of weight `n + 3` for
`Γ₁(3)`. Proved from the library's Eichler–Shimura theorem for `Γ₁'(3)` (injectivity of the
parity-projected period maps, `levelPeriodMap_injective_levelThree`, and the exact dimension of
the parabolic cohomology) by extending the `±` parts of a parabolic cocycle to the two twists. -/
theorem eichler_shimura_spanning_levelThree (n : ℕ) :
    TernaryPeriodPolynomials.Argument.SeedC3S4c.ESSpan (CongruenceSubgroup.Gamma1 3) n :=
  TernaryPeriodPolynomials.Argument.SeedC3S4c.esSpan_gam3 n

open TernaryPeriodPolynomials.SphericalDetection.Helpers in
/-- **Lemma C.3, spanning clause at level three (unconditional).** For `Λ = Γ₁(3)`: a class of
`H²(ℤ² ⋊ Γ₁(3), E_n)` with zero radical restriction and parabolic edge lies in the span of the
complexified de Rham classes of the seeds `ω_f`, `\overline{ω_f}`, `f ∈ S_{n+3}(Γ₁(3))`. -/
theorem seed_span_levelThree (n : ℕ) (y : groupCohomology.H2
      (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelRep (CongruenceSubgroup.Gamma1 3) n))
    (hy : twoCohomologyRestriction (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelExt (CongruenceSubgroup.Gamma1 3)).inl
      (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelRep (CongruenceSubgroup.Gamma1 3) n) y = 0)
    (hpar : TernaryPeriodPolynomials.Argument.SeedC3S4c.levelEdge (CongruenceSubgroup.Gamma1 3) n ⟨y, hy⟩ ∈
      TernaryPeriodPolynomials.Argument.SeedC3S4c.parabolicH1 (CongruenceSubgroup.Gamma1 3) n) :
    y ∈ TernaryPeriodPolynomials.Argument.SeedC3S4c.seedSpan (CongruenceSubgroup.Gamma1 3) n :=
  TernaryPeriodPolynomials.Argument.SeedC3S4c.seed_span_conditional _ n (TernaryPeriodPolynomials.Argument.SeedC3S4c.esSpan_gam3 n) y hy hpar

/-- **The seeds lie in the mixed cuspidal group (unconditional).** For a subgroup `Λ ⊆ SL₂(ℤ)` and a
cusp form `f` of weight `n + 3` for its image in `GL₂(ℝ)`, the holomorphic period cocycle
`m ↦ ε_f(m)` is a coboundary on every parabolic element of `Λ`: the classes of the seeds `ω_f` are
parabolic. Proof: the obstruction at `γ = ± g T^k g⁻¹` is the value of `ε_f(γ)` at the first column
of `g`; it vanishes because `f` tends to `0` at the cusp `g · ∞` (a constant translation defect of
a primitive of a function tending to `0` is `0`). -/
theorem seed_cocycle_parabolic (Λ : Subgroup SL(2, ℤ)) (n : ℕ)
    (f : CuspForm (TernaryPeriodPolynomials.Argument.SeedC3S4c.LamGL Λ) ((n + 3 : ℕ) : ℤ)) :
    TernaryPeriodPolynomials.Argument.SeedC3S4c.holCocycle f ∈ TernaryPeriodPolynomials.Argument.SeedC3S4c.parabolicCocycles Λ n :=
  TernaryPeriodPolynomials.Argument.SeedC3S4c.holCocycle_mem_parabolicCocycles f

/-- **The antiholomorphic seeds lie in the mixed cuspidal group (unconditional).** -/
theorem seed_conj_cocycle_parabolic (Λ : Subgroup SL(2, ℤ)) (n : ℕ)
    (f : CuspForm (TernaryPeriodPolynomials.Argument.SeedC3S4c.LamGL Λ) ((n + 3 : ℕ) : ℤ)) :
    TernaryPeriodPolynomials.Argument.SeedC3S4c.antiholCocycle f ∈ TernaryPeriodPolynomials.Argument.SeedC3S4c.parabolicCocycles Λ n :=
  TernaryPeriodPolynomials.Argument.SeedC3S4c.antiholCocycle_mem_parabolicCocycles f

open TernaryPeriodPolynomials.SphericalDetection.Helpers in
/-- **The edges of the seeds are parabolic (unconditional).** The seeds `ω_f`, `\overline{ω_f}`,
`f ∈ S_{n+3}(Λ)`, span a subspace of the classes of `H²(ℤ² ⋊ Λ, E_n)` with zero radical restriction
whose Hochschild–Serre edge lies in the parabolic cohomology
`H¹_par(Λ, Sym^{n+1} ⊗ det⁻¹)` (an algebraic edge condition on `H²(ℤ² ⋊ Λ, E_n)`, not the
geometric equality with the paper's `𝒞_P(E)`). -/
theorem seed_span_le_parabolic (Λ : Subgroup SL(2, ℤ)) (n : ℕ) :
    TernaryPeriodPolynomials.Argument.SeedC3S4c.seedKerSpan Λ n ≤ Submodule.comap (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelEdge Λ n)
      (TernaryPeriodPolynomials.Argument.SeedC3S4c.parabolicH1 Λ n) :=
  TernaryPeriodPolynomials.Argument.SeedC3S4c.seedKerSpan_le_comap

open TernaryPeriodPolynomials.SphericalDetection.Helpers in
/-- **Lemma C.3, spanning clause as an equivalence, CONDITIONAL on `ESSpan Λ n`.** Under the
Eichler–Shimura spanning proposition `ESSpan Λ n` (a hypothesis, not an axiom; proved for `SL₂(ℤ)`,
`Γ₁(3)` and every `Γ₂(N)`), a class `y ∈ H²(ℤ² ⋊ Λ, E_n)` is in the span of the complexified de Rham classes of the
seeds `ω_f`, `\overline{ω_f}` (`f ∈ S_{n+3}(Λ)`) if and only if it restricts to zero on the radical
lattice and its Hochschild–Serre edge is a parabolic class. (Algebraic radical-kernel/parabolic-edge
characterization on `H²(ℤ² ⋊ Λ, E_n)`; not the geometric `𝒞_P(E)` equality.) -/
theorem seed_span_iff_of_eichlerShimura (Λ : Subgroup SL(2, ℤ)) (n : ℕ)
    (hES : TernaryPeriodPolynomials.Argument.SeedC3S4c.ESSpan Λ n) (y : groupCohomology.H2 (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelRep Λ n)) :
    y ∈ TernaryPeriodPolynomials.Argument.SeedC3S4c.seedSpan Λ n ↔
      ∃ hy : twoCohomologyRestriction (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelExt Λ).inl
        (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelRep Λ n) y = 0,
      TernaryPeriodPolynomials.Argument.SeedC3S4c.levelEdge Λ n ⟨y, hy⟩ ∈ TernaryPeriodPolynomials.Argument.SeedC3S4c.parabolicH1 Λ n :=
  TernaryPeriodPolynomials.Argument.SeedC3S4c.mem_seedSpan_iff hES y

open TernaryPeriodPolynomials.SphericalDetection.Helpers in
/-- **Lemma C.3, spanning clause as an equivalence at level one (unconditional):** the span of the
seeds on `ℤ² ⋊ SL₂(ℤ)` is exactly the classes with zero radical restriction and parabolic edge. -/
theorem seed_span_iff_levelOne (n : ℕ)
    (y : groupCohomology.H2 (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelRep (⊤ : Subgroup SL(2, ℤ)) n)) :
    y ∈ TernaryPeriodPolynomials.Argument.SeedC3S4c.seedSpan (⊤ : Subgroup SL(2, ℤ)) n ↔
      ∃ hy : twoCohomologyRestriction (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelExt (⊤ : Subgroup SL(2, ℤ))).inl
        (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelRep (⊤ : Subgroup SL(2, ℤ)) n) y = 0,
      TernaryPeriodPolynomials.Argument.SeedC3S4c.levelEdge (⊤ : Subgroup SL(2, ℤ)) n ⟨y, hy⟩ ∈
        TernaryPeriodPolynomials.Argument.SeedC3S4c.parabolicH1 (⊤ : Subgroup SL(2, ℤ)) n :=
  TernaryPeriodPolynomials.Argument.SeedC3S4c.mem_seedSpan_iff (TernaryPeriodPolynomials.Argument.SeedC3S4c.esSpan_top n) y

open TernaryPeriodPolynomials.SphericalDetection.Helpers in
/-- **Lemma C.3, spanning clause as an equivalence at level three (unconditional):** for
`Λ = Γ₁(3)`. -/
theorem seed_span_iff_levelThree (n : ℕ)
    (y : groupCohomology.H2 (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelRep (CongruenceSubgroup.Gamma1 3) n)) :
    y ∈ TernaryPeriodPolynomials.Argument.SeedC3S4c.seedSpan (CongruenceSubgroup.Gamma1 3) n ↔
      ∃ hy : twoCohomologyRestriction (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelExt (CongruenceSubgroup.Gamma1 3)).inl
        (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelRep (CongruenceSubgroup.Gamma1 3) n) y = 0,
      TernaryPeriodPolynomials.Argument.SeedC3S4c.levelEdge (CongruenceSubgroup.Gamma1 3) n ⟨y, hy⟩ ∈
        TernaryPeriodPolynomials.Argument.SeedC3S4c.parabolicH1 (CongruenceSubgroup.Gamma1 3) n :=
  TernaryPeriodPolynomials.Argument.SeedC3S4c.mem_seedSpan_iff (TernaryPeriodPolynomials.Argument.SeedC3S4c.esSpan_gam3 n) y

/-! ### The paper's plane group `Γ_P = Γ(N) ∩ P(ℤ)` (radical `Nℤ²`)

The statements above use the group `ℤ² ⋊ Λ` (radical `ℤ²`). The paper's group is the
principal-congruence subgroup `Γ(N) ∩ P(ℤ) ≤ SL₃(ℤ)`, an extension of `Γ(N)` by the radical `Nℤ²`.
It is conjugate to `ℤ² ⋊ Γ₂(N)` by `diag(1,1,N)` over `ℚ`; the identification below is carried out
at the level of cocycles (the conjugation `T = ρ(diag(1,1,N))` matches the edge cocycles exactly)
and is stated at the paper's group. Scope: the carrier is `Γ(N) ∩ P(ℤ)` (bottom row
`(0,0,1)`); it is the full rational-plane stabilizer `Γ(N) ∩ P(ℚ)` only for `N ≥ 3`
(`ConvergenceC4.gammaN_inf_rationalPlane`); for `N = 1, 2` it can be strictly smaller (for example
`diag(-1,1,-1) ∈ Γ(2)`). -/

open TernaryPeriodPolynomials.SphericalDetection.Helpers in
/-- **The Hochschild--Serre edge at `Γ(N) ∩ P(ℤ)` is injective on classes with zero radical
restriction (unconditional).** The edge `H²(Γ_P, E_n) ⊇ ker(res to Nℤ²) → H¹(Γ₂(N), Sym^{n+1} ⊗
det⁻¹)` identifies `H¹(Nℤ², E_n)^{Γ(N)}` with the binary representation and is injective because
`H²(Γ(N), W) = 0`. -/
theorem seed_gammaP_edge_injective (N n : ℕ) [NeZero N] :
    Function.Injective (TernaryPeriodPolynomials.Argument.SeedC3S4c.gammaNEdge N n) :=
  TernaryPeriodPolynomials.Argument.SeedC3S4c.gammaNEdge_injective_binary N n

open TernaryPeriodPolynomials.SphericalDetection.Helpers in
/-- **The edge of the seed on `Γ(N) ∩ P(ℤ)` (unconditional).** For a cusp form `f` of weight `n+3`
for `Γ₂(N)`, the Hochschild--Serre edge of the class of the seed `ω_f` on the paper's plane
group (radical `Nℤ²`), in the binary coordinates of `H¹(Γ₂(N), Sym^{n+1} ⊗ det⁻¹)`, is `(n+1)⁻¹`
times the class of the holomorphic period cocycle. -/
theorem seed_gammaP_edge (N n : ℕ) [NeZero N]
    (f : CuspForm (TernaryPeriodPolynomials.Argument.SeedC3S4c.LamGL (CongruenceSubgroup.Gamma N)) ((n + 3 : ℕ) : ℤ)) :
    TernaryPeriodPolynomials.Argument.SeedC3S4c.gammaNEdge N n
        (relativeTwoCocycleClass (TernaryPeriodPolynomials.Argument.SeedC3S4c.gammaNExt N).inl
          (TernaryPeriodPolynomials.Argument.SeedC3S4c.gammaNRep N n) (TernaryPeriodPolynomials.Argument.SeedC3S4c.gammaNRel f)) =
      (((n : ℂ) + 1)⁻¹) • groupCohomology.H1π
        (TernaryPeriodPolynomials.Argument.SeedC3S4c.binRep (CongruenceSubgroup.Gamma N) n)
        (TernaryPeriodPolynomials.Argument.SeedC3S4c.holCocycle f) :=
  TernaryPeriodPolynomials.Argument.SeedC3S4c.gammaNSeedEdge f

open TernaryPeriodPolynomials.SphericalDetection.Helpers in
/-- **The edge of the antiholomorphic seed on `Γ(N) ∩ P(ℤ)` (unconditional).** -/
theorem seed_gammaP_conj_edge (N n : ℕ) [NeZero N]
    (f : CuspForm (TernaryPeriodPolynomials.Argument.SeedC3S4c.LamGL (CongruenceSubgroup.Gamma N)) ((n + 3 : ℕ) : ℤ)) :
    TernaryPeriodPolynomials.Argument.SeedC3S4c.gammaNEdge N n
        (relativeTwoCocycleClass (TernaryPeriodPolynomials.Argument.SeedC3S4c.gammaNExt N).inl
          (TernaryPeriodPolynomials.Argument.SeedC3S4c.gammaNRep N n) (TernaryPeriodPolynomials.Argument.SeedC3S4c.gammaNConjRel f)) =
      (((n : ℂ) + 1)⁻¹) • groupCohomology.H1π
        (TernaryPeriodPolynomials.Argument.SeedC3S4c.binRep (CongruenceSubgroup.Gamma N) n)
        (TernaryPeriodPolynomials.Argument.SeedC3S4c.antiholCocycle f) :=
  TernaryPeriodPolynomials.Argument.SeedC3S4c.gammaNSeedConjEdge f

/-- **The complexified de Rham class of the seed on `Γ(N) ∩ P(ℤ)` is the class of the relative
cocycle (unconditional).** -/
theorem seed_gammaP_class (N n : ℕ) [NeZero N]
    (f : CuspForm (TernaryPeriodPolynomials.Argument.SeedC3S4c.LamGL (CongruenceSubgroup.Gamma N)) ((n + 3 : ℕ) : ℤ)) :
    TernaryPeriodPolynomials.Argument.SeedC3S4c.complexifyG N n (SeedC3.cuspSeedClass (SeedC3.gammaNPlaneData N)
        (SeedC3.gammaNPlaneData_lam_mem N) (f := f)) =
      (TernaryPeriodPolynomials.SphericalDetection.Helpers.relativeTwoCocycleClass
        (TernaryPeriodPolynomials.Argument.SeedC3S4c.gammaNExt N).inl (TernaryPeriodPolynomials.Argument.SeedC3S4c.gammaNRep N n)
        (TernaryPeriodPolynomials.Argument.SeedC3S4c.gammaNRel f)).val :=
  TernaryPeriodPolynomials.Argument.SeedC3S4c.complexifyG_cuspSeedClass f

open TernaryPeriodPolynomials.SphericalDetection.Helpers in
/-- **The seeds on `Γ(N) ∩ P(ℤ)` have parabolic edge (unconditional).** -/
theorem seed_gammaP_span_le_parabolic (N n : ℕ) [NeZero N] :
    TernaryPeriodPolynomials.Argument.SeedC3S4c.gammaNSeedKerSpan N n ≤ Submodule.comap (TernaryPeriodPolynomials.Argument.SeedC3S4c.gammaNEdge N n)
      (TernaryPeriodPolynomials.Argument.SeedC3S4c.parabolicH1 (CongruenceSubgroup.Gamma N) n) :=
  TernaryPeriodPolynomials.Argument.SeedC3S4c.gammaNSeedKerSpan_le_comap N n

open TernaryPeriodPolynomials.SphericalDetection.Helpers in
/-- **Lemma C.3, spanning clause at the paper's plane group `Γ(N) ∩ P(ℤ)` (radical `Nℤ²`),
stated with the hypothesis `ESSpan (Γ(N)) n`** (a hypothesis, not an axiom; discharged for every
`N > 0` by `Statements.EichlerShimura.eichler_shimura_spanning_gammaN`, giving the unconditional
`Statements.EichlerShimura.seed_gammaP_span`): a class of `H²(Γ_P, E_n)` that
restricts to zero on the radical `Nℤ²` and whose Hochschild--Serre edge is a parabolic class lies in
the span of the complexified de Rham classes of the seeds `ω_f`, `\overline{ω_f}`,
`f ∈ S_{n+3}(Γ₂(N))`. This is the algebraic radical-kernel/parabolic-edge statement; the
comparison with the geometric mixed `𝒞_P(E)` is not included. -/
theorem seed_gammaP_span_conditional (N n : ℕ) [NeZero N]
    (hES : TernaryPeriodPolynomials.Argument.SeedC3S4c.ESSpan (CongruenceSubgroup.Gamma N) n)
    (y : groupCohomology.H2 (TernaryPeriodPolynomials.Argument.SeedC3S4c.gammaNRep N n))
    (hy : twoCohomologyRestriction (TernaryPeriodPolynomials.Argument.SeedC3S4c.gammaNExt N).inl
      (TernaryPeriodPolynomials.Argument.SeedC3S4c.gammaNRep N n) y = 0)
    (hpar : TernaryPeriodPolynomials.Argument.SeedC3S4c.gammaNEdge N n ⟨y, hy⟩ ∈
      TernaryPeriodPolynomials.Argument.SeedC3S4c.parabolicH1 (CongruenceSubgroup.Gamma N) n) :
    y ∈ TernaryPeriodPolynomials.Argument.SeedC3S4c.gammaNSeedSpan N n :=
  TernaryPeriodPolynomials.Argument.SeedC3S4c.gammaN_seed_span_conditional N n hES y hy hpar

end TernaryPeriodPolynomials.Argument.Statements.SeedC3
