module

public import TernaryPeriodPolynomials.ArithmeticCohomology.RightEdge.Core
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.ConjInvariance
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.SemidirectModel

@[expose] public section


/-!
# The Hochschild-Serre right edge in group cohomology: `range (res_{N}) = H²(N, E)^{L}` for a split extension with `H²(L, ·) = 0`

Formalized by Claude Sonnet 5.5.

For a split extension `ext` of `L` by `N` with splitting `s` (`GroupExtension.Splitting`) and `ρ : Rep ℂ E`:

* `splitRadicalH2Action s ρ l`: the action of the Levi on `H²(N, E)`: transport along the conjugation `splitRadicalInput s l = conjAct(l⁻¹)` of the radical with the coefficient map
  `ρ(s l)` (the degree-two analogue of the library's `splitRadicalH1Action`, built with `EdgeNat.h2Map`); `splitRadicalH2Action_π` / `_cocycle`: the formula
  `(l·z)(a, b) = ρ(s l) z(conj_{l⁻¹} a, conj_{l⁻¹} b)` on cocycles;
* `restriction_invariant` (easy half): the image of `twoCohomologyRestriction ext.inl ρ` is `L`-invariant, because inner automorphisms act trivially on `H²(E, ρ)`
  (the `GammaNStokes.h2Map_conj_self`);
* `exists_lift` (the content): if `H²(L, ·)` vanishes, every `L`-invariant class of `H²(N, E)` is the restriction of a class of `H²(E, ρ)` (transport to the semidirect model
  `N ⋊ L ≃* E` and `RightEdge.Core.right_edge_cochain_map`);
* `right_edge_iff`, `right_edge_range`: `range res = {y | ∀ l, l·y = y}`.
-/

open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.RightEdge

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c

variable {N E L : Type} [Group N] [Group E] [Group L] {ext : GroupExtension N E L}
  (s : ext.Splitting) (ρ : Rep ℂ E)

theorem splitRadicalH2_hT (l : L) (g : N) (v : Rep.res ext.inl ρ) :
    ρ.ρ (s l) ((Rep.res ext.inl ρ).ρ (splitRadicalInput s l g) v) =
      (Rep.res ext.inl ρ).ρ g (ρ.ρ (s l) v) := by
  have := splitRadicalCoefficient_intertwines s ρ l g
  exact (congrArg (fun f => f v) this).symm

/-- **The action of the Levi `L` on `H²(N, E)`** for a split extension: transport along the conjugation `splitRadicalInput s l = conjAct(l⁻¹)` of the radical with the coefficient
map `ρ(s l)` (the degree-two analogue of `splitRadicalH1Action`). -/
def splitRadicalH2Action (l : L) :
    groupCohomology.H2 (Rep.res ext.inl ρ) →ₗ[ℂ] groupCohomology.H2 (Rep.res ext.inl ρ) :=
  EdgeNat.h2Map (splitRadicalInput s l) (Rep.res ext.inl ρ) (Rep.res ext.inl ρ) (ρ.ρ (s l))
    (splitRadicalH2_hT s ρ l)

/-- The action on cocycles: `(l·z)(a, b) = ρ(s l) z(conj_{l⁻¹} a, conj_{l⁻¹} b)`. -/
theorem splitRadicalH2Action_π (l : L) (z : groupCohomology.cocycles₂ (Rep.res ext.inl ρ)) :
    splitRadicalH2Action s ρ l (groupCohomology.H2π (Rep.res ext.inl ρ) z) =
      groupCohomology.H2π (Rep.res ext.inl ρ)
        (groupCohomology.mapCocycles₂ (splitRadicalInput s l)
          (EdgeNat.comparison (splitRadicalInput s l) (Rep.res ext.inl ρ) (Rep.res ext.inl ρ) (ρ.ρ (s l))
            (splitRadicalH2_hT s ρ l)) z) :=
  EdgeNat.h2Map_π _ _ _ _ _ z

theorem splitRadicalH2Action_cocycle (l : L) (z : groupCohomology.cocycles₂ (Rep.res ext.inl ρ)) (a b : N) :
    (groupCohomology.mapCocycles₂ (splitRadicalInput s l)
          (EdgeNat.comparison (splitRadicalInput s l) (Rep.res ext.inl ρ) (Rep.res ext.inl ρ) (ρ.ρ (s l))
            (splitRadicalH2_hT s ρ l)) z) (a, b) =
      ρ.ρ (s l) (z (splitRadicalInput s l a, splitRadicalInput s l b)) := rfl


theorem innerConj_inl (l : L) (a : N) :
    (TernaryPeriodPolynomials.Argument.GammaNStokes.innerConjHom (s l)⁻¹) (ext.inl a) =
      ext.inl (splitRadicalInput s l a) := by
  have h := splitRadicalInput_commute s l a
  change (s l)⁻¹ * ext.inl a * ((s l)⁻¹)⁻¹ = _
  rw [inv_inv, mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]

/-- **The image of the restriction is `L`-invariant**: inner automorphisms act trivially on `H²(E, ρ)`. -/
theorem restriction_invariant (l : L) (y : groupCohomology.H2 ρ) :
    splitRadicalH2Action s ρ l (twoCohomologyRestriction ext.inl ρ y) = twoCohomologyRestriction ext.inl ρ y := by
  obtain ⟨z, rfl⟩ := twoCocycle_H2_surjective ρ y
  have key := TernaryPeriodPolynomials.Argument.GammaNStokes.h2Map_conj_self ρ (s l)⁻¹ (groupCohomology.H2π ρ z)
  rw [EdgeNat.h2Map_π] at key
  have key2 := congrArg (twoCohomologyRestriction ext.inl ρ) key
  rw [twoCohomologyRestriction_apply, twoCohomologyRestriction_apply] at key2
  rw [twoCohomologyRestriction_apply, splitRadicalH2Action_π, ← key2]
  congr 1
  apply Subtype.ext
  funext p
  obtain ⟨a, b⟩ := p
  change ρ.ρ (s l) (z.1 (ext.inl (splitRadicalInput s l a), ext.inl (splitRadicalInput s l b))) =
    ρ.ρ ((s l)⁻¹⁻¹) (z.1 (TernaryPeriodPolynomials.Argument.GammaNStokes.innerConjHom (s l)⁻¹ (ext.inl a),
      TernaryPeriodPolynomials.Argument.GammaNStokes.innerConjHom (s l)⁻¹ (ext.inl b)))
  rw [innerConj_inl, innerConj_inl, inv_inv]


theorem exists_lift (hL : H2Vanishes L) (y : groupCohomology.H2 (Rep.res ext.inl ρ))
    (hy : ∀ l, splitRadicalH2Action s ρ l y = y) :
    ∃ y' : groupCohomology.H2 ρ, twoCohomologyRestriction ext.inl ρ y' = y := by
  obtain ⟨z, rfl⟩ := twoCocycle_H2_surjective (Rep.res ext.inl ρ) y
  let e := s.semidirectProductMulEquiv
  let ρ' : Representation ℂ (N ⋊[s.conjAct] L) ρ := ρ.ρ.comp e.toMonoidHom
  have hz : ∀ a b c, ρ' (SemidirectProduct.inl a) (z.1 (b, c)) - z.1 (a * b, c) + z.1 (a, b * c) - z.1 (a, b) = 0 := by
    intro a b c
    have := (groupCohomology.mem_cocycles₂_iff z.1).1 z.2 a b c
    change z.1 (a * b, c) + z.1 (a, b) = ρ.ρ (ext.inl a) (z.1 (b, c)) + z.1 (a, b * c) at this
    change ρ.ρ (e (SemidirectProduct.inl a)) (z.1 (b, c)) - z.1 (a * b, c) + z.1 (a, b * c) - z.1 (a, b) = 0
    have hinl : e (SemidirectProduct.inl a) = ext.inl a := semidirect_inl s a
    rw [hinl]
    linear_combination (norm := abel) -this
  have hinv : ∀ l : L, ∃ η : N → ρ, ∀ a b, ρ' (SemidirectProduct.inr l) (z.1 (((s.conjAct l)⁻¹) a, ((s.conjAct l)⁻¹) b)) - z.1 (a, b) =
      ρ' (SemidirectProduct.inl a) (η b) - η (a * b) + η a := by
    intro l
    have h1 := hy l
    rw [splitRadicalH2Action_π, groupCohomology.H2π_eq_iff] at h1
    obtain ⟨η, hη⟩ := h1
    refine ⟨η, fun a b => ?_⟩
    have hp := congrFun hη (a, b)
    rw [groupCohomology.d₁₂_hom_apply] at hp
    have hp' : ρ.ρ (ext.inl a) (η b) - η (a * b) + η a =
        ρ.ρ (s l) (z.1 (splitRadicalInput s l a, splitRadicalInput s l b)) - z.1 (a, b) := hp
    have hα : ∀ a : N, splitRadicalInput s l a = ((s.conjAct l)⁻¹) a := fun a => by
      change (s.conjAct l⁻¹) a = _
      rw [map_inv]
    have hinr : e (SemidirectProduct.inr l) = s l := semidirect_inr s l
    have hinl : e (SemidirectProduct.inl a) = ext.inl a := semidirect_inl s a
    rw [hα, hα] at hp'
    change ρ.ρ (e (SemidirectProduct.inr l)) (z.1 (((s.conjAct l)⁻¹) a, ((s.conjAct l)⁻¹) b)) - z.1 (a, b) =
      ρ.ρ (e (SemidirectProduct.inl a)) (η b) - η (a * b) + η a
    rw [hinr, hinl]
    exact hp'.symm
  obtain ⟨Z, ζ, hZ, hZinl⟩ := right_edge_cochain_map s.conjAct ρ' hL (fun a b => z.1 (a, b)) hz hinv
  let ZE : E × E → ρ := fun p => Z (e.symm p.1) (e.symm p.2)
  have hρ' : ∀ g : E, ρ' (e.symm g) = ρ.ρ g := by
    intro g
    change ρ.ρ (e (e.symm g)) = _
    rw [e.apply_symm_apply]
  have hZE : ZE ∈ groupCohomology.cocycles₂ ρ := by
    rw [groupCohomology.mem_cocycles₂_iff]
    intro g h j
    have := hZ (e.symm g) (e.symm h) (e.symm j)
    rw [hρ'] at this
    change Z (e.symm (g * h)) (e.symm j) + Z (e.symm g) (e.symm h) =
      ρ.ρ g (Z (e.symm h) (e.symm j)) + Z (e.symm g) (e.symm (h * j))
    rw [map_mul, map_mul]
    linear_combination (norm := abel) -this
  have hinlsymm : ∀ a : N, e.symm (ext.inl a) = SemidirectProduct.inl a := fun a =>
    e.symm_apply_eq.2 (semidirect_inl s a).symm
  refine ⟨groupCohomology.H2π ρ ⟨ZE, hZE⟩, ?_⟩
  rw [twoCohomologyRestriction_apply, groupCohomology.H2π_eq_iff]
  refine ⟨ζ, ?_⟩
  funext p
  obtain ⟨a, b⟩ := p
  rw [groupCohomology.d₁₂_hom_apply]
  have h1 : (twoCocycleRestriction ext.inl ρ ⟨ZE, hZE⟩) (a, b) = Z (SemidirectProduct.inl a) (SemidirectProduct.inl b) := by
    rw [twoCocycleRestriction_apply]
    change Z (e.symm (ext.inl a)) (e.symm (ext.inl b)) = _
    rw [hinlsymm, hinlsymm]
  have h2 : (Rep.res ext.inl ρ).ρ a = ρ' (SemidirectProduct.inl a) := by
    have hinl : e (SemidirectProduct.inl a) = ext.inl a := semidirect_inl s a
    change ρ.ρ (ext.inl a) = ρ.ρ (e (SemidirectProduct.inl a))
    rw [hinl]
  change (Rep.res ext.inl ρ).ρ a (ζ b) - ζ (a * b) + ζ a =
    (twoCocycleRestriction ext.inl ρ ⟨ZE, hZE⟩) (a, b) - z.1 (a, b)
  rw [h1, hZinl, h2]
  abel


/-- **The invariants of the Levi action on `H²(N, E)`.** -/
def splitRadicalH2Invariants : Submodule ℂ (groupCohomology.H2 (Rep.res ext.inl ρ)) where
  carrier := {y | ∀ l, splitRadicalH2Action s ρ l y = y}
  zero_mem' := fun l => map_zero _
  add_mem' := by
    intro x y hx hy l
    rw [map_add, hx l, hy l]
  smul_mem' := by
    intro c x hx l
    rw [map_smul, hx l]

/-- **The Hochschild-Serre right edge**: for a split extension whose Levi has vanishing complex `H²`, a class of `H²(N, E)` is the restriction of a class of
`H²(E, ρ)` iff it is invariant under the Levi action. -/
theorem right_edge_iff (hL : H2Vanishes L) (y : groupCohomology.H2 (Rep.res ext.inl ρ)) :
    y ∈ LinearMap.range (twoCohomologyRestriction ext.inl ρ) ↔ ∀ l, splitRadicalH2Action s ρ l y = y := by
  constructor
  · rintro ⟨y', rfl⟩ l
    exact restriction_invariant s ρ l y'
  · intro hy
    exact exists_lift s ρ hL y hy

/-- `range res = H²(N, E)^L`. -/
theorem right_edge_range (hL : H2Vanishes L) :
    LinearMap.range (twoCohomologyRestriction ext.inl ρ) = splitRadicalH2Invariants s ρ :=
  Submodule.ext fun y => right_edge_iff s ρ hL y

end TernaryPeriodPolynomials.Argument.RightEdge
