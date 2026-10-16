module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneEven
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.ModularH2

@[expose] public section


/-!
# Generic tools for the vanishing of degree-two cohomology at the level-three cusps

The statements of this file are independent of the cusp. They are the bridge from the homogeneous
local cohomology `H2 Γ ρ` to Mathlib's `groupCohomology.H2`, the transport of vanishing along a
group isomorphism, the Hochschild–Serre vanishing criterion for a split extension
`1 → N → E → L → 1` (restriction to `N` zero, `L` embedding in `GL₂(ℤ) × ℤˣ`, a central element of
`L` acting by `-1` on `H¹(N, V)`), and the alternation lemmas that show that the restriction to a
lattice radical `ℤ²` vanishes.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral

namespace TernaryPeriodPolynomials.SourceConstruction

/-! ### From homogeneous cohomology to group cohomology -/

section Bridge

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

/-- If the Mathlib group cohomology of a subgroup vanishes, so does its homogeneous model. -/
theorem homogeneousH2_eq_zero_of_group (Γ : Subgroup G) (ρ : Representation ℂ G V)
    (h : ∀ y : groupCohomology.H2 (subgroupCoefficientRep Γ ρ), y = 0) (x : H2 Γ ρ) :
    x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | _ C =>
  change classOf Γ ρ C = 0
  rw [classOf_eq_zero_iff]
  exact (ambientCocycle_H2_zero_iff Γ ρ C).mp (h _)

theorem subsingleton_of_forall_eq_zero {M : Type*} [Zero M] (h : ∀ x : M, x = 0) :
    Subsingleton M :=
  ⟨fun x y => (h x).trans (h y).symm⟩

end Bridge

/-! ### Transport of vanishing along a group isomorphism -/

/-- If the cohomology of the restriction of `A` along an isomorphism `e : K ≃* L` vanishes, then so
does that of `A`. -/
theorem groupH2_eq_zero_of_mulEquiv {K L : Type} [Group K] [Group L] (e : K ≃* L)
    (A : Rep ℂ L) (h : ∀ y : groupCohomology.H2 (Rep.res e.toMonoidHom A), y = 0)
    (x : groupCohomology.H2 A) : x = 0 := by
  obtain ⟨cycle, rfl⟩ := twoCocycle_H2_surjective A x
  let transported : K × K → Rep.res e.toMonoidHom A := fun pair => cycle (e pair.1, e pair.2)
  have closed : transported ∈ groupCohomology.cocycles₂ (Rep.res e.toMonoidHom A) := by
    rw [groupCohomology.mem_cocycles₂_iff]
    intro g k j
    change cycle (e (g * k), e j) + cycle (e g, e k) =
      A.ρ (e g) (cycle (e k, e j)) + cycle (e g, e (k * j))
    rw [map_mul, map_mul]
    exact twoCocycle_relation A cycle _ _ _
  have zero := h (groupCohomology.H2π (Rep.res e.toMonoidHom A) ⟨transported, closed⟩)
  rw [groupCohomology.H2π_eq_zero_iff] at zero
  obtain ⟨primitive, hprimitive⟩ := zero
  have hcycle : cycle = twoBoundaryCycle A (fun l => primitive (e.symm l)) := by
    apply Subtype.ext
    funext pair
    have value := congrFun hprimitive (e.symm pair.1, e.symm pair.2)
    change (Rep.res e.toMonoidHom A).ρ (e.symm pair.1) (primitive (e.symm pair.2)) -
      primitive (e.symm pair.1 * e.symm pair.2) + primitive (e.symm pair.1) =
        cycle (e (e.symm pair.1), e (e.symm pair.2)) at value
    rw [e.apply_symm_apply, e.apply_symm_apply] at value
    change cycle (pair.1, pair.2) = A.ρ pair.1 (primitive (e.symm pair.2)) -
      primitive (e.symm (pair.1 * pair.2)) + primitive (e.symm pair.1)
    rw [map_mul, ← value]
    change A.ρ (e (e.symm pair.1)) (primitive (e.symm pair.2)) - _ + _ = _
    rw [e.apply_symm_apply]
  rw [hcycle, twoBoundaryCycle_H2_zero]

/-! ### The Hochschild–Serre vanishing criterion -/

/-- **Vanishing of `H²` of a split extension.** Let `1 → N → E → L → 1` be a split extension, `V` a
representation of `E`. Assume the restriction `H²(E, V) → H²(N, V)` vanishes, that `L` embeds in
`GL₂(ℤ) × ℤˣ` (so that `H²(L, ·)` vanishes), and that a central element of `L` acts by `-1` on
`H¹(N, V)`. Then `H²(E, V) = 0`. -/
theorem groupH2_eq_zero_of_split {N E L : Type} [Group N] [Group E] [Group L]
    {extension : GroupExtension N E L} (splitting : extension.Splitting) (V : Rep ℂ E)
    (ψ : L →* GeneralLinearGroup (Fin 2) ℤ × ℤˣ) (hψ : Function.Injective ψ)
    (hres : ∀ x : groupCohomology.H2 V, twoCohomologyRestriction extension.inl V x = 0)
    (z : L) (hz : ∀ g, z * g = g * z)
    (hneg : ∀ w : groupCohomology.H1 (Rep.res extension.inl V),
      splitRadicalH1Action splitting V z w = -w)
    (x : groupCohomology.H2 V) : x = 0 := by
  have hker := hres x
  have hedge : splitCohomologyEdge splitting V ⟨x, hker⟩ = splitCohomologyEdge splitting V 0 :=
    (IdentityPlaneEven.H1_eq_zero_of_central_neg (splitRadicalH1Representation splitting V) z hz
        hneg _).trans
      (IdentityPlaneEven.H1_eq_zero_of_central_neg (splitRadicalH1Representation splitting V) z hz
        hneg _).symm
  have injective := ModularH2.splitCohomologyEdge_injective_of_binary splitting V ψ hψ hedge
  exact congrArg Subtype.val injective

/-- Conjugation of the radical by a Levi element, in terms of `splitRadicalInput`. -/
theorem splitting_conj_inl {N E L : Type} [Group N] [Group E] [Group L]
    {extension : GroupExtension N E L} (splitting : extension.Splitting) (ℓ : L) (r : N) :
    (splitting ℓ)⁻¹ * extension.inl r * splitting ℓ =
      extension.inl (splitRadicalInput splitting ℓ r) := by
  have h := splitRadicalInput_commute splitting ℓ r
  rw [mul_assoc, h, inv_mul_cancel_left]

/-! ### Alternation lemmas on the radical lattice -/

section Alternation

variable {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W]

/-- Conjugating the generators of the radical by `z` transforms the projected alternation by the
induced operator `L`. (Version of `IdentityPlaneEven.projected_alternation_conj` for explicit
images of the two generators.) -/
theorem projected_alternation_reflect (inclusion : RadicalLattice →* G) (representation : Rep ℂ G)
    (projection : representation →ₗ[ℂ] W)
    (radical_trivial : ∀ radical vector,
      projection (representation.ρ (inclusion radical) vector) = projection vector)
    (z : G) (a b a' b' : RadicalLattice)
    (ha : z⁻¹ * inclusion a * z = inclusion a') (hb : z⁻¹ * inclusion b * z = inclusion b')
    (L : W →ₗ[ℂ] W)
    (intertwines : ∀ vector, projection (representation.ρ z vector) = L (projection vector))
    (cycle : groupCohomology.cocycles₂ representation) :
    L (projection (cycle (inclusion a', inclusion b') - cycle (inclusion b', inclusion a'))) =
      projection (cycle (inclusion a, inclusion b) - cycle (inclusion b, inclusion a)) := by
  have equation0 := congrArg projection (conjugationTwoCocycleHomotopy_boundary representation
    z cycle (inclusion a) (inclusion b))
  have equation1 := congrArg projection (conjugationTwoCocycleHomotopy_boundary representation
    z cycle (inclusion b) (inclusion a))
  simp only [twoBoundaryCycle_apply, map_add, map_sub, radical_trivial, intertwines,
    ha, hb] at equation0 equation1
  rw [← map_mul, mul_comm a b, map_mul] at equation0
  rw [map_sub, map_sub, map_sub]
  linear_combination (norm := abel) equation1 - equation0

/-- The projected alternation of a two-cocycle on the radical lattice is `det • (value at the
generators)`. -/
theorem projected_alternation_eq_det (inclusion : RadicalLattice →* G) (representation : Rep ℂ G)
    (projection : representation →ₗ[ℂ] W)
    (radical_trivial : ∀ radical vector,
      projection (representation.ρ (inclusion radical) vector) = projection vector)
    (cycle : groupCohomology.cocycles₂ representation) (u v : RadicalLattice) :
    projection (cycle (inclusion u, inclusion v) - cycle (inclusion v, inclusion u)) =
      (u.toAdd.1 * v.toAdd.2 - u.toAdd.2 * v.toAdd.1) •
        projection (cycle (inclusion radicalLatticeFirst, inclusion radicalLatticeSecond) -
          cycle (inclusion radicalLatticeSecond, inclusion radicalLatticeFirst)) := by
  have h := IdentityPlaneEven.alternating_eq_det
    (fun u v : RadicalLattice =>
      projection (cycle (inclusion u, inclusion v) - cycle (inclusion v, inclusion u)))
    (fun x y z => IdentityPlaneEven.projected_alternation_mul inclusion representation projection
      radical_trivial cycle x y z)
    (fun x y => IdentityPlaneEven.map_sub_eq_neg_map_sub projection _ _)
    (fun x => by simp) u v
  exact h

theorem eq_zero_of_neg_one_zsmul_eq (x : W) (h : (-1 : ℤ) • x = x) : x = 0 := by
  have h' : -x = x := by simpa using h
  have two : (2 : ℂ) • x = 0 := by
    rw [two_smul]
    calc x + x = -x + x := by rw [h']
      _ = 0 := neg_add_cancel x
  exact (smul_eq_zero.mp two).resolve_left (by norm_num)

/-- **A reflection kills the projected alternation.** If `z` inverts the first generator, fixes the
second, and fixes the projection, then the projected alternation of every two-cocycle vanishes. -/
theorem projected_alternation_zero_of_reflection (inclusion : RadicalLattice →* G)
    (representation : Rep ℂ G) (projection : representation →ₗ[ℂ] W)
    (radical_trivial : ∀ radical vector,
      projection (representation.ρ (inclusion radical) vector) = projection vector)
    (z : G) (h1 : z⁻¹ * inclusion radicalLatticeFirst * z = inclusion radicalLatticeFirst⁻¹)
    (h2 : z⁻¹ * inclusion radicalLatticeSecond * z = inclusion radicalLatticeSecond)
    (fixed : ∀ vector, projection (representation.ρ z vector) = projection vector)
    (cycle : groupCohomology.cocycles₂ representation) :
    projection (cycle (inclusion radicalLatticeFirst, inclusion radicalLatticeSecond) -
      cycle (inclusion radicalLatticeSecond, inclusion radicalLatticeFirst)) = 0 := by
  have reflect := projected_alternation_reflect inclusion representation projection
    radical_trivial z radicalLatticeFirst radicalLatticeSecond radicalLatticeFirst⁻¹
    radicalLatticeSecond h1 h2 LinearMap.id (fun vector => fixed vector) cycle
  have det := projected_alternation_eq_det inclusion representation projection radical_trivial
    cycle radicalLatticeFirst⁻¹ radicalLatticeSecond
  have hd : ((radicalLatticeFirst⁻¹).toAdd.1 * radicalLatticeSecond.toAdd.2 -
      (radicalLatticeFirst⁻¹).toAdd.2 * radicalLatticeSecond.toAdd.1 : ℤ) = -1 := by
    simp [radicalLatticeFirst, radicalLatticeSecond]
  rw [hd] at det
  rw [LinearMap.id_apply, det] at reflect
  exact eq_zero_of_neg_one_zsmul_eq _ reflect

/-- **The coboundary criterion on the radical lattice.** A two-cocycle of the lattice `ℤ²` whose
alternation lies in the kernel of a projection `π` that contains in its kernel only sums of values of
`ρ(e₁) - 1` and `ρ(e₂) - 1` is a coboundary. -/
theorem latticeH2_eq_zero_of_projected (A : Rep ℂ RadicalLattice) (π : A →ₗ[ℂ] W)
    (hker : LinearMap.ker π ≤ LinearMap.range (A.ρ radicalLatticeFirst - 1) ⊔
      LinearMap.range (A.ρ radicalLatticeSecond - 1))
    (cycle : groupCohomology.cocycles₂ A)
    (hzero : π (latticeTwoCocycleAlternation A cycle) = 0) :
    groupCohomology.H2π A cycle = 0 := by
  rw [latticeTwoCocycle_H2_zero_iff]
  obtain ⟨y, ⟨beta, rfl⟩, w, ⟨gamma, rfl⟩, hyw⟩ :=
    Submodule.mem_sup.mp (hker (LinearMap.mem_ker.mpr hzero))
  refine ⟨-gamma, beta, ?_⟩
  rw [map_neg, sub_neg_eq_add]
  exact hyw.symm

end Alternation

/-! ### Rewriting helpers that avoid motive problems between defeq carrier types -/

section Helpers

variable {M : Type*} [AddCommGroup M]

theorem sub_apply_aux {a b y v : M} (h : a = b) (hy : b - y = v) : a - y = v := by
  rw [h]
  exact hy

theorem sub_congr_aux {a b : M} (h : a = b) (y : M) : a - y = b - y := by
  rw [h]

theorem eq_add_aux {p q r s : M} (key : p = q + r) (h : q = s) : p = s + r := by
  rw [key, h]

theorem eq_swap_add_aux {p q r s : M} (key : p = q + r) (rep : s = q) : p = r + s := by
  rw [key, rep]
  exact add_comm _ _

/-- The algebra of the coboundary equation `ρ(-x) - (-x) = S + ξ` when `ρ x - x = L - ξ` and
`S = -L`. -/
theorem neg_cocycle_aux {R : M → M} {a x L ξ S : M} (hRn : R (-x) = -R x) (hrep : R x = a)
    (hxr : a - x = L - ξ) (hL : S = -L) : R (-x) - -x = S + ξ := by
  rw [hRn, hrep, hL]
  calc -a - -x = -(a - x) := by abel
    _ = -(L - ξ) := by rw [hxr]
    _ = -L + ξ := by abel

end Helpers

end TernaryPeriodPolynomials.SourceConstruction
