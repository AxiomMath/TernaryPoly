module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Helpers
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.AmbientGroupH2
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.RelativeTwoCocycleNormalization

@[expose] public section


/-!
# Exactness of restrictions of homogeneous two-cocycles to lattices

Let `E` be a subgroup of a group `G`, `ρ` a representation of `G`, and `c` a homogeneous two-cocycle
for `E` (a function on triples of vertices of `G`, equivariant under `E`). For a monoid map
`ψ : G → G` and a subgroup `U` with `ψ U ⊆ E`, the pullback `x ↦ c (ψ x₀, ψ x₁, ψ x₂)` is a
homogeneous two-cocycle for `U` with coefficients `ρ ∘ ψ`.

* If the class of `c` in `H²(E, ρ)` vanishes, so does the class of the pullback
  (`classOf_pullback_eq_zero`): pull back a primitive.
* If the restriction of the class of `c` in the group cohomology `H²(↥E, ρ)` along an injective
  homomorphism `ι : N → E` vanishes, and `ψ U` lies in the image of `ι`, then the class of the
  pullback vanishes (`classOf_pullback_eq_zero_of_restriction_zero`): the vanishing of the
  restriction gives a one-cochain `f` on `N` with `d f = c ∘ ι`; the function `u ↦ f (ι⁻¹ (ψ u))`
  on `U` is a primitive in the group cohomology of `U`, and the retraction of vertices converts
  it into a homogeneous primitive.

These are the two steps that turn vanishing statements for the radical lattice of a stabilizer,
phrased in group cohomology, into the vanishing of classes in the homogeneous model on the vertices
of `GL₃(ℚ)`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointMembershipEngine

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

/-- **Pullback of an exact two-cocycle is exact.** -/
theorem classOf_pullback_eq_zero (ρ ρ' : Representation ℂ G V) (ψ : G →* G)
    (hρ' : ∀ g, ρ' g = ρ (ψ g)) (E U : Subgroup G) (hψ : ∀ u ∈ U, ψ u ∈ E)
    (c : cocycles E ρ) (cU : cocycles U ρ')
    (hcU : ∀ x : Fin 3 → G, cU.val.val x = c.val.val (fun i => ψ (x i)))
    (h : classOf E ρ c = 0) : classOf U ρ' cU = 0 := by
  obtain ⟨p, hp⟩ := (classOf_eq_zero_iff E ρ c).mp h
  have t2 : ∀ a b : G, p.val (fun i : Fin 2 => ψ (![a, b] i)) = p.val ![ψ a, ψ b] := by
    intro a b
    exact congrArg p.val (by funext i; fin_cases i <;> rfl)
  refine (classOf_eq_zero_iff U ρ' cU).mpr ⟨⟨fun x => p.val (fun i => ψ (x i)), ?_⟩, ?_⟩
  · intro γ x
    have h1 := p.property ⟨ψ γ.val, hψ γ.val γ.property⟩ (fun i => ψ (x i))
    change p.val (fun i => ψ (γ.val * x i)) = ρ' γ.val (p.val fun i => ψ (x i))
    rw [hρ' γ.val]
    simp only [map_mul]
    exact h1
  · apply Subtype.ext
    funext x
    have e : c.val.val (fun i => ψ (x i)) =
        p.val ![ψ (x 1), ψ (x 2)] - p.val ![ψ (x 0), ψ (x 2)] + p.val ![ψ (x 0), ψ (x 1)] :=
      (congrFun (congrArg Subtype.val hp) (fun i => ψ (x i))).symm
    show p.val (fun i => ψ (![x 1, x 2] i)) - p.val (fun i => ψ (![x 0, x 2] i)) +
      p.val (fun i => ψ (![x 0, x 1] i)) = cU.val.val x
    rw [hcU x, e, t2, t2, t2]

/-- **A primitive on a lattice gives an exact pullback.** Let `ι : N → ↥E` be an injective
homomorphism and `f : N → V` a one-cochain with `d f = c ∘ ι` (written in homogeneous coordinates).
If every `ψ u` (`u ∈ U`) is a value `ι a`, then the pullback of `c` along `ψ` to `U` is exact. -/
theorem classOf_pullback_eq_zero_of_primitive (ρ ρ' : Representation ℂ G V) (ψ : G →* G)
    (hρ' : ∀ g, ρ' g = ρ (ψ g)) (E U : Subgroup G) (c : cocycles E ρ) (cU : cocycles U ρ')
    (hcU : ∀ x : Fin 3 → G, cU.val.val x = c.val.val (fun i => ψ (x i)))
    {N : Type} [Group N] (ι : N →* ↥E) (hι : Function.Injective ι) (f : N → V)
    (rel : ∀ a b : N, ρ (ι a).val (f b) - f (a * b) + f a =
      c.val.val ![1, (ι a).val, (ι a).val * (ι b).val])
    (hU : ∀ u ∈ U, ∃ a : N, (ι a).val = ψ u) : classOf U ρ' cU = 0 := by
  have hU' : ∀ u : U, ∃ a : N, (ι a).val = ψ u.val := fun u => hU u.val u.property
  choose a ha using hU'
  have hmul : ∀ u v : U, a (u * v) = a u * a v := by
    intro u v
    apply hι
    apply Subtype.ext
    rw [map_mul, Subgroup.coe_mul, ha, ha, ha, Subgroup.coe_mul, map_mul]
  have relU : ∀ u v : U, ρ' u.val (f (a v)) - f (a (u * v)) + f (a u) =
      cU.val.val ![1, u.val, u.val * v.val] := by
    intro u v
    have h1 := rel (a u) (a v)
    rw [← hmul u v, ha u, ha v] at h1
    have t3 : c.val.val (fun i => ψ (![1, u.val, u.val * v.val] i)) =
        c.val.val ![1, ψ u.val, ψ u.val * ψ v.val] := by
      exact congrArg c.val.val (by funext i; fin_cases i <;> simp)
    rw [hρ' u.val, hcU, t3]
    exact h1
  have hzeroU : groupCohomology.H2π (subgroupCoefficientRep U ρ')
      (ambientCocycleToGroup U ρ' cU) = 0 := by
    rw [groupCohomology.H2π_eq_zero_iff]
    refine ⟨fun u => f (a u), ?_⟩
    funext pair
    exact relU pair.1 pair.2
  obtain ⟨prim, hprim⟩ := ambientCocycle_primitive_of_H2_zero U ρ' cU hzeroU
  exact (classOf_eq_zero_iff U ρ' cU).mpr ⟨prim, hprim⟩

/-- **Vanishing restriction to a lattice gives an exact pullback.** Let `ι : N → ↥E` be an injective
homomorphism whose composite restriction of the group cohomology class of `c` vanishes. If every
`ψ u` (`u ∈ U`) is a value `ι a`, then the pullback of `c` along `ψ` to `U` is exact. -/
theorem classOf_pullback_eq_zero_of_restriction_zero (ρ ρ' : Representation ℂ G V) (ψ : G →* G)
    (hρ' : ∀ g, ρ' g = ρ (ψ g)) (E U : Subgroup G) (c : cocycles E ρ) (cU : cocycles U ρ')
    (hcU : ∀ x : Fin 3 → G, cU.val.val x = c.val.val (fun i => ψ (x i)))
    {N : Type} [Group N] (ι : N →* ↥E) (hι : Function.Injective ι)
    (hzero : twoCohomologyRestriction ι (subgroupCoefficientRep E ρ)
      (groupCohomology.H2π (subgroupCoefficientRep E ρ) (ambientCocycleToGroup E ρ c)) = 0)
    (hU : ∀ u ∈ U, ∃ a : N, (ι a).val = ψ u) : classOf U ρ' cU = 0 := by
  rw [twoCohomologyRestriction_apply, groupCohomology.H2π_eq_zero_iff] at hzero
  obtain ⟨f, hf⟩ := hzero
  change N → V at f
  exact classOf_pullback_eq_zero_of_primitive ρ ρ' ψ hρ' E U c cU hcU ι hι f
    (fun a b => congrFun hf (a, b)) hU

/-- The restriction of a homogeneous two-cocycle to a subgroup. -/
def restrictCocycle (ρ : Representation ℂ G V) (E U : Subgroup G) (h : U ≤ E)
    (c : cocycles E ρ) : cocycles U ρ :=
  ⟨⟨c.val.val, fun γ x => c.val.property ⟨γ.val, h γ.property⟩ x⟩,
    LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp c.property)⟩

/-- **Twisted pullback of an exact cocycle.** Let `c'` be the conjugate of the cocycle `cF` by
`w`, `c' v = ρ(w)⁻¹ cF (w v)`, and suppose `c'` has a primitive `prim` on a subgroup `U''`. If
`w⁻¹ φ(u) w ∈ U''` for `u ∈ U`, the cocycle `x ↦ cF (φ x)` on `U` (coefficients `ρ ∘ φ`) is
exact, with primitive `x ↦ ρ(w) prim (w⁻¹ φ x)`. -/
theorem classOf_twistedPullback_eq_zero (ρ ρ' : Representation ℂ G V) (φ : G →* G) (w : G)
    (hρ' : ∀ g, ρ' g = ρ (φ g)) (E U'' U : Subgroup G)
    (hU : ∀ u ∈ U, w⁻¹ * φ u * w ∈ U'') (cF : cocycles E ρ) (cprime : (Fin 3 → G) → V)
    (hc' : ∀ v : Fin 3 → G, cprime v = ρ w⁻¹ (cF.val.val (fun i => w * v i)))
    (cU : cocycles U ρ') (hcU : ∀ x : Fin 3 → G, cU.val.val x = cF.val.val (fun i => φ (x i)))
    (prim : cochains U'' ρ 1)
    (hprim : ∀ v : Fin 3 → G, (differentialOne U'' ρ prim).val v = cprime v) :
    classOf U ρ' cU = 0 := by
  have hr : ∀ (a b : G) (v : V), ρ a (ρ b v) = ρ (a * b) v := by
    intro a b v
    rw [map_mul, Module.End.mul_apply]
  have t2 : ∀ a b : G, prim.val (fun i : Fin 2 => w⁻¹ * φ (![a, b] i)) =
      prim.val ![w⁻¹ * φ a, w⁻¹ * φ b] := by
    intro a b
    exact congrArg prim.val (by funext i; fin_cases i <;> rfl)
  refine (classOf_eq_zero_iff U ρ' cU).mpr
    ⟨⟨fun x => ρ w (prim.val (fun i => w⁻¹ * φ (x i))), ?_⟩, ?_⟩
  · intro γ x
    have hmem := hU γ.val γ.property
    have h1 : prim.val (fun i => (w⁻¹ * φ γ.val * w) * (w⁻¹ * φ (x i))) =
        ρ (w⁻¹ * φ γ.val * w) (prim.val fun i => w⁻¹ * φ (x i)) :=
      prim.property ⟨w⁻¹ * φ γ.val * w, hmem⟩ (fun i => w⁻¹ * φ (x i))
    have hx : (fun i => w⁻¹ * φ (γ.val * x i)) =
        fun i => (w⁻¹ * φ γ.val * w) * (w⁻¹ * φ (x i)) := by
      funext i
      rw [map_mul]
      group
    change ρ w (prim.val (fun i => w⁻¹ * φ (γ.val * x i))) =
      ρ' γ.val (ρ w (prim.val fun i => w⁻¹ * φ (x i)))
    rw [hx, h1, hρ' γ.val, hr, hr]
    congr 1
    group
  · apply Subtype.ext
    funext x
    show ρ w (prim.val (fun i => w⁻¹ * φ (![x 1, x 2] i))) -
        ρ w (prim.val (fun i => w⁻¹ * φ (![x 0, x 2] i))) +
        ρ w (prim.val (fun i => w⁻¹ * φ (![x 0, x 1] i))) = cU.val.val x
    have hcv : cprime (fun i => w⁻¹ * φ (x i)) = ρ w⁻¹ (cF.val.val (fun i => φ (x i))) := by
      rw [hc']
      exact congrArg (fun y => ρ w⁻¹ (cF.val.val y)) (funext fun i => by group)
    have hd := hprim (fun i => w⁻¹ * φ (x i))
    rw [hcv] at hd
    have hd' : prim.val ![w⁻¹ * φ (x 1), w⁻¹ * φ (x 2)] -
        prim.val ![w⁻¹ * φ (x 0), w⁻¹ * φ (x 2)] + prim.val ![w⁻¹ * φ (x 0), w⁻¹ * φ (x 1)] =
        ρ w⁻¹ (cF.val.val (fun i => φ (x i))) := hd
    rw [t2, t2, t2, hcU x, ← map_sub, ← map_add, hd', hr, mul_inv_cancel]
    simp

end TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointMembershipEngine
