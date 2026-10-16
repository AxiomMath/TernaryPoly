module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.LinearDuality

@[expose] public section


/-!
# From crossed homomorphisms to the triple model

For a group `G` with two elements `a, g₂` (put `b = a g₂`, `g₃ = b⁻¹`) a crossed homomorphism
`z : G → V` (`z (g h) = z g + g • z h`) is *primitive* at `v ∈ V³` if
`z a = (a - 1) v₁`, `z g₂ = (g₂ - 1) v₂`, `z g₃ = (g₃ - 1) v₃`.  Then `v` satisfies the triple
constraint, the cup-product formula of `z` with another cocycle `z'`

    (z ∪ z')[a | g₂] + (z ∪ z')[a g₂ | g₃] - ∑ᵢ B (vᵢ, z' gᵢ)

is `tripleForm v v'`, it does not depend on the choice of the primitives, it vanishes when `z` is a
coboundary, and (given that cocycles are determined by their values at `a, g₂` and that every
constrained triple is the primitive of a cocycle) the radicals of the pairing on cocycles are exactly the
coboundaries.
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.CocycleBridge

open TripleModel LinearDuality

section Definitions

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

/-- A crossed homomorphism: `z (g h) = z g + g • z h`. -/
def IsCocycle (ρ : Representation ℂ G V) (z : G → V) : Prop :=
  ∀ g h, z (g * h) = z g + ρ g (z h)

/-- `z` has the primitive triple `v` at the three special elements `a`, `g₂`, `(a g₂)⁻¹`. -/
def IsPrimitive (ρ : Representation ℂ G V) (a g₂ : G) (z : G → V) (v : V × V × V) : Prop :=
  z a = (ρ a - 1) v.1 ∧ z g₂ = (ρ g₂ - 1) v.2.1 ∧ z (a * g₂)⁻¹ = (ρ (a * g₂)⁻¹ - 1) v.2.2

variable {ρ : Representation ℂ G V} {z : G → V}

theorem IsCocycle.map_one (hz : IsCocycle ρ z) : z 1 = 0 := by
  have h := hz 1 1
  rw [mul_one, _root_.map_one, Module.End.one_apply] at h
  exact add_eq_left.mp h.symm

theorem isCocycle_boundary (ρ : Representation ℂ G V) (u : V) :
    IsCocycle ρ (fun g => ρ g u - u) := by
  intro g h
  simp only [map_mul, Module.End.mul_apply, map_sub]
  abel

theorem isPrimitive_boundary (ρ : Representation ℂ G V) (a g₂ : G) (u : V) :
    IsPrimitive ρ a g₂ (fun g => ρ g u - u) (u, u, u) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [LinearMap.sub_apply]

/-- A primitive triple of a cocycle satisfies the constraint. -/
theorem IsPrimitive.mem_tripleCycles (hz : IsCocycle ρ z) {a g₂ : G} {v : V × V × V}
    (hv : IsPrimitive ρ a g₂ z v) : v ∈ tripleCycles ρ a g₂ := by
  obtain ⟨p1, p2, p3⟩ := hv
  have h1 : z (a * g₂) = z a + ρ a (z g₂) := hz a g₂
  have h2 := hz (a * g₂) (a * g₂)⁻¹
  rw [mul_inv_cancel, hz.map_one, h1, p1, p2, p3] at h2
  have m1 : ρ a (ρ g₂ v.2.1) = ρ (a * g₂) v.2.1 := (rep_mul_apply ρ a g₂ _).symm
  have m2 : ρ (a * g₂) (ρ (a * g₂)⁻¹ v.2.2) = v.2.2 := rep_apply_inv ρ (a * g₂) _
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, m1, m2] at h2
  show v ∈ LinearMap.ker (constraint ρ a g₂)
  rw [LinearMap.mem_ker, constraint_apply]
  simp only [LinearMap.sub_apply, Module.End.one_apply]
  linear_combination (norm := module) (-1 : ℂ) • h2

end Definitions

section Pairing

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W} {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ}

/-- The cup-product formula on the fundamental two-chain of the three-point sphere, corrected by the
primitives `v` of `z`. -/
def cupFormula (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (ρ' : Representation ℂ G W) (a g₂ : G) (z : G → V)
    (z' : G → W) (v : V × V × V) : ℂ :=
  B (z a) (ρ' a (z' g₂)) + B (z (a * g₂)) (ρ' (a * g₂) (z' (a * g₂)⁻¹)) -
    (B v.1 (z' a) + B v.2.1 (z' g₂) + B v.2.2 (z' (a * g₂)⁻¹))

/-- A cocycle with primitive triple `v` takes the value `(b - 1) v₃` at `b = a g₂`. -/
theorem IsPrimitive.value_mul {z : G → V} (hz : IsCocycle ρ z) {a g₂ : G} {v : V × V × V}
    (hv : IsPrimitive ρ a g₂ z v) : z (a * g₂) = (ρ (a * g₂) - 1) v.2.2 := by
  obtain ⟨_, _, p3⟩ := hv
  have h := hz (a * g₂) (a * g₂)⁻¹
  rw [mul_inv_cancel, hz.map_one, p3] at h
  have m2 : ρ (a * g₂) (ρ (a * g₂)⁻¹ v.2.2) = v.2.2 := rep_apply_inv ρ (a * g₂) _
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, m2] at h
  simp only [LinearMap.sub_apply, Module.End.one_apply]
  linear_combination (norm := module) (-1 : ℂ) • h

/-- **The cup formula is the triple form.** -/
theorem cupFormula_eq_tripleForm (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w) {a g₂ : G}
    {z : G → V} {z' : G → W} {v : V × V × V} {v' : W × W × W}
    (hz : IsCocycle ρ z) (hv : IsPrimitive ρ a g₂ z v) (hv' : IsPrimitive ρ' a g₂ z' v') :
    cupFormula B ρ' a g₂ z z' v = tripleForm B ρ' a g₂ v v' := by
  have zb := hv.value_mul hz
  obtain ⟨p1, p2, p3⟩ := hv
  obtain ⟨q1, q2, q3⟩ := hv'
  have e : ρ' (a * g₂) v'.2.1 = ρ' a (ρ' g₂ v'.2.1) := rep_mul_apply ρ' a g₂ _
  unfold cupFormula
  rw [zb, p1, q1, q2, q3, tripleForm_apply]
  simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.one_apply, map_sub, map_add,
    pair_rep_left hinv a, pair_rep_left hinv (a * g₂), rep_inv_apply ρ', rep_apply_inv ρ', e]
  ring

/-- The cup formula does not depend on the choice of the primitives of the first cocycle. -/
theorem tripleForm_eq_of_primitive (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w) {a g₂ : G}
    {z : G → V} {v v₀ : V × V × V} (hv : IsPrimitive ρ a g₂ z v)
    (hv₀ : IsPrimitive ρ a g₂ z v₀) (v' : W × W × W) :
    tripleForm B ρ' a g₂ v v' = tripleForm B ρ' a g₂ v₀ v' := by
  obtain ⟨p1, p2, p3⟩ := hv
  obtain ⟨r1, r2, r3⟩ := hv₀
  have f1 : v.1 - v₀.1 ∈ fixedBy ρ a := by
    rw [mem_fixedBy, map_sub]
    have := p1.symm.trans r1
    simp only [LinearMap.sub_apply, Module.End.one_apply] at this
    linear_combination (norm := module) this
  have f2 : v.2.1 - v₀.2.1 ∈ fixedBy ρ g₂ := by
    rw [mem_fixedBy, map_sub]
    have := p2.symm.trans r2
    simp only [LinearMap.sub_apply, Module.End.one_apply] at this
    linear_combination (norm := module) this
  have f3 : v.2.2 - v₀.2.2 ∈ fixedBy ρ (a * g₂)⁻¹ := by
    rw [mem_fixedBy, map_sub]
    have := p3.symm.trans r3
    simp only [LinearMap.sub_apply, Module.End.one_apply] at this
    linear_combination (norm := module) this
  have key := tripleForm_fixed (B := B) (ρ' := ρ') hinv a g₂ f1 f2 f3 v'
  have split : v = v₀ + (v.1 - v₀.1, v.2.1 - v₀.2.1, v.2.2 - v₀.2.2) := by
    refine Prod.ext (by simp) (Prod.ext (by simp) (by simp))
  rw [split, map_add, LinearMap.add_apply, key, add_zero]

/-- The cup formula vanishes on a coboundary in the first slot, for a cocycle in the second. -/
theorem tripleForm_boundary_left {a g₂ : G} {z' : G → W} {v' : W × W × W}
    (hz' : IsCocycle ρ' z') (hv' : IsPrimitive ρ' a g₂ z' v') (u : V) :
    tripleForm B ρ' a g₂ (u, u, u) v' = 0 := by
  have hc : constraint ρ' a g₂ v' = 0 := LinearMap.mem_ker.1 (hv'.mem_tripleCycles hz')
  rw [tripleForm_diag, hc, map_zero, neg_zero]

/-- **Left nondegeneracy.**  If the cup pairing of `z` with every cocycle `z'` vanishes, then `z` is
a coboundary.  Hypotheses: `B` is a perfect invariant pairing, cocycles are determined by their values
at `a` and `g₂`, and every constrained triple of `W` is the primitive of a cocycle. -/
theorem left_nondegenerate [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (hL : ∀ v, (∀ w, B v w = 0) → v = 0) (hR : ∀ w, (∀ v, B v w = 0) → w = 0)
    (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w) (a g₂ : G)
    (generated : ∀ z z' : G → V, IsCocycle ρ z → IsCocycle ρ z' → z a = z' a → z g₂ = z' g₂ →
      z = z')
    (exists_dual : ∀ v' ∈ tripleCycles ρ' a g₂, ∃ z' : G → W, IsCocycle ρ' z' ∧
      IsPrimitive ρ' a g₂ z' v')
    {z : G → V} (hz : IsCocycle ρ z) {v : V × V × V} (hv : IsPrimitive ρ a g₂ z v)
    (zero : ∀ (z' : G → W) (v' : W × W × W), IsCocycle ρ' z' → IsPrimitive ρ' a g₂ z' v' →
      tripleForm B ρ' a g₂ v v' = 0) :
    ∃ u : V, ∀ g, z g = ρ g u - u := by
  have hrad : ∀ v' ∈ tripleCycles ρ' a g₂, tripleForm B ρ' a g₂ v v' = 0 := by
    intro v' hv'
    obtain ⟨z', hz', hp⟩ := exists_dual v' hv'
    exact zero z' v' hz' hp
  have htriv := (leftRadical_iff hL hR hinv a g₂ v).1 hrad
  obtain ⟨y, hy, w, hw, hsum⟩ := Submodule.mem_sup.1 htriv
  obtain ⟨u, rfl⟩ := hw
  rw [Submodule.mem_prod] at hy
  obtain ⟨hy1, hy23⟩ := hy
  rw [Submodule.mem_prod] at hy23
  obtain ⟨hy2, _⟩ := hy23
  have hv1 : v.1 = y.1 + u := by rw [← hsum]; rfl
  have hv2 : v.2.1 = y.2.1 + u := by rw [← hsum]; rfl
  refine ⟨u, ?_⟩
  have y1 : ρ a y.1 = y.1 := mem_fixedBy.1 hy1
  have y2 : ρ g₂ y.2.1 = y.2.1 := mem_fixedBy.1 hy2
  have eq := generated z (fun g => ρ g u - u) hz (isCocycle_boundary ρ u) ?_ ?_
  · intro g
    exact congrFun eq g
  · rw [hv.1, hv1]
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_add, y1]
    abel
  · rw [hv.2.1, hv2]
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_add, y2]
    abel

/-- **Right nondegeneracy.** -/
theorem right_nondegenerate [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (hL : ∀ v, (∀ w, B v w = 0) → v = 0) (hR : ∀ w, (∀ v, B v w = 0) → w = 0)
    (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w) (a g₂ : G)
    (generated : ∀ z z' : G → W, IsCocycle ρ' z → IsCocycle ρ' z' → z a = z' a → z g₂ = z' g₂ →
      z = z')
    (exists_dual : ∀ v ∈ tripleCycles ρ a g₂, ∃ z : G → V, IsCocycle ρ z ∧
      IsPrimitive ρ a g₂ z v)
    {z' : G → W} (hz' : IsCocycle ρ' z') {v' : W × W × W} (hv' : IsPrimitive ρ' a g₂ z' v')
    (zero : ∀ (z : G → V) (v : V × V × V), IsCocycle ρ z → IsPrimitive ρ a g₂ z v →
      tripleForm B ρ' a g₂ v v' = 0) :
    ∃ u : W, ∀ g, z' g = ρ' g u - u := by
  have hrad : ∀ v ∈ tripleCycles ρ a g₂, tripleForm B ρ' a g₂ v v' = 0 := by
    intro v hv
    obtain ⟨z, hz, hp⟩ := exists_dual v hv
    exact zero z v hz hp
  have htriv := (rightRadical_iff hL hR hinv a g₂ v').1 hrad
  obtain ⟨y, hy, w, hw, hsum⟩ := Submodule.mem_sup.1 htriv
  obtain ⟨u, rfl⟩ := hw
  rw [Submodule.mem_prod] at hy
  obtain ⟨hy1, hy23⟩ := hy
  rw [Submodule.mem_prod] at hy23
  obtain ⟨hy2, _⟩ := hy23
  have hv1 : v'.1 = y.1 + u := by rw [← hsum]; rfl
  have hv2 : v'.2.1 = y.2.1 + u := by rw [← hsum]; rfl
  refine ⟨u, ?_⟩
  have y1 : ρ' a y.1 = y.1 := mem_fixedBy.1 hy1
  have y2 : ρ' g₂ y.2.1 = y.2.1 := mem_fixedBy.1 hy2
  have eq := generated z' (fun g => ρ' g u - u) hz' (isCocycle_boundary ρ' u) ?_ ?_
  · intro g
    exact congrFun eq g
  · rw [hv'.1, hv1]
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_add, y1]
    abel
  · rw [hv'.2.1, hv2]
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_add, y2]
    abel

end Pairing

end TernaryPeriodPolynomials.BoundaryDuality.CocycleBridge
