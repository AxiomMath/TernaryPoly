module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.CocycleBridge

@[expose] public section


/-!
# The orientation-reversing involution on the triple model

Let `σ` be an involutive automorphism of `G` inverting the two special elements (`σ a = a⁻¹`,
`σ g₂ = g₂⁻¹`; for `Γ₁(3)` it is conjugation by `ε = diag(-1, 1)`), and `e`, `e'` involutions of the
coefficient spaces intertwining `ρ ∘ σ` with `ρ` and satisfying `B (e v) (e' w) = s B v w`.

* `tripleForm_theta`: the transport `Θ` of primitive triples along `σ` multiplies the cup form by
  `-s` up to the two constraint terms: the cup pairing is orientation-reversing, so for `s = -1`
  (the twisted coefficient system) the pairing of the `σ`-invariant classes is the restriction of the
  perfect pairing and `σ`-anti-invariant classes pair to zero with `σ`-invariant ones.
* `left_nondegenerate_reflect`: a `σ`-invariant parabolic cocycle which pairs to zero with every
  `σ`-invariant parabolic cocycle is the coboundary of a `σ`-invariant vector.
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.EpsilonSplit

open TripleModel LinearDuality CocycleBridge

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The reflection data: an involutive automorphism `σ` of `G` inverting `a` and `g₂`, involutions
`e`, `e'` of the coefficient spaces intertwining the actions along `σ`, and a pairing which is
invariant under `a`, `g₂` and changes by the factor `s` under `(e, e')`. -/
structure ReflectData (ρ : Representation ℂ G V) (ρ' : Representation ℂ G W)
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (a g₂ : G) (s : ℂ) where
  σ : G →* G
  e : V →ₗ[ℂ] V
  e' : W →ₗ[ℂ] W
  σσ : ∀ h, σ (σ h) = h
  ee : ∀ v, e (e v) = v
  ee' : ∀ w, e' (e' w) = w
  equiv : ∀ h v, e (ρ h v) = ρ (σ h) (e v)
  equiv' : ∀ h w, e' (ρ' h w) = ρ' (σ h) (e' w)
  sa : σ a = a⁻¹
  sg : σ g₂ = g₂⁻¹
  pair : ∀ v w, B (e v) (e' w) = s * B v w
  invA : ∀ v w, B (ρ a v) (ρ' a w) = B v w
  invG : ∀ v w, B (ρ g₂ v) (ρ' g₂ w) = B v w

/-- The transport of a primitive triple along the reflection. -/
def thetaOf (ρ : Representation ℂ G V) (e : V →ₗ[ℂ] V) (a : G) (v : V × V × V) : V × V × V :=
  (e v.1, e v.2.1, e (v.1 - ρ a⁻¹ v.1 + ρ a⁻¹ v.2.2))

section Identity

variable {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W} {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ}
  {a g₂ : G} {s : ℂ} (D : ReflectData ρ ρ' B a g₂ s)

/-- The cup form is multiplied by `-s` by the reflection, up to the constraint terms. -/
theorem tripleForm_theta (v : V × V × V) (w : W × W × W) :
    tripleForm B ρ' a g₂ (thetaOf ρ D.e a v) (thetaOf ρ' D.e' a w) + s * tripleForm B ρ' a g₂ v w =
      s * (B (constraint ρ a g₂ v) ((1 - ρ' a) w.1 + (ρ' (a * g₂) - 1) w.2.2) +
        B v.1 ((ρ' a⁻¹ - 1 - ρ' (a * g₂)⁻¹ + ρ' (a⁻¹ * (a * g₂)⁻¹)) (constraint ρ' a g₂ w)) +
        B v.2.1 ((ρ' (a * g₂)⁻¹ - ρ' a⁻¹) (constraint ρ' a g₂ w))) := by
  have ca : ∀ y, ρ' a (D.e' y) = D.e' (ρ' a⁻¹ y) := fun y => by
    rw [D.equiv', map_inv, D.sa, inv_inv]
  have cg : ∀ y, ρ' g₂ (D.e' y) = D.e' (ρ' g₂⁻¹ y) := fun y => by
    rw [D.equiv', map_inv, D.sg, inv_inv]
  have aL : ∀ x z, B (ρ a x) z = B x (ρ' a⁻¹ z) := fun x z => by
    have := D.invA x (ρ' a⁻¹ z)
    rwa [rep_apply_inv ρ'] at this
  have aiL : ∀ x z, B (ρ a⁻¹ x) z = B x (ρ' a z) := fun x z => by
    have := D.invA (ρ a⁻¹ x) z
    rw [rep_apply_inv ρ] at this
    exact this.symm
  have gL : ∀ x z, B (ρ g₂ x) z = B x (ρ' g₂⁻¹ z) := fun x z => by
    have := D.invG x (ρ' g₂⁻¹ z)
    rwa [rep_apply_inv ρ'] at this
  have giL : ∀ x z, B (ρ g₂⁻¹ x) z = B x (ρ' g₂ z) := fun x z => by
    have := D.invG (ρ g₂⁻¹ x) z
    rw [rep_apply_inv ρ] at this
    exact this.symm
  simp only [thetaOf, tripleForm_apply, constraint_apply]
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply,
    mul_inv_rev, map_mul, Module.End.mul_apply, ca, cg, D.pair, aL, aiL, gL,
    rep_apply_inv ρ', rep_inv_apply ρ']
  ring

end Identity

section Transport

variable {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W} {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ}
  {a g₂ : G} {s : ℂ}

theorem isCocycle_map_inv {z : G → V} (hz : IsCocycle ρ z) (g : G) :
    z g⁻¹ = -ρ g⁻¹ (z g) := by
  have h := hz g⁻¹ g
  rw [inv_mul_cancel, hz.map_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- Transport of a cochain along the reflection. -/
def reflect (σ : G →* G) (e : V →ₗ[ℂ] V) (z : G → V) : G → V := fun h => e (z (σ h))

theorem isCocycle_reflect {z : G → V} (hz : IsCocycle ρ z) (σ : G →* G) (e : V →ₗ[ℂ] V)
    (equiv : ∀ h v, e (ρ h v) = ρ (σ h) (e v)) (σσ : ∀ h, σ (σ h) = h) :
    IsCocycle ρ (reflect σ e z) := by
  intro g h
  simp only [reflect, map_mul]
  rw [hz (σ g) (σ h), map_add, equiv, σσ]

theorem reflect_reflect (σ : G →* G) (e : V →ₗ[ℂ] V) (σσ : ∀ h, σ (σ h) = h)
    (ee : ∀ v, e (e v) = v) (z : G → V) : reflect σ e (reflect σ e z) = z := by
  funext h
  simp only [reflect, σσ, ee]

/-- The reflected cocycle has the transported primitive triple. -/
theorem isPrimitive_reflect {z : G → V} (σ : G →* G) (e : V →ₗ[ℂ] V)
    (equiv : ∀ h v, e (ρ h v) = ρ (σ h) (e v)) (_σσ : ∀ h, σ (σ h) = h)
    (sa : σ a = a⁻¹) (sg : σ g₂ = g₂⁻¹) (hz : IsCocycle ρ z)
    {v : V × V × V} (hv : IsPrimitive ρ a g₂ z v) :
    IsPrimitive ρ a g₂ (reflect σ e z) (thetaOf ρ e a v) := by
  have zb := hv.value_mul hz
  obtain ⟨p1, p2, p3⟩ := hv
  have hsa' : σ a⁻¹ = a := by rw [map_inv, sa, inv_inv]
  have hsg' : σ g₂⁻¹ = g₂ := by rw [map_inv, sg, inv_inv]
  refine ⟨?_, ?_, ?_⟩
  · show e (z (σ a)) = (ρ a - 1) (e v.1)
    rw [sa, isCocycle_map_inv hz, p1]
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, map_neg, rep_inv_apply ρ,
      equiv, hsa']
    abel
  · show e (z (σ g₂)) = (ρ g₂ - 1) (e v.2.1)
    rw [sg, isCocycle_map_inv hz, p2]
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, map_neg, rep_inv_apply ρ,
      equiv, hsg']
    abel
  · have key : σ (a * g₂)⁻¹ = a⁻¹ * (a * g₂) * a := by
      rw [map_inv, map_mul, sa, sg]; group
    have e1 : z (a⁻¹ * (a * g₂) * a) =
        z a⁻¹ + ρ a⁻¹ (z (a * g₂)) + ρ (a⁻¹ * (a * g₂)) (z a) := by
      rw [hz (a⁻¹ * (a * g₂)) a, hz a⁻¹ (a * g₂)]
    show e (z (σ (a * g₂)⁻¹)) = (ρ (a * g₂)⁻¹ - 1) (e (v.1 - ρ a⁻¹ v.1 + ρ a⁻¹ v.2.2))
    rw [key, e1, isCocycle_map_inv hz, zb, p1]
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, map_add,
      map_neg, equiv, map_inv, map_mul, sa, sg, inv_inv, mul_inv_rev, Module.End.mul_apply,
      rep_inv_apply ρ]
    module

theorem isCocycle_add {z z' : G → V} (hz : IsCocycle ρ z) (hz' : IsCocycle ρ z') :
    IsCocycle ρ (fun x => z x + z' x) := by
  intro g h
  simp only [hz g h, hz' g h, map_add]
  abel

theorem isCocycle_sub {z z' : G → V} (hz : IsCocycle ρ z) (hz' : IsCocycle ρ z') :
    IsCocycle ρ (fun x => z x - z' x) := by
  intro g h
  simp only [hz g h, hz' g h, map_sub]
  abel

theorem isCocycle_smul {z : G → V} (hz : IsCocycle ρ z) (c : ℂ) :
    IsCocycle ρ (fun x => c • z x) := by
  intro g h
  simp only [hz g h, map_smul, smul_add]

theorem isPrimitive_add {z z' : G → V} {v v' : V × V × V} (h : IsPrimitive ρ a g₂ z v)
    (h' : IsPrimitive ρ a g₂ z' v') : IsPrimitive ρ a g₂ (fun x => z x + z' x) (v + v') := by
  obtain ⟨p1, p2, p3⟩ := h
  obtain ⟨q1, q2, q3⟩ := h'
  refine ⟨?_, ?_, ?_⟩
  · show z a + z' a = (ρ a - 1) (v.1 + v'.1)
    rw [p1, q1, map_add]
  · show z g₂ + z' g₂ = (ρ g₂ - 1) (v.2.1 + v'.2.1)
    rw [p2, q2, map_add]
  · show z (a * g₂)⁻¹ + z' (a * g₂)⁻¹ = (ρ (a * g₂)⁻¹ - 1) (v.2.2 + v'.2.2)
    rw [p3, q3, map_add]

theorem isPrimitive_sub {z z' : G → V} {v v' : V × V × V} (h : IsPrimitive ρ a g₂ z v)
    (h' : IsPrimitive ρ a g₂ z' v') : IsPrimitive ρ a g₂ (fun x => z x - z' x) (v - v') := by
  obtain ⟨p1, p2, p3⟩ := h
  obtain ⟨q1, q2, q3⟩ := h'
  refine ⟨?_, ?_, ?_⟩
  · show z a - z' a = (ρ a - 1) (v.1 - v'.1)
    rw [p1, q1, map_sub]
  · show z g₂ - z' g₂ = (ρ g₂ - 1) (v.2.1 - v'.2.1)
    rw [p2, q2, map_sub]
  · show z (a * g₂)⁻¹ - z' (a * g₂)⁻¹ = (ρ (a * g₂)⁻¹ - 1) (v.2.2 - v'.2.2)
    rw [p3, q3, map_sub]

theorem isPrimitive_smul {z : G → V} {v : V × V × V} (h : IsPrimitive ρ a g₂ z v) (c : ℂ) :
    IsPrimitive ρ a g₂ (fun x => c • z x) (c • v) := by
  obtain ⟨p1, p2, p3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · show c • z a = (ρ a - 1) (c • v.1)
    rw [p1, map_smul]
  · show c • z g₂ = (ρ g₂ - 1) (c • v.2.1)
    rw [p2, map_smul]
  · show c • z (a * g₂)⁻¹ = (ρ (a * g₂)⁻¹ - 1) (c • v.2.2)
    rw [p3, map_smul]

end Transport

section Independence

variable {ρ' : Representation ℂ G W} {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ} {a g₂ : G}

/-- The cup form does not depend on the choice of the primitives of the second cocycle. -/
theorem tripleForm_eq_of_primitive_right {z' : G → W} {v' v₀' : W × W × W}
    (hv' : IsPrimitive ρ' a g₂ z' v') (hv₀' : IsPrimitive ρ' a g₂ z' v₀') (v : V × V × V) :
    tripleForm B ρ' a g₂ v v' = tripleForm B ρ' a g₂ v v₀' := by
  obtain ⟨p1, p2, p3⟩ := hv'
  obtain ⟨r1, r2, r3⟩ := hv₀'
  have f1 : v'.1 - v₀'.1 ∈ fixedBy ρ' a := by
    rw [mem_fixedBy, map_sub]
    have := p1.symm.trans r1
    simp only [LinearMap.sub_apply, Module.End.one_apply] at this
    linear_combination (norm := module) this
  have f2 : v'.2.1 - v₀'.2.1 ∈ fixedBy ρ' g₂ := by
    rw [mem_fixedBy, map_sub]
    have := p2.symm.trans r2
    simp only [LinearMap.sub_apply, Module.End.one_apply] at this
    linear_combination (norm := module) this
  have f3 : v'.2.2 - v₀'.2.2 ∈ fixedBy ρ' (a * g₂)⁻¹ := by
    rw [mem_fixedBy, map_sub]
    have := p3.symm.trans r3
    simp only [LinearMap.sub_apply, Module.End.one_apply] at this
    linear_combination (norm := module) this
  have key := tripleForm_fixed' (B := B) (ρ' := ρ') a g₂ v f1 f2 f3
  have split : v' = v₀' + (v'.1 - v₀'.1, v'.2.1 - v₀'.2.1, v'.2.2 - v₀'.2.2) := by
    refine Prod.ext (by simp) (Prod.ext (by simp) (by simp))
  rw [split, map_add, key, add_zero]

end Independence

section Main

variable {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W} {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ}
  {a g₂ : G}

/-- **Left nondegeneracy for the reflection-invariant parabolic classes** (twisted coefficient
system, `s = -1`): a `σ`-invariant parabolic cocycle which pairs to zero with every `σ`-invariant
parabolic cocycle is the coboundary of a `σ`-invariant vector. -/
theorem left_nondegenerate_reflect [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (hL : ∀ v, (∀ w, B v w = 0) → v = 0) (hR : ∀ w, (∀ v, B v w = 0) → w = 0)
    (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w) (D : ReflectData ρ ρ' B a g₂ (-1))
    (generated : ∀ z z' : G → V, IsCocycle ρ z → IsCocycle ρ z' → z a = z' a → z g₂ = z' g₂ →
      z = z')
    (exists_dual : ∀ v' ∈ tripleCycles ρ' a g₂, ∃ z' : G → W, IsCocycle ρ' z' ∧
      IsPrimitive ρ' a g₂ z' v')
    {z : G → V} (hz : IsCocycle ρ z) {v : V × V × V} (hv : IsPrimitive ρ a g₂ z v)
    (zinv : reflect D.σ D.e z = z)
    (zero : ∀ (z' : G → W) (v' : W × W × W), IsCocycle ρ' z' → IsPrimitive ρ' a g₂ z' v' →
      reflect D.σ D.e' z' = z' → cupFormula B ρ' a g₂ z z' v = 0) :
    ∃ u : V, D.e u = u ∧ ∀ g, z g = ρ g u - u := by
  have hΘv : IsPrimitive ρ a g₂ z (thetaOf ρ D.e a v) := by
    have := isPrimitive_reflect D.σ D.e D.equiv D.σσ D.sa D.sg hz hv
    rwa [zinv] at this
  have hall : ∀ (z'' : G → W) (w'' : W × W × W), IsCocycle ρ' z'' → IsPrimitive ρ' a g₂ z'' w'' →
      tripleForm B ρ' a g₂ v w'' = 0 := by
    intro z'' w'' hz'' hw''
    have hy : IsCocycle ρ' (reflect D.σ D.e' z'') :=
      isCocycle_reflect hz'' D.σ D.e' D.equiv' D.σσ
    have hyw : IsPrimitive ρ' a g₂ (reflect D.σ D.e' z'') (thetaOf ρ' D.e' a w'') :=
      isPrimitive_reflect D.σ D.e' D.equiv' D.σσ D.sa D.sg hz'' hw''
    -- invariant part
    have hzp : IsCocycle ρ' (fun x => (1 / 2 : ℂ) • (z'' x + reflect D.σ D.e' z'' x)) :=
      isCocycle_smul (isCocycle_add hz'' hy) _
    have hwp : IsPrimitive ρ' a g₂ (fun x => (1 / 2 : ℂ) • (z'' x + reflect D.σ D.e' z'' x))
        ((1 / 2 : ℂ) • (w'' + thetaOf ρ' D.e' a w'')) :=
      isPrimitive_smul (isPrimitive_add hw'' hyw) _
    have hpinv : reflect D.σ D.e' (fun x => (1 / 2 : ℂ) • (z'' x + reflect D.σ D.e' z'' x)) =
        fun x => (1 / 2 : ℂ) • (z'' x + reflect D.σ D.e' z'' x) := by
      funext x
      have h1 := congrFun (reflect_reflect D.σ D.e' D.σσ D.ee' z'') x
      simp only [reflect] at h1 ⊢
      rw [map_smul, map_add, h1]
      module
    have vp := zero _ _ hzp hwp hpinv
    rw [cupFormula_eq_tripleForm hinv hz hv hwp] at vp
    -- anti-invariant part
    have hzm : IsCocycle ρ' (fun x => (1 / 2 : ℂ) • (z'' x - reflect D.σ D.e' z'' x)) :=
      isCocycle_smul (isCocycle_sub hz'' hy) _
    have hwm : IsPrimitive ρ' a g₂ (fun x => (1 / 2 : ℂ) • (z'' x - reflect D.σ D.e' z'' x))
        ((1 / 2 : ℂ) • (w'' - thetaOf ρ' D.e' a w'')) :=
      isPrimitive_smul (isPrimitive_sub hw'' hyw) _
    have hminv : reflect D.σ D.e' (fun x => (1 / 2 : ℂ) • (z'' x - reflect D.σ D.e' z'' x)) =
        fun x => (-1 : ℂ) • ((1 / 2 : ℂ) • (z'' x - reflect D.σ D.e' z'' x)) := by
      funext x
      have h1 := congrFun (reflect_reflect D.σ D.e' D.σσ D.ee' z'') x
      simp only [reflect] at h1 ⊢
      rw [map_smul, map_sub, h1]
      module
    have hwm_neg : IsPrimitive ρ' a g₂
        (fun x => (-1 : ℂ) • ((1 / 2 : ℂ) • (z'' x - reflect D.σ D.e' z'' x)))
        ((-1 : ℂ) • ((1 / 2 : ℂ) • (w'' - thetaOf ρ' D.e' a w''))) :=
      isPrimitive_smul hwm _
    have hmΘ : IsPrimitive ρ' a g₂
        (reflect D.σ D.e' (fun x => (1 / 2 : ℂ) • (z'' x - reflect D.σ D.e' z'' x)))
        (thetaOf ρ' D.e' a ((1 / 2 : ℂ) • (w'' - thetaOf ρ' D.e' a w''))) :=
      isPrimitive_reflect D.σ D.e' D.equiv' D.σσ D.sa D.sg hzm hwm
    rw [hminv] at hmΘ
    set wm : W × W × W := (1 / 2 : ℂ) • (w'' - thetaOf ρ' D.e' a w'') with hwmdef
    have hΨv : constraint ρ a g₂ v = 0 := LinearMap.mem_ker.1 (hv.mem_tripleCycles hz)
    have hΨw : constraint ρ' a g₂ wm = 0 := LinearMap.mem_ker.1 (hwm.mem_tripleCycles hzm)
    have ident := tripleForm_theta D v wm
    rw [hΨv, hΨw] at ident
    simp only [map_zero, LinearMap.zero_apply, add_zero, mul_zero] at ident
    have s1 : tripleForm B ρ' a g₂ (thetaOf ρ D.e a v) (thetaOf ρ' D.e' a wm) =
        tripleForm B ρ' a g₂ v (thetaOf ρ' D.e' a wm) :=
      tripleForm_eq_of_primitive hinv hΘv hv _
    have s2 : tripleForm B ρ' a g₂ v (thetaOf ρ' D.e' a wm) =
        tripleForm B ρ' a g₂ v ((-1 : ℂ) • wm) :=
      tripleForm_eq_of_primitive_right hmΘ hwm_neg v
    have s3 : tripleForm B ρ' a g₂ v ((-1 : ℂ) • wm) = -tripleForm B ρ' a g₂ v wm := by
      rw [map_smul]
      simp
    have ht : tripleForm B ρ' a g₂ v wm = 0 := by
      linear_combination (1 / 2 : ℂ) * (s1.trans (s2.trans s3)) - (1 / 2 : ℂ) * ident
    have hsplit : w'' = (1 / 2 : ℂ) • (w'' + thetaOf ρ' D.e' a w'') + wm := by
      rw [hwmdef]
      module
    have hsum : tripleForm B ρ' a g₂ v w'' =
        tripleForm B ρ' a g₂ v ((1 / 2 : ℂ) • (w'' + thetaOf ρ' D.e' a w'')) +
          tripleForm B ρ' a g₂ v wm := by
      rw [← map_add, ← hsplit]
    rw [hsum, vp, ht, add_zero]
  obtain ⟨u₀, hu₀⟩ := CocycleBridge.left_nondegenerate hL hR hinv a g₂ generated exists_dual hz hv
    (fun z' v' hz' hp => hall z' v' hz' hp)
  refine ⟨(1 / 2 : ℂ) • (u₀ + D.e u₀), ?_, ?_⟩
  · simp only [map_smul, map_add, D.ee]
    module
  · intro g
    have h1 := hu₀ g
    have h2 : z g = ρ g (D.e u₀) - D.e u₀ := by
      have h4 := congrFun zinv g
      have h3 := hu₀ (D.σ g)
      simp only [reflect] at h4
      rw [← h4, h3, map_sub, D.equiv, D.σσ]
    simp only [map_smul, map_add]
    linear_combination (norm := module) (1 / 2 : ℂ) • h1 + (1 / 2 : ℂ) • h2

end Main

end TernaryPeriodPolynomials.BoundaryDuality.EpsilonSplit
