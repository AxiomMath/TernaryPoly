module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.EpsilonSplit
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section


/-!
# The parabolic cup pairing on crossed homomorphisms and its descent to first cohomology

Let `Γ` be a group, `ι : N → Γ` a homomorphism and `a, g₂ ∈ N` two elements, with `b = a g₂` and
`g₃ = b⁻¹`, as in the triple model.  A crossed homomorphism `Z : Γ → V` is *parabolic* if its
restriction along `ι` has a primitive triple at `a`, `g₂`, `g₃`, that is, if `Z a`, `Z g₂`, `Z g₃`
are coboundaries of the corresponding cyclic subgroups.  The cup pairing of two parabolic crossed
homomorphisms `Z`, `Z'` is the cup formula of the restrictions along `ι`, computed from a primitive
triple of the first one; it does not depend on this choice, is bilinear, and vanishes as soon as one
of the two crossed homomorphisms is a coboundary.

* A crossed homomorphism takes on an element of finite order a value in the image of `g - 1`
  (`exists_sub_of_pow`), so a crossed homomorphism whose values at the unipotent generators are
  coboundaries has a primitive triple as soon as the third special element has finite order.
* `parabolicCochains`: the parabolic crossed homomorphisms, a submodule of the functions `Γ → V`.
* `pairFun`, `pairFun_eq`: the cup pairing, as the triple form of any two primitive triples.
* `parPairing`: the pairing as a bilinear map on the parabolic crossed homomorphisms.
* `exists_descent`: a bilinear form on submodules `P`, `P'` of cochain modules which vanishes when a
  factor maps to zero under a linear map `f`, `g` descends to the images `f(P)`, `g(P')`.
* `classPairing`: the pairing on the parabolic classes of any cohomology model `f : K → H` of the
  crossed homomorphisms modulo coboundaries, with its value on representatives
  (`classPairing_apply`, `cochainPairing_eq_cupFormula`) and the transfer of left nondegeneracy from
  the crossed homomorphisms to the classes (`classPairing_left_nondegenerate`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality

open TripleModel LinearDuality CocycleBridge EpsilonSplit

section FiniteOrder

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  {z : G → V}

/-- A crossed homomorphism takes on an element `g` of finite order a value in the image of `g - 1`
(averaging over the cyclic group, in characteristic zero). -/
theorem exists_sub_of_pow (hz : IsCocycle ρ z) {g : G} {k : ℕ} (hk : 0 < k) (hg : g ^ k = 1) :
    ∃ u : V, z g = (ρ g - 1) u := by
  have step : ∀ i : ℕ, ρ g (z (g ^ i)) = z (g ^ (i + 1)) - z g := by
    intro i
    have h := hz g (g ^ i)
    rw [← pow_succ'] at h
    rw [h]
    abel
  have tele : ∑ i ∈ Finset.range k, (z (g ^ (i + 1)) - z (g ^ i)) = 0 := by
    refine (Finset.sum_range_sub (fun i => z (g ^ i)) k).trans ?_
    show z (g ^ k) - z (g ^ 0) = 0
    rw [hg, pow_zero, hz.map_one, sub_self]
  have hkc : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have key : ρ g (∑ i ∈ Finset.range k, z (g ^ i)) - ∑ i ∈ Finset.range k, z (g ^ i) =
      -((k : ℂ) • z g) := by
    rw [map_sum, ← Finset.sum_sub_distrib]
    have e : ∀ i ∈ Finset.range k, ρ g (z (g ^ i)) - z (g ^ i) =
        (z (g ^ (i + 1)) - z (g ^ i)) - z g := by
      intro i _
      rw [step i]
      abel
    rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, tele, Finset.sum_const, Finset.card_range,
      zero_sub, ← Nat.cast_smul_eq_nsmul ℂ]
  refine ⟨(-((k : ℂ)⁻¹)) • (∑ i ∈ Finset.range k, z (g ^ i)), ?_⟩
  rw [LinearMap.sub_apply, Module.End.one_apply, map_smul, ← smul_sub, key, smul_neg, smul_smul]
  have c1 : (-((k : ℂ)⁻¹)) * (k : ℂ) = -1 := by
    rw [neg_mul, inv_mul_cancel₀ hkc]
  rw [c1, neg_smul, one_smul, neg_neg]

/-- If the value of a crossed homomorphism at `g` is a coboundary, so is its value at `g⁻¹`. -/
theorem exists_sub_inv (hz : IsCocycle ρ z) {g : G} (h : ∃ u : V, z g = (ρ g - 1) u) :
    ∃ u : V, z g⁻¹ = (ρ g⁻¹ - 1) u := by
  obtain ⟨u, hu⟩ := h
  refine ⟨u, ?_⟩
  rw [isCocycle_map_inv hz g, hu]
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, rep_inv_apply ρ]
  abel

/-- A crossed homomorphism whose values at the three special elements are coboundaries has a
primitive triple. -/
theorem exists_primitive_of_exists {a g₂ : G} (h₁ : ∃ u : V, z a = (ρ a - 1) u)
    (h₂ : ∃ u : V, z g₂ = (ρ g₂ - 1) u) (h₃ : ∃ u : V, z (a * g₂)⁻¹ = (ρ (a * g₂)⁻¹ - 1) u) :
    ∃ v : V × V × V, IsPrimitive ρ a g₂ z v := by
  obtain ⟨u₁, p₁⟩ := h₁
  obtain ⟨u₂, p₂⟩ := h₂
  obtain ⟨u₃, p₃⟩ := h₃
  exact ⟨(u₁, u₂, u₃), p₁, p₂, p₃⟩

end FiniteOrder

section Cochains

variable {Γ N V W : Type} [Group Γ] [Group N] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]

/-- The restriction of a crossed homomorphism along a homomorphism is a crossed homomorphism. -/
theorem isCocycle_comp {ρ : Representation ℂ Γ V} {Z : Γ → V} (hZ : IsCocycle ρ Z) (ι : N →* Γ) :
    IsCocycle (ρ.comp ι) (fun n => Z (ι n)) := by
  intro g h
  show Z (ι (g * h)) = Z (ι g) + ρ (ι g) (Z (ι h))
  rw [map_mul]
  exact hZ _ _

/-- The parabolic crossed homomorphisms: the crossed homomorphisms `Γ → V` whose restriction along
`ι` has a primitive triple at `a`, `g₂`, `(a g₂)⁻¹`. -/
def parabolicCochains (ι : N →* Γ) (ρ : Representation ℂ Γ V) (a g₂ : N) :
    Submodule ℂ (Γ → V) where
  carrier := {Z | IsCocycle ρ Z ∧ ∃ v, IsPrimitive (ρ.comp ι) a g₂ (fun n => Z (ι n)) v}
  zero_mem' := by
    refine ⟨?_, 0, ?_⟩
    · intro g h
      simp
    · refine ⟨?_, ?_, ?_⟩ <;> simp
  add_mem' := by
    rintro Z₁ Z₂ ⟨h₁, v₁, p₁⟩ ⟨h₂, v₂, p₂⟩
    exact ⟨isCocycle_add h₁ h₂, v₁ + v₂, isPrimitive_add p₁ p₂⟩
  smul_mem' := by
    rintro c Z ⟨h, v, p⟩
    exact ⟨isCocycle_smul h c, c • v, isPrimitive_smul p c⟩

/-- Membership in the parabolic crossed homomorphisms, unfolded. -/
theorem mem_parabolicCochains {ι : N →* Γ} {ρ : Representation ℂ Γ V} {a g₂ : N} {Z : Γ → V} :
    Z ∈ parabolicCochains ι ρ a g₂ ↔
      IsCocycle ρ Z ∧ ∃ v, IsPrimitive (ρ.comp ι) a g₂ (fun n => Z (ι n)) v := Iff.rfl

open Classical in
/-- The cup pairing of two cochains: the cup formula of the restrictions along `ι`, computed from a
(chosen) primitive triple of the first cochain; zero if there is none. -/
def pairFun (ι : N →* Γ) (ρ : Representation ℂ Γ V) (ρ' : Representation ℂ Γ W)
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (a g₂ : N) (Z : Γ → V) (Z' : Γ → W) : ℂ :=
  if h : ∃ v, IsPrimitive (ρ.comp ι) a g₂ (fun n => Z (ι n)) v then
    cupFormula B (ρ'.comp ι) a g₂ (fun n => Z (ι n)) (fun n => Z' (ι n)) h.choose
  else 0

/-- **The cup pairing is the triple form of any two primitive triples.** -/
theorem pairFun_eq (ι : N →* Γ) (ρ : Representation ℂ Γ V) (ρ' : Representation ℂ Γ W)
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (a g₂ : N)
    (hinv : ∀ n v w, B (ρ (ι n) v) (ρ' (ι n) w) = B v w) {Z : Γ → V} {Z' : Γ → W}
    (hZ : IsCocycle ρ Z) {v : V × V × V}
    (hv : IsPrimitive (ρ.comp ι) a g₂ (fun n => Z (ι n)) v) {v' : W × W × W}
    (hv' : IsPrimitive (ρ'.comp ι) a g₂ (fun n => Z' (ι n)) v') :
    pairFun ι ρ ρ' B a g₂ Z Z' = tripleForm B (ρ'.comp ι) a g₂ v v' := by
  have hex : ∃ v, IsPrimitive (ρ.comp ι) a g₂ (fun n => Z (ι n)) v := ⟨v, hv⟩
  have hinv' : ∀ (n : N) (x : V) (y : W), B ((ρ.comp ι) n x) ((ρ'.comp ι) n y) = B x y := hinv
  have h0 := hex.choose_spec
  unfold pairFun
  rw [dite_eq_left hex, cupFormula_eq_tripleForm hinv' (isCocycle_comp hZ ι) h0 hv',
    tripleForm_eq_of_primitive hinv' h0 hv]

/-- **The cup pairing is the cup formula of any primitive triple of the first cocycle.** -/
theorem pairFun_eq_cupFormula (ι : N →* Γ) (ρ : Representation ℂ Γ V)
    (ρ' : Representation ℂ Γ W) (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (a g₂ : N)
    (hinv : ∀ n v w, B (ρ (ι n) v) (ρ' (ι n) w) = B v w) {Z : Γ → V} {Z' : Γ → W}
    (hZ : IsCocycle ρ Z) {v : V × V × V}
    (hv : IsPrimitive (ρ.comp ι) a g₂ (fun n => Z (ι n)) v)
    (hZ' : Z' ∈ parabolicCochains ι ρ' a g₂) :
    pairFun ι ρ ρ' B a g₂ Z Z' =
      cupFormula B (ρ'.comp ι) a g₂ (fun n => Z (ι n)) (fun n => Z' (ι n)) v := by
  obtain ⟨_, v', hv'⟩ := mem_parabolicCochains.mp hZ'
  have hinv' : ∀ (n : N) (x : V) (y : W), B ((ρ.comp ι) n x) ((ρ'.comp ι) n y) = B x y := hinv
  rw [pairFun_eq ι ρ ρ' B a g₂ hinv hZ hv hv',
    cupFormula_eq_tripleForm hinv' (isCocycle_comp hZ ι) hv hv']

/-- The cup pairing is additive in the first variable. -/
theorem pairFun_add_left (ι : N →* Γ) (ρ : Representation ℂ Γ V) (ρ' : Representation ℂ Γ W)
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (a g₂ : N)
    (hinv : ∀ n v w, B (ρ (ι n) v) (ρ' (ι n) w) = B v w) {Z₁ Z₂ : Γ → V} {Z' : Γ → W}
    (h₁ : Z₁ ∈ parabolicCochains ι ρ a g₂) (h₂ : Z₂ ∈ parabolicCochains ι ρ a g₂)
    (h' : Z' ∈ parabolicCochains ι ρ' a g₂) :
    pairFun ι ρ ρ' B a g₂ (Z₁ + Z₂) Z' =
      pairFun ι ρ ρ' B a g₂ Z₁ Z' + pairFun ι ρ ρ' B a g₂ Z₂ Z' := by
  obtain ⟨c₁, v₁, p₁⟩ := mem_parabolicCochains.mp h₁
  obtain ⟨c₂, v₂, p₂⟩ := mem_parabolicCochains.mp h₂
  obtain ⟨_, v', p'⟩ := mem_parabolicCochains.mp h'
  rw [pairFun_eq ι ρ ρ' B a g₂ hinv (Z := Z₁ + Z₂) (isCocycle_add c₁ c₂) (isPrimitive_add p₁ p₂) p',
    pairFun_eq ι ρ ρ' B a g₂ hinv c₁ p₁ p', pairFun_eq ι ρ ρ' B a g₂ hinv c₂ p₂ p', map_add,
    LinearMap.add_apply]

/-- The cup pairing is homogeneous in the first variable. -/
theorem pairFun_smul_left (ι : N →* Γ) (ρ : Representation ℂ Γ V) (ρ' : Representation ℂ Γ W)
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (a g₂ : N)
    (hinv : ∀ n v w, B (ρ (ι n) v) (ρ' (ι n) w) = B v w) (c : ℂ) {Z : Γ → V} {Z' : Γ → W}
    (h : Z ∈ parabolicCochains ι ρ a g₂) (h' : Z' ∈ parabolicCochains ι ρ' a g₂) :
    pairFun ι ρ ρ' B a g₂ (c • Z) Z' = c • pairFun ι ρ ρ' B a g₂ Z Z' := by
  obtain ⟨c₁, v₁, p₁⟩ := mem_parabolicCochains.mp h
  obtain ⟨_, v', p'⟩ := mem_parabolicCochains.mp h'
  rw [pairFun_eq ι ρ ρ' B a g₂ hinv (Z := c • Z) (isCocycle_smul c₁ c) (isPrimitive_smul p₁ c) p',
    pairFun_eq ι ρ ρ' B a g₂ hinv c₁ p₁ p', map_smul, LinearMap.smul_apply]

/-- The cup pairing is additive in the second variable. -/
theorem pairFun_add_right (ι : N →* Γ) (ρ : Representation ℂ Γ V) (ρ' : Representation ℂ Γ W)
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (a g₂ : N)
    (hinv : ∀ n v w, B (ρ (ι n) v) (ρ' (ι n) w) = B v w) {Z : Γ → V} {Z₁' Z₂' : Γ → W}
    (h : Z ∈ parabolicCochains ι ρ a g₂) (h₁ : Z₁' ∈ parabolicCochains ι ρ' a g₂)
    (h₂ : Z₂' ∈ parabolicCochains ι ρ' a g₂) :
    pairFun ι ρ ρ' B a g₂ Z (Z₁' + Z₂') =
      pairFun ι ρ ρ' B a g₂ Z Z₁' + pairFun ι ρ ρ' B a g₂ Z Z₂' := by
  obtain ⟨c, v, p⟩ := mem_parabolicCochains.mp h
  obtain ⟨_, v₁, p₁⟩ := mem_parabolicCochains.mp h₁
  obtain ⟨_, v₂, p₂⟩ := mem_parabolicCochains.mp h₂
  rw [pairFun_eq ι ρ ρ' B a g₂ hinv (Z' := Z₁' + Z₂') c p (isPrimitive_add p₁ p₂),
    pairFun_eq ι ρ ρ' B a g₂ hinv c p p₁, pairFun_eq ι ρ ρ' B a g₂ hinv c p p₂, map_add]

/-- The cup pairing is homogeneous in the second variable. -/
theorem pairFun_smul_right (ι : N →* Γ) (ρ : Representation ℂ Γ V) (ρ' : Representation ℂ Γ W)
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (a g₂ : N)
    (hinv : ∀ n v w, B (ρ (ι n) v) (ρ' (ι n) w) = B v w) (c : ℂ) {Z : Γ → V} {Z' : Γ → W}
    (h : Z ∈ parabolicCochains ι ρ a g₂) (h' : Z' ∈ parabolicCochains ι ρ' a g₂) :
    pairFun ι ρ ρ' B a g₂ Z (c • Z') = c • pairFun ι ρ ρ' B a g₂ Z Z' := by
  obtain ⟨c₁, v, p⟩ := mem_parabolicCochains.mp h
  obtain ⟨_, v', p'⟩ := mem_parabolicCochains.mp h'
  rw [pairFun_eq ι ρ ρ' B a g₂ hinv (Z' := c • Z') c₁ p (isPrimitive_smul p' c),
    pairFun_eq ι ρ ρ' B a g₂ hinv c₁ p p', map_smul]

/-- **The cup pairing of parabolic crossed homomorphisms**, as a bilinear map. -/
def parPairing (ι : N →* Γ) (ρ : Representation ℂ Γ V) (ρ' : Representation ℂ Γ W)
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (a g₂ : N)
    (hinv : ∀ n v w, B (ρ (ι n) v) (ρ' (ι n) w) = B v w) :
    parabolicCochains ι ρ a g₂ →ₗ[ℂ] parabolicCochains ι ρ' a g₂ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun Z Z' => pairFun ι ρ ρ' B a g₂ Z.1 Z'.1)
    (fun Z₁ Z₂ Z' => pairFun_add_left ι ρ ρ' B a g₂ hinv Z₁.2 Z₂.2 Z'.2)
    (fun c Z Z' => pairFun_smul_left ι ρ ρ' B a g₂ hinv c Z.2 Z'.2)
    (fun Z Z₁' Z₂' => pairFun_add_right ι ρ ρ' B a g₂ hinv Z.2 Z₁'.2 Z₂'.2)
    (fun c Z Z' => pairFun_smul_right ι ρ ρ' B a g₂ hinv c Z.2 Z'.2)

/-- The cup pairing vanishes when the first cochain is a coboundary. -/
theorem pairFun_eq_zero_of_boundary_left (ι : N →* Γ) (ρ : Representation ℂ Γ V)
    (ρ' : Representation ℂ Γ W) (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (a g₂ : N)
    (hinv : ∀ n v w, B (ρ (ι n) v) (ρ' (ι n) w) = B v w) {Z : Γ → V} {Z' : Γ → W}
    (hZ' : Z' ∈ parabolicCochains ι ρ' a g₂) (u : V) (hu : ∀ γ, Z γ = ρ γ u - u) :
    pairFun ι ρ ρ' B a g₂ Z Z' = 0 := by
  have hZe : Z = fun γ => ρ γ u - u := funext hu
  subst hZe
  obtain ⟨hc', v', hv'⟩ := mem_parabolicCochains.mp hZ'
  rw [pairFun_eq ι ρ ρ' B a g₂ hinv (isCocycle_boundary ρ u)
    (isPrimitive_boundary (ρ.comp ι) a g₂ u) hv']
  exact tripleForm_boundary_left (isCocycle_comp hc' ι) hv' u

/-- The cup pairing vanishes when the second cochain is a coboundary. -/
theorem pairFun_eq_zero_of_boundary_right (ι : N →* Γ) (ρ : Representation ℂ Γ V)
    (ρ' : Representation ℂ Γ W) (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (a g₂ : N)
    (hinv : ∀ n v w, B (ρ (ι n) v) (ρ' (ι n) w) = B v w) {Z : Γ → V} {Z' : Γ → W}
    (hZ : Z ∈ parabolicCochains ι ρ a g₂) (u : W) (hu : ∀ γ, Z' γ = ρ' γ u - u) :
    pairFun ι ρ ρ' B a g₂ Z Z' = 0 := by
  have hZe : Z' = fun γ => ρ' γ u - u := funext hu
  subst hZe
  obtain ⟨hc, v, hv⟩ := mem_parabolicCochains.mp hZ
  have hinv' : ∀ (n : N) (x : V) (y : W), B ((ρ.comp ι) n x) ((ρ'.comp ι) n y) = B x y := hinv
  have hcon : constraint (ρ.comp ι) a g₂ v = 0 :=
    LinearMap.mem_ker.1 (hv.mem_tripleCycles (isCocycle_comp hc ι))
  rw [pairFun_eq ι ρ ρ' B a g₂ hinv hc hv (isPrimitive_boundary (ρ'.comp ι) a g₂ u),
    tripleForm_diag' hinv' a g₂ v u, hcon, map_zero, LinearMap.zero_apply]

end Cochains

section Descent

variable {K K' H H' : Type} [AddCommGroup K] [Module ℂ K] [AddCommGroup K'] [Module ℂ K']
  [AddCommGroup H] [Module ℂ H] [AddCommGroup H'] [Module ℂ H']

/-- **Descent of a bilinear form.**  A bilinear form on submodules `P ⊆ K`, `P' ⊆ K'` which vanishes
whenever one of the arguments is killed by `f`, `g` induces a bilinear form on the images. -/
theorem exists_descent (f : K →ₗ[ℂ] H) (g : K' →ₗ[ℂ] H') {P : Submodule ℂ K} {P' : Submodule ℂ K'}
    (β : P →ₗ[ℂ] P' →ₗ[ℂ] ℂ) (hleft : ∀ (x : P) (y : P'), f x.1 = 0 → β x y = 0)
    (hright : ∀ (x : P) (y : P'), g y.1 = 0 → β x y = 0) :
    ∃ β' : P.map f →ₗ[ℂ] P'.map g →ₗ[ℂ] ℂ,
      ∀ (x : P) (y : P') (hx : f x.1 ∈ P.map f) (hy : g y.1 ∈ P'.map g),
        β' ⟨f x.1, hx⟩ ⟨g y.1, hy⟩ = β x y := by
  have s : ∀ c : P.map f, ∃ x : P, f x.1 = c.1 := by
    intro c
    obtain ⟨x, hx, hxc⟩ := Submodule.mem_map.mp c.2
    exact ⟨⟨x, hx⟩, hxc⟩
  have s' : ∀ c : P'.map g, ∃ y : P', g y.1 = c.1 := by
    intro c
    obtain ⟨y, hy, hyc⟩ := Submodule.mem_map.mp c.2
    exact ⟨⟨y, hy⟩, hyc⟩
  choose r hrf using s
  choose r' hrf' using s'
  refine ⟨LinearMap.mk₂ ℂ (fun c c' => β (r c) (r' c')) ?_ ?_ ?_ ?_, ?_⟩
  · intro c₁ c₂ c'
    show β (r (c₁ + c₂)) (r' c') = β (r c₁) (r' c') + β (r c₂) (r' c')
    have hd : f ((r (c₁ + c₂) - r c₁ - r c₂ : P) : K) = 0 := by
      rw [Submodule.coe_sub, Submodule.coe_sub, map_sub, map_sub, hrf, hrf, hrf,
        Submodule.coe_add]
      abel
    have e := hleft _ (r' c') hd
    rw [map_sub, map_sub, LinearMap.sub_apply, LinearMap.sub_apply] at e
    linear_combination e
  · intro a c c'
    show β (r (a • c)) (r' c') = a • β (r c) (r' c')
    have hd : f ((r (a • c) - a • r c : P) : K) = 0 := by
      rw [Submodule.coe_sub, map_sub, Submodule.coe_smul, map_smul, hrf, hrf, Submodule.coe_smul]
      exact sub_self _
    have e := hleft _ (r' c') hd
    rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at e
    rw [smul_eq_mul]
    linear_combination e
  · intro c c₁' c₂'
    show β (r c) (r' (c₁' + c₂')) = β (r c) (r' c₁') + β (r c) (r' c₂')
    have hd : g ((r' (c₁' + c₂') - r' c₁' - r' c₂' : P') : K') = 0 := by
      rw [Submodule.coe_sub, Submodule.coe_sub, map_sub, map_sub, hrf', hrf', hrf',
        Submodule.coe_add]
      abel
    have e := hright (r c) _ hd
    rw [map_sub, map_sub] at e
    linear_combination e
  · intro a c c'
    show β (r c) (r' (a • c')) = a • β (r c) (r' c')
    have hd : g ((r' (a • c') - a • r' c' : P') : K') = 0 := by
      rw [Submodule.coe_sub, map_sub, Submodule.coe_smul, map_smul, hrf', hrf', Submodule.coe_smul]
      exact sub_self _
    have e := hright (r c) _ hd
    rw [map_sub, map_smul, smul_eq_mul] at e
    rw [smul_eq_mul]
    linear_combination e
  · intro x y hx hy
    have h1 : f ((r ⟨f x.1, hx⟩ - x : P) : K) = 0 := by
      rw [Submodule.coe_sub, map_sub, hrf]
      exact sub_self _
    have h2 : g ((r' ⟨g y.1, hy⟩ - y : P') : K') = 0 := by
      rw [Submodule.coe_sub, map_sub, hrf']
      exact sub_self _
    have e1 := hleft _ (r' ⟨g y.1, hy⟩) h1
    have e2 := hright x _ h2
    rw [map_sub, LinearMap.sub_apply] at e1
    rw [map_sub] at e2
    show β (r ⟨f x.1, hx⟩) (r' ⟨g y.1, hy⟩) = β x y
    linear_combination e1 + e2

end Descent

section Model

variable {Γ N V W K K' H H' : Type} [Group Γ] [Group N] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup K] [Module ℂ K] [AddCommGroup K'] [Module ℂ K']
  [AddCommGroup H] [Module ℂ H] [AddCommGroup H'] [Module ℂ H']

/-- The parabolic part of a module `K` of cochains (given by a linear map `c` to the functions
`Γ → V`): the elements whose cochain is parabolic. -/
abbrev parabolicSub (ι : N →* Γ) (ρ : Representation ℂ Γ V) (a g₂ : N) (c : K →ₗ[ℂ] (Γ → V)) :
    Submodule ℂ K :=
  (parabolicCochains ι ρ a g₂).comap c

/-- Membership in the parabolic part, unfolded. -/
theorem mem_parabolicSub {ι : N →* Γ} {ρ : Representation ℂ Γ V} {a g₂ : N}
    {c : K →ₗ[ℂ] (Γ → V)} {x : K} :
    x ∈ parabolicSub ι ρ a g₂ c ↔ c x ∈ parabolicCochains ι ρ a g₂ := Iff.rfl

/-- The cup pairing on the parabolic part of two modules of cochains. -/
def cochainPairing (ι : N →* Γ) (ρ : Representation ℂ Γ V) (ρ' : Representation ℂ Γ W)
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (a g₂ : N)
    (hinv : ∀ n v w, B (ρ (ι n) v) (ρ' (ι n) w) = B v w) (c : K →ₗ[ℂ] (Γ → V))
    (c' : K' →ₗ[ℂ] (Γ → W)) :
    parabolicSub ι ρ a g₂ c →ₗ[ℂ] parabolicSub ι ρ' a g₂ c' →ₗ[ℂ] ℂ :=
  (parPairing ι ρ ρ' B a g₂ hinv).compl₁₂ (c.restrict (fun _ hx => mem_parabolicSub.mp hx))
    (c'.restrict (fun _ hx => mem_parabolicSub.mp hx))

/-- The cup pairing on the parabolic part is the cup pairing of the cochains. -/
theorem cochainPairing_apply (ι : N →* Γ) (ρ : Representation ℂ Γ V) (ρ' : Representation ℂ Γ W)
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (a g₂ : N)
    (hinv : ∀ n v w, B (ρ (ι n) v) (ρ' (ι n) w) = B v w) (c : K →ₗ[ℂ] (Γ → V))
    (c' : K' →ₗ[ℂ] (Γ → W)) (x : parabolicSub ι ρ a g₂ c) (y : parabolicSub ι ρ' a g₂ c') :
    cochainPairing ι ρ ρ' B a g₂ hinv c c' x y = pairFun ι ρ ρ' B a g₂ (c x.1) (c' y.1) := rfl

/-- The cup pairing of two parabolic elements of cochain modules is the cup formula of any
primitive triple of the first one. -/
theorem cochainPairing_eq_cupFormula (ι : N →* Γ) (ρ : Representation ℂ Γ V)
    (ρ' : Representation ℂ Γ W) (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (a g₂ : N)
    (hinv : ∀ n v w, B (ρ (ι n) v) (ρ' (ι n) w) = B v w) (c : K →ₗ[ℂ] (Γ → V))
    (c' : K' →ₗ[ℂ] (Γ → W)) (x : parabolicSub ι ρ a g₂ c) (y : parabolicSub ι ρ' a g₂ c')
    {v : V × V × V} (hv : IsPrimitive (ρ.comp ι) a g₂ (fun n => c x.1 (ι n)) v) :
    cochainPairing ι ρ ρ' B a g₂ hinv c c' x y =
      cupFormula B (ρ'.comp ι) a g₂ (fun n => c x.1 (ι n)) (fun n => c' y.1 (ι n)) v := by
  rw [cochainPairing_apply]
  exact pairFun_eq_cupFormula ι ρ ρ' B a g₂ hinv
    (mem_parabolicCochains.mp (mem_parabolicSub.mp x.2)).1 hv (mem_parabolicSub.mp y.2)

/-- The pairing vanishes if the first argument maps to zero, when the kernel of `f` consists of
coboundaries. -/
theorem cochainPairing_left_vanish (ι : N →* Γ) (ρ : Representation ℂ Γ V)
    (ρ' : Representation ℂ Γ W) (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (a g₂ : N)
    (hinv : ∀ n v w, B (ρ (ι n) v) (ρ' (ι n) w) = B v w) (c : K →ₗ[ℂ] (Γ → V))
    (c' : K' →ₗ[ℂ] (Γ → W)) (f : K →ₗ[ℂ] H)
    (hker : ∀ x, f x = 0 → ∃ u : V, ∀ γ, c x γ = ρ γ u - u)
    (x : parabolicSub ι ρ a g₂ c) (y : parabolicSub ι ρ' a g₂ c') (h : f x.1 = 0) :
    cochainPairing ι ρ ρ' B a g₂ hinv c c' x y = 0 := by
  obtain ⟨u, hu⟩ := hker x.1 h
  rw [cochainPairing_apply]
  exact pairFun_eq_zero_of_boundary_left ι ρ ρ' B a g₂ hinv (mem_parabolicSub.mp y.2) u hu

/-- The pairing vanishes if the second argument maps to zero, when the kernel of `g` consists of
coboundaries. -/
theorem cochainPairing_right_vanish (ι : N →* Γ) (ρ : Representation ℂ Γ V)
    (ρ' : Representation ℂ Γ W) (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (a g₂ : N)
    (hinv : ∀ n v w, B (ρ (ι n) v) (ρ' (ι n) w) = B v w) (c : K →ₗ[ℂ] (Γ → V))
    (c' : K' →ₗ[ℂ] (Γ → W)) (g : K' →ₗ[ℂ] H')
    (hker' : ∀ y, g y = 0 → ∃ u : W, ∀ γ, c' y γ = ρ' γ u - u)
    (x : parabolicSub ι ρ a g₂ c) (y : parabolicSub ι ρ' a g₂ c') (h : g y.1 = 0) :
    cochainPairing ι ρ ρ' B a g₂ hinv c c' x y = 0 := by
  obtain ⟨u, hu⟩ := hker' y.1 h
  rw [cochainPairing_apply]
  exact pairFun_eq_zero_of_boundary_right ι ρ ρ' B a g₂ hinv (mem_parabolicSub.mp x.2) u hu

/-- The parabolic classes: the image of the parabolic part under `f`. -/
abbrev parabolicClasses (ι : N →* Γ) (ρ : Representation ℂ Γ V) (a g₂ : N)
    (c : K →ₗ[ℂ] (Γ → V)) (f : K →ₗ[ℂ] H) : Submodule ℂ H :=
  (parabolicSub ι ρ a g₂ c).map f

/-- **The cup pairing on parabolic classes** of a cohomology model `f : K → H` of the crossed
homomorphisms `c : K → (Γ → V)` modulo coboundaries. -/
def classPairing (ι : N →* Γ) (ρ : Representation ℂ Γ V) (ρ' : Representation ℂ Γ W)
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (a g₂ : N)
    (hinv : ∀ n v w, B (ρ (ι n) v) (ρ' (ι n) w) = B v w) (c : K →ₗ[ℂ] (Γ → V))
    (c' : K' →ₗ[ℂ] (Γ → W)) (f : K →ₗ[ℂ] H) (g : K' →ₗ[ℂ] H')
    (hker : ∀ x, f x = 0 → ∃ u : V, ∀ γ, c x γ = ρ γ u - u)
    (hker' : ∀ y, g y = 0 → ∃ u : W, ∀ γ, c' y γ = ρ' γ u - u) :
    parabolicClasses ι ρ a g₂ c f →ₗ[ℂ] parabolicClasses ι ρ' a g₂ c' g →ₗ[ℂ] ℂ :=
  Classical.choose (exists_descent f g (cochainPairing ι ρ ρ' B a g₂ hinv c c')
    (fun x y h => cochainPairing_left_vanish ι ρ ρ' B a g₂ hinv c c' f hker x y h)
    (fun x y h => cochainPairing_right_vanish ι ρ ρ' B a g₂ hinv c c' g hker' x y h))

/-- **The value of the class pairing on representatives.** -/
theorem classPairing_apply (ι : N →* Γ) (ρ : Representation ℂ Γ V) (ρ' : Representation ℂ Γ W)
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (a g₂ : N)
    (hinv : ∀ n v w, B (ρ (ι n) v) (ρ' (ι n) w) = B v w) (c : K →ₗ[ℂ] (Γ → V))
    (c' : K' →ₗ[ℂ] (Γ → W)) (f : K →ₗ[ℂ] H) (g : K' →ₗ[ℂ] H')
    (hker : ∀ x, f x = 0 → ∃ u : V, ∀ γ, c x γ = ρ γ u - u)
    (hker' : ∀ y, g y = 0 → ∃ u : W, ∀ γ, c' y γ = ρ' γ u - u)
    (x : parabolicSub ι ρ a g₂ c) (y : parabolicSub ι ρ' a g₂ c')
    (hx : f x.1 ∈ parabolicClasses ι ρ a g₂ c f) (hy : g y.1 ∈ parabolicClasses ι ρ' a g₂ c' g) :
    classPairing ι ρ ρ' B a g₂ hinv c c' f g hker hker' ⟨f x.1, hx⟩ ⟨g y.1, hy⟩ =
      pairFun ι ρ ρ' B a g₂ (c x.1) (c' y.1) :=
  (Classical.choose_spec (exists_descent f g (cochainPairing ι ρ ρ' B a g₂ hinv c c')
    (fun x y h => cochainPairing_left_vanish ι ρ ρ' B a g₂ hinv c c' f hker x y h)
    (fun x y h => cochainPairing_right_vanish ι ρ ρ' B a g₂ hinv c c' g hker' x y h)) x y hx hy).trans
    (cochainPairing_apply ι ρ ρ' B a g₂ hinv c c' x y)

/-- **The class pairing is the cup formula of any primitive triple of a representative.** -/
theorem classPairing_eq_cupFormula (ι : N →* Γ) (ρ : Representation ℂ Γ V)
    (ρ' : Representation ℂ Γ W) (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (a g₂ : N)
    (hinv : ∀ n v w, B (ρ (ι n) v) (ρ' (ι n) w) = B v w) (c : K →ₗ[ℂ] (Γ → V))
    (c' : K' →ₗ[ℂ] (Γ → W)) (f : K →ₗ[ℂ] H) (g : K' →ₗ[ℂ] H')
    (hker : ∀ x, f x = 0 → ∃ u : V, ∀ γ, c x γ = ρ γ u - u)
    (hker' : ∀ y, g y = 0 → ∃ u : W, ∀ γ, c' y γ = ρ' γ u - u)
    (x : parabolicSub ι ρ a g₂ c) (y : parabolicSub ι ρ' a g₂ c')
    (hx : f x.1 ∈ parabolicClasses ι ρ a g₂ c f) (hy : g y.1 ∈ parabolicClasses ι ρ' a g₂ c' g)
    {v : V × V × V} (hv : IsPrimitive (ρ.comp ι) a g₂ (fun n => c x.1 (ι n)) v) :
    classPairing ι ρ ρ' B a g₂ hinv c c' f g hker hker' ⟨f x.1, hx⟩ ⟨g y.1, hy⟩ =
      cupFormula B (ρ'.comp ι) a g₂ (fun n => c x.1 (ι n)) (fun n => c' y.1 (ι n)) v :=
  (classPairing_apply ι ρ ρ' B a g₂ hinv c c' f g hker hker' x y hx hy).trans
    ((cochainPairing_apply ι ρ ρ' B a g₂ hinv c c' x y).symm.trans
      (cochainPairing_eq_cupFormula ι ρ ρ' B a g₂ hinv c c' x y hv))

/-- Left nondegeneracy of the cup pairing on the parabolic crossed homomorphisms: a parabolic
crossed homomorphism whose pairing with every parabolic crossed homomorphism vanishes is a
coboundary. -/
def CochainNondegenerate (ι : N →* Γ) (ρ : Representation ℂ Γ V) (ρ' : Representation ℂ Γ W)
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (a g₂ : N) : Prop :=
  ∀ Z ∈ parabolicCochains ι ρ a g₂,
    (∀ Z' ∈ parabolicCochains ι ρ' a g₂, pairFun ι ρ ρ' B a g₂ Z Z' = 0) →
      ∃ u : V, ∀ γ, Z γ = ρ γ u - u

/-- **Left nondegeneracy on parabolic classes.**  A parabolic class which pairs to zero with every
parabolic class is zero, provided left nondegeneracy holds for the crossed homomorphisms, the kernel
of `f` is exactly the coboundaries, and every crossed homomorphism of the second system comes from
`K'`. -/
theorem classPairing_left_nondegenerate (ι : N →* Γ) (ρ : Representation ℂ Γ V)
    (ρ' : Representation ℂ Γ W) (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (a g₂ : N)
    (hinv : ∀ n v w, B (ρ (ι n) v) (ρ' (ι n) w) = B v w) (c : K →ₗ[ℂ] (Γ → V))
    (c' : K' →ₗ[ℂ] (Γ → W)) (f : K →ₗ[ℂ] H) (g : K' →ₗ[ℂ] H')
    (hker : ∀ x, f x = 0 ↔ ∃ u : V, ∀ γ, c x γ = ρ γ u - u)
    (hker' : ∀ y, g y = 0 → ∃ u : W, ∀ γ, c' y γ = ρ' γ u - u)
    (hsurj' : ∀ Z' : Γ → W, IsCocycle ρ' Z' → ∃ y, c' y = Z')
    (hnd : CochainNondegenerate ι ρ ρ' B a g₂)
    (cl : parabolicClasses ι ρ a g₂ c f)
    (h : ∀ cl' : parabolicClasses ι ρ' a g₂ c' g,
      classPairing ι ρ ρ' B a g₂ hinv c c' f g (fun x hx => (hker x).1 hx) hker' cl cl' = 0) :
    cl = 0 := by
  obtain ⟨x, hx, hxc⟩ := Submodule.mem_map.mp cl.2
  have hcl : cl = ⟨f x, Submodule.mem_map_of_mem hx⟩ := Subtype.ext hxc.symm
  have hf0 : f x = 0 := by
    refine (hker x).2 (hnd (c x) (mem_parabolicSub.mp hx) ?_)
    intro Z' hZ'
    obtain ⟨y, hy⟩ := hsurj' Z' (mem_parabolicCochains.mp hZ').1
    have hym : y ∈ parabolicSub ι ρ' a g₂ c' := by
      rw [mem_parabolicSub, hy]
      exact hZ'
    have h1 := h ⟨g y, Submodule.mem_map_of_mem hym⟩
    have e := classPairing_apply ι ρ ρ' B a g₂ hinv c c' f g (fun x hx => (hker x).1 hx) hker'
      ⟨x, hx⟩ ⟨y, hym⟩ (Submodule.mem_map_of_mem hx) (Submodule.mem_map_of_mem hym)
    rw [hcl] at h1
    rw [← hy]
    exact e.symm.trans h1
  apply Subtype.ext
  rw [← hxc]
  exact hf0

end Model

end TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality
