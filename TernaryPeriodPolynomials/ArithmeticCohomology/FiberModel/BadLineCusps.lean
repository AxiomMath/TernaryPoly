module

public import Mathlib
public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.Gamma2Presentation
public import Batteries.Data.MLList.Basic
public import Batteries.Lean.LawfulMonadLift
public import Batteries.Lean.Meta.Simp
public import Batteries.Recycling.MonadSatisfying.Lean
public import Batteries.Util.Pickle

@[expose] public section


/-!
# The binary quotient and its cusps: the literal argument of the paper

Proof of
`lem:bad-line-coordinate`, the passages "The binary quotient and its cusps":

* "Transport to `(a,b)=(-Y,Z-2Y)` ... The actions become `𝒜(a,b)=(-b,a-b)`, `ℬ(a,b)=(-a,b-a)`,
  `ℛ(a,b)=(-a,b-4a)`. The positive cocycle `𝒥(φ_l)` has values `Ĵ,0,0` on `A₀,B₀,R₀`. Their
  finite-group relations give `(1+𝒜+𝒜²)Ĵ=0` and `Ĵ(a,b)=-Ĵ(b,a)`. For `u=(2Ĵ+𝒜Ĵ)/3`, one has
  `(1-𝒜)u=Ĵ` and `ℬu=u`."  (`PositiveCocycle.relations`, `BadLineRelations.hat_cube`,
  `hat_antisymm`, `hat_primitive`; the coordinate change `hatAlg` and the maps `calA, calB, calR`
  are intertwined with the coefficient action of `A₀, B₀, R₀` by `hat_a0, hat_b0, hat_r0`.)
* "At the lower cusp the translation is `Z ↦ Z - 3Y`, whose degree-`d` coinvariant is the `Z^d`
  coefficient. Its reflection fixes that coefficient and reverses the translation, so its full cusp
  `H¹` vanishes." (`lower_coinvariants`, `lower_invariants`, `PositiveCocycle.lower_reflection_sign`,
  `PositiveCocycle.lower_cusp`.)
* "At the upper cusp the translation is `Y ↦ Y - Z`, with coinvariant the `Y^d` coefficient. The
  reflection acts on `H¹` by `(-1)^{d+1}`. Thus this restriction is automatically zero for even
  `d`." (`upper_coinvariants`, `BadLineRelations.upper_reflection_sign`, `upper_eval_even`.)
* "For odd `d` ... `J_f(Y,3Y)=0`, or `Ĵ(a,-a)=0`. For the upper translation `𝒜²ℬℛ`, its cocycle
  value is `Ĵ+𝒜Ĵ`. On `Z=0`, that is `b=2a`, the cocycle relations give
  `(Ĵ+𝒜Ĵ)(a,2a)=-Ĵ(a,-a)=0`. Both cusp restrictions therefore vanish in every parity."
  (`BadLineRelations.upper_eval_of_J3`, `upper_cusp`, `PositiveCocycle.cusp_restrictions_vanish`.)
* "Detection of the polynomial. Suppose `j_F=0`. Write the positive cocycle as `(1-l)m`. Its zero
  values at `B₀,R₀` make `m` invariant under their product `U₀`, hence `m=cY^d`. For odd `d` the
  reflection makes `c=0`. For even `d`, its `A₀` value is `J_f(Y,Z)=c(Y^d-(-2Y+Z)^d)`. But
  `J_f(0,Z)=0` by the opposite-pair vanishing. Thus `c=0` here as well." (`detection`.)

Scope. The group is `Γ₂ = ` `Gamma2` acting on `K[Y,Z]` by `P(v) ↦ P(g⁻¹ v)`
(`J(v) ↦ J(L⁻¹ v)`), `K` a field of characteristic zero.

* "The restriction to a cusp stabilizer `⟨T, R⟩` vanishes" is formalized as: the restriction of the
  cocycle to the subgroup is a coboundary, `∃ m, ∀ s ∈ S, c s = m - s m` (the vanishing of its
  class in `H¹(S, V)`, in the shape of Mathlib's `groupCohomology.IsCoboundary₁`).  The
  Hochschild-Serre step "translation coinvariants, then reflection invariants" is proved directly
  for the infinite dihedral stabilizers (`IsCocycle.dihedral_iff`: averaging over `⟨R⟩`), so that
  `lower_cusp_H1_vanishes`, `upper_cusp_restriction_iff`, `upper_cusp_H1_vanishes_of_even` and
  `PositiveCocycle.cusp_H1_restrictions_vanish` are statements about the actual stabilizers
  `cuspStabLower = ⟨U₀, R₀⟩` and `cuspStabUpper = ⟨T, R₀⟩`; `upper_class_sign` is the reflection
  sign `(-1)^{d+1}` for an arbitrary cocycle valued in the degree-`d` forms.
* The inputs `J_f(Y,3Y) = 0` (odd `d`) and `J_f(0,Z) = 0` are hypotheses here; they are proved from
  `lem:sym-boundary-factors` in `SymBoundaryFactors`/`BadLineCuspsWiring`.

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FiberModel.BadLineCusps

variable {K : Type*} [Field K]

/-! ### Section 1: translation coinvariants on binary forms -/


def shearZ (k : K) : MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 2) K :=
  bind₁ ![X 0, X 1 - C k * X 0]

theorem eval_shearZ (k : K) (P : MvPolynomial (Fin 2) K) (y z : K) :
    eval ![y, z] (shearZ k P) = eval ![y, z - k * y] P := by
  unfold shearZ
  have := eval₂Hom_bind₁ (RingHom.id K) ![y, z] ![X 0, X 1 - C k * X 0] P
  change eval ![y, z] _ = _ at this ⊢
  rw [this]
  have hc : (fun i => (eval₂Hom (RingHom.id K) ![y, z]) (![X 0, X 1 - C k * X 0] i)) =
      ![y, z - k * y] := by
    funext i; fin_cases i <;> simp
  rw [hc]; rfl

theorem shearZ_homog (k : K) {d : ℕ} {P : MvPolynomial (Fin 2) K} (hP : P.IsHomogeneous d) :
    (shearZ k P).IsHomogeneous d := by
  have := hP.aeval (n := 1) (![X (0 : Fin 2), X 1 - C k * X 0] : Fin 2 → MvPolynomial (Fin 2) K)
    (fun i => by
      fin_cases i
      · simpa using isHomogeneous_X K (0 : Fin 2)
      · simpa using (isHomogeneous_X K (1 : Fin 2)).sub ((isHomogeneous_X K (0 : Fin 2)).C_mul k))
  simpa [shearZ, one_mul] using this

theorem eval_smul_homog {d : ℕ} {P : MvPolynomial (Fin 2) K}
    (hP : P.IsHomogeneous d) (t : K) (v : Fin 2 → K) :
    eval (t • v) P = t ^ d * eval v P := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hd : ∑ i, s i = d := by
    have := hP (mem_support_iff.mp hs)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hd]
  ring

/-- A homogeneous binary form vanishing on the line `Y = 1` is zero. -/
theorem homog_eq_zero_of_eval_one [Infinite K] {d : ℕ} {Q : MvPolynomial (Fin 2) K}
    (hQ : Q.IsHomogeneous d) (h : ∀ z, eval ![1, z] Q = 0) : Q = 0 := by
  have hXQ : X 0 * Q = 0 := by
    apply MvPolynomial.funext
    intro v
    by_cases hy : v 0 = 0
    · simp [hy]
    · have hv : v = (v 0) • ![1, v 1 / v 0] := by
        funext i; fin_cases i
        · simp
        · simp; field_simp
      rw [map_mul, hv, eval_smul_homog hQ, h]; simp
  rcases mul_eq_zero.mp hXQ with h0 | h0
  · exact absurd h0 (X_ne_zero 0)
  · exact h0

theorem eval_pow_X0 (d : ℕ) (y z : K) : eval ![y, z] ((X 0 : MvPolynomial (Fin 2) K) ^ d) = y ^ d := by
  simp

/-- A homogeneous binary form with `P(Y, Z - kY) = P(Y, Z)` is a multiple of `Y^d`. -/
theorem shearZ_ker [CharZero K] {k : K} (hk : k ≠ 0) {d : ℕ} {P : MvPolynomial (Fin 2) K}
    (hP : P.IsHomogeneous d) (h : shearZ k P = P) :
    ∃ c : K, P = C c * X 0 ^ d := by
  have hq : ∀ z, eval ![1, z - k] P = eval ![1, z] P := by
    intro z
    have := eval_shearZ k P 1 z
    rw [h] at this
    simpa using this.symm
  let g : Fin 2 → Polynomial K := ![1, Polynomial.X]
  let p : Polynomial K := MvPolynomial.aeval g P
  have hp : ∀ z, p.eval z = eval ![1, z] P := by
    intro z
    have : (Polynomial.aeval z).comp (MvPolynomial.aeval g) =
        MvPolynomial.aeval (fun i => Polynomial.aeval z (g i)) := by
      apply MvPolynomial.algHom_ext
      intro i; simp
    have h2 := congrArg (fun F => F P) this
    simp only [AlgHom.comp_apply] at h2
    have h3 : (fun i => Polynomial.aeval z (g i)) = ![1, z] := by
      funext i; fin_cases i <;> simp [g]
    rw [h3] at h2
    simpa [p, Polynomial.aeval_def, Polynomial.eval₂_id] using h2
  let r : Polynomial K := p - Polynomial.C (p.eval 0)
  have hr : ∀ n : ℕ, r.IsRoot ((n : K) * k) := by
    intro n
    induction n with
    | zero => simp [r, Polynomial.IsRoot]
    | succ n ih =>
      have e := hq (((n + 1 : ℕ) : K) * k)
      have e2 : (((n + 1 : ℕ) : K) * k) - k = (n : K) * k := by push_cast; ring
      rw [e2] at e
      have ih' : p.eval ((n : K) * k) = p.eval 0 := by
        simpa [r, Polynomial.IsRoot, sub_eq_zero] using ih
      have hs : p.eval (((n + 1 : ℕ) : K) * k) = p.eval 0 := by
        rw [hp, ← e, ← hp, ih']
      simpa [r, Polynomial.IsRoot, sub_eq_zero] using hs
  have hinf : {x : K | r.IsRoot x}.Infinite := by
    refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (n : K) * k) ?_ hr
    intro a b hab
    have := mul_right_cancel₀ hk hab
    exact_mod_cast this
  have hr0 : r = 0 := Polynomial.eq_zero_of_infinite_isRoot r hinf
  have hconst : ∀ z, eval ![1, z] P = p.eval 0 := by
    intro z
    have := congrArg (Polynomial.eval z) hr0
    simpa [r, hp, sub_eq_zero] using this
  refine ⟨p.eval 0, ?_⟩
  have hQ : (P - C (p.eval 0) * X 0 ^ d).IsHomogeneous d := by
    refine hP.sub ?_
    simpa using isHomogeneous_C_mul_X_pow (p.eval 0) (0 : Fin 2) d
  have := homog_eq_zero_of_eval_one hQ (fun z => by simp [hconst])
  exact sub_eq_zero.mp this

theorem shearZ_X0_pow (k : K) (d : ℕ) : shearZ k ((X 0 : MvPolynomial (Fin 2) K) ^ d) = X 0 ^ d := by
  simp [shearZ]

instance finiteHom (d : ℕ) : FiniteDimensional K (homogeneousSubmodule (Fin 2) K d) :=
  Module.Finite.of_fg (homogeneousSubmodule_fg (Fin 2) K d)

/-- Over a field of characteristic zero, a homogeneous form vanishing at `(0, 1)` is a
translation difference `Q - Q(Y, Z - kY)` of a homogeneous form. -/
theorem shearZ_range [CharZero K] {k : K} (hk : k ≠ 0) {d : ℕ} {P : MvPolynomial (Fin 2) K}
    (hP : P.IsHomogeneous d) (h0 : eval ![0, 1] P = 0) :
    ∃ Q : MvPolynomial (Fin 2) K, Q.IsHomogeneous d ∧ P = Q - shearZ k Q := by
  let V := homogeneousSubmodule (Fin 2) K d
  have hV : ∀ x ∈ V, shearZ k x ∈ V := fun x hx =>
    (mem_homogeneousSubmodule d _).mpr (shearZ_homog k ((mem_homogeneousSubmodule d x).mp hx))
  let S : V →ₗ[K] V := (shearZ k).toLinearMap.restrict hV
  let D : V →ₗ[K] V := LinearMap.id - S
  let ev : V →ₗ[K] K := (MvPolynomial.aeval (R := K) (S₁ := K) ![0, 1]).toLinearMap ∘ₗ V.subtype
  have hev : ∀ x : V, ev x = eval ![0, 1] (x : MvPolynomial (Fin 2) K) := fun x => rfl
  have hSx : ∀ x : V, ((S x : V) : MvPolynomial (Fin 2) K) = shearZ k x := fun x => rfl
  have hrange : LinearMap.range D ≤ LinearMap.ker ev := by
    rintro _ ⟨x, rfl⟩
    simp only [LinearMap.mem_ker, D, LinearMap.sub_apply, LinearMap.id_apply, hev]
    have := eval_shearZ k (x : MvPolynomial (Fin 2) K) 0 1
    simp only [mul_zero, sub_zero] at this
    rw [Submodule.coe_sub, map_sub, hSx, this, sub_self]
  have hX0V : (X 0 : MvPolynomial (Fin 2) K) ^ d ∈ V :=
    (mem_homogeneousSubmodule d _).mpr (by simpa using isHomogeneous_C_mul_X_pow (1 : K) (0 : Fin 2) d)
  have hX1V : (X 1 : MvPolynomial (Fin 2) K) ^ d ∈ V :=
    (mem_homogeneousSubmodule d _).mpr (by simpa using isHomogeneous_C_mul_X_pow (1 : K) (1 : Fin 2) d)
  have hkerD : LinearMap.ker D = Submodule.span K {(⟨_, hX0V⟩ : V)} := by
    apply le_antisymm
    · intro x hx
      have hx' : shearZ k (x : MvPolynomial (Fin 2) K) = x := by
        have : D x = 0 := hx
        have h2 : ((D x : V) : MvPolynomial (Fin 2) K) = 0 := by rw [this]; rfl
        simp only [D, LinearMap.sub_apply, LinearMap.id_apply, Submodule.coe_sub, hSx] at h2
        exact (sub_eq_zero.mp h2).symm
      obtain ⟨c, hc⟩ := shearZ_ker hk ((mem_homogeneousSubmodule d _).mp x.2) hx'
      refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
      apply Subtype.ext
      simp [hc, smul_eq_C_mul]
    · rw [Submodule.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      show D _ = 0
      apply Subtype.ext
      simp only [D, LinearMap.sub_apply, LinearMap.id_apply, Submodule.coe_sub, hSx, shearZ_X0_pow]
      simp
  have hX0ne : (⟨_, hX0V⟩ : V) ≠ 0 := by
    intro h
    have := congrArg Subtype.val h
    simp at this
  have hfr1 : Module.finrank K (LinearMap.ker D) = 1 := by
    rw [hkerD]; exact finrank_span_singleton hX0ne
  have hD := LinearMap.finrank_range_add_finrank_ker D
  have hevsurj : LinearMap.range ev = ⊤ := by
    rw [eq_top_iff]
    intro c _
    refine ⟨c • (⟨_, hX1V⟩ : V), ?_⟩
    rw [map_smul, hev]
    simp
  have hE := LinearMap.finrank_range_add_finrank_ker ev
  rw [hevsurj, finrank_top, Module.finrank_self] at hE
  have heq : LinearMap.range D = LinearMap.ker ev := by
    apply Submodule.eq_of_le_of_finrank_eq hrange
    omega
  have hmem : (⟨P, (mem_homogeneousSubmodule d _).mpr hP⟩ : V) ∈ LinearMap.range D := by
    rw [heq]; exact h0
  obtain ⟨y, hy⟩ := hmem
  refine ⟨y, (mem_homogeneousSubmodule d _).mp y.2, ?_⟩
  have := congrArg Subtype.val hy
  simp only [D, LinearMap.sub_apply, LinearMap.id_apply, Submodule.coe_sub, hSx] at this
  exact this.symm

/-! ### Section 2: swap, reflection, evaluation functionals -/

/-- The coordinate swap `P(Y, Z) ↦ P(Z, Y)`. -/
def swapAlg : MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 2) K := bind₁ ![X 1, X 0]

/-- The reflection substitution `P(Y, Z) ↦ P(-Y, Z)`. -/
def reflAlg : MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 2) K := bind₁ ![-X 0, X 1]

/-- The upper translation `P(Y, Z) ↦ P(Y - Z, Z)`. -/
def shearY : MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 2) K := bind₁ ![X 0 - X 1, X 1]

theorem eval_bind₁_two (f : Fin 2 → MvPolynomial (Fin 2) K) (P : MvPolynomial (Fin 2) K)
    (v : Fin 2 → K) :
    eval v (bind₁ f P) = eval (fun i => eval v (f i)) P := by
  have := eval₂Hom_bind₁ (RingHom.id K) v f P
  exact this

theorem eval_vec_congr {u w : Fin 2 → K} (h0 : u 0 = w 0) (h1 : u 1 = w 1)
    (P : MvPolynomial (Fin 2) K) : eval u P = eval w P := by
  have : u = w := by funext i; fin_cases i <;> assumption
  rw [this]

theorem eval_bind₁_vec (a b P : MvPolynomial (Fin 2) K) (v : Fin 2 → K) :
    eval v (bind₁ ![a, b] P) = eval ![eval v a, eval v b] P := by
  rw [eval_bind₁_two]
  have hc : (fun i => eval v ((![a, b] : Fin 2 → MvPolynomial (Fin 2) K) i)) =
      ![eval v a, eval v b] := by
    funext i; fin_cases i <;> rfl
  rw [hc]

theorem eval_swapAlg (P : MvPolynomial (Fin 2) K) (y z : K) :
    eval ![y, z] (swapAlg P) = eval ![z, y] P := by
  unfold swapAlg
  rw [eval_bind₁_vec]
  simp

theorem eval_reflAlg (P : MvPolynomial (Fin 2) K) (y z : K) :
    eval ![y, z] (reflAlg P) = eval ![-y, z] P := by
  unfold reflAlg
  rw [eval_bind₁_vec]
  simp

theorem eval_shearY (P : MvPolynomial (Fin 2) K) (y z : K) :
    eval ![y, z] (shearY P) = eval ![y - z, z] P := by
  unfold shearY
  rw [eval_bind₁_vec]
  simp

theorem swapAlg_swapAlg [CharZero K] (P : MvPolynomial (Fin 2) K) : swapAlg (swapAlg P) = P := by
  have := CharZero.infinite K
  apply MvPolynomial.funext
  intro v
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hv, eval_swapAlg, eval_swapAlg]

theorem swapAlg_homog {d : ℕ} {P : MvPolynomial (Fin 2) K} (hP : P.IsHomogeneous d) :
    (swapAlg P).IsHomogeneous d := by
  have := hP.aeval (n := 1) (![X (1 : Fin 2), X 0] : Fin 2 → MvPolynomial (Fin 2) K)
    (fun i => by fin_cases i <;> simpa using isHomogeneous_X K _)
  simpa [swapAlg, one_mul] using this

theorem shearY_homog {d : ℕ} {P : MvPolynomial (Fin 2) K} (hP : P.IsHomogeneous d) :
    (shearY P).IsHomogeneous d := by
  have := hP.aeval (n := 1) (![X (0 : Fin 2) - X 1, X 1] : Fin 2 → MvPolynomial (Fin 2) K)
    (fun i => by
      fin_cases i
      · simpa using (isHomogeneous_X K (0 : Fin 2)).sub (isHomogeneous_X K (1 : Fin 2))
      · simpa using isHomogeneous_X K (1 : Fin 2))
  simpa [shearY, one_mul] using this

theorem reflAlg_homog {d : ℕ} {P : MvPolynomial (Fin 2) K} (hP : P.IsHomogeneous d) :
    (reflAlg P).IsHomogeneous d := by
  have := hP.aeval (n := 1) (![-X (0 : Fin 2), X 1] : Fin 2 → MvPolynomial (Fin 2) K)
    (fun i => by
      fin_cases i
      · simpa using (isHomogeneous_X K (0 : Fin 2)).neg
      · simpa using isHomogeneous_X K (1 : Fin 2))
  simpa [reflAlg, one_mul] using this

/-- `shearY = swap ∘ shearZ 1 ∘ swap`. -/
theorem shearY_eq [CharZero K] (P : MvPolynomial (Fin 2) K) :
    shearY P = swapAlg (shearZ 1 (swapAlg P)) := by
  have := CharZero.infinite K
  apply MvPolynomial.funext
  intro v
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hv, eval_shearY, eval_swapAlg, eval_shearZ, eval_swapAlg]
  simp

/-- On a homogeneous form of degree `d`, the value at `(1,0)` is the coefficient of `Y^d`. -/
theorem eval10_eq_coeff {d : ℕ} {P : MvPolynomial (Fin 2) K} (hP : P.IsHomogeneous d) :
    eval ![1, 0] P = P.coeff (Finsupp.single 0 d) := by
  rw [eval_eq']
  rw [Finset.sum_eq_single (Finsupp.single 0 d)]
  · simp [Fin.prod_univ_two]
  · intro s hs hne
    have hd : ∑ i, s i = d := by
      have := hP (mem_support_iff.mp hs)
      simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
    have : s 1 ≠ 0 := by
      intro h1
      apply hne
      ext i
      fin_cases i
      · simp; simpa [Fin.sum_univ_two, h1] using hd
      · simp [h1]
    simp [Fin.prod_univ_two, this]
  · intro h
    rw [notMem_support_iff.mp h]; simp

/-- On a homogeneous form of degree `d`, the value at `(0,1)` is the coefficient of `Z^d`. -/
theorem eval01_eq_coeff {d : ℕ} {P : MvPolynomial (Fin 2) K} (hP : P.IsHomogeneous d) :
    eval ![0, 1] P = P.coeff (Finsupp.single 1 d) := by
  rw [eval_eq']
  rw [Finset.sum_eq_single (Finsupp.single 1 d)]
  · simp [Fin.prod_univ_two]
  · intro s hs hne
    have hd : ∑ i, s i = d := by
      have := hP (mem_support_iff.mp hs)
      simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
    have : s 0 ≠ 0 := by
      intro h0
      apply hne
      ext i
      fin_cases i
      · simp [h0]
      · simp; simpa [Fin.sum_univ_two, h0] using hd
    simp [Fin.prod_univ_two, this]
  · intro h
    rw [notMem_support_iff.mp h]; simp

/-- The value at `(1,0)` is `(-1)^d` times the value at `(-1,0)`: the reflection acts on the
`Y^d` coefficient by `(-1)^d`. -/
theorem eval10_reflAlg {d : ℕ} {P : MvPolynomial (Fin 2) K} (hP : P.IsHomogeneous d) :
    eval ![1, 0] (reflAlg P) = (-1) ^ d * eval ![1, 0] P := by
  rw [eval_reflAlg]
  have := eval_smul_homog hP (-1) ![1, 0]
  have hv : (-1 : K) • (![1, 0] : Fin 2 → K) = ![-1, 0] := by
    funext i; fin_cases i <;> simp
  rw [hv] at this
  exact this

theorem eval01_reflAlg (P : MvPolynomial (Fin 2) K) :
    eval ![0, 1] (reflAlg P) = eval ![0, 1] P := by
  rw [eval_reflAlg]; simp

theorem eval01_shearZ (k : K) (P : MvPolynomial (Fin 2) K) :
    eval ![0, 1] (shearZ k P) = eval ![0, 1] P := by
  rw [eval_shearZ]; simp

theorem eval10_shearY (P : MvPolynomial (Fin 2) K) :
    eval ![1, 0] (shearY P) = eval ![1, 0] P := by
  rw [eval_shearY]; simp

/-- Upper analogue of `shearZ_range`: a homogeneous form vanishing at `(1,0)` is a difference
`Q - Q(Y - Z, Z)`. -/
theorem shearY_range [CharZero K] {d : ℕ} {P : MvPolynomial (Fin 2) K}
    (hP : P.IsHomogeneous d) (h0 : eval ![1, 0] P = 0) :
    ∃ Q : MvPolynomial (Fin 2) K, Q.IsHomogeneous d ∧ P = Q - shearY Q := by
  have hP' := swapAlg_homog hP
  have h0' : eval ![0, 1] (swapAlg P) = 0 := by rw [eval_swapAlg]; exact h0
  obtain ⟨Q', hQ', hPQ⟩ := shearZ_range (one_ne_zero : (1 : K) ≠ 0) hP' h0'
  refine ⟨swapAlg Q', swapAlg_homog hQ', ?_⟩
  rw [shearY_eq, swapAlg_swapAlg]
  have := congrArg swapAlg hPQ
  rw [swapAlg_swapAlg, map_sub] at this
  exact this


/-! ### Section 3: the coefficient action of `GL₂(ℤ)` on `K[Y,Z]` -/

/-- The substitution `P(v) ↦ P(g⁻¹ v)` for `g ∈ GL₂(ℤ)` (the coefficient action on the radical
coordinate, `J(v) ↦ J(L⁻¹ v)`). -/
def actAlg (K : Type*) [Field K] (g : GL2Z) : MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 2) K :=
  bind₁ ![C (((g⁻¹ : GL2Z).val 0 0 : ℤ) : K) * X 0 + C (((g⁻¹ : GL2Z).val 0 1 : ℤ) : K) * X 1,
    C (((g⁻¹ : GL2Z).val 1 0 : ℤ) : K) * X 0 + C (((g⁻¹ : GL2Z).val 1 1 : ℤ) : K) * X 1]

theorem eval_actAlg (g : GL2Z) (P : MvPolynomial (Fin 2) K) (v : Fin 2 → K) :
    eval v (actAlg K g P) =
      eval ![(((g⁻¹ : GL2Z).val 0 0 : ℤ) : K) * v 0 + (((g⁻¹ : GL2Z).val 0 1 : ℤ) : K) * v 1,
        (((g⁻¹ : GL2Z).val 1 0 : ℤ) : K) * v 0 + (((g⁻¹ : GL2Z).val 1 1 : ℤ) : K) * v 1] P := by
  unfold actAlg
  rw [eval_bind₁_vec]
  simp

theorem actAlg_homog (g : GL2Z) {d : ℕ} {P : MvPolynomial (Fin 2) K} (hP : P.IsHomogeneous d) :
    (actAlg K g P).IsHomogeneous d := by
  have := hP.aeval (n := 1)
    (![C (((g⁻¹ : GL2Z).val 0 0 : ℤ) : K) * X 0 + C (((g⁻¹ : GL2Z).val 0 1 : ℤ) : K) * X 1,
    C (((g⁻¹ : GL2Z).val 1 0 : ℤ) : K) * X 0 + C (((g⁻¹ : GL2Z).val 1 1 : ℤ) : K) * X 1] :
      Fin 2 → MvPolynomial (Fin 2) K)
    (fun i => by
      fin_cases i
      · exact ((isHomogeneous_X K (0 : Fin 2)).C_mul _).add ((isHomogeneous_X K (1 : Fin 2)).C_mul _)
      · exact ((isHomogeneous_X K (0 : Fin 2)).C_mul _).add ((isHomogeneous_X K (1 : Fin 2)).C_mul _))
  simpa [actAlg, one_mul] using this

theorem actAlg_one : actAlg K 1 = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro i; fin_cases i <;> simp [actAlg]

theorem actAlg_mul (g h : GL2Z) : actAlg K (g * h) = (actAlg K g).comp (actAlg K h) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;>
  · simp [actAlg, mul_inv_rev, Matrix.mul_apply, Fin.sum_univ_two]
    ring

/-- The coefficient representation of `GL₂(ℤ)` on `K[Y, Z]`. -/
def rep (K : Type*) [Field K] : Representation K GL2Z (MvPolynomial (Fin 2) K) where
  toFun g := (actAlg K g).toLinearMap
  map_one' := by rw [actAlg_one]; rfl
  map_mul' g h := by rw [actAlg_mul]; rfl

theorem rep_apply (g : GL2Z) (P : MvPolynomial (Fin 2) K) : rep K g P = actAlg K g P := rfl

/-! ### Section 4: cocycle calculus (abstract) -/

section Abstract

variable {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module K M]
  (ρ : Representation K G M) (c : G → M)

/-- `c` is a one-cocycle for `ρ`. -/
def IsCocycle : Prop := ∀ g h, c (g * h) = c g + ρ g (c h)

variable {ρ c}

theorem IsCocycle.c_one (hc : IsCocycle ρ c) : c 1 = 0 := by
  have h := hc 1 1
  have h1 : ρ 1 (c 1) = c 1 := by rw [_root_.map_one]; rfl
  rw [mul_one, h1] at h
  exact left_eq_add.mp h

theorem IsCocycle.c_inv (hc : IsCocycle ρ c) (g : G) : c g⁻¹ = -(ρ g⁻¹ (c g)) := by
  have h := hc g g⁻¹
  rw [mul_inv_cancel, hc.c_one] at h
  have h2 := congrArg (ρ g⁻¹) h
  rw [_root_.map_add, ← Module.End.mul_apply, ← _root_.map_mul, inv_mul_cancel, _root_.map_one,
    Module.End.one_apply, _root_.map_zero] at h2
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact h2.symm.trans (by simp)

/-- **Finite-group relation for an element of order three**:
`(1 + a + a²) c(a) = 0`. -/
theorem IsCocycle.cube (hc : IsCocycle ρ c) {a : G} (ha : a ^ 3 = 1) :
    c a + ρ a (c a) + ρ a (ρ a (c a)) = 0 := by
  have h : c (a * (a * a)) = c a + ρ a (c a + ρ a (c a)) := by
    rw [hc, hc]
  have h3 : a * (a * a) = 1 := by rw [← ha, pow_succ, pow_two, mul_assoc]
  rw [h3, hc.c_one, map_add] at h
  rw [add_assoc]; exact h.symm

/-- **Reflection relation**: if `c(b) = 0`, `a³ = 1` and `b a b = a⁻¹`, then
`b · c(a) = c(a) + a · c(a)`. -/
theorem IsCocycle.reflection_of_order_three (hc : IsCocycle ρ c) {a b : G} (ha : a ^ 3 = 1)
    (hb : c b = 0) (hbab : b * a * b = a⁻¹) : ρ b (c a) = c a + ρ a (c a) := by
  have hinv : a⁻¹ = a * a := by
    rw [inv_eq_iff_mul_eq_one, ← ha, pow_succ, pow_two, mul_assoc]
  have e1 : c (b * a * b) = ρ b (c a) := by
    rw [mul_assoc, hc, hb, hc, hb]; simp
  rw [hbab, hinv, hc] at e1
  exact e1.symm

/-- The value at the product `a² b r` when `c(b) = c(r) = 0`. -/
theorem IsCocycle.translation_value (hc : IsCocycle ρ c) {a b r : G} (hb : c b = 0)
    (hr : c r = 0) : c (a * a * (b * r)) = c a + ρ a (c a) := by
  rw [hc, hc, hc, hb, hr]; simp

/-- **Reflection reverses translations**: if `c(r) = 0` and
`r t r = t⁻¹` then `t · r · c(t) = - c(t)`; in coinvariants, `r` acts on `c(t)` by `-1` composed
with the action of `r`. -/
theorem IsCocycle.reflection_translation (hc : IsCocycle ρ c) {r t : G} (hr : c r = 0)
    (hrtr : r * t * r = t⁻¹) : ρ t (ρ r (c t)) = -c t := by
  have e1 : c (r * t * r) = ρ r (c t) := by
    rw [mul_assoc, hc, hr, hc, hr]; simp
  rw [hrtr, hc.c_inv] at e1
  have h2 := congrArg (ρ t) e1
  rw [_root_.map_neg, ← Module.End.mul_apply, ← _root_.map_mul, mul_inv_cancel, _root_.map_one,
    Module.End.one_apply] at h2
  exact h2.symm

end Abstract

/-! ### Section 5: the group `Γ₂` and the generators `A₀, B₀, R₀, U₀, T` -/

/-- The coefficient representation of `Γ₂` on `K[Y, Z]`. -/
def repG (K : Type*) [Field K] : Representation K Gamma2G (MvPolynomial (Fin 2) K) :=
  (rep K).comp Gamma2.subtype

/-- `U₀ = (1 0; 3 1) ∈ Γ₂`. -/
def u0 : Gamma2G := ⟨U0, U0_mem⟩
/-- `T = (1 1; 0 1) ∈ Γ₂`. -/
def t0 : Gamma2G := ⟨Tm, Tm_mem⟩

theorem repG_apply (g : Gamma2G) (P : MvPolynomial (Fin 2) K) : repG K g P = actAlg K g.1 P := rfl

theorem U0_eq' : U0 = B0 * R0 := by decide +kernel
theorem Tm_eq : Tm = A0 * A0 * (B0 * R0) := by decide +kernel
theorem R0_Tm : R0 * Tm * R0 = Tm⁻¹ := by decide +kernel

theorem a0_cube : a0 ^ 3 = 1 := Subtype.ext (by simpa [a0] using A0_cube)
theorem b0_a0 : b0 * a0 * b0 = a0⁻¹ := Subtype.ext (by simpa [a0, b0] using B0_A0)
theorem r0_t0 : r0 * t0 * r0 = t0⁻¹ := Subtype.ext (by simpa [r0, t0] using R0_Tm)
theorem r0_u0 : r0 * u0 * r0 = u0⁻¹ := Subtype.ext (by simpa [r0, u0] using R0_U0)
theorem t0_eq : t0 = a0 * a0 * (b0 * r0) := Subtype.ext (by simpa [a0, b0, r0, t0] using Tm_eq)
theorem u0_eq : u0 = b0 * r0 := Subtype.ext (by simpa [b0, r0, u0] using U0_eq')

theorem repG_u0 (P : MvPolynomial (Fin 2) K) : repG K u0 P = shearZ 3 P := by
  have : actAlg K U0 = shearZ 3 := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [actAlg, shearZ, U0]
    ring
  rw [repG_apply]; exact congrArg (fun F => F P) this

theorem repG_t0 (P : MvPolynomial (Fin 2) K) : repG K t0 P = shearY P := by
  have : actAlg K Tm = shearY := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [actAlg, shearY, Tm]
    ring
  rw [repG_apply]; exact congrArg (fun F => F P) this

theorem repG_r0 (P : MvPolynomial (Fin 2) K) : repG K r0 P = reflAlg P := by
  have : actAlg K R0 = reflAlg := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [actAlg, reflAlg, R0]
  rw [repG_apply]; exact congrArg (fun F => F P) this

/-! ### Section 6: the positive cocycle `𝒥(φ_l)` and the cusp computations -/

theorem a0_val : (a0 : GL2Z) = A0 := rfl

theorem A0inv_00 : ((A0⁻¹ : GL2Z).val 0 0) = -2 := rfl
theorem A0inv_01 : ((A0⁻¹ : GL2Z).val 0 1) = 1 := rfl
theorem A0inv_10 : ((A0⁻¹ : GL2Z).val 1 0) = -3 := rfl
theorem A0inv_11 : ((A0⁻¹ : GL2Z).val 1 1) = 1 := rfl

theorem eval_repG_a0 (P : MvPolynomial (Fin 2) K) (x y : K) :
    eval ![x, y] (repG K a0 P) = eval ![-2 * x + y, -3 * x + y] P := by
  rw [repG_apply, eval_actAlg]
  simp only [a0_val, A0inv_00, A0inv_01, A0inv_10, A0inv_11]
  push_cast
  simp

/-- **The relations the cusp argument consumes**: a binary form `J` of
degree `d` satisfying the finite-group relations of the positive cocycle with values `J, 0, 0` on
`A₀, B₀, R₀`, namely `(1 + A + A²) J = 0` (from `A₀³ = 1`), `B J = J + A J` (from
`B₀ A₀ B₀ = A₀⁻¹`), and the reflection relation `T R (J + A J) = -(J + A J)` at the upper
translation `T = A₀² B₀ R₀` (from `R₀ T R₀ = T⁻¹`). -/
structure BadLineRelations (K : Type*) [Field K] (d : ℕ) (J : MvPolynomial (Fin 2) K) : Prop where
  hom : J.IsHomogeneous d
  cube : J + repG K a0 J + repG K a0 (repG K a0 J) = 0
  refl : repG K b0 J = J + repG K a0 J
  refl_t : repG K t0 (repG K r0 (J + repG K a0 J)) = -(J + repG K a0 J)

/-- The data of the paper: a cocycle of `Γ₂` for the coefficient action on binary forms of
degree `d` with values `J, 0, 0` on `A₀, B₀, R₀` ("the positive cocycle `𝒥(φ_l)` has values
`Ĵ, 0, 0` on `A₀, B₀, R₀`"; here in the coordinates `(Y, Z)`, `J = J_f`). -/
structure PositiveCocycle (K : Type*) [Field K] (d : ℕ) (c : Gamma2G → MvPolynomial (Fin 2) K) :
    Prop where
  cocycle : IsCocycle (repG K) c
  hB : c b0 = 0
  hR : c r0 = 0
  hom : (c a0).IsHomogeneous d

namespace PositiveCocycle

variable {d : ℕ} {c : Gamma2G → MvPolynomial (Fin 2) K} (h : PositiveCocycle K d c)
include h

/-- `(1 + A + A²) J = 0`. -/
theorem cube : c a0 + repG K a0 (c a0) + repG K a0 (repG K a0 (c a0)) = 0 :=
  h.cocycle.cube a0_cube

/-- `B J = J + A J = -A⁻¹ J`. -/
theorem reflection : repG K b0 (c a0) = c a0 + repG K a0 (c a0) :=
  h.cocycle.reflection_of_order_three a0_cube h.hB b0_a0

theorem value_u0 : c u0 = 0 := by
  rw [u0_eq, h.cocycle, h.hB, h.hR]; simp

theorem value_t0 : c t0 = c a0 + repG K a0 (c a0) := by
  rw [t0_eq]; exact h.cocycle.translation_value h.hB h.hR

theorem reflection_t0 : repG K t0 (repG K r0 (c t0)) = -c t0 :=
  h.cocycle.reflection_translation h.hR r0_t0

/-- A positive cocycle yields the relations. -/
theorem relations : BadLineRelations K d (c a0) where
  hom := h.hom
  cube := h.cube
  refl := h.reflection
  refl_t := by rw [← h.value_t0]; exact h.reflection_t0

/-- Lower cusp (translation `Z ↦ Z - 3Y`): the reflection fixes the `Z^d`
coefficient and reverses the translation, so the cocycle value at the translation has
`Z^d`-coefficient equal to its own negative; the class in the coinvariants vanishes
(here already `c(U₀) = 0`). -/
theorem lower_reflection_sign : eval ![0, 1] (c u0) = -eval ![0, 1] (c u0) := by
  have e := h.cocycle.reflection_translation h.hR r0_u0
  have e2 := congrArg (eval ![0, 1]) e
  rw [repG_u0, repG_r0, eval01_shearZ, eval01_reflAlg] at e2
  simpa using e2

/-- The lower cusp restriction is the zero class of the coinvariants `V / (U₀ - 1)V`. -/
theorem lower_cusp : ∃ Q : MvPolynomial (Fin 2) K, Q.IsHomogeneous d ∧ c u0 = Q - repG K u0 Q :=
  ⟨0, isHomogeneous_zero _ _ _, by simp [h.value_u0]⟩

end PositiveCocycle

namespace BadLineRelations

variable {d : ℕ} {J : MvPolynomial (Fin 2) K} (R : BadLineRelations K d J)
include R

theorem hom_v : (J + repG K a0 J).IsHomogeneous d :=
  R.hom.add (actAlg_homog _ R.hom)

/-- Upper cusp (translation `Y ↦ Y - Z`): the reflection acts on the `Y^d`
coefficient of the value `J + A J` at the translation by `(-1)^{d+1}`. -/
theorem upper_reflection_sign :
    eval ![1, 0] (J + repG K a0 J) = (-1) ^ (d + 1) * eval ![1, 0] (J + repG K a0 J) := by
  have e2 := congrArg (eval ![1, 0]) R.refl_t
  rw [repG_t0, repG_r0, eval10_shearY, eval10_reflAlg R.hom_v] at e2
  rw [pow_succ]
  simp only [map_neg] at e2
  linear_combination e2

/-- For even `d` the upper restriction vanishes automatically. -/
theorem upper_eval_even [CharZero K] (hd : Even d) : eval ![1, 0] (J + repG K a0 J) = 0 := by
  have e := R.upper_reflection_sign
  rw [hd.add_one.neg_one_pow] at e
  have : (2 : K) * eval ![1, 0] (J + repG K a0 J) = 0 := by linear_combination e
  simpa using this

/-- For odd `d`, `J_f(Y, 3Y) = 0` (from `w ∣ f`) forces the upper restriction to
vanish: `(Ĵ + 𝒜Ĵ)(a, 2a) = -Ĵ(a, -a)`. -/
theorem upper_eval_of_J3 (hJ : eval ![1, 3] J = 0) : eval ![1, 0] (J + repG K a0 J) = 0 := by
  have e : J + repG K a0 J = -(repG K a0 (repG K a0 J)) := by
    linear_combination R.cube
  have key : eval ![(-2) * ((-2) * 1 + 0) + (-3 * 1 + 0), (-3) * ((-2) * 1 + 0) + (-3 * 1 + 0)]
      J = 0 := by
    have : (![(-2) * ((-2) * 1 + 0) + (-3 * 1 + 0), (-3) * ((-2) * 1 + 0) + (-3 * 1 + 0)] :
        Fin 2 → K) = ![1, 3] := by
      funext i; fin_cases i <;> norm_num
    rw [this]; exact hJ
  rw [e, map_neg, eval_repG_a0, eval_repG_a0, key, neg_zero]

end BadLineRelations

/-! ### Section 7: both cusp restrictions vanish; detection; the transported (hatted) relations -/

namespace BadLineRelations

variable {d : ℕ} {J : MvPolynomial (Fin 2) K} (R : BadLineRelations K d J)
include R

/-- The upper cusp restriction vanishes, in every parity: `Q - Q(Y - Z, Z)` form.
For odd `d` the input is `J_f(Y, 3Y) = 0`; for even `d` nothing is needed. -/
theorem upper_cusp [CharZero K] (hodd : Odd d → eval ![1, 3] J = 0) :
    ∃ Q : MvPolynomial (Fin 2) K, Q.IsHomogeneous d ∧
      J + repG K a0 J = Q - repG K t0 Q := by
  have h0 : eval ![1, 0] (J + repG K a0 J) = 0 := by
    rcases Nat.even_or_odd d with hd | hd
    · exact R.upper_eval_even hd
    · exact R.upper_eval_of_J3 (hodd hd)
  obtain ⟨Q, hQ, hcQ⟩ := shearY_range R.hom_v h0
  exact ⟨Q, hQ, by rw [repG_t0]; exact hcQ⟩

end BadLineRelations

namespace PositiveCocycle

variable {d : ℕ} {c : Gamma2G → MvPolynomial (Fin 2) K} (h : PositiveCocycle K d c)
include h

/-- **Both cusp restrictions vanish in every parity**. -/
theorem cusp_restrictions_vanish [CharZero K] (hodd : Odd d → eval ![1, 3] (c a0) = 0) :
    (∃ Q : MvPolynomial (Fin 2) K, Q.IsHomogeneous d ∧ c u0 = Q - repG K u0 Q) ∧
    (∃ Q : MvPolynomial (Fin 2) K, Q.IsHomogeneous d ∧ c t0 = Q - repG K t0 Q) := by
  refine ⟨h.lower_cusp, ?_⟩
  rw [h.value_t0]
  exact h.relations.upper_cusp hodd

end PositiveCocycle

/-- **Translation coinvariants at the lower cusp**: for a binary form of degree
`d`, being a coboundary `Q - U₀ Q` of a degree-`d` form is equivalent to the vanishing of the
`Z^d` coefficient; the invariants of `U₀` are the multiples of `Y^d`. -/
theorem lower_coinvariants [CharZero K] {d : ℕ} {P : MvPolynomial (Fin 2) K}
    (hP : P.IsHomogeneous d) :
    (∃ Q : MvPolynomial (Fin 2) K, Q.IsHomogeneous d ∧ P = Q - repG K u0 Q) ↔
      P.coeff (Finsupp.single 1 d) = 0 := by
  rw [← eval01_eq_coeff hP]
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    rw [repG_u0, map_sub, eval01_shearZ, sub_self]
  · intro h0
    obtain ⟨Q, hQ, hPQ⟩ := shearZ_range (by norm_num : (3 : K) ≠ 0) hP h0
    exact ⟨Q, hQ, by rw [repG_u0]; exact hPQ⟩

theorem lower_invariants [CharZero K] {d : ℕ} {P : MvPolynomial (Fin 2) K}
    (hP : P.IsHomogeneous d) :
    repG K u0 P = P ↔ ∃ c : K, P = C c * X 0 ^ d := by
  constructor
  · intro h
    rw [repG_u0] at h
    exact shearZ_ker (by norm_num : (3 : K) ≠ 0) hP h
  · rintro ⟨c, rfl⟩
    rw [repG_u0]
    simp [shearZ]

/-- **Translation coinvariants at the upper cusp**: coboundaries `Q - T Q` are
exactly the forms with vanishing `Y^d` coefficient. -/
theorem upper_coinvariants [CharZero K] {d : ℕ} {P : MvPolynomial (Fin 2) K}
    (hP : P.IsHomogeneous d) :
    (∃ Q : MvPolynomial (Fin 2) K, Q.IsHomogeneous d ∧ P = Q - repG K t0 Q) ↔
      P.coeff (Finsupp.single 0 d) = 0 := by
  rw [← eval10_eq_coeff hP]
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    rw [repG_t0, map_sub, eval10_shearY, sub_self]
  · intro h0
    obtain ⟨Q, hQ, hPQ⟩ := shearY_range hP h0
    exact ⟨Q, hQ, by rw [repG_t0]; exact hPQ⟩

/-- **Detection of the polynomial**. Suppose the positive cocycle is a
coboundary `c(g) = m - g m`, with `m` of degree `d ≥ 1`. Zero values at `B₀, R₀` make `m`
invariant under `U₀ = B₀ R₀`, hence `m = cY^d`; the reflection kills `c` for odd `d`; for even `d`
the `A₀` value is `c (Y^d - (-2Y + Z)^d)` and `J(0, Z) = 0` forces `c = 0`. -/
theorem detection [CharZero K] {d : ℕ} (hd : 1 ≤ d) {m J : MvPolynomial (Fin 2) K}
    (hm : m.IsHomogeneous d) (hJ : J = m - repG K a0 m) (hB : repG K b0 m = m)
    (hR : repG K r0 m = m) (h0 : eval ![0, 1] J = 0) : J = 0 := by
  have hU : repG K u0 m = m := by
    rw [u0_eq, _root_.map_mul, Module.End.mul_apply, hR, hB]
  obtain ⟨c, hc⟩ := (lower_invariants hm).mp hU
  have hR' : reflAlg m = m := by rw [← repG_r0]; exact hR
  have e1 : eval ![1, 0] m = c := by rw [hc]; simp
  have hd0 : (0 : K) ^ d = 0 := zero_pow (by omega)
  have hc0 : c = 0 := by
    rcases Nat.even_or_odd d with hev | hodd
    · -- J(0,1) = eval (0,1) m - eval (1,1) m = -c
      have e2 : eval ![0, 1] J = -c := by
        rw [hJ, map_sub, repG_apply, eval_actAlg]
        simp only [a0_val, A0inv_00, A0inv_01, A0inv_10, A0inv_11]
        rw [hc]
        simp [hd0]
      rw [e2] at h0
      simpa using h0
    · have e3 := congrArg (eval ![1, 0]) hR'
      rw [eval10_reflAlg hm, e1, hodd.neg_one_pow] at e3
      have : (2 : K) * c = 0 := by linear_combination -e3
      simpa using this
  have hm0 : m = 0 := by rw [hc, hc0]; simp
  rw [hJ, hm0]; simp

/-! #### The transported coordinates `(a, b) = (-Y, Z - 2Y)` -/

/-- `Ĵ(a, b) = J(-a, b - 2a)`. -/
def hatAlg : MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 2) K :=
  bind₁ ![-X 0, X 1 - C 2 * X 0]

/-- `𝒜(a, b) = (-b, a - b)`. -/
def calA : MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 2) K := bind₁ ![-X 1, X 0 - X 1]
/-- `ℬ(a, b) = (-a, b - a)`. -/
def calB : MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 2) K := bind₁ ![-X 0, X 1 - X 0]
/-- `ℛ(a, b) = (-a, b - 4a)`. -/
def calR : MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 2) K := bind₁ ![-X 0, X 1 - C 4 * X 0]

theorem eval_hatAlg (P : MvPolynomial (Fin 2) K) (x y : K) :
    eval ![x, y] (hatAlg P) = eval ![-x, y - 2 * x] P := by
  unfold hatAlg; rw [eval_bind₁_vec]; simp

theorem eval_calA (P : MvPolynomial (Fin 2) K) (x y : K) :
    eval ![x, y] (calA P) = eval ![-y, x - y] P := by
  unfold calA; rw [eval_bind₁_vec]; simp

theorem eval_calB (P : MvPolynomial (Fin 2) K) (x y : K) :
    eval ![x, y] (calB P) = eval ![-x, y - x] P := by
  unfold calB; rw [eval_bind₁_vec]; simp

theorem eval_calR (P : MvPolynomial (Fin 2) K) (x y : K) :
    eval ![x, y] (calR P) = eval ![-x, y - 4 * x] P := by
  unfold calR; rw [eval_bind₁_vec]; simp

theorem eval_repG_b0 (P : MvPolynomial (Fin 2) K) (x y : K) :
    eval ![x, y] (repG K b0 P) = eval ![-x, -3 * x + y] P := by
  rw [repG_apply, eval_actAlg]
  have h : (B0⁻¹ : GL2Z) = B0 := by decide +kernel
  have h00 : ((B0⁻¹ : GL2Z).val 0 0) = -1 := by rw [h]; rfl
  have h01 : ((B0⁻¹ : GL2Z).val 0 1) = 0 := by rw [h]; rfl
  have h10 : ((B0⁻¹ : GL2Z).val 1 0) = -3 := by rw [h]; rfl
  have h11 : ((B0⁻¹ : GL2Z).val 1 1) = 1 := by rw [h]; rfl
  have hb : (b0 : GL2Z) = B0 := rfl
  simp only [hb, h00, h01, h10, h11]
  push_cast
  simp

theorem eval_repG_r0 (P : MvPolynomial (Fin 2) K) (x y : K) :
    eval ![x, y] (repG K r0 P) = eval ![-x, y] P := by
  rw [repG_r0, eval_reflAlg]

theorem hat_a0 [CharZero K] (P : MvPolynomial (Fin 2) K) :
    hatAlg (repG K a0 P) = calA (hatAlg P) := by
  have := CharZero.infinite K
  apply MvPolynomial.funext
  intro v
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hv, eval_hatAlg, eval_repG_a0, eval_calA, eval_hatAlg]
  refine eval_vec_congr ?_ ?_ _ <;> simp
  ring

theorem hat_b0 [CharZero K] (P : MvPolynomial (Fin 2) K) :
    hatAlg (repG K b0 P) = calB (hatAlg P) := by
  have := CharZero.infinite K
  apply MvPolynomial.funext
  intro v
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hv, eval_hatAlg, eval_repG_b0, eval_calB, eval_hatAlg]
  refine eval_vec_congr ?_ ?_ _ <;> simp
  ring

theorem hat_r0 [CharZero K] (P : MvPolynomial (Fin 2) K) :
    hatAlg (repG K r0 P) = calR (hatAlg P) := by
  have := CharZero.infinite K
  apply MvPolynomial.funext
  intro v
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hv, eval_hatAlg, eval_repG_r0, eval_calR, eval_hatAlg]
  refine eval_vec_congr ?_ ?_ _ <;> simp
  ring

theorem calA_cube [CharZero K] (P : MvPolynomial (Fin 2) K) : calA (calA (calA P)) = P := by
  have := CharZero.infinite K
  apply MvPolynomial.funext
  intro v
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hv, eval_calA, eval_calA, eval_calA]
  refine eval_vec_congr ?_ ?_ _ <;> simp
  ring

theorem calB_sq [CharZero K] (P : MvPolynomial (Fin 2) K) : calB (calB P) = P := by
  have := CharZero.infinite K
  apply MvPolynomial.funext
  intro v
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hv, eval_calB, eval_calB]
  refine eval_vec_congr ?_ ?_ _ <;> simp

theorem calB_calA [CharZero K] (P : MvPolynomial (Fin 2) K) :
    calB (calA P) = calA (calA (calB P)) := by
  have := CharZero.infinite K
  apply MvPolynomial.funext
  intro v
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hv, eval_calB, eval_calA, eval_calA, eval_calA, eval_calB]
  refine eval_vec_congr ?_ ?_ _ <;> simp
  ring

theorem calB_calA_calA [CharZero K] (P : MvPolynomial (Fin 2) K) :
    calB (calA (calA P)) = swapAlg P := by
  have := CharZero.infinite K
  apply MvPolynomial.funext
  intro v
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hv, eval_calB, eval_calA, eval_calA, eval_swapAlg]
  refine eval_vec_congr ?_ ?_ _ <;> simp
  ring

namespace BadLineRelations

variable {d : ℕ} {J : MvPolynomial (Fin 2) K} (R : BadLineRelations K d J)
include R

/-- **The finite-group relations in the transported coordinates**:
`(1 + 𝒜 + 𝒜²) Ĵ = 0` and `Ĵ(a, b) = -Ĵ(b, a)`. -/
theorem hat_cube [CharZero K] :
    hatAlg (J) + calA (hatAlg (J)) + calA (calA (hatAlg (J))) = 0 := by
  have e := congrArg (hatAlg (K := K)) R.cube
  simpa only [map_add, hat_a0, map_zero] using e

theorem hat_reflection [CharZero K] :
    calB (hatAlg (J)) = hatAlg (J) + calA (hatAlg (J)) := by
  have e := congrArg (hatAlg (K := K)) R.refl
  simpa only [map_add, hat_a0, hat_b0] using e

theorem hat_antisymm [CharZero K] : swapAlg (hatAlg (J)) = -hatAlg (J) := by
  have h1 : calA (calA (hatAlg (J))) = -calB (hatAlg (J)) := by
    rw [R.hat_reflection]; linear_combination R.hat_cube
  rw [← calB_calA_calA, h1, map_neg, calB_sq]

/-- `u = (2Ĵ + 𝒜Ĵ)/3` satisfies `(1 - 𝒜) u = Ĵ` and `ℬ u = u`. -/
theorem hat_primitive [CharZero K] :
    ((3 : K)⁻¹ • ((2 : K) • hatAlg (J) + calA (hatAlg (J)))) -
        calA ((3 : K)⁻¹ • ((2 : K) • hatAlg (J) + calA (hatAlg (J)))) = hatAlg (J) ∧
    calB ((3 : K)⁻¹ • ((2 : K) • hatAlg (J) + calA (hatAlg (J)))) =
      (3 : K)⁻¹ • ((2 : K) • hatAlg (J) + calA (hatAlg (J))) := by
  have hcube := R.hat_cube
  have hb : calB (hatAlg (J)) = -calA (calA (hatAlg (J))) := by
    rw [R.hat_reflection]; linear_combination hcube
  have hba : calB (calA (hatAlg (J))) = -calA (hatAlg (J)) := by
    rw [calB_calA, hb, map_neg, map_neg, calA_cube]
  constructor
  · simp only [map_smul, map_add]
    have : calA (calA (hatAlg (J))) = -hatAlg (J) - calA (hatAlg (J)) := by
      linear_combination hcube
    rw [this]
    module
  · simp only [map_smul, map_add, hb, hba]
    have : calA (calA (hatAlg (J))) = -hatAlg (J) - calA (hatAlg (J)) := by
      linear_combination hcube
    rw [this]
    module

end BadLineRelations

/-! ### Section 8: the restriction to a cusp stabilizer `⟨t, r⟩` is the translation-coinvariant class

For a cusp stabilizer `S = ⟨t, r⟩` with `r² = 1` and `r t r = t⁻¹` (infinite dihedral), the
Hochschild-Serre computation `H¹(S, V) = H¹(⟨t⟩, V)^{⟨r⟩}` over a field of characteristic zero says
that the restriction of a cocycle to `S` is a coboundary exactly when its value at the translation
`t` is a coboundary `Q - t Q`.  We prove this directly (averaging over `⟨r⟩`). -/

section Dihedral

variable {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module K M]
  {ρ : Representation K G M} {c : G → M}

theorem rep_apply_rep (g h : G) (x : M) : ρ g (ρ h x) = ρ (g * h) x := by
  rw [_root_.map_mul]; rfl

theorem IsCocycle.coboundary_closure (hc : IsCocycle ρ c) (m : M) (S : Set G)
    (hS : ∀ s ∈ S, c s = m - ρ s m) : ∀ g ∈ Subgroup.closure S, c g = m - ρ g m := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => rw [hc.c_one]; simp
  | mul x y _ _ hx hy =>
    rw [hc, hx, hy, ← rep_apply_rep, map_sub]; abel
  | inv x _ hx =>
    rw [hc.c_inv, hx, _root_.map_sub, rep_apply_rep, inv_mul_cancel, _root_.map_one]
    simp

/-- **Averaging over the reflection** (normalized case `c(r) = 0`). -/
theorem IsCocycle.dihedral_normalized [CharZero K] (hc : IsCocycle ρ c) {r t : G} (hr : c r = 0)
    (hrr : r * r = 1) (hrtr : r * t * r = t⁻¹) (Q : M) (hQ : c t = Q - ρ t Q) :
    ∃ m : M, ∀ s ∈ Subgroup.closure ({t, r} : Set G), c s = m - ρ s m := by
  have hrel := hc.reflection_translation hr hrtr
  have h1 : ∀ x, ρ r (ρ r x) = x := fun x => by rw [rep_apply_rep, hrr, _root_.map_one]; rfl
  have htrt : t * r * t = r := by
    have : r * t = t⁻¹ * r := by
      calc r * t = r * t * r * r := by rw [mul_assoc _ r r, hrr, mul_one]
        _ = t⁻¹ * r := by rw [hrtr]
    calc t * r * t = t * (r * t) := by rw [mul_assoc]
      _ = r := by rw [this, ← mul_assoc, mul_inv_cancel, one_mul]
  have h2 : ∀ x, ρ t (ρ r (ρ t x)) = ρ r x := fun x => by
    rw [rep_apply_rep, rep_apply_rep, htrt]
  refine ⟨(2 : K)⁻¹ • (Q + ρ r Q), ?_⟩
  apply hc.coboundary_closure
  intro s hs
  rcases hs with rfl | rfl
  · -- s = t
    rw [hQ] at hrel ⊢
    simp only [map_sub, h2] at hrel
    simp only [map_smul, map_add]
    have key : ρ s (ρ r Q) = ρ r Q - Q + ρ s Q := by
      calc ρ s (ρ r Q) = (ρ s (ρ r Q) - ρ r Q) + ρ r Q := by abel
        _ = -(Q - ρ s Q) + ρ r Q := by rw [hrel]
        _ = ρ r Q - Q + ρ s Q := by abel
    rw [key]
    module
  · rw [hr]
    simp only [map_smul, map_add, h1]
    rw [smul_add, smul_add]
    module

theorem IsCocycle.sub_coboundary (hc : IsCocycle ρ c) (n : M) :
    IsCocycle ρ (fun g => c g - (n - ρ g n)) := by
  intro g h
  simp only [hc g h, _root_.map_sub, rep_apply_rep]
  abel

theorem IsCocycle.of_r_sq (hc : IsCocycle ρ c) {r : G} (hrr : r * r = 1) :
    ρ r (c r) = -c r := by
  have h := hc r r
  rw [hrr, hc.c_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- The normalization of a cocycle by the coboundary of `n = c(r)/2`. -/
theorem IsCocycle.normalize [CharZero K] (hc : IsCocycle ρ c) {r : G} (hrr : r * r = 1) :
    IsCocycle ρ (fun g => c g - ((2 : K)⁻¹ • c r - ρ g ((2 : K)⁻¹ • c r))) ∧
    (fun g => c g - ((2 : K)⁻¹ • c r - ρ g ((2 : K)⁻¹ • c r))) r = 0 := by
  refine ⟨hc.sub_coboundary _, ?_⟩
  simp only [map_smul, hc.of_r_sq hrr]
  module

/-- **Hochschild-Serre for the infinite dihedral cusp stabilizer**: over a field
of characteristic zero, the restriction of a cocycle to `⟨t, r⟩` (`r² = 1`, `r t r = t⁻¹`) is a
coboundary if and only if its value at the translation `t` is a coboundary `Q - t Q`. -/
theorem IsCocycle.dihedral_iff [CharZero K] (hc : IsCocycle ρ c) {r t : G} (hrr : r * r = 1)
    (hrtr : r * t * r = t⁻¹) :
    (∃ m : M, ∀ s ∈ Subgroup.closure ({t, r} : Set G), c s = m - ρ s m) ↔
      ∃ Q : M, c t = Q - ρ t Q := by
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, hm t (Subgroup.subset_closure (by simp))⟩
  · rintro ⟨Q, hQ⟩
    obtain ⟨hc', hr'⟩ := hc.normalize hrr
    set n : M := (2 : K)⁻¹ • c r with hn
    obtain ⟨m, hm⟩ := (hc.sub_coboundary n).dihedral_normalized (c := fun g => c g - (n - ρ g n))
      hr' hrr hrtr (Q - n) (by simp only [hQ, map_sub]; abel)
    refine ⟨m + n, fun s hs => ?_⟩
    have := hm s hs
    simp only [map_add]
    rw [sub_eq_iff_eq_add] at this
    rw [this]; abel

end Dihedral

/-! ### Section 9: the cusp stabilizers of `Γ₂` and their `H¹` -/

theorem r0_sq' : r0 * r0 = 1 := Subtype.ext (by simpa [r0, pow_two] using R0_sq)

/-- The lower cusp stabilizer `⟨U₀, R₀⟩` (translation of width three, reflection). -/
def cuspStabLower : Subgroup Gamma2G := Subgroup.closure ({u0, r0} : Set Gamma2G)

/-- The upper cusp stabilizer `⟨T, R₀⟩` (translation of width one, reflection). -/
def cuspStabUpper : Subgroup Gamma2G := Subgroup.closure ({t0, r0} : Set Gamma2G)

section CuspH1

variable {d : ℕ} {c : Gamma2G → MvPolynomial (Fin 2) K}

private theorem homog_smul_inv2 [CharZero K] {P : MvPolynomial (Fin 2) K} (hP : P.IsHomogeneous d) :
    ((2 : K)⁻¹ • P).IsHomogeneous d := by
  rw [smul_eq_C_mul]; exact hP.C_mul _

/-- The normalized cocycle `c - ∂(c(R₀)/2)` is again valued in the degree-`d` forms. -/
private theorem normalized_hom [CharZero K] (hd : ∀ g, (c g).IsHomogeneous d) (g : Gamma2G) :
    (c g - ((2 : K)⁻¹ • c r0 - repG K g ((2 : K)⁻¹ • c r0))).IsHomogeneous d := by
  have hn := homog_smul_inv2 (hd r0)
  exact (hd g).sub (hn.sub (actAlg_homog _ hn))

/-- **The restriction to the lower cusp stabilizer vanishes: its full cusp `H¹` is zero**.  For every cocycle of `Γ₂` valued in the degree-`d` binary forms, the restriction
to `⟨U₀, R₀⟩` is a coboundary, for every `d`. -/
theorem lower_cusp_H1_vanishes [CharZero K] (hc : IsCocycle (repG K) c)
    (hd : ∀ g, (c g).IsHomogeneous d) :
    ∃ m : MvPolynomial (Fin 2) K, ∀ s ∈ cuspStabLower, c s = m - repG K s m := by
  obtain ⟨hcn, hrn⟩ := hc.normalize (r0_sq' )
  have e := hcn.reflection_translation hrn r0_u0
  have e2 := congrArg (eval ![0, 1]) e
  rw [repG_u0, repG_r0, eval01_shearZ, eval01_reflAlg] at e2
  simp only [map_neg, map_sub, repG_u0, eval01_shearZ] at e2
  have h0 : eval ![0, 1] (c u0) = 0 := by
    have : (2 : K) * eval ![0, 1] (c u0 - ((2 : K)⁻¹ • c r0 - repG K u0 ((2 : K)⁻¹ • c r0))) = 0 := by
      simp only [map_sub, repG_u0, eval01_shearZ, sub_self, sub_zero] at e2 ⊢
      linear_combination e2
    simpa [map_sub, repG_u0, eval01_shearZ] using this
  obtain ⟨Q, -, hQ⟩ := (lower_coinvariants (hd u0)).mpr
    (by rw [← eval01_eq_coeff (hd u0)]; exact h0)
  exact (hc.dihedral_iff r0_sq' r0_u0).mpr ⟨Q, hQ⟩

/-- The sign of the reflection on the upper cusp class, for an arbitrary cocycle valued in the
degree-`d` forms: `λ_Y(c(T)) = (-1)^{d+1} λ_Y(c(T))`. -/
theorem upper_class_sign [CharZero K] (hc : IsCocycle (repG K) c)
    (hd : ∀ g, (c g).IsHomogeneous d) :
    eval ![1, 0] (c t0) = (-1) ^ (d + 1) * eval ![1, 0] (c t0) := by
  obtain ⟨hcn, hrn⟩ := hc.normalize (r0_sq')
  have e := hcn.reflection_translation hrn r0_t0
  have e2 := congrArg (eval ![1, 0]) e
  have hh := normalized_hom hd t0
  rw [repG_t0, repG_r0, eval10_shearY, eval10_reflAlg hh] at e2
  simp only [map_neg, map_sub, repG_t0, eval10_shearY, sub_self, sub_zero] at e2
  rw [pow_succ]
  linear_combination e2

/-- **Upper cusp: the restriction to `⟨T, R₀⟩` vanishes iff the `Y^d` coefficient of `c(T)`
vanishes**, i.e. iff the translation-coinvariant class vanishes. -/
theorem upper_cusp_restriction_iff [CharZero K] (hc : IsCocycle (repG K) c)
    (hd : ∀ g, (c g).IsHomogeneous d) :
    (∃ m : MvPolynomial (Fin 2) K, ∀ s ∈ cuspStabUpper, c s = m - repG K s m) ↔
      eval ![1, 0] (c t0) = 0 := by
  rw [cuspStabUpper, hc.dihedral_iff r0_sq' r0_t0]
  constructor
  · rintro ⟨Q, hQ⟩
    rw [hQ, map_sub, repG_t0, eval10_shearY, sub_self]
  · intro h0
    obtain ⟨Q, -, hQ⟩ := (upper_coinvariants (hd t0)).mpr
      (by rw [← eval10_eq_coeff (hd t0)]; exact h0)
    exact ⟨Q, hQ⟩

/-- For even `d` the upper cusp `H¹` vanishes: the reflection acts by `(-1)^{d+1} = -1`. -/
theorem upper_cusp_H1_vanishes_of_even [CharZero K] (hc : IsCocycle (repG K) c)
    (hd : ∀ g, (c g).IsHomogeneous d) (hev : Even d) :
    ∃ m : MvPolynomial (Fin 2) K, ∀ s ∈ cuspStabUpper, c s = m - repG K s m := by
  rw [upper_cusp_restriction_iff hc hd]
  have e := upper_class_sign hc hd
  rw [hev.add_one.neg_one_pow] at e
  have : (2 : K) * eval ![1, 0] (c t0) = 0 := by linear_combination e
  simpa using this

end CuspH1

namespace PositiveCocycle

variable {d : ℕ} {c : Gamma2G → MvPolynomial (Fin 2) K} (h : PositiveCocycle K d c)
include h

/-- **Both cusp restrictions vanish in `H¹` of the cusp stabilizers, in every parity**: the restrictions of the positive cocycle to `⟨U₀, R₀⟩` and `⟨T, R₀⟩` are
coboundaries.  The cocycle is valued in the degree-`d` forms; for odd `d` the input is
`J_f(Y,3Y) = 0`. -/
theorem cusp_H1_restrictions_vanish [CharZero K] (hd : ∀ g, (c g).IsHomogeneous d)
    (hodd : Odd d → eval ![1, 3] (c a0) = 0) :
    (∃ m : MvPolynomial (Fin 2) K, ∀ s ∈ cuspStabLower, c s = m - repG K s m) ∧
    (∃ m : MvPolynomial (Fin 2) K, ∀ s ∈ cuspStabUpper, c s = m - repG K s m) := by
  refine ⟨lower_cusp_H1_vanishes h.cocycle hd, ?_⟩
  rw [upper_cusp_restriction_iff h.cocycle hd, h.value_t0]
  rcases Nat.even_or_odd d with hev | hodd'
  · exact h.relations.upper_eval_even hev
  · exact h.relations.upper_eval_of_J3 (hodd hodd')

end PositiveCocycle

end TernaryPeriodPolynomials.Argument.FiberModel.BadLineCusps
