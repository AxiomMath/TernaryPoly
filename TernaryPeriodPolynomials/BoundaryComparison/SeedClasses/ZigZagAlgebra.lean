module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Units.Opposite
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.Perm.Option
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


/-!
# The Čech--de Rham zig-zag, algebraic part

Paper: Lemma C.3 (`ar:lem:seed`) uses the seed forms `ω_h` as classes in the cohomology of the
plane parabolic `Γ_P`, which acts on the contractible face `e(P) = N_P × ℍ`. A closed
`Γ_P`-equivariant `E`-valued 2-form on a contractible space defines a class in `H²(Γ_P, E)` by the
standard zig-zag: choose `η` with `dη = ω`, then functions `θ_g` with `dθ_g = g^*η - ρ(g)η`,
and put `c(g,h) = h^*θ_g + ρ(g)θ_h - θ_{gh}` (a function with zero differential, i.e. a constant of
the coefficient module `V`).

This file proves the algebra of that construction, abstractly: for linear data
`d₀ : Ω⁰ → Ω¹`, `d₁ : Ω¹ → Ω²`, pullback operators `P_i g`, coefficient twists `T_i g` and
constants `c : V → Ω⁰`, subject to the evident laws, (1) the constants `c(g,h)` form a 2-cocycle
(`IsCocycle₂` convention of Mathlib), (2) any two choices of `(η, θ)` for the same form give
cohomologous cocycles, and (3) the construction is additive.
The instantiation by smooth forms on a convex open set is in `ZigZagDeRham`.

Formalized by Claude Sonnet 5.5.
-/

namespace TernaryPeriodPolynomials.Argument.SeedC3.ZigZag

universe u

variable {k : Type u} [CommRing k] {G : Type u} [Group G]
  {V Ω0 Ω1 Ω2 : Type u} [AddCommGroup V] [Module k V] [AddCommGroup Ω0] [Module k Ω0]
  [AddCommGroup Ω1] [Module k Ω1] [AddCommGroup Ω2] [Module k Ω2]

/-- The laws of the zig-zag data. -/
structure Laws (ρ : Representation k G V) (d0 : Ω0 →ₗ[k] Ω1) (d1 : Ω1 →ₗ[k] Ω2)
    (P0 : G → Ω0 →ₗ[k] Ω0) (P1 : G → Ω1 →ₗ[k] Ω1) (P2 : G → Ω2 →ₗ[k] Ω2)
    (T0 : G → Ω0 →ₗ[k] Ω0) (T1 : G → Ω1 →ₗ[k] Ω1) (T2 : G → Ω2 →ₗ[k] Ω2)
    (c : V →ₗ[k] Ω0) : Prop where
  d_P0 : ∀ g w, d0 (P0 g w) = P1 g (d0 w)
  d_T0 : ∀ g w, d0 (T0 g w) = T1 g (d0 w)
  d_P1 : ∀ g w, d1 (P1 g w) = P2 g (d1 w)
  d_T1 : ∀ g w, d1 (T1 g w) = T2 g (d1 w)
  P0_mul : ∀ g h w, P0 (g * h) w = P0 h (P0 g w)
  P1_mul : ∀ g h w, P1 (g * h) w = P1 h (P1 g w)
  T0_mul : ∀ g h w, T0 (g * h) w = T0 g (T0 h w)
  T1_mul : ∀ g h w, T1 (g * h) w = T1 g (T1 h w)
  PT0 : ∀ g h w, P0 g (T0 h w) = T0 h (P0 g w)
  PT1 : ∀ g h w, P1 g (T1 h w) = T1 h (P1 g w)
  c_injective : Function.Injective c
  d_c : ∀ v, d0 (c v) = 0
  P_c : ∀ g v, P0 g (c v) = c v
  T_c : ∀ g v, T0 g (c v) = c (ρ g v)
  const_of_closed : ∀ w, d0 w = 0 → ∃ v, w = c v
  exact1 : ∀ w, d1 w = 0 → ∃ w', d0 w' = w

variable {ρ : Representation k G V} {d0 : Ω0 →ₗ[k] Ω1} {d1 : Ω1 →ₗ[k] Ω2}
  {P0 : G → Ω0 →ₗ[k] Ω0} {P1 : G → Ω1 →ₗ[k] Ω1} {P2 : G → Ω2 →ₗ[k] Ω2}
  {T0 : G → Ω0 →ₗ[k] Ω0} {T1 : G → Ω1 →ₗ[k] Ω1} {T2 : G → Ω2 →ₗ[k] Ω2}
  {c : V →ₗ[k] Ω0}

/-- Zig-zag data for a 2-form `ω`: a primitive `η` and functions `θ_g` with
`dθ_g = g^*η - ρ(g)η`. -/
structure Datum (d0 : Ω0 →ₗ[k] Ω1) (d1 : Ω1 →ₗ[k] Ω2) (P1 : G → Ω1 →ₗ[k] Ω1)
    (T1 : G → Ω1 →ₗ[k] Ω1) (ω : Ω2) where
  η : Ω1
  θ : G → Ω0
  dη : d1 η = ω
  dθ : ∀ g, d0 (θ g) = P1 g η - T1 g η

/-- The cocycle defect `h^*θ_g + ρ(g)θ_h - θ_{gh}` is a constant. -/
theorem defect_const (L : Laws ρ d0 d1 P0 P1 P2 T0 T1 T2 c) {ω : Ω2}
    (D : Datum d0 d1 P1 T1 ω) (g h : G) :
    ∃ v, P0 h (D.θ g) + T0 g (D.θ h) - D.θ (g * h) = c v := by
  apply L.const_of_closed
  rw [map_sub, map_add, L.d_P0, L.d_T0, D.dθ, D.dθ, D.dθ]
  simp only [map_sub, L.P1_mul, L.T1_mul, L.PT1]
  abel

/-- The coefficient-valued zig-zag cochain. -/
noncomputable def cochain (L : Laws ρ d0 d1 P0 P1 P2 T0 T1 T2 c) {ω : Ω2}
    (D : Datum d0 d1 P1 T1 ω) (g h : G) : V :=
  Classical.choose (defect_const L D g h)

theorem c_cochain (L : Laws ρ d0 d1 P0 P1 P2 T0 T1 T2 c) {ω : Ω2} (D : Datum d0 d1 P1 T1 ω)
    (g h : G) :
    c (cochain L D g h) = P0 h (D.θ g) + T0 g (D.θ h) - D.θ (g * h) :=
  (Classical.choose_spec (defect_const L D g h)).symm

/-- **The zig-zag cochain is a 2-cocycle** (Mathlib's `IsCocycle₂` convention). -/
theorem cochain_isCocycle (L : Laws ρ d0 d1 P0 P1 P2 T0 T1 T2 c) {ω : Ω2}
    (D : Datum d0 d1 P1 T1 ω) (g h j : G) :
    cochain L D (g * h) j + cochain L D g h = ρ g (cochain L D h j) + cochain L D g (h * j) := by
  apply L.c_injective
  have e1 := c_cochain L D (g * h) j
  have e2 := c_cochain L D g h
  have e3 := c_cochain L D h j
  have e4 := c_cochain L D g (h * j)
  have e5 : c (ρ g (cochain L D h j)) = T0 g (c (cochain L D h j)) := (L.T_c g _).symm
  have e6 : c (cochain L D g h) = P0 j (c (cochain L D g h)) := (L.P_c j _).symm
  rw [map_add, map_add, e1, e5, e3, e4]
  conv_lhs => rw [e6, e2]
  simp only [map_sub, map_add, L.P0_mul, L.T0_mul, L.PT0, mul_assoc]
  abel

/-- **Independence of the choices.** Two zig-zag data for the same form give cocycles differing by
the coboundary of a function `κ : G → V` (Mathlib's `IsCoboundary₂` convention). -/
theorem cochain_indep (L : Laws ρ d0 d1 P0 P1 P2 T0 T1 T2 c) {ω : Ω2}
    (D D' : Datum d0 d1 P1 T1 ω) :
    ∃ κ : G → V, ∀ g h, cochain L D' g h = cochain L D g h + (ρ g (κ h) - κ (g * h) + κ g) := by
  obtain ⟨β, hβ⟩ := L.exact1 (D'.η - D.η) (by rw [map_sub, D.dη, D'.dη, sub_self])
  have hκ : ∀ g, ∃ v, D'.θ g - D.θ g - P0 g β + T0 g β = c v := by
    intro g
    apply L.const_of_closed
    rw [map_add, map_sub, map_sub, L.d_P0, L.d_T0, D'.dθ, D.dθ, hβ]
    simp only [map_sub]
    abel
  choose κ hκ using hκ
  refine ⟨κ, fun g h => ?_⟩
  apply L.c_injective
  have hθ : ∀ g, D'.θ g = D.θ g + (c (κ g) + P0 g β - T0 g β) := by
    intro g
    have e := hκ g
    rw [← e]
    abel
  simp only [map_add, map_sub]
  rw [c_cochain L D', c_cochain L D, ← L.T_c, hθ g, hθ h, hθ (g * h)]
  simp only [map_add, map_sub, L.P_c, L.P0_mul, L.T0_mul, L.PT0]
  abel

/-- The sum of zig-zag data is zig-zag data for the sum. -/
def Datum.add {ω ω' : Ω2} (D : Datum d0 d1 P1 T1 ω) (D' : Datum d0 d1 P1 T1 ω') :
    Datum d0 d1 P1 T1 (ω + ω') where
  η := D.η + D'.η
  θ g := D.θ g + D'.θ g
  dη := by rw [map_add, D.dη, D'.dη]
  dθ g := by rw [map_add, D.dθ, D'.dθ, map_add, map_add]; abel

/-- **Additivity.** The zig-zag cochain of a sum of data is the sum of the cochains. -/
theorem cochain_add (L : Laws ρ d0 d1 P0 P1 P2 T0 T1 T2 c) {ω ω' : Ω2}
    (D : Datum d0 d1 P1 T1 ω) (D' : Datum d0 d1 P1 T1 ω') (g h : G) :
    cochain L (D.add D') g h = cochain L D g h + cochain L D' g h := by
  apply L.c_injective
  rw [map_add, c_cochain L (D.add D'), c_cochain L D, c_cochain L D']
  simp only [Datum.add, map_add]
  abel

/-- Scalar multiples of zig-zag data. -/
def Datum.smul (a : k) {ω : Ω2} (D : Datum d0 d1 P1 T1 ω) : Datum d0 d1 P1 T1 (a • ω) where
  η := a • D.η
  θ g := a • D.θ g
  dη := by rw [map_smul, D.dη]
  dθ g := by rw [map_smul, D.dθ, map_smul, map_smul, smul_sub]

theorem cochain_smul (L : Laws ρ d0 d1 P0 P1 P2 T0 T1 T2 c) (a : k) {ω : Ω2}
    (D : Datum d0 d1 P1 T1 ω) (g h : G) :
    cochain L (D.smul a) g h = a • cochain L D g h := by
  apply L.c_injective
  rw [map_smul, c_cochain L (D.smul a), c_cochain L D]
  simp only [Datum.smul, map_smul, smul_add, smul_sub]

/-- **Existence of zig-zag data** for a closed equivariant 2-form, from the Poincaré lemma in
degree 2 (`exact2`). -/
theorem exists_datum (L : Laws ρ d0 d1 P0 P1 P2 T0 T1 T2 c) (Cl2 : Ω2 → Prop)
    (exact2 : ∀ ω, Cl2 ω → ∃ η, d1 η = ω) {ω : Ω2} (hω : Cl2 ω)
    (hinv : ∀ g, P2 g ω = T2 g ω) : Nonempty (Datum d0 d1 P1 T1 ω) := by
  obtain ⟨η, hη⟩ := exact2 ω hω
  have h : ∀ g, ∃ x, d0 x = P1 g η - T1 g η := fun g => by
    apply L.exact1
    rw [map_sub, L.d_P1, L.d_T1, hη, hinv g, sub_self]
  choose θ hθ using h
  exact ⟨⟨η, θ, hη, hθ⟩⟩

end TernaryPeriodPolynomials.Argument.SeedC3.ZigZag
