module

public import TernaryPeriodPolynomials.GroupCohomology.Koszul.Koszul
public import TernaryPeriodPolynomials.GroupCohomology.Homology.Additive

@[expose] public section


/-!
# `H₂(ℤ², V)` for a trivial coefficient space `V`: the fundamental class

Formalized by Claude Sonnet 5.5.

For `U2 = ℤ²` (multiplicative) and a finite-dimensional `ℚ`-space `V` with trivial action, `kappa v w : V → H₂(U2, V)` sends
`a` to the class of the 2-cycle `a·([v|w] - [w|v])` (Mathlib's `groupHomology.cycles₂`/`H2π`).  The alternating form
`ω(x, y) = x₀y₁ - x₁y₀` is a 2-cocycle, hence a functional `omegaH : H₂(U2, V) → V` with `omegaH (kappa v w a) = 2 ω(v, w) a`
(`omegaH_kappa`).  Consequently `kappa0 = kappa e₁ e₂` is injective; it is surjective (`kappa0_surjective`) because
`H₂(U2, ℚ)` has rank at most one (the Koszul resolution, `rank_groupHomology_U2_two`) and `V` decomposes along a basis
(additivity of `H₂`).  The class of a general parallelogram is `ω(v, w)` times the fundamental class
(`kappa_eq_smul`); for a group endomorphism `μ` of `ℤ²` and a linear map `f` the induced map on `H₂` multiplies
the fundamental class by `ω(μ e₁, μ e₂)`, the determinant of `μ` (`map_kappa0_gen`).
-/

open CategoryTheory Representation

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HochschildSerre

open TernaryPeriodPolynomials.Argument.GroupHomologyDescent (T2 U2)

variable (V : Type) [AddCommGroup V] [Module ℚ V]

/-- The alternating form `ω(x, y) = x₀ y₁ − x₁ y₀` on `U2 = ℤ²`. -/
def omegaZ (x y : U2) : ℤ :=
  Multiplicative.toAdd x 0 * Multiplicative.toAdd y 1 - Multiplicative.toAdd x 1 * Multiplicative.toAdd y 0

/-- The trivial `U2`-representation on `V`. -/
abbrev TV : Rep.{0} ℚ U2 := Rep.trivial ℚ U2 V

/-- The 2-chain `[v|w] − [w|v]` with coefficient `a`. -/
def cyc (v w : U2) (a : V) : U2 × U2 →₀ V := Finsupp.single (v, w) a - Finsupp.single (w, v) a

theorem cyc_mem (v w : U2) (a : V) : cyc V v w a ∈ groupHomology.cycles₂ (TV V) := by
  rw [groupHomology.cycles₂, LinearMap.mem_ker]
  have h1 := groupHomology.d₂₁_single (A := TV V) (v, w) a
  have h2 := groupHomology.d₂₁_single (A := TV V) (w, v) a
  simp only [cyc, map_sub]
  erw [h1, h2]
  have e1 : ((TV V).ρ (v, w).1⁻¹) a = a := rfl
  have e2 : ((TV V).ρ (w, v).1⁻¹) a = a := rfl
  rw [e1, e2, mul_comm w v]
  abel

/-- The linear form `[x|y] ↦ ω(x, y)` on 2-chains. -/
def omegaTilde : (U2 × U2 →₀ V) →ₗ[ℚ] V :=
  Finsupp.lsum ℚ (fun p : U2 × U2 => ((omegaZ p.1 p.2 : ℚ)) • (LinearMap.id : V →ₗ[ℚ] V))

theorem omegaTilde_single (p : U2 × U2) (a : V) :
    omegaTilde V (Finsupp.single p a) = (omegaZ p.1 p.2 : ℚ) • a := by
  simp [omegaTilde]

theorem omegaZ_cocycle (x y z : U2) :
    (omegaZ y z : ℤ) - omegaZ (x * y) z + omegaZ x (y * z) - omegaZ x y = 0 := by
  simp only [omegaZ, toAdd_mul, Pi.add_apply]
  ring

theorem omegaTilde_d₃₂ (z : U2 × U2 × U2 →₀ V) :
    omegaTilde V ((groupHomology.d₃₂ (TV V)).hom z) = 0 := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | single g a =>
    have h := groupHomology.d₃₂_single (A := TV V) g a
    change omegaTilde V ((groupHomology.d₃₂ (TV V)) (Finsupp.single g a)) = 0
    rw [h]
    simp only [map_sub, map_add, omegaTilde_single]
    have e : ((TV V).ρ g.1⁻¹) a = a := rfl
    rw [e]
    have hc := omegaZ_cocycle g.1 g.2.1 g.2.2
    have hc' : ((omegaZ g.2.1 g.2.2 : ℤ) : ℚ) - (omegaZ (g.1 * g.2.1) g.2.2 : ℤ) +
        (omegaZ g.1 (g.2.1 * g.2.2) : ℤ) - (omegaZ g.1 g.2.1 : ℤ) = 0 := by exact_mod_cast hc
    calc _ = (((omegaZ g.2.1 g.2.2 : ℤ) : ℚ) - (omegaZ (g.1 * g.2.1) g.2.2 : ℤ) +
        (omegaZ g.1 (g.2.1 * g.2.2) : ℤ) - (omegaZ g.1 g.2.1 : ℤ)) • a := by
          simp only [sub_smul, add_smul]
      _ = 0 := by rw [hc', zero_smul]

theorem omegaTilde_boundary {x : U2 × U2 →₀ V} (hx : x ∈ groupHomology.boundaries₂ (TV V)) :
    omegaTilde V x = 0 := by
  obtain ⟨y, rfl⟩ := hx
  exact omegaTilde_d₃₂ V y

/-- The map `[z] ↦ ω(z)` on `H₂(U2, V)`. -/
def omegaH : groupHomology (TV V) 2 →ₗ[ℚ] V :=
  haveI hsurj : Function.Surjective (groupHomology.H2π (TV V)).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  haveI hker : LinearMap.ker (groupHomology.H2π (TV V)).hom ≤
      LinearMap.ker (omegaTilde V ∘ₗ (groupHomology.cycles₂ (TV V)).subtype) := by
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have h := (groupHomology.H2π_eq_zero_iff x).1 hx
    exact omegaTilde_boundary V h
  ((LinearMap.ker (groupHomology.H2π (TV V)).hom).liftQ _ hker) ∘ₗ
    ((groupHomology.H2π (TV V)).hom.quotKerEquivOfSurjective hsurj).symm.toLinearMap

theorem omegaH_H2π (x : groupHomology.cycles₂ (TV V)) :
    omegaH V ((groupHomology.H2π (TV V)).hom x) = omegaTilde V x.1 := by
  have hsurj : Function.Surjective (groupHomology.H2π (TV V)).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  unfold omegaH
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

/-- The linear map `a ↦ [a·[v|w] − a·[w|v]]`. -/
def cycLin (v w : U2) : V →ₗ[ℚ] (U2 × U2 →₀ V) :=
  Finsupp.lsingle (v, w) - Finsupp.lsingle (w, v)

theorem cycLin_apply (v w : U2) (a : V) : cycLin V v w a = cyc V v w a := rfl

/-- The class of the 2-cycle `a·([v|w] − [w|v])` in `H₂(U2, V)`. -/
def kappa (v w : U2) : V →ₗ[ℚ] groupHomology (TV V) 2 :=
  (groupHomology.H2π (TV V)).hom ∘ₗ
    ((cycLin V v w).codRestrict (groupHomology.cycles₂ (TV V)) (cyc_mem V v w))

theorem kappa_apply (v w : U2) (a : V) :
    kappa V v w a = (groupHomology.H2π (TV V)).hom ⟨cyc V v w a, cyc_mem V v w a⟩ := rfl

theorem omegaH_kappa (v w : U2) (a : V) :
    omegaH V (kappa V v w a) = (2 * (omegaZ v w : ℚ)) • a := by
  rw [kappa_apply, omegaH_H2π]
  change omegaTilde V (cyc V v w a) = _
  simp only [cyc, map_sub, omegaTilde_single]
  have : (omegaZ w v : ℚ) = - (omegaZ v w : ℚ) := by
    simp only [omegaZ]; push_cast; ring
  rw [this]
  module

/-- The first basis vector of `ℤ²`. -/
def e1 : U2 := Multiplicative.ofAdd (Pi.single 0 1)

/-- The second basis vector of `ℤ²`. -/
def e2 : U2 := Multiplicative.ofAdd (Pi.single 1 1)

theorem omegaZ_e1_e2 : omegaZ e1 e2 = 1 := by
  simp [omegaZ, e1, e2]

/-- The class of the fundamental 2-cycle. -/
abbrev kappa0 : V →ₗ[ℚ] groupHomology (TV V) 2 := kappa V e1 e2

theorem omegaH_kappa0 (a : V) : omegaH V (kappa0 V a) = (2 : ℚ) • a := by
  rw [kappa0, omegaH_kappa, omegaZ_e1_e2]
  norm_num

theorem kappa0_injective : Function.Injective (kappa0 V) := by
  intro a b h
  have := congrArg (omegaH V) h
  rw [omegaH_kappa0, omegaH_kappa0] at this
  exact smul_right_injective V (two_ne_zero) this

variable {V} {W : Type} [AddCommGroup W] [Module ℚ W]

/-- A linear map as a morphism of trivial representations. -/
def trivHom (f : V →ₗ[ℚ] W) : TV V ⟶ TV W := Rep.ofHom ⟨f, fun _ => rfl⟩

theorem map_kappa (f : V →ₗ[ℚ] W) (v w : U2) (a : V) :
    groupHomology.map (MonoidHom.id U2) (trivHom f) 2 (kappa V v w a) = kappa W v w (f a) := by
  rw [kappa_apply, kappa_apply]
  have h := groupHomology.H2π_comp_map (A := TV V) (B := TV W) (MonoidHom.id U2) (trivHom f)
  have h2 := congrArg (fun φ => φ.hom ⟨cyc V v w a, cyc_mem V v w a⟩) h
  have e : (groupHomology.mapCycles₂ (A := TV V) (B := TV W) (MonoidHom.id U2) (trivHom f)).hom
      ⟨cyc V v w a, cyc_mem V v w a⟩ = ⟨cyc W v w (f a), cyc_mem W v w (f a)⟩ := by
    apply Subtype.ext
    erw [groupHomology.coe_mapCycles₂]
    simp only [groupHomology.chainsMap₂, cyc, trivHom]
    have := (Finsupp.mapRange.linearMap f : (U2 × U2 →₀ V) →ₗ[ℚ] (U2 × U2 →₀ W)).map_sub
      (Finsupp.single (v, w) a) (Finsupp.single (w, v) a)
    simpa [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single] using this
  exact h2.trans (congrArg (groupHomology.H2π (TV W)).hom e)

open TernaryPeriodPolynomials.Argument.GroupHomology in
instance functorAdditive (G : Type) [Group G] (n : ℕ) : (groupHomology.functor ℚ G n).Additive :=
  ⟨fun {_ _ f g} => functor_map_add f g n⟩

theorem rank_two : Module.rank ℚ (groupHomology (TV ℚ) 2) ≤ 1 :=
  TernaryPeriodPolynomials.Argument.GroupHomologyDescent.rank_groupHomology_U2_two

theorem kappa0_surjective_rat : Function.Surjective (kappa0 ℚ) := by
  obtain ⟨v0, hv0⟩ := (rank_le_one_iff (K := ℚ) (V := groupHomology (TV ℚ) 2)).1 (rank_two)
  intro x
  obtain ⟨r, hr⟩ := hv0 x
  obtain ⟨s, hs⟩ := hv0 (kappa0 ℚ 1)
  have hs0 : s ≠ 0 := by
    rintro rfl
    have h0 : kappa0 ℚ 1 = 0 := by rw [← hs, zero_smul]
    have := kappa0_injective ℚ (h0.trans (map_zero (kappa0 ℚ)).symm)
    exact one_ne_zero this
  refine ⟨r / s, ?_⟩
  have h1 : kappa0 ℚ (r / s) = (r / s) • kappa0 ℚ 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
  rw [h1, ← hs, smul_smul, div_mul_cancel₀ _ hs0, hr]

theorem trivHom_id : trivHom (LinearMap.id : V →ₗ[ℚ] V) = 𝟙 (TV V) := rfl

theorem trivHom_comp {X : Type} [AddCommGroup X] [Module ℚ X] (f : V →ₗ[ℚ] W) (g : W →ₗ[ℚ] X) :
    trivHom (g ∘ₗ f) = trivHom f ≫ trivHom g := rfl

theorem trivHom_sum {ι : Type} (s : Finset ι) (f : ι → (V →ₗ[ℚ] W)) :
    trivHom (∑ i ∈ s, f i) = ∑ i ∈ s, trivHom (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro a
    simp [trivHom]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro a
    simp [trivHom, Rep.add_hom]

theorem kappa0_surjective [Module.Finite ℚ V] : Function.Surjective (kappa0 V) := by
  classical
  let b := Module.finBasis ℚ V
  let F := groupHomology.functor ℚ U2 2
  have hid : (𝟙 (TV V) : TV V ⟶ TV V) =
      ∑ i, trivHom (b.coord i) ≫ trivHom (LinearMap.toSpanSingleton ℚ V (b i)) := by
    rw [← trivHom_id (V := V)]
    have : (LinearMap.id : V →ₗ[ℚ] V) = ∑ i, (LinearMap.toSpanSingleton ℚ V (b i)) ∘ₗ (b.coord i) := by
      ext x
      simp [Module.Basis.sum_repr]
    rw [this, trivHom_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact trivHom_comp _ _
  intro x
  have hx : x = ∑ i, (F.map (trivHom (LinearMap.toSpanSingleton ℚ V (b i)))).hom
      ((F.map (trivHom (b.coord i))).hom x) := by
    have h1 : F.map (𝟙 (TV V)) = 𝟙 _ := F.map_id _
    rw [hid, Functor.map_sum] at h1
    have h2 := congrArg (fun φ => φ.hom x) h1
    simp only [ModuleCat.hom_sum, Functor.map_comp, ModuleCat.hom_comp, ModuleCat.hom_id] at h2
    erw [LinearMap.sum_apply] at h2
    exact h2.symm
  have ht : ∀ i, ∃ t : ℚ, kappa0 ℚ t = (F.map (trivHom (b.coord i))).hom x := fun i =>
    kappa0_surjective_rat _
  choose t ht using ht
  refine ⟨∑ i, LinearMap.toSpanSingleton ℚ V (b i) (t i), ?_⟩
  rw [map_sum]
  conv_rhs => rw [hx]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← ht i]
  exact (map_kappa (LinearMap.toSpanSingleton ℚ V (b i)) e1 e2 (t i)).symm

theorem kappa_eq_smul [Module.Finite ℚ V] (v w : U2) (a : V) :
    kappa V v w a = kappa0 V ((omegaZ v w : ℚ) • a) := by
  obtain ⟨b, hb⟩ := kappa0_surjective (V := V) (kappa V v w a)
  have h1 := omegaH_kappa0 V b
  rw [hb, omegaH_kappa] at h1
  have h2 : b = (omegaZ v w : ℚ) • a := by
    have : (2 : ℚ) • b = (2 : ℚ) • ((omegaZ v w : ℚ) • a) := by
      rw [← h1, smul_smul]
    exact smul_right_injective V (two_ne_zero) this
  rw [← hb, h2]

/-- A group endomorphism `μ` of `U2` and a linear map `f` give a morphism of homology. -/
def trivHomRes (μ : U2 →* U2) (f : V →ₗ[ℚ] W) : TV V ⟶ Rep.res μ (TV W) :=
  Rep.ofHom ⟨f, fun _ => rfl⟩

theorem map_kappa_gen (μ : U2 →* U2) (f : V →ₗ[ℚ] W) (v w : U2) (a : V) :
    groupHomology.map μ (trivHomRes μ f) 2 (kappa V v w a) = kappa W (μ v) (μ w) (f a) := by
  rw [kappa_apply, kappa_apply]
  have h := groupHomology.H2π_comp_map (A := TV V) (B := TV W) μ (trivHomRes μ f)
  have h2 := congrArg (fun φ => φ.hom ⟨cyc V v w a, cyc_mem V v w a⟩) h
  have e : (groupHomology.mapCycles₂ (A := TV V) (B := TV W) μ (trivHomRes μ f)).hom
      ⟨cyc V v w a, cyc_mem V v w a⟩ = ⟨cyc W (μ v) (μ w) (f a), cyc_mem W _ _ _⟩ := by
    apply Subtype.ext
    erw [groupHomology.coe_mapCycles₂]
    simp only [groupHomology.chainsMap₂, cyc, trivHomRes]
    have := (Finsupp.mapRange.linearMap f : (U2 × U2 →₀ V) →ₗ[ℚ] (U2 × U2 →₀ W)).map_sub
      (Finsupp.mapDomain (Prod.map μ μ) (Finsupp.single (v, w) a))
      (Finsupp.mapDomain (Prod.map μ μ) (Finsupp.single (w, v) a))
    simpa [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Finsupp.mapDomain_single,
      Finsupp.mapDomain_sub] using this
  exact h2.trans (congrArg (groupHomology.H2π (TV W)).hom e)

theorem map_kappa0_gen [Module.Finite ℚ W] (μ : U2 →* U2) (f : V →ₗ[ℚ] W) (a : V) :
    groupHomology.map μ (trivHomRes μ f) 2 (kappa0 V a) =
      (omegaZ (μ e1) (μ e2) : ℚ) • kappa0 W (f a) := by
  rw [kappa0, map_kappa_gen, kappa_eq_smul, map_smul]

end TernaryPeriodPolynomials.Argument.HochschildSerre
