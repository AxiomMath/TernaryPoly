module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Level.ChangeShapiro

@[expose] public section


/-!
# Mackey decomposition of `Res_S Fun(G/Δ, E)` and the vanishing criterion for the restriction of an induced class

Formalized by Claude Sonnet 5.5.

Let `V = permRep ρ Δ = Fun(G/Δ, E)` (see `LevelChangeShapiro`), `S ≤ G` a subgroup and assume the `S`-orbits on `G/Δ` are finitely many.
For `x ∈ G/Δ` the `S`-orbit `S·x ≅ S/Stab_S(x)` gives morphisms of `S`-modules
`jRep : Fun(S/Stab_S x, E) ⟶ Res_S V` (extension by zero) and `qRep : Res_S V ⟶ Fun(S/Stab_S x, E)` (restriction to the orbit) with
`jRep ≫ qRep = 𝟙` (`jRep_qRep`) and `∑_orbits qRep ≫ jRep = 𝟙` (`sum_qRep_jRep`); `e_O = jL ∘ qL` are the orthogonal idempotents of `V`
cut out by the orbits (`sum_jL_qL`).  Since `H²(S, -)` is additive (`functorAdditive`, `h2Hom_sum`), every class `r ∈ H²(S, Res_S V)`
is the sum of its orbit components (`res_decomp`).

The component of `res_S c_V` at the orbit of `uΔ` corresponds, under the Shapiro isomorphism `PhiH`, to the `uΔ`-coordinate of the
restriction of `c_V` to `S ∩ uΔu⁻¹` (`phi_qRep`, a composition of `EdgeNat.h2Map`s via `h2Map_comp`).  Consequently
`res_eq_zero_of_coords`: if all coordinates `coordH (res_{S ∩ uΔu⁻¹} c_V)` vanish, then `res_S c_V = 0`.  Combined with `exists_ind_class`
(whose coordinates are the pull-backs of the class `c ∈ H²(Δ, E)` along `k ↦ u⁻¹ k u`), the restriction of the induced class to a face group `S`
of `G` vanishes as soon as `c` restricts to zero on the groups `Δ ∩ S` (for `Δ` normal in `G`, `S ∩ uΔu⁻¹ = S ∩ Δ`).
-/

open CategoryTheory GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.SphericalDetection.Helpers

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

section Orbit

open MulAction

variable {G E : Type} [Group G] [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E) {Δ : Subgroup G}
  (S : Subgroup G) (x : G ⧸ Δ)

/-- The bijection between the `S`-orbit of `x` and `S / Stab_S(x)`. -/
def orbEq : orbit ↥S x ≃ (↥S ⧸ stabilizer ↥S x) := orbitEquivQuotientStabilizer ↥S x

theorem orbEq_symm_mk (t : S) : ((orbEq S x).symm (t : ↥S ⧸ stabilizer ↥S x) : G ⧸ Δ) = t • x := rfl

theorem smul_mem_orbit' (s : S) {y : G ⧸ Δ} (hy : y ∈ orbit ↥S x) : s • y ∈ orbit ↥S x := by
  obtain ⟨t, rfl⟩ := hy
  exact ⟨s * t, mul_smul s t x⟩

theorem orbEq_smul (s : S) (y : orbit ↥S x) :
    orbEq S x ⟨s • (y : G ⧸ Δ), smul_mem_orbit' S x s y.2⟩ = s • orbEq S x y := by
  obtain ⟨y, t, rfl⟩ := y
  have h1 : orbEq S x ⟨t • x, ⟨t, rfl⟩⟩ = (t : ↥S ⧸ stabilizer ↥S x) := by
    rw [← Equiv.eq_symm_apply]
    rfl
  have h2 : orbEq S x ⟨s • t • x, smul_mem_orbit' S x s ⟨t, rfl⟩⟩ = ((s * t : ↥S) : ↥S ⧸ stabilizer ↥S x) := by
    rw [← Equiv.eq_symm_apply]
    apply Subtype.ext
    exact (mul_smul s t x).symm
  rw [h2]
  change _ = s • orbEq S x ⟨t • x, ⟨t, rfl⟩⟩
  rw [h1]
  rfl

theorem orbEq_symm_smul (s : S) (w : ↥S ⧸ stabilizer ↥S x) :
    ((orbEq S x).symm (s • w) : G ⧸ Δ) = s • ((orbEq S x).symm w : G ⧸ Δ) := by
  have h := orbEq_smul S x s ((orbEq S x).symm w)
  rw [Equiv.apply_symm_apply] at h
  have h2 : (orbEq S x).symm (s • w) = ⟨s • ((orbEq S x).symm w : G ⧸ Δ), smul_mem_orbit' S x s ((orbEq S x).symm w).2⟩ := by
    rw [Equiv.symm_apply_eq]
    exact h.symm
  rw [h2]

open Classical in
/-- Extension by zero along `S/Stab ≅ S·x ⊆ G/Δ`. -/
def jL : ((↥S ⧸ stabilizer ↥S x) → E) →ₗ[ℂ] ((G ⧸ Δ) → E) where
  toFun φ y := if h : y ∈ orbit ↥S x then φ (orbEq S x ⟨y, h⟩) else 0
  map_add' φ ψ := by
    funext y
    by_cases h : y ∈ orbit ↥S x <;> simp [h]
  map_smul' a φ := by
    funext y
    by_cases h : y ∈ orbit ↥S x <;> simp [h]

/-- Restriction to the orbit of `x`. -/
def qL : ((G ⧸ Δ) → E) →ₗ[ℂ] ((↥S ⧸ stabilizer ↥S x) → E) where
  toFun f w := f ((orbEq S x).symm w : G ⧸ Δ)
  map_add' f g := by funext w; rfl
  map_smul' a f := by funext w; rfl

theorem qL_jL (φ : (↥S ⧸ stabilizer ↥S x) → E) : qL S x (jL S x φ) = φ := by
  funext w
  change jL S x φ ((orbEq S x).symm w : G ⧸ Δ) = φ w
  classical
  simp [jL]

theorem jL_qL_of_mem (f : (G ⧸ Δ) → E) {y : G ⧸ Δ} (hy : y ∈ orbit ↥S x) : jL S x (qL S x f) y = f y := by
  classical
  simp [jL, qL, hy]

theorem jL_qL_of_not_mem (f : (G ⧸ Δ) → E) {y : G ⧸ Δ} (hy : y ∉ orbit ↥S x) : jL S x (qL S x f) y = 0 := by
  classical
  simp [jL, hy]

theorem mem_orbit_inv (s : S) {y : G ⧸ Δ} : s⁻¹ • y ∈ orbit ↥S x ↔ y ∈ orbit ↥S x := by
  constructor
  · intro h
    have := smul_mem_orbit' S x s h
    simpa using this
  · exact smul_mem_orbit' S x s⁻¹

/-- Extension by zero as a morphism of `S`-modules `Fun(S/Stab, E) ⟶ Res_S Fun(G/Δ, E)`. -/
def jRep : Rep.of (permRep (ρ.comp S.subtype) (stabilizer ↥S x)) ⟶ Rep.res S.subtype (Rep.of (permRep ρ Δ)) :=
  Rep.ofHom ⟨jL S x, fun s => by
    ext φ y
    classical
    change jL S x (permRep (ρ.comp S.subtype) (stabilizer ↥S x) s φ) y = permRep ρ Δ s.val (jL S x φ) y
    rw [permRep_apply]
    by_cases hy : y ∈ orbit ↥S x
    · have hy' : s⁻¹ • y ∈ orbit ↥S x := (mem_orbit_inv S x s).mpr hy
      have e1 : jL S x (permRep (ρ.comp S.subtype) (stabilizer ↥S x) s φ) y =
          permRep (ρ.comp S.subtype) (stabilizer ↥S x) s φ (orbEq S x ⟨y, hy⟩) := by simp [jL, hy]
      have e2 : jL S x φ (s.val⁻¹ • y) = φ (orbEq S x ⟨s⁻¹ • y, hy'⟩) := by simp only [jL]; exact dite_eq_left hy'
      rw [e1, e2, permRep_apply]
      have e3 := orbEq_smul S x s⁻¹ ⟨y, hy⟩
      change ρ s.val (φ (s⁻¹ • orbEq S x ⟨y, hy⟩)) = ρ s.val (φ (orbEq S x ⟨s⁻¹ • y, hy'⟩))
      rw [← e3]
    · have hy' : ¬ (s⁻¹ • y ∈ orbit ↥S x) := fun h => hy ((mem_orbit_inv S x s).mp h)
      have e1 : jL S x (permRep (ρ.comp S.subtype) (stabilizer ↥S x) s φ) y = 0 := by simp [jL, hy]
      have e2 : jL S x φ (s.val⁻¹ • y) = 0 := by simp [jL]; intro h; exact absurd h hy'
      rw [e1, e2, map_zero]⟩

/-- Restriction to the orbit of `x`, as a morphism of `S`-modules `Res_S Fun(G/Δ, E) ⟶ Fun(S/Stab, E)`. -/
def qRep : Rep.res S.subtype (Rep.of (permRep ρ Δ)) ⟶ Rep.of (permRep (ρ.comp S.subtype) (stabilizer ↥S x)) :=
  Rep.ofHom ⟨qL S x, fun s => by
    ext f w
    change qL S x (permRep ρ Δ s.val f) w = permRep (ρ.comp S.subtype) (stabilizer ↥S x) s (qL S x f) w
    rw [permRep_apply]
    change permRep ρ Δ s.val f ((orbEq S x).symm w : G ⧸ Δ) = ρ s.val (qL S x f (s⁻¹ • w))
    rw [permRep_apply]
    change ρ s.val (f (s.val⁻¹ • ((orbEq S x).symm w : G ⧸ Δ))) = ρ s.val (f ((orbEq S x).symm (s⁻¹ • w) : G ⧸ Δ))
    rw [orbEq_symm_smul]
    rfl⟩

theorem jRep_qRep : jRep ρ S x ≫ qRep ρ S x = 𝟙 _ := by
  ext φ w
  exact congrFun (qL_jL S x φ) w

end Orbit


section Decomp

open MulAction

variable {G E : Type} [Group G] [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E) {Δ : Subgroup G}
  (S : Subgroup G)

theorem out_mem_orbit_iff (o : orbitRel.Quotient ↥S (G ⧸ Δ)) (y : G ⧸ Δ) :
    y ∈ orbit ↥S (Quotient.out o : G ⧸ Δ) ↔ (Quotient.mk'' y : orbitRel.Quotient ↥S (G ⧸ Δ)) = o := by
  rw [← orbitRel.Quotient.mem_orbit, orbitRel.Quotient.orbit_eq_orbit_out o Quotient.out_eq']

theorem sum_jL_qL [Fintype (orbitRel.Quotient ↥S (G ⧸ Δ))] (f : (G ⧸ Δ) → E) (y : G ⧸ Δ) :
    ∑ o : orbitRel.Quotient ↥S (G ⧸ Δ), jL S (Quotient.out o : G ⧸ Δ) (qL S (Quotient.out o : G ⧸ Δ) f) y = f y := by
  rw [Finset.sum_eq_single (Quotient.mk'' y : orbitRel.Quotient ↥S (G ⧸ Δ))]
  · exact jL_qL_of_mem S _ f ((out_mem_orbit_iff S _ y).mpr rfl)
  · intro o _ ho
    exact jL_qL_of_not_mem S _ f (fun h => ho ((out_mem_orbit_iff S o y).mp h).symm)
  · intro h; exact absurd (Finset.mem_univ _) h

theorem sum_qRep_jRep [Fintype (orbitRel.Quotient ↥S (G ⧸ Δ))] :
    ∑ o : orbitRel.Quotient ↥S (G ⧸ Δ), qRep ρ S (Quotient.out o : G ⧸ Δ) ≫ jRep ρ S (Quotient.out o : G ⧸ Δ) =
      𝟙 (Rep.res S.subtype (Rep.of (permRep ρ Δ))) := by
  ext f y
  classical
  have key : ∀ (T : Finset (orbitRel.Quotient ↥S (G ⧸ Δ))),
      (∑ o ∈ T, qRep ρ S (Quotient.out o : G ⧸ Δ) ≫ jRep ρ S (Quotient.out o : G ⧸ Δ)).hom f y =
        ∑ o ∈ T, jL S (Quotient.out o : G ⧸ Δ) (qL S (Quotient.out o : G ⧸ Δ) f) y := by
    intro T
    induction T using Finset.induction_on with
    | empty => rfl
    | insert a T ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Rep.add_hom]
      have e : (qRep ρ S (Quotient.out a : G ⧸ Δ) ≫ jRep ρ S (Quotient.out a : G ⧸ Δ)).hom f y +
          (∑ o ∈ T, qRep ρ S (Quotient.out o : G ⧸ Δ) ≫ jRep ρ S (Quotient.out o : G ⧸ Δ)).hom f y =
          jL S (Quotient.out a : G ⧸ Δ) (qL S (Quotient.out a : G ⧸ Δ) f) y +
            ∑ o ∈ T, jL S (Quotient.out o : G ⧸ Δ) (qL S (Quotient.out o : G ⧸ Δ) f) y := by
        rw [ih]; rfl
      exact e
  exact (key Finset.univ).trans (sum_jL_qL S f y)

end Decomp

section H2Hom

open MulAction

/-- The additivity of `H^n(G, -)` on morphisms of representations (not an instance in Mathlib at this revision). -/
instance functorAdditive {G : Type} [Group G] (n : ℕ) : (groupCohomology.functor ℂ G n).Additive where
  map_add {X Y f g} := by
    change groupCohomology.map (MonoidHom.id G) (f + g) n =
      groupCohomology.map (MonoidHom.id G) f n + groupCohomology.map (MonoidHom.id G) g n
    have h := (groupCohomology.cochainsFunctor ℂ G).map_add (f := f) (g := g)
    unfold groupCohomology.map
    have h' : groupCohomology.cochainsMap (MonoidHom.id G) (f + g) =
        groupCohomology.cochainsMap (MonoidHom.id G) f + groupCohomology.cochainsMap (MonoidHom.id G) g := h
    rw [h', HomologicalComplex.homologyMap_add]
    rfl

variable {S : Type} [Group S]

/-- The map `H²(S, A) → H²(S, B)` induced by a morphism of `S`-modules. -/
def h2Hom {A B : Rep ℂ S} (f : A ⟶ B) : groupCohomology.H2 A →ₗ[ℂ] groupCohomology.H2 B :=
  (groupCohomology.map (MonoidHom.id S) f 2).hom

theorem h2Hom_comp {A B C : Rep ℂ S} (f : A ⟶ B) (g : B ⟶ C) (r : groupCohomology.H2 A) :
    h2Hom (f ≫ g) r = h2Hom g (h2Hom f r) := by
  have := congrArg (fun φ => φ.hom r) (groupCohomology.map_id_comp f g 2)
  exact this

theorem h2Hom_id {A : Rep ℂ S} (r : groupCohomology.H2 A) : h2Hom (𝟙 A) r = r := by
  have := congrArg (fun φ => φ.hom r) (groupCohomology.map_id (B := A) (n := 2))
  exact this

theorem h2Hom_add {A B : Rep ℂ S} (f g : A ⟶ B) (r : groupCohomology.H2 A) :
    h2Hom (f + g) r = h2Hom f r + h2Hom g r := by
  have := congrArg (fun φ => φ.hom r)
    (Functor.map_add (F := groupCohomology.functor ℂ S 2) (f := f) (g := g))
  exact this

theorem h2Hom_zero {A B : Rep ℂ S} (r : groupCohomology.H2 A) : h2Hom (0 : A ⟶ B) r = 0 := by
  have := congrArg (fun φ => φ.hom r)
    (Functor.map_zero (groupCohomology.functor ℂ S 2) A B)
  exact this

theorem h2Hom_sum {A B : Rep ℂ S} {ι : Type} (T : Finset ι) (F : ι → (A ⟶ B)) (r : groupCohomology.H2 A) :
    h2Hom (∑ i ∈ T, F i) r = ∑ i ∈ T, h2Hom (F i) r := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using h2Hom_zero (A := A) (B := B) r
  | insert a T ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h2Hom_add, ih]

end H2Hom

section H2MapAlgebra

variable {K H G : Type} [Group K] [Group H] [Group G]

theorem compHT (α₁ : H →* G) (α₂ : K →* H) (A : Rep ℂ G) (B : Rep ℂ H) (C : Rep ℂ K)
    (T₁ : A →ₗ[ℂ] B) (hT₁ : ∀ (g : H) (v : A), T₁ (A.ρ (α₁ g) v) = B.ρ g (T₁ v))
    (T₂ : B →ₗ[ℂ] C) (hT₂ : ∀ (g : K) (v : B), T₂ (B.ρ (α₂ g) v) = C.ρ g (T₂ v)) (g : K) (v : A) :
    (T₂ ∘ₗ T₁) (A.ρ ((α₁.comp α₂) g) v) = C.ρ g ((T₂ ∘ₗ T₁) v) := by
  simp only [LinearMap.comp_apply, MonoidHom.comp_apply]
  rw [hT₁, hT₂]

theorem h2Map_comp (α₁ : H →* G) (α₂ : K →* H) (A : Rep ℂ G) (B : Rep ℂ H) (C : Rep ℂ K)
    (T₁ : A →ₗ[ℂ] B) (hT₁ : ∀ (g : H) (v : A), T₁ (A.ρ (α₁ g) v) = B.ρ g (T₁ v))
    (T₂ : B →ₗ[ℂ] C) (hT₂ : ∀ (g : K) (v : B), T₂ (B.ρ (α₂ g) v) = C.ρ g (T₂ v))
    (x : groupCohomology.H2 A) :
    EdgeNat.h2Map α₂ B C T₂ hT₂ (EdgeNat.h2Map α₁ A B T₁ hT₁ x) =
      EdgeNat.h2Map (α₁.comp α₂) A C (T₂ ∘ₗ T₁) (compHT α₁ α₂ A B C T₁ hT₁ T₂ hT₂) x := by
  have key := congrArg (fun φ => φ.hom x) (groupCohomology.map_comp α₁ α₂ (EdgeNat.comparison α₁ A B T₁ hT₁)
    (EdgeNat.comparison α₂ B C T₂ hT₂) 2)
  have hc := groupCohomology.map_congr (A := A) (B := C) (f := α₁.comp α₂) (g := α₁.comp α₂)
    (φ := ((Rep.resFunctor α₂).map (EdgeNat.comparison α₁ A B T₁ hT₁) ≫ EdgeNat.comparison α₂ B C T₂ hT₂))
    (ψ := EdgeNat.comparison (α₁.comp α₂) A C (T₂ ∘ₗ T₁) (compHT α₁ α₂ A B C T₁ hT₁ T₂ hT₂)) rfl rfl 2
  exact key.symm.trans (congrArg (fun φ => φ.hom x) hc)

theorem h2Map_congr {α α' : H →* G} (hα : α = α') (A : Rep ℂ G) (B : Rep ℂ H) {T T' : A →ₗ[ℂ] B}
    (hT : ∀ (g : H) (v : A), T (A.ρ (α g) v) = B.ρ g (T v))
    (hT' : ∀ (g : H) (v : A), T' (A.ρ (α' g) v) = B.ρ g (T' v)) (hTT : T = T') (x : groupCohomology.H2 A) :
    EdgeNat.h2Map α A B T hT x = EdgeNat.h2Map α' A B T' hT' x := by
  subst hα; subst hTT; rfl

theorem twoCohomologyRestriction_eq_h2Map (ι : H →* G) (A : Rep ℂ G) (x : groupCohomology.H2 A) :
    twoCohomologyRestriction ι A x = EdgeNat.h2Map ι A (Rep.res ι A) LinearMap.id (fun _ _ => rfl) x := rfl

theorem h2Hom_eq_h2Map (A B : Rep ℂ G) (f : A ⟶ B) (x : groupCohomology.H2 A) :
    h2Hom f x = EdgeNat.h2Map (MonoidHom.id G) A B f.hom.toLinearMap (fun g v => Rep.hom_comm_apply f g v) x := rfl

end H2MapAlgebra

section Final

open MulAction

variable {G E : Type} [Group G] [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E) (Δ S : Subgroup G)

theorem mem_stabilizer_quot_iff (u : G) (s : S) :
    s ∈ stabilizer ↥S (u : G ⧸ Δ) ↔ u⁻¹ * s.val * u ∈ Δ := by
  rw [MulAction.mem_stabilizer_iff]
  change ((s.val * u : G) : G ⧸ Δ) = (u : G ⧸ Δ) ↔ _
  rw [QuotientGroup.eq, ← inv_mem_iff]
  simp [mul_assoc]

/-- `S ∩ uΔu⁻¹`, as a subgroup of `G`. -/
def stabAt (u : G) : Subgroup G where
  carrier := {g | g ∈ S ∧ u⁻¹ * g * u ∈ Δ}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨S.mul_mem ha hb, ?_⟩
    have := Δ.mul_mem ha' hb'
    simpa [mul_assoc] using this
  one_mem' := ⟨S.one_mem, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨S.inv_mem ha, ?_⟩
    have := Δ.inv_mem ha'
    simpa [mul_assoc] using this

theorem mem_stabAt (u g : G) : g ∈ stabAt Δ S u ↔ g ∈ S ∧ u⁻¹ * g * u ∈ Δ := Iff.rfl

theorem stabAt_hu (u : G) : ∀ k ∈ stabAt Δ S u, u⁻¹ * k * u ∈ Δ := fun _ hk => hk.2

/-- The stabilizer of `uΔ` in `S` maps isomorphically onto `S ∩ uΔu⁻¹`. -/
def stabToAt (u : G) : stabilizer ↥S (u : G ⧸ Δ) →* stabAt Δ S u where
  toFun s := ⟨s.val.val, s.val.2, (mem_stabilizer_quot_iff Δ S u s.val).mp s.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem stabToAt_hT (u : G) (g : stabilizer ↥S (u : G ⧸ Δ)) (v : Rep.of (ρ.comp (stabAt Δ S u).subtype)) :
    (LinearMap.id : E →ₗ[ℂ] E)
      ((Rep.of (ρ.comp (stabAt Δ S u).subtype)).ρ (stabToAt Δ S u g) v) =
    (Rep.of ((ρ.comp S.subtype).comp (stabilizer ↥S (u : G ⧸ Δ)).subtype)).ρ g (LinearMap.id (R := ℂ) (M := E) v) := rfl

theorem phi_qRep (cV : groupCohomology.H2 (Rep.of (permRep ρ Δ))) (u : G) :
    PhiH (ρ.comp S.subtype) (stabilizer ↥S (u : G ⧸ Δ))
        (h2Hom (qRep ρ S (u : G ⧸ Δ)) (twoCohomologyRestriction S.subtype (Rep.of (permRep ρ Δ)) cV)) =
      EdgeNat.h2Map (stabToAt Δ S u) (Rep.of (ρ.comp (stabAt Δ S u).subtype))
        (Rep.of ((ρ.comp S.subtype).comp (stabilizer ↥S (u : G ⧸ Δ)).subtype)) LinearMap.id (stabToAt_hT ρ Δ S u)
        (coordH ρ Δ (stabAt Δ S u) u (stabAt_hu Δ S u)
          (twoCohomologyRestriction (stabAt Δ S u).subtype (Rep.of (permRep ρ Δ)) cV)) := by
  simp only [PhiH, LinearMap.comp_apply, coordH, twoCohomologyRestriction_eq_h2Map, h2Hom_eq_h2Map]
  simp only [h2Map_comp]
  refine h2Map_congr ?_ _ _ _ _ ?_ cV
  · ext k; rfl
  · ext f
    change f (((orbEq S (u : G ⧸ Δ)).symm ((1 : ↥S) : ↥S ⧸ stabilizer ↥S (u : G ⧸ Δ)) : G ⧸ Δ)) = f (u : G ⧸ Δ)
    rw [orbEq_symm_mk, one_smul]


theorem res_decomp [Fintype (orbitRel.Quotient ↥S (G ⧸ Δ))]
    (r : groupCohomology.H2 (Rep.res S.subtype (Rep.of (permRep ρ Δ)))) :
    ∑ o : orbitRel.Quotient ↥S (G ⧸ Δ),
        h2Hom (jRep ρ S (Quotient.out o : G ⧸ Δ)) (h2Hom (qRep ρ S (Quotient.out o : G ⧸ Δ)) r) = r := by
  calc _ = ∑ o : orbitRel.Quotient ↥S (G ⧸ Δ),
        h2Hom (qRep ρ S (Quotient.out o : G ⧸ Δ) ≫ jRep ρ S (Quotient.out o : G ⧸ Δ)) r :=
        Finset.sum_congr rfl fun o _ => (h2Hom_comp _ _ r).symm
    _ = h2Hom (∑ o : orbitRel.Quotient ↥S (G ⧸ Δ),
        qRep ρ S (Quotient.out o : G ⧸ Δ) ≫ jRep ρ S (Quotient.out o : G ⧸ Δ)) r := (h2Hom_sum _ _ r).symm
    _ = r := by rw [sum_qRep_jRep, h2Hom_id]

/-- **Mackey vanishing criterion.**  If every `uΔ`-coordinate of `res_{S ∩ uΔu⁻¹} c_V` vanishes, then `res_S c_V = 0`. -/
theorem res_eq_zero_of_coords [Fintype (orbitRel.Quotient ↥S (G ⧸ Δ))]
    (cV : groupCohomology.H2 (Rep.of (permRep ρ Δ)))
    (h : ∀ u : G, coordH ρ Δ (stabAt Δ S u) u (stabAt_hu Δ S u)
      (twoCohomologyRestriction (stabAt Δ S u).subtype (Rep.of (permRep ρ Δ)) cV) = 0) :
    twoCohomologyRestriction S.subtype (Rep.of (permRep ρ Δ)) cV = 0 := by
  rw [← res_decomp ρ Δ S (twoCohomologyRestriction S.subtype (Rep.of (permRep ρ Δ)) cV)]
  refine Finset.sum_eq_zero fun o _ => ?_
  have key : ∀ x : G ⧸ Δ, h2Hom (qRep ρ S x) (twoCohomologyRestriction S.subtype (Rep.of (permRep ρ Δ)) cV) = 0 := by
    intro x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    apply PhiH_injective (ρ.comp S.subtype) (stabilizer ↥S (u : G ⧸ Δ))
    rw [phi_qRep, h u, map_zero, map_zero]
  rw [key, map_zero]

/-- **The induced class of `c` restricts to zero on `S`** as soon as the pull-backs `κ_u^* c` of `c` along the conjugations `S ∩ uΔu⁻¹ → Δ`
vanish; its Shapiro coordinate is `c`. -/
theorem exists_ind_class_res_zero [Fintype (orbitRel.Quotient ↥S (G ⧸ Δ))]
    (c : groupCohomology.H2 (Rep.of (ρ.comp Δ.subtype)))
    (hc : ∀ u : G, EdgeNat.h2Map (kappa Δ (stabAt Δ S u) u (stabAt_hu Δ S u)) (Rep.of (ρ.comp Δ.subtype))
      (Rep.of (ρ.comp (stabAt Δ S u).subtype)) (ρ u) (kappa_hT ρ Δ (stabAt Δ S u) u (stabAt_hu Δ S u)) c = 0) :
    ∃ cV : groupCohomology.H2 (Rep.of (permRep ρ Δ)),
      PhiH ρ Δ cV = c ∧ twoCohomologyRestriction S.subtype (Rep.of (permRep ρ Δ)) cV = 0 := by
  obtain ⟨cV, hcV⟩ := exists_ind_class ρ Δ c
  refine ⟨cV, ?_, res_eq_zero_of_coords ρ Δ S cV fun u => ?_⟩
  · have := hcV Δ 1 (fun k hk => by simpa using hk)
    exact this.trans (h2Map_kappa_one ρ Δ c)
  · rw [hcV (stabAt Δ S u) u (stabAt_hu Δ S u)]
    exact hc u

end Final

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
