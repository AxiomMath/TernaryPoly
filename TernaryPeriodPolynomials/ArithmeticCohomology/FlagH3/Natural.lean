module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagH3.FrameIndep
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagH3.Sum7

@[expose] public section



/-!
# Naturality of the flag functional under group homomorphisms

Formalized by Claude Sonnet 5.5.

* `cocyclesMap_cocyclesMk`, `map_class_cocyclesMk`: `groupCohomology.map f φ n` sends the class of the cocycle `c` to the class of the cocycle `φ ∘ c ∘ f`;
* `FlagCohomDatum.lam_transport`: if a flag datum `D'` on `G` has cycle carried by `f : G →* H` to the cycle of a datum `D` on `H` (`chainEval D'.z (θ ∘ f) = chainEval D.z θ`), then `λ' ∘ f^* = λ`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FlagH3

open CategoryTheory

universe u

variable {k : Type u} [CommRing k] {G H : Type u} [Group G] [Group H]

set_option backward.isDefEq.respectTransparency false in
/-- The cocycles functor on cocycles of the inhomogeneous complex: the image of `cocyclesMk c` is the cocycle `φ ∘ c ∘ f`. -/
theorem cocyclesMap_cocyclesMk {A : Rep k H} {B : Rep k G} (f : G →* H) (φ : Rep.res f A ⟶ B) (n : ℕ)
    (c : (Fin n → H) → A) (hc : (inhomogeneousCochains.d A n).hom c = 0) :
    ∃ hc' : (inhomogeneousCochains.d B n).hom (fun x : Fin n → G => φ.hom (c (f ∘ x))) = 0,
      groupCohomology.cocyclesMap f φ n (groupCohomology.cocyclesMk c hc) =
        groupCohomology.cocyclesMk (fun x : Fin n → G => φ.hom (c (f ∘ x))) hc' := by
  have hcomm := (groupCohomology.cochainsMap f φ).comm n (n + 1)
  have key : (inhomogeneousCochains.d B n).hom (fun x : Fin n → G => φ.hom (c (f ∘ x))) =
      ((groupCohomology.cochainsMap f φ).f (n + 1)).hom ((inhomogeneousCochains.d A n).hom c) := by
    have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hcomm) c
    rw [groupCohomology.inhomogeneousCochains.d_def, groupCohomology.inhomogeneousCochains.d_def] at h
    exact h
  have hc' : (inhomogeneousCochains.d B n).hom (fun x : Fin n → G => φ.hom (c (f ∘ x))) = 0 := by
    rw [key, hc, map_zero]
  refine ⟨hc', ?_⟩
  have hmono : Function.Injective (groupCohomology.iCocycles B n).hom :=
    (ModuleCat.mono_iff_injective (groupCohomology.iCocycles B n)).1 inferInstance
  apply hmono
  have e1 := groupCohomology.iCocycles_mk (A := B) (fun x : Fin n → G => φ.hom (c (f ∘ x))) hc'
  have e2 := groupCohomology.iCocycles_mk (A := A) c hc
  have e3 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (HomologicalComplex.cyclesMap_i (groupCohomology.cochainsMap f φ) n)) (groupCohomology.cocyclesMk c hc)
  refine Eq.trans ?_ e1.symm
  refine Eq.trans e3 ?_
  show ((groupCohomology.cochainsMap f φ).f n).hom ((groupCohomology.iCocycles A n).hom (groupCohomology.cocyclesMk c hc)) = _
  rw [e2]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The map on cohomology of `(f, φ)` sends the class of `cocyclesMk c` to the class of `cocyclesMk (φ ∘ c ∘ f)`. -/
theorem map_class_cocyclesMk {A : Rep k H} {B : Rep k G} (f : G →* H) (φ : Rep.res f A ⟶ B) (n : ℕ)
    (c : (Fin n → H) → A) (hc : (inhomogeneousCochains.d A n).hom c = 0) :
    ∃ hc' : (inhomogeneousCochains.d B n).hom (fun x : Fin n → G => φ.hom (c (f ∘ x))) = 0,
      (groupCohomology.map f φ n).hom ((groupCohomology.π A n).hom (groupCohomology.cocyclesMk c hc)) =
        (groupCohomology.π B n).hom (groupCohomology.cocyclesMk (fun x : Fin n → G => φ.hom (c (f ∘ x))) hc') := by
  obtain ⟨hc', h⟩ := cocyclesMap_cocyclesMk f φ n c hc
  refine ⟨hc', ?_⟩
  have := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (groupCohomology.π_map f φ n)) (groupCohomology.cocyclesMk c hc)
  refine this.trans ?_
  show (groupCohomology.π B n).hom ((groupCohomology.cocyclesMap f φ n).hom (groupCohomology.cocyclesMk c hc)) = _
  rw [h]

/-- The identity comparison `Res_f (trivial) ⟶ trivial`. -/
def trivMap {G H : Type} [Group G] [Group H] (f : G →* H) : Rep.res f (Rep.trivial ℚ H ℚ) ⟶ Rep.trivial ℚ G ℚ :=
  Rep.ofHom
    { toFun := fun v => v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      isIntertwining' := fun g => by
        ext
        rfl }

set_option backward.isDefEq.respectTransparency false in
/-- **Transport of the flag functional along a group homomorphism**: if the cycle of `D'` is carried by `f` to the cycle of `D`
(`chainEval D'.z (θ ∘ f) = chainEval D.z θ`), then `λ' ∘ f^* = λ`. -/
theorem FlagCohomDatum.lam_transport {G H : Type} [Group G] [Group H] (D : FlagCohomDatum H) (D' : FlagCohomDatum G)
    (f : G →* H)
    (hz : ∀ θ : (Fin 3 → H) → ℚ, chainEval D'.z (fun x : Fin 3 → G => θ (f ∘ x)) = chainEval D.z θ)
    (y : groupCohomology (Rep.trivial ℚ H ℚ) 3) :
    D'.lam ((groupCohomology.map f (trivMap f) 3).hom y) = D.lam y := by
  obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective (groupCohomology.π (Rep.trivial ℚ H ℚ) 3)).1 inferInstance y
  have hmono : Function.Injective (groupCohomology.iCocycles (Rep.trivial ℚ H ℚ) 3).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  set θ := (groupCohomology.iCocycles (Rep.trivial ℚ H ℚ) 3).hom w with hθdef
  have hθ : (inhomogeneousCochains.d (Rep.trivial ℚ H ℚ) 3).hom θ = 0 := by
    have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      ((groupCohomology.inhomogeneousCochains (Rep.trivial ℚ H ℚ)).iCycles_d 3 4)) w
    rw [groupCohomology.inhomogeneousCochains.d_def] at h
    exact h
  have hw : w = groupCohomology.cocyclesMk θ hθ := by
    apply hmono
    exact (groupCohomology.iCocycles_mk (A := Rep.trivial ℚ H ℚ) θ hθ).symm
  obtain ⟨hc', h⟩ := map_class_cocyclesMk f (trivMap f) 3 θ hθ
  rw [hw, h]
  have e1 : D'.lam ((groupCohomology.π (Rep.trivial ℚ G ℚ) 3).hom
      (groupCohomology.cocyclesMk (fun x : Fin 3 → G => (trivMap f).hom (θ (f ∘ x))) hc')) =
      chainEval D'.z (fun x : Fin 3 → G => θ (f ∘ x)) :=
    D'.lam_cocycle (fun x : Fin 3 → G => θ (f ∘ x)) hc'
  have e2 : D.lam ((groupCohomology.π (Rep.trivial ℚ H ℚ) 3).hom (groupCohomology.cocyclesMk θ hθ)) = chainEval D.z θ :=
    D.lam_cocycle θ hθ
  rw [e2]
  exact e1.trans (hz θ)

set_option backward.isDefEq.respectTransparency false in
/-- Every class of `Hⁿ(G, A)` is the class of an inhomogeneous cocycle. -/
theorem exists_class_cocyclesMk {A : Rep k G} (n : ℕ) (x : groupCohomology A n) :
    ∃ (c : (Fin n → G) → A) (hc : (inhomogeneousCochains.d A n).hom c = 0),
      (groupCohomology.π A n).hom (groupCohomology.cocyclesMk c hc) = x := by
  obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective (groupCohomology.π A n)).1 inferInstance x
  have hmono : Function.Injective (groupCohomology.iCocycles A n).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hc : (inhomogeneousCochains.d A n).hom ((groupCohomology.iCocycles A n).hom w) = 0 := by
    have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      ((groupCohomology.inhomogeneousCochains A).iCycles_d n (n + 1))) w
    rw [groupCohomology.inhomogeneousCochains.d_def] at h
    exact h
  refine ⟨_, hc, ?_⟩
  congr 1
  apply hmono
  exact groupCohomology.iCocycles_mk (A := A) _ hc

/-- … with the cocycle proof as a free argument (proof irrelevance). -/
theorem map_class_cocyclesMk' {A : Rep k H} {B : Rep k G} (f : G →* H) (φ : Rep.res f A ⟶ B) (n : ℕ)
    (c : (Fin n → H) → A) (hc : (inhomogeneousCochains.d A n).hom c = 0)
    (hc' : (inhomogeneousCochains.d B n).hom (fun x : Fin n → G => φ.hom (c (f ∘ x))) = 0) :
    (groupCohomology.map f φ n).hom ((groupCohomology.π A n).hom (groupCohomology.cocyclesMk c hc)) =
      (groupCohomology.π B n).hom (groupCohomology.cocyclesMk (fun x : Fin n → G => φ.hom (c (f ∘ x))) hc') :=
  (map_class_cocyclesMk f φ n c hc).choose_spec

/-- **The Heisenberg cycle is natural**: a homomorphism carrying `(X', Y')` to `(X, Y)` carries the cycle to the cycle. -/
theorem chainEval_heisCycle_comp {G H : Type} [Group G] [Group H] (f : G →* H) (X' Y' : G) (X Y : H)
    (hX : f X' = X) (hY : f Y' = Y) (θ : (Fin 3 → H) → ℚ) :
    chainEval (heisCycle X' Y') (fun x : Fin 3 → G => θ (f ∘ x)) = chainEval (heisCycle X Y) θ := by
  have e1 : (fun x : Fin 3 → G => θ (f ∘ x)) =
      fun x : Fin 3 → G => (fun a b c : G => θ ![f a, f b, f c]) (x 0) (x 1) (x 2) := by
    funext x
    congr 1
    funext i
    fin_cases i <;> rfl
  have e0 : θ = fun x : Fin 3 → H => (fun a b c : H => θ ![a, b, c]) (x 0) (x 1) (x 2) := by
    funext x
    congr 1
    funext i
    fin_cases i <;> rfl
  have h1 := heisCycle_eval X' Y' (fun a b c : G => θ ![f a, f b, f c])
  have h0 := heisCycle_eval X Y (fun a b c : H => θ ![a, b, c])
  rw [e1, h1]
  conv_rhs => rw [e0]
  rw [h0]
  simp only [comm, map_mul, map_inv, hX, hY]

end TernaryPeriodPolynomials.Argument.FlagH3
