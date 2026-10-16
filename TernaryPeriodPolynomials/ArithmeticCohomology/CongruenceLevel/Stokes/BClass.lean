module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Const.Rel
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagH3.FlagCoords

@[expose] public section


/-!
# Classes of explicit `3`-cocycles on stabilizers, and their transport along group homomorphisms

Formalized by Claude Sonnet 5.5.

For a subgroup `S ≤ Γ(6)` and an explicit rational `3`-cocycle `T3` of the group `S`, `clsRes S T3` is its class in `H³(S; ℚ)` in the form `groupCohomology (Rep.res S.subtype 𝟙_) 3` used by the corner
decomposition (via the `resTrivialEquiv`).  `map_cocycleClass`: the map induced by a group homomorphism `f` and a comparison `φ` sends the class of `θ` to the class of `φ ∘ θ ∘ f`;
`transport_clsRes`: the conjugation transport `lineTransportAt` sends `clsRes S T3` to `clsRes K (T3 ∘ f)`.
-/

open CategoryTheory MonoidalCategory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.FlagH3 groupCohomology Rep
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

section Generic

variable {G H : Type} [Group G] [Group H] (A : Rep.{0, 0, 0} ℚ H) (B : Rep.{0, 0, 0} ℚ G) (f : G →* H) (φ : res f A ⟶ B)

theorem map_cochain_cocycle (θ : (Fin 3 → H) → A) (hθ : inhomogeneousCochains.d A 3 θ = 0) :
    inhomogeneousCochains.d B 3 (fun x : Fin 3 → G => φ.hom (θ (f ∘ x))) = 0 := by
  have h := congrArg (fun t => ModuleCat.Hom.hom t (θ : (inhomogeneousCochains A).X 3)) ((cochainsMap f φ).comm 3 4)
  change (inhomogeneousCochains B).d 3 4 ((cochainsMap f φ).f 3 θ) = (cochainsMap f φ).f 4 ((inhomogeneousCochains A).d 3 4 θ) at h
  have h0 : (inhomogeneousCochains A).d 3 4 θ = 0 := hθ
  rw [h0, map_zero] at h
  exact h

theorem map_cocycleClass (θ : (Fin 3 → H) → A) (hθ : inhomogeneousCochains.d A 3 θ = 0) :
    groupCohomology.map f φ 3 (π A 3 (cocyclesMk θ hθ)) =
      π B 3 (cocyclesMk (fun x : Fin 3 → G => φ.hom (θ (f ∘ x))) (map_cochain_cocycle A B f φ θ hθ)) := by
  have e := groupCohomology.π_map_apply f φ 3 (cocyclesMk θ hθ)
  rw [e]
  congr 1
  apply (ModuleCat.mono_iff_injective (iCocycles B 3)).1 inferInstance
  have h1 := congrArg (fun t => t.hom (cocyclesMk θ hθ)) (HomologicalComplex.cyclesMap_i (cochainsMap f φ) 3)
  change (iCocycles B 3) ((cocyclesMap f φ 3) (cocyclesMk θ hθ)) = ((cochainsMap f φ).f 3) ((iCocycles A 3) (cocyclesMk θ hθ)) at h1
  rw [h1, iCocycles_mk, iCocycles_mk]
  rfl

end Generic

section Cls

variable (S : Subgroup Γ6)

/-- The class in `H³(S; ℚ)` (in the `Rep.res` form) of an explicit rational `3`-cocycle of the group `S`. -/
def clsRes (T3 : (Fin 3 → S) → ℚ) (hT : dThree T3 = 0) :
    groupCohomology (Rep.res S.subtype (𝟙_ (Rep.{0} ℚ Γ6))) 3 :=
  (resTrivialEquiv Γ6 S 3).symm (cocycleClass T3 hT)

/-- The identity comparison from the trivial representation of `S` to the restriction of the trivial representation of `Γ(6)`. -/
def trivToRes : Rep.res (MonoidHom.id S) (Rep.trivial ℚ S ℚ) ⟶ Rep.res S.subtype (𝟙_ (Rep.{0} ℚ Γ6)) :=
  ofHom ⟨LinearEquiv.refl ℚ ℚ, fun _ => rfl⟩

theorem clsRes_eq (T3 : (Fin 3 → S) → ℚ) (hT : dThree T3 = 0) :
    clsRes S T3 hT = (groupCohomology.map (MonoidHom.id S) (trivToRes S) 3) (cocycleClass T3 hT) := rfl

theorem dThree_comp {K S : Type} [Group K] [Group S] (f : K →* S) (T3 : (Fin 3 → S) → ℚ) (hT : dThree T3 = 0) :
    dThree (fun x : Fin 3 → K => T3 (f ∘ x)) = 0 := by
  have e3 : ∀ a b c : K, (fun x : Fin 3 => f (![a, b, c] x)) = ![f a, f b, f c] := by
    intro a b c; funext x; fin_cases x <;> rfl
  funext g
  have h := congrFun hT (f ∘ g)
  rw [dThree_apply] at h ⊢
  simp only [Function.comp_def] at h ⊢
  simp only [e3] at h ⊢
  simpa using h

example (γ : Γ6) (x : ℚ) : (𝟙_ (Rep.{0} ℚ Γ6)).ρ γ x = x := rfl

theorem transport_clsRes {K : Subgroup Γ6} (f : K →* S)
    (φ : Rep.res f (Rep.res S.subtype (𝟙_ (Rep.{0} ℚ Γ6))) ⟶ Rep.res K.subtype (𝟙_ (Rep.{0} ℚ Γ6)))
    (hφ : ∀ x, φ.hom x = x) (T3 : (Fin 3 → S) → ℚ) (hT : dThree T3 = 0) :
    groupCohomology.map f φ 3 (clsRes S T3 hT) = clsRes K (fun x => T3 (f ∘ x)) (dThree_comp f T3 hT) := by
  rw [clsRes_eq S, clsRes_eq K]
  have c1 : ∀ (G : Type) [Group G] (T : (Fin 3 → G) → ℚ) (h : dThree T = 0), cocycleClass T h = (π (Rep.trivial ℚ G ℚ) 3) (cocyclesMk T h) := fun _ _ _ _ => rfl
  rw [c1, c1]
  rw [map_cocycleClass (Rep.trivial ℚ S ℚ) _ (MonoidHom.id S) (trivToRes S) T3 hT]
  rw [map_cocycleClass _ _ f φ]
  rw [map_cocycleClass (Rep.trivial ℚ K ℚ) _ (MonoidHom.id K) (trivToRes K) _ (dThree_comp f T3 hT)]
  congr 3
  funext x
  simp [hφ, trivToRes]

end Cls

section Transport

open TernaryPoly.BoundaryFaceResolutionComparison
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)

/-- **The line transport sends the class of a cocycle to the class of the pulled back cocycle.** -/
theorem lineTransportAt_cls (o : labelOrbits Γ6 Flag) (γ : Γ6) (hγ : γ • (flagLineOrbit o).out = flagLineOf o.out)
    (T3 : (Fin 3 → MulAction.stabilizer Γ6 (flagLineOrbit o).out) → ℚ) (hT : dThree T3 = 0) :
    (lineTransportAt o γ hγ).hom (clsRes (MulAction.stabilizer Γ6 (flagLineOrbit o).out) T3 hT) =
      clsRes (MulAction.stabilizer Γ6 o.out)
        (fun x => T3 (conjStabHom γ (flagLineOrbit o).out (MulAction.stabilizer Γ6 o.out) (stab_fixes_line_of o γ hγ) ∘ x))
        (dThree_comp _ T3 hT) :=
  transport_clsRes _ _ _ (fun _ => rfl) T3 hT

theorem planeTransportAt_cls (o : labelOrbits Γ6 Flag) (γ : Γ6) (hγ : γ • (flagPlaneOrbit o).out = flagPlaneOf o.out)
    (T3 : (Fin 3 → MulAction.stabilizer Γ6 (flagPlaneOrbit o).out) → ℚ) (hT : dThree T3 = 0) :
    (planeTransportAt o γ hγ).hom (clsRes (MulAction.stabilizer Γ6 (flagPlaneOrbit o).out) T3 hT) =
      clsRes (MulAction.stabilizer Γ6 o.out)
        (fun x => T3 (conjStabHom γ (flagPlaneOrbit o).out (MulAction.stabilizer Γ6 o.out) (stab_fixes_plane_of o γ hγ) ∘ x))
        (dThree_comp _ T3 hT) :=
  transport_clsRes _ _ _ (fun _ => rfl) T3 hT

end Transport

end TernaryPeriodPolynomials.Argument.GammaNStokes
