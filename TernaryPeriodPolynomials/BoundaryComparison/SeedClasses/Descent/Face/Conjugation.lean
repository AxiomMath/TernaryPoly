module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.EdgeNaturalityIso
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Face.LocallyInner

@[expose] public section


/-!
# Change of the integral conjugator: the faces `h⁻¹Ph` and `(hγ)⁻¹P(hγ)`

Paper: Lemma C.3 (`ar:lem:seed`),
 ("Rationally conjugate the finitely many other plane cusps to `P`"), and.

* `EdgeNat.kerMap_surjective`: the transport of radical-kernel classes along bijective `α`, `τ`, `T`
  is surjective.
* `conjGammaHom N h γ : Γ_{(hγ)⁻¹P(hγ)} ≃ Γ_{h⁻¹Ph}`, `p ↦ γ p γ⁻¹`, with the coefficient comparison
  `ρ(γ⁻¹)` (`faceConjT`), is an isomorphism of split extensions compatible with the radicals,
  Levis and splittings (`conjGammaHom_inl`, `conjGammaHom_split`).
* `map_faceCuspidalInH2_conj`: the induced isomorphism `H²(Γ_{h⁻¹Ph}, E_n) → H²(Γ_{(hγ)⁻¹P(hγ)}, E_n)`
  maps the classes with edge in the mixed cuspidal group of the cusp `h⁻¹Ph` onto those of
  `(hγ)⁻¹P(hγ)`. In particular, for `γ ∈ Γ(N)` (the same face of the locally symmetric space), the
  group `𝒞_{P'}(E)` is independent of the choice of the representative of the orbit.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace EdgeNat

variable {N₁ N₂ E₁ E₂ L₁ L₂ : Type} [Group N₁] [Group N₂] [Group E₁] [Group E₂] [Group L₁]
  [Group L₂] {ext₁ : GroupExtension N₁ E₁ L₁} {ext₂ : GroupExtension N₂ E₂ L₂}
  (α : E₂ →* E₁) (τ : N₂ →* N₁)
  (hinl : ∀ r, α (ext₂.inl r) = ext₁.inl (τ r))
  (ρ₁ : Rep ℂ E₁) (ρ₂ : Rep ℂ E₂) (T : ρ₁ →ₗ[ℂ] ρ₂)
  (hT : ∀ (g : E₂) (v : ρ₁), T (ρ₁.ρ (α g) v) = ρ₂.ρ g (T v))
  (hα : Function.Bijective α) (hTb : Function.Bijective T) (hτ : Function.Bijective τ)

include hinl hT hα hTb hτ in
/-- The transport of the radical-kernel classes is surjective when `α`, `T`, `τ` are bijective. -/
theorem kerMap_surjective : Function.Surjective (kerMap α τ hinl ρ₁ ρ₂ T hT) := by
  intro x₂
  obtain ⟨z₂, hz₂⟩ := relativeTwoCocycleClass_surjective ext₂.inl ext₂.inl_injective ρ₂ x₂
  let e : E₂ ≃* E₁ := MulEquiv.ofBijective α hα
  let eτ : N₂ ≃* N₁ := MulEquiv.ofBijective τ hτ
  let z₁ := invCocycle₂ α ρ₁ ρ₂ T hT hα hTb z₂.val
  have hrel : z₁ ∈ relativeTwoCocycles ext₁.inl ρ₁ := by
    intro a b
    have hs : ∀ c : N₁, e.symm (ext₁.inl c) = ext₂.inl (eτ.symm c) := by
      intro c
      apply e.injective
      rw [e.apply_symm_apply]
      change ext₁.inl c = α (ext₂.inl (eτ.symm c))
      rw [hinl]
      rw [show τ (eτ.symm c) = c from eτ.apply_symm_apply c]
    have hz := z₂.property (eτ.symm a) (eτ.symm b)
    change z₂.val.1 (ext₂.inl (eτ.symm a), ext₂.inl (eτ.symm b)) = 0 at hz
    change (LinearEquiv.ofBijective T hTb).symm
      (z₂.val.1 (e.symm (ext₁.inl a), e.symm (ext₁.inl b))) = 0
    rw [hs, hs, hz, map_zero]
  refine ⟨relativeTwoCocycleClass ext₁.inl ρ₁ ⟨z₁, hrel⟩, ?_⟩
  rw [← hz₂]
  apply Subtype.ext
  rw [kerMap_val, relativeTwoCocycleClass_apply, relativeTwoCocycleClass_apply]
  change h2Map α ρ₁ ρ₂ T hT (groupCohomology.H2π ρ₁ z₁) = groupCohomology.H2π ρ₂ z₂.val
  rw [h2Map_π]
  congr 1
  apply groupCohomology.cocycles₂_ext
  intro a b
  let Te : ρ₁ ≃ₗ[ℂ] ρ₂ := LinearEquiv.ofBijective T hTb
  change T (Te.symm (z₂.val.1 (e.symm (α a), e.symm (α b)))) = z₂.val.1 (a, b)
  have h1 : e.symm (α a) = a := e.symm_apply_apply a
  have h2 : e.symm (α b) = b := e.symm_apply_apply b
  rw [h1, h2]
  exact Te.apply_symm_apply _

end EdgeNat

section Conj

open TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.ConvergenceC4

variable (N : ℕ) (h γ : SL(3, ℤ))

/-- Conjugation by `γ`: `Γ_{(hγ)⁻¹P(hγ)} → Γ_{h⁻¹Ph}`, `p ↦ γ p γ⁻¹`. -/
def conjGammaHom : gammaNPAt N (h * γ) →* gammaNPAt N h where
  toFun p := ⟨γ * p.1 * γ⁻¹, by
    have hp := p.2
    rw [mem_gammaNPAt] at hp ⊢
    have e : h * (γ * p.1 * γ⁻¹) * h⁻¹ = h * γ * p.1 * (h * γ)⁻¹ := by group
    rw [e]; exact hp⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp [mul_assoc]

theorem conjGammaHom_apply (p : gammaNPAt N (h * γ)) :
    ((conjGammaHom N h γ p : gammaNPAt N h) : SL(3, ℤ)) = γ * p.1 * γ⁻¹ := rfl

theorem conjGammaHom_bijective : Function.Bijective (conjGammaHom N h γ) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    have h1 : γ * a.1 * γ⁻¹ = γ * b.1 * γ⁻¹ := by
      have := congrArg (fun x : gammaNPAt N h => (x : SL(3, ℤ))) hab
      simpa only [conjGammaHom_apply] using this
    exact mul_left_cancel (mul_right_cancel h1)
  · intro b
    have hb : h * b.1 * h⁻¹ ∈ gammaNP N := b.2
    have hmem : γ⁻¹ * b.1 * γ ∈ gammaNPAt N (h * γ) := by
      show h * γ * (γ⁻¹ * b.1 * γ) * (h * γ)⁻¹ ∈ gammaNP N
      have e : h * γ * (γ⁻¹ * b.1 * γ) * (h * γ)⁻¹ = h * b.1 * h⁻¹ := by group
      rw [e]; exact hb
    refine ⟨⟨γ⁻¹ * b.1 * γ, hmem⟩, ?_⟩
    apply Subtype.ext
    show γ * (γ⁻¹ * b.1 * γ) * γ⁻¹ = b.1
    group

end Conj

section ConjFace

open TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.ConvergenceC4

variable (N : ℕ) [NeZero N] (h γ : SL(3, ℤ)) (n : ℕ)

/-- The coefficient comparison `E_n|_{Γ_h} → E_n|_{Γ_{hγ}}`, `v ↦ ρ(γ⁻¹) v`. -/
def faceConjT : GeneralEisenstein.HomogeneousPoly n →ₗ[ℂ] GeneralEisenstein.HomogeneousPoly n :=
  ambRep n γ⁻¹

omit [NeZero N] in
theorem faceConjT_intertwines (g : gammaNPAt N (h * γ)) (v : GeneralEisenstein.HomogeneousPoly n) :
    faceConjT γ n ((faceRep N h n).ρ (conjGammaHom N h γ g) v) =
      (faceRep N (h * γ) n).ρ g (faceConjT γ n v) := by
  change ambRep n γ⁻¹ (ambRep n (γ * g.1 * γ⁻¹) v) = ambRep n g.1 (ambRep n γ⁻¹ v)
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  congr 2
  group

theorem faceConjT_bijective : Function.Bijective (faceConjT γ n) := by
  constructor
  · intro a b hab
    have := congrArg (ambRep n γ) hab
    change ambRep n γ (ambRep n γ⁻¹ a) = ambRep n γ (ambRep n γ⁻¹ b) at this
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one] at this
    exact this
  · intro b
    refine ⟨ambRep n γ b, ?_⟩
    change ambRep n γ⁻¹ (ambRep n γ b) = b
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl

theorem conjGammaHom_inl (r : RadicalLattice) :
    conjGammaHom N h γ ((faceExt N (h * γ)).inl r) = (faceExt N h).inl ((MonoidHom.id RadicalLattice) r) := by
  apply Subtype.ext
  show γ * ((h * γ)⁻¹ * (gammaNInl N r).1 * (h * γ)) * γ⁻¹ = h⁻¹ * (gammaNInl N r).1 * h
  group

theorem conjGammaHom_split (m : CongruenceSubgroup.Gamma N) :
    conjGammaHom N h γ ((faceSplitting N (h * γ)).toMonoidHom m) =
      (faceSplitting N h).toMonoidHom ((MonoidHom.id _) m) := by
  apply Subtype.ext
  show γ * ((h * γ)⁻¹ * (gammaNSect N m).1 * (h * γ)) * γ⁻¹ = h⁻¹ * (gammaNSect N m).1 * h
  group


/-- **Change of the integral conjugator by `γ ∈ SL₃(ℤ)`** (in particular the choice of a representative
in a `Γ(N)`-orbit of planes): the pullback by conjugation
`H²(Γ_{h⁻¹Ph}, E_n) → H²(Γ_{(hγ)⁻¹P(hγ)}, E_n)` is an isomorphism carrying the group of
classes with edge in the mixed cuspidal group of the cusp `h⁻¹Ph` onto that of `(hγ)⁻¹P(hγ)`. -/
theorem map_faceCuspidalInH2_conj :
    Submodule.map (EdgeNat.h2Map (conjGammaHom N h γ) (faceRep N h n) (faceRep N (h * γ) n)
        (faceConjT γ n) (faceConjT_intertwines N h γ n)) (faceCuspidalInH2 N h n) =
      faceCuspidalInH2 N (h * γ) n := by
  have hα := conjGammaHom_bijective N h γ
  have hTb := faceConjT_bijective γ n
  have hτ : Function.Bijective (MonoidHom.id RadicalLattice) := Function.bijective_id
  have hinl := conjGammaHom_inl N h γ
  have hsplit := conjGammaHom_split N h γ
  have hbij := EdgeNat.radH1Map_bijective (conjGammaHom N h γ) (faceRep N h n)
    (faceRep N (h * γ) n) (faceConjT γ n) (faceConjT_intertwines N h γ n)
    (MonoidHom.id RadicalLattice) hinl hτ hTb
  have hcusp : ∀ x : groupCohomology.H1 (faceRadH1 N h n), x ∈ faceCuspidal N h n ↔
      (groupCohomology.map (MonoidHom.id (CongruenceSubgroup.Gamma N))
        (EdgeNat.modMor (faceSplitting N h) (faceSplitting N (h * γ)) (conjGammaHom N h γ)
          (MonoidHom.id _) (MonoidHom.id RadicalLattice) hinl hsplit (faceRep N h n)
          (faceRep N (h * γ) n) (faceConjT γ n) (faceConjT_intertwines N h γ n)) 1).hom x ∈
        faceCuspidal N (h * γ) n := fun x =>
    EdgeNat.mem_cuspidalFamily_map_id_iff (leviCuspStab (CongruenceSubgroup.Gamma N)) _ hbij x
  ext z
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨EdgeNat.kerMap (conjGammaHom N h γ) (MonoidHom.id RadicalLattice) hinl (faceRep N h n)
      (faceRep N (h * γ) n) (faceConjT γ n) (faceConjT_intertwines N h γ n) x, ?_, rfl⟩
    show faceEdge N (h * γ) n _ ∈ faceCuspidal N (h * γ) n
    rw [EdgeNat.edge_kerMap (faceSplitting N h) (faceSplitting N (h * γ)) (conjGammaHom N h γ)
      (MonoidHom.id _) (MonoidHom.id RadicalLattice) hinl hsplit (faceRep N h n)
      (faceRep N (h * γ) n) (faceConjT γ n) (faceConjT_intertwines N h γ n) x]
    exact (hcusp _).mp hx
  · rintro ⟨x₂, hx₂, rfl⟩
    obtain ⟨x₁, rfl⟩ := EdgeNat.kerMap_surjective (conjGammaHom N h γ) (MonoidHom.id RadicalLattice)
      hinl (faceRep N h n) (faceRep N (h * γ) n) (faceConjT γ n) (faceConjT_intertwines N h γ n) hα
      hTb hτ x₂
    refine ⟨x₁.val, ⟨x₁, ?_, rfl⟩, rfl⟩
    have h2 : faceEdge N (h * γ) n
        (EdgeNat.kerMap (conjGammaHom N h γ) (MonoidHom.id RadicalLattice) hinl (faceRep N h n)
          (faceRep N (h * γ) n) (faceConjT γ n) (faceConjT_intertwines N h γ n) x₁) ∈
        faceCuspidal N (h * γ) n := hx₂
    rw [EdgeNat.edge_kerMap (faceSplitting N h) (faceSplitting N (h * γ)) (conjGammaHom N h γ)
      (MonoidHom.id _) (MonoidHom.id RadicalLattice) hinl hsplit (faceRep N h n)
      (faceRep N (h * γ) n) (faceConjT γ n) (faceConjT_intertwines N h γ n) x₁] at h2
    exact (hcusp _).mpr h2

end ConjFace

end TernaryPeriodPolynomials.Argument.SeedC3S4c
