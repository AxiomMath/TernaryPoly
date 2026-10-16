module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.ConjRestriction
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.QComparison
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.OrbitPairing

@[expose] public section


/-!
# The face dictionary, generically: stabilizers of orbit representatives versus face groups

Formalized by Claude Sonnet 5.5.

Let `Z` be a `Γ(6)`-set (lines or planes), `o : F → labelOrbits Γ6 Z` a family of orbits, `b i ∈ o i` a point of each orbit, and `emb i : Grp i →* Γ(6)` injective homomorphisms whose
image is the stabilizer of `b i`.  For `g i` with `g i • (o i).out = b i`, conjugation by `g i` identifies the stabilizer of the chosen representative `(o i).out` with
`Grp i` (`faceAlpha`), and the coefficient comparison `ρ(g i⁻¹)` completes it to the isomorphism `faceTau` of `H²`: it carries the restriction of a class of `H²(Γ(6), E)` to
`Grp i` onto its restriction to the stabilizer of `(o i).out` (`faceTau_restriction`), by the triviality of inner automorphisms (`res_conj`).
-/

open CategoryTheory


noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPoly.BoundaryFaceResolutionComparison

section Generic

variable {Z : Type} [MulAction Γ6 Z] {F : Type} (o : F → labelOrbits Γ6 Z) (b : F → Z)
  (hb : ∀ i, b i ∈ labelOrbit Γ6 Z (o i))
  (Grp : F → Type) [∀ i, Group (Grp i)] (emb : ∀ i, Grp i →* Γ6) (hinj : ∀ i, Function.Injective (emb i))
  (hrange : ∀ i, (emb i).range = MulAction.stabilizer Γ6 (b i))

/-- A group element moving the representative of the orbit to the chosen point. -/
def faceG (i : F) : Γ6 := Classical.choose (MulAction.mem_orbit_iff.1 (hb i))

theorem faceG_smul (i : F) : faceG o b hb i • (o i).out = b i :=
  Classical.choose_spec (MulAction.mem_orbit_iff.1 (hb i))

theorem faceG_conj_mem (i : F) (s : MulAction.stabilizer Γ6 (o i).out) :
    faceG o b hb i * s * (faceG o b hb i)⁻¹ ∈ MulAction.stabilizer Γ6 (b i) := by
  rw [MulAction.mem_stabilizer_iff]
  have hs : (s : Γ6) • (o i).out = (o i).out := s.2
  conv_lhs => rw [mul_smul, mul_smul]
  rw [← faceG_smul o b hb i, inv_smul_smul, hs]


/-- Conjugation by `g i` maps the stabilizer of the representative into the image of the face group. -/
def faceConj (i : F) : ↥(MulAction.stabilizer Γ6 (o i).out) →* ↥(emb i).range where
  toFun s := ⟨faceG o b hb i * s * (faceG o b hb i)⁻¹, by
    rw [hrange i]; exact faceG_conj_mem o b hb i s⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a c := Subtype.ext (by
    change faceG o b hb i * ((a : Γ6) * (c : Γ6)) * (faceG o b hb i)⁻¹ =
      faceG o b hb i * (a : Γ6) * (faceG o b hb i)⁻¹ * (faceG o b hb i * (c : Γ6) * (faceG o b hb i)⁻¹)
    group)

/-- **The isomorphism of the stabilizer of the representative with the face group.** -/
def faceAlpha (i : F) : ↥(MulAction.stabilizer Γ6 (o i).out) →* Grp i :=
  (MonoidHom.ofInjective (hinj i)).symm.toMonoidHom.comp (faceConj o b hb Grp emb hrange i)

theorem emb_faceAlpha (i : F) (s : MulAction.stabilizer Γ6 (o i).out) :
    emb i (faceAlpha o b hb Grp emb hinj hrange i s) = faceG o b hb i * s * (faceG o b hb i)⁻¹ := by
  unfold faceAlpha
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [MonoidHom.apply_ofInjective_symm]
  rfl

theorem faceAlpha_bijective (i : F) : Function.Bijective (faceAlpha o b hb Grp emb hinj hrange i) := by
  constructor
  · intro s t hst
    have h := congrArg (emb i) hst
    rw [emb_faceAlpha, emb_faceAlpha] at h
    apply Subtype.ext
    have := mul_left_cancel (mul_right_cancel h)
    exact this
  · intro p
    have hp : emb i p ∈ MulAction.stabilizer Γ6 (b i) := by
      rw [← hrange i]; exact ⟨p, rfl⟩
    have hs : (faceG o b hb i)⁻¹ * emb i p * faceG o b hb i ∈ MulAction.stabilizer Γ6 (o i).out := by
      rw [MulAction.mem_stabilizer_iff] at hp ⊢
      rw [mul_smul, mul_smul, faceG_smul o b hb i, hp]
      rw [← faceG_smul o b hb i]
      exact inv_smul_smul _ _
    refine ⟨⟨_, hs⟩, ?_⟩
    apply hinj i
    rw [emb_faceAlpha]
    group



section Tau

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ6 V)

theorem faceTau_hT (i : F) (s : MulAction.stabilizer Γ6 (o i).out) (v : Rep.res (emb i) (Rep.of ρ)) :
    (Rep.of ρ).ρ (faceG o b hb i)⁻¹ ((Rep.res (emb i) (Rep.of ρ)).ρ (faceAlpha o b hb Grp emb hinj hrange i s) v) =
      (Rep.res (MulAction.stabilizer Γ6 (o i).out).subtype (Rep.of ρ)).ρ s ((Rep.of ρ).ρ (faceG o b hb i)⁻¹ v) := by
  change ρ (faceG o b hb i)⁻¹ (ρ (emb i (faceAlpha o b hb Grp emb hinj hrange i s)) v) = ρ (s : Γ6) (ρ (faceG o b hb i)⁻¹ v)
  rw [emb_faceAlpha, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  group

/-- **The transport of `H²` from the face group to the stabilizer of the representative of the orbit.** -/
def faceTau (i : F) : groupCohomology.H2 (Rep.res (emb i) (Rep.of ρ)) →ₗ[ℂ]
    groupCohomology.H2 (Rep.res (MulAction.stabilizer Γ6 (o i).out).subtype (Rep.of ρ)) :=
  EdgeNat.h2Map (faceAlpha o b hb Grp emb hinj hrange i) (Rep.res (emb i) (Rep.of ρ))
    (Rep.res (MulAction.stabilizer Γ6 (o i).out).subtype (Rep.of ρ)) (ρ (faceG o b hb i)⁻¹)
    (faceTau_hT o b hb Grp emb hinj hrange ρ i)

theorem faceTau_bijective (i : F) : Function.Bijective (faceTau o b hb Grp emb hinj hrange ρ i) := by
  have hT : Function.Bijective (ρ (faceG o b hb i)⁻¹) := by
    constructor
    · intro v w h
      have := congrArg (ρ (faceG o b hb i)) h
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one] at this
      exact this
    · intro v
      refine ⟨ρ (faceG o b hb i) v, ?_⟩
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
  exact ⟨EdgeNat.h2Map_injective _ _ _ _ _ (faceAlpha_bijective o b hb Grp emb hinj hrange i) hT,
    EdgeNat.h2Map_surjective _ _ _ _ _ (faceAlpha_bijective o b hb Grp emb hinj hrange i) hT⟩

/-- **The restriction of a global class to the stabilizer of the orbit representative is the transport of its restriction to the face group.** -/
theorem faceTau_restriction (i : F) (c : groupCohomology.H2 (Rep.of ρ)) :
    faceTau o b hb Grp emb hinj hrange ρ i (twoCohomologyRestriction (emb i) (Rep.of ρ) c) =
      twoCohomologyRestriction (MulAction.stabilizer Γ6 (o i).out).subtype (Rep.of ρ) c :=
  res_conj (Rep.of ρ) (faceG o b hb i) (emb i) (MulAction.stabilizer Γ6 (o i).out).subtype
    (faceAlpha o b hb Grp emb hinj hrange i) (fun s => emb_faceAlpha o b hb Grp emb hinj hrange i s)
    (faceTau_hT o b hb Grp emb hinj hrange ρ i) c

section Rational

variable [Module ℚ V] [IsScalarTower ℚ ℂ V]

/-- The transport to the rational cohomology of the stabilizer of the representative. -/
def faceTauQ (i : F) : groupCohomology.H2 (Rep.res (emb i) (Rep.of ρ)) →+
    groupCohomology (Rep.res (MulAction.stabilizer Γ6 (o i).out).subtype (qRepG ρ)) 2 :=
  (qH2 (ρ.comp (MulAction.stabilizer Γ6 (o i).out).subtype)).comp
    (faceTau o b hb Grp emb hinj hrange ρ i).toAddMonoidHom

theorem faceTauQ_bijective (i : F) : Function.Bijective (faceTauQ o b hb Grp emb hinj hrange ρ i) :=
  (qH2_bijective (ρ.comp (MulAction.stabilizer Γ6 (o i).out).subtype)).comp
    (faceTau_bijective o b hb Grp emb hinj hrange ρ i)

/-- **The key identity**: the rational coordinate at the representative of the orbit of the geometric class `qH2 c` is the transport of the restriction of `c` to the face group. -/
theorem faceTauQ_restriction (i : F) (c : groupCohomology.H2 (Rep.of ρ)) :
    faceTauQ o b hb Grp emb hinj hrange ρ i (twoCohomologyRestriction (emb i) (Rep.of ρ) c) =
      (groupCohomology.map (MulAction.stabilizer Γ6 (o i).out).subtype
        (𝟙 (Rep.res (MulAction.stabilizer Γ6 (o i).out).subtype (qRepG ρ))) 2).hom (qH2 ρ c) := by
  change qH2 (ρ.comp (MulAction.stabilizer Γ6 (o i).out).subtype)
    (faceTau o b hb Grp emb hinj hrange ρ i (twoCohomologyRestriction (emb i) (Rep.of ρ) c)) = _
  rw [faceTau_restriction]
  exact qH2_map ρ (MulAction.stabilizer Γ6 (o i).out).subtype c

end Rational

end Tau

end Generic

end TernaryPeriodPolynomials.Argument.GammaNStokes
