module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FaceDescent.FaceActionInner
public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.CuspConjNat
public import TernaryPeriodPolynomials.ArithmeticCohomology.FaceDescent.Descent

@[expose] public section


/-!
# The descended canonical face pairing is perfect

Formalized by Claude Sonnet 5.5.

`FaceAction.pairing_scale`: for a covering group `G` acting on the face data (`FaceAction`), the canonical pairing `facePairingCan` satisfies
`⟨g x, g y⟩ = det(φ_g) · det(A_g) · ⟨x, y⟩` (the `facePairingCan_twist`: Koszul sign times modular-curve sign); when the radical determinant is the Levi determinant (`hrad`) the two signs cancel (`pairing_scale_eq_one`).
`FaceAction.cusp_descends_left/right/finrank`: if a normal subgroup `K` of finite index acts through inner elements of the face group `E` (so trivially, `cuspAct_inner`), the restriction of the canonical pairing to the
`G`-invariants of the cuspidal groups `𝒞(H¹(N, ρ))`, `𝒞(H¹(N, ρ^*))` is perfect in both arguments and the invariants have the same dimension.
-/

open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FaceDescent

open CongruenceSubgroup
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.FrameInvariance
open TernaryPeriodPolynomials.Argument.CuspidalInduction
open TernaryPeriodPolynomials.Argument.SeedC3S4c (cuspidalSubspace)
open TernaryPoly.RankTwoAugmentedFrames

section Quotient

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (R : Representation ℂ G V) (K : Subgroup G) [K.Normal]
  (hK : ∀ k ∈ K, ∀ v, R k v = v)

omit [K.Normal] in
include hK in
theorem asGroupHom_eq_one (k : G) (hk : k ∈ K) : R.asGroupHom k = 1 :=
  Units.ext (LinearMap.ext fun v => by simpa [Representation.asGroupHom_apply] using hK k hk v)

/-- The representation of `G ⧸ K` induced by a representation of `G` on which the normal subgroup `K` acts trivially. -/
def quotRep : Representation ℂ (G ⧸ K) V :=
  (Units.coeHom (V →ₗ[ℂ] V)).comp (QuotientGroup.lift K R.asGroupHom (fun k hk => asGroupHom_eq_one R K hK k hk))

include hK in
theorem quotRep_mk (g : G) : quotRep R K hK (g : G ⧸ K) = R g := by
  have h := QuotientGroup.lift_mk (N := K) (φ := R.asGroupHom) (fun k hk => asGroupHom_eq_one R K hK k hk) g
  unfold quotRep
  rw [MonoidHom.comp_apply, h]
  exact Representation.asGroupHom_apply R g

include hK in
theorem mem_isoSub_quotRep_one {v : V} : v ∈ isoSub (quotRep R K hK) 1 ↔ ∀ g, R g v = v := by
  constructor
  · intro h g
    have := h (g : G ⧸ K)
    rwa [quotRep_mk, MonoidHom.one_apply, Units.val_one, one_smul] at this
  · intro h q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [quotRep_mk]
    simpa using h g

end Quotient

section Pairing

variable {N : ℕ} {hN : 3 ≤ N} {E : Type} [Group E] {ext : GroupExtension RadicalLattice E (Gamma N)} {ρ : Rep ℂ E}
  {G : Type} [Group G] (F : FaceAction hN ext ρ G) [FiniteDimensional ℂ ρ] (s : ext.Splitting)
  (hdet : ∀ A, radDet (splitRadicalInput s A) = 1)

/-- **The canonical pairing is scaled by `det φ · det A`** (Koszul sign times modular-curve sign). -/
theorem FaceAction.pairing_scale (g : G) (x : cuspidalSubspace (Gamma N) (splitRadicalH1Representation s ρ))
    (y : cuspidalSubspace (Gamma N) (splitRadicalH1Representation s (dualRepG ρ))) :
    facePairingCan hN s hdet ρ (F.cuspAct s g x) (F.dual.cuspAct s g y) =
      (radDet (F.twist g).φ.toMonoidHom : ℂ) * ((((F.A g)⁻¹).val.det : ℤ) : ℂ) * facePairingCan hN s hdet ρ x y :=
  facePairingCan_twist hN (F.twist g) s s ρ ρ (F.T g) (F.hTtw g) hdet hdet (F.A g)⁻¹ (F.hAtw g) (cuspConjNat N hN) x y

omit [FiniteDimensional ℂ ρ] in
/-- **The two orientation signs cancel**: if the radical determinant of `g` is the determinant of its Levi block. -/
theorem FaceAction.pairing_scale_eq_one (hrad : ∀ g, radDet (F.twist g).φ.toMonoidHom = (((F.A g)⁻¹).val.det : ℤ)) (g : G) :
    (radDet (F.twist g).φ.toMonoidHom : ℂ) * ((((F.A g)⁻¹).val.det : ℤ) : ℂ) = 1 := by
  have hu : IsUnit (((F.A g)⁻¹).val.det) := by simp
  rw [hrad g]
  have := det_mul_self_eq_one hu
  exact_mod_cast this

theorem FaceAction.pairing_invariant (hrad : ∀ g, radDet (F.twist g).φ.toMonoidHom = (((F.A g)⁻¹).val.det : ℤ)) (g : G)
    (x : cuspidalSubspace (Gamma N) (splitRadicalH1Representation s ρ))
    (y : cuspidalSubspace (Gamma N) (splitRadicalH1Representation s (dualRepG ρ))) :
    facePairingCan hN s hdet ρ (F.cuspAct s g x) (F.dual.cuspAct s g y) = facePairingCan hN s hdet ρ x y := by
  rw [F.pairing_scale s hdet, F.pairing_scale_eq_one hrad, one_mul]

section Descent

variable (K : Subgroup G) [K.Normal]
  (hK : ∀ k ∈ K, ∃ e : E, (∀ e', F.θ k e' = e * e' * e⁻¹) ∧ ∀ v, F.T k v = ρ.ρ e v)

omit [FiniteDimensional ℂ ρ] [K.Normal] in
include hK in
theorem FaceAction.cuspRep_trivial (k : G) (hk : k ∈ K) (x : cuspidalSubspace (Gamma N) (splitRadicalH1Representation s ρ)) :
    F.cuspRep s k x = x := by
  obtain ⟨e, h1, h2⟩ := hK k hk
  exact F.cuspAct_inner s k e h1 h2 x

omit [FiniteDimensional ℂ ρ] [K.Normal] in
include hK in
theorem FaceAction.dual_cuspRep_trivial (k : G) (hk : k ∈ K)
    (y : cuspidalSubspace (Gamma N) (splitRadicalH1Representation s (dualRepG ρ))) :
    F.dual.cuspRep s k y = y := by
  obtain ⟨e, h1, h2⟩ := hK k hk
  refine F.dual.cuspAct_inner s k e h1 (fun φ => ?_) y
  apply LinearMap.ext
  intro v
  show dualEquiv ρ ρ (F.T k) φ v = (dualRepG ρ).ρ e φ v
  rw [dualEquiv_apply, dualRepG_inv]
  congr 1
  rw [LinearEquiv.symm_apply_eq, h2, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

variable [Finite (G ⧸ K)]
  (hrad : ∀ g, radDet (F.twist g).φ.toMonoidHom = (((F.A g)⁻¹).val.det : ℤ))

include hK hrad in
/-- **The descended canonical face pairing is perfect (left kernel).**  The covering group `G` acts on the cuspidal groups with all determinant and reflection actions retained; `K` (finite index) acts trivially.
A class of the `G`-invariants of `𝒞(H¹(N, ρ))` which pairs to zero with all `G`-invariants of `𝒞(H¹(N, ρ^*))` is zero. -/
theorem FaceAction.cusp_descends_left (x : F.invariants s)
    (h : ∀ y : F.invariantsDual s, facePairingCan hN s hdet ρ x.1 y.1 = 0) : x = 0 := by
  classical
  have := Fintype.ofFinite (G ⧸ K)
  have hK1 : ∀ k ∈ K, ∀ v, F.cuspRep s k v = v := fun k hk v => F.cuspRep_trivial s K hK k hk v
  have hK2 : ∀ k ∈ K, ∀ v, F.dual.cuspRep s k v = v := fun k hk v => F.dual_cuspRep_trivial s K hK k hk v
  have hinv : ∀ (q : G ⧸ K) v w, facePairingCan hN s hdet ρ (quotRep (F.cuspRep s) K hK1 q v)
      (quotRep (F.dual.cuspRep s) K hK2 q w) = facePairingCan hN s hdet ρ v w := by
    intro q v w
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [quotRep_mk, quotRep_mk]
    exact F.pairing_invariant s hdet hrad g v w
  have hx : x.1 ∈ isoSub (quotRep (F.cuspRep s) K hK1) 1 := (mem_isoSub_quotRep_one _ K hK1).2 x.2
  exact Subtype.ext (isotypic_left (facePairingCan hN s hdet ρ) 1 1 1 (fun g => by simp)
    (fun q v w => by simpa using hinv q v w) (facePairingCan_perfect hN s hdet ρ).1 hx
    (fun y hy => h ⟨y, (mem_isoSub_quotRep_one _ K hK2).1 hy⟩))

include hK hrad in
/-- **The descended canonical face pairing is perfect (right kernel).** -/
theorem FaceAction.cusp_descends_right (y : F.invariantsDual s)
    (h : ∀ x : F.invariants s, facePairingCan hN s hdet ρ x.1 y.1 = 0) : y = 0 := by
  classical
  have := Fintype.ofFinite (G ⧸ K)
  have hK1 : ∀ k ∈ K, ∀ v, F.cuspRep s k v = v := fun k hk v => F.cuspRep_trivial s K hK k hk v
  have hK2 : ∀ k ∈ K, ∀ v, F.dual.cuspRep s k v = v := fun k hk v => F.dual_cuspRep_trivial s K hK k hk v
  have hinv : ∀ (q : G ⧸ K) v w, facePairingCan hN s hdet ρ (quotRep (F.cuspRep s) K hK1 q v)
      (quotRep (F.dual.cuspRep s) K hK2 q w) = facePairingCan hN s hdet ρ v w := by
    intro q v w
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [quotRep_mk, quotRep_mk]
    exact F.pairing_invariant s hdet hrad g v w
  have hy : y.1 ∈ isoSub (quotRep (F.dual.cuspRep s) K hK2) 1 := (mem_isoSub_quotRep_one _ K hK2).2 y.2
  exact Subtype.ext (isotypic_right (facePairingCan hN s hdet ρ) 1 1 1 (fun g => by simp)
    (fun q v w => by simpa using hinv q v w) (facePairingCan_perfect hN s hdet ρ).2 hy
    (fun x hx => h ⟨x, (mem_isoSub_quotRep_one _ K hK1).1 hx⟩))

end Descent

end Pairing

end TernaryPeriodPolynomials.Argument.FaceDescent
