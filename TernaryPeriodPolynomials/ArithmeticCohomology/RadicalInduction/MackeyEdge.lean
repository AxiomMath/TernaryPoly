module

public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.OrbitComp
public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.RadIsoFace

@[expose] public section


/-!
# The canonical face pairing of the orbit components of an induced module

Formalized by Claude Sonnet 5.5.

**`mackey_edge`**: let `G ⊇ S, Δ`, `ρ` a representation of `G`, `x ∈ G/Δ`, `Stab = Stab_S(x)`, `V = Fun(S/Stab, E)`, `W = Res_S Fun(G/Δ, E)`, `ext` a split extension of `S` over `Γ(N)` and `ext'` one of `Stab` over `Γ(M)`
compatible with the inclusion (`Compat`).  For classes `a` (coefficients `V`) and `b` (coefficients `V^*`) with radical restriction zero and cuspidal edges, the canonical face pairing at `S` of the images
`j_* a`, `(q^T)_* b` in `W`, `W^*` (extension by zero and transpose of the orbit projection) equals the canonical face pairing at `Stab` of their evaluations at the base point
(`kerMapW`, `kerMapWD`).  The constant is exactly `1`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.RadicalInduction

open CongruenceSubgroup
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.CuspidalInduction
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
open MulAction
open scoped Classical

section Mackey

variable {G E : Type} [Group G] [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] (ρ : Representation ℂ G E)
  {Δ : Subgroup G} (S : Subgroup G) (x : G ⧸ Δ) [Fintype (G ⧸ Δ)] [Fintype (↥S ⧸ stabilizer ↥S x)]
  {N M m0 : ℕ} [hN : Fact (3 ≤ N)] (hM : 3 ≤ M) {hle : Gamma M ≤ Gamma N}
  {ext : GroupExtension RadicalLattice ↥S (Gamma N)} {s : ext.Splitting}
  {ext' : GroupExtension RadicalLattice ↥(stabilizer ↥S x) (Gamma M)} {s' : ext'.Splitting}
  (hc : Compat ext s (stabilizer ↥S x) (stabilizer ↥S x).subtype ext' s' (Subgroup.inclusion hle) m0)
  (hdet' : ∀ A, radDet (splitRadicalInput s' A) = 1) [NeZero m0] [Fintype (Gamma N ⧸ subM N M)]

omit [FiniteDimensional ℂ E] [Fintype (G ⧸ Δ)] [Fintype (↥S ⧸ stabilizer ↥S x)] hN in
/-- The inclusion of the orbit component, as an `S`-equivariant map of the representations `WI` and `Res_S Fun(G/Δ, E)`. -/
theorem jL_equivariant (g : ↥S) (v : WI ext (stabilizer ↥S x) (ρ.comp S.subtype)) :
    jL S x ((WI ext (stabilizer ↥S x) (ρ.comp S.subtype)).ρ g v) =
      (Rep.res S.subtype (Rep.of (permRep ρ Δ))).ρ g (jL S x v) :=
  Rep.hom_comm_apply (jRep ρ S x) g v

omit [FiniteDimensional ℂ E] [Fintype (G ⧸ Δ)] [Fintype (↥S ⧸ stabilizer ↥S x)] hN in
theorem qDual_equivariant' (g : ↥S) (f : dualRepG (WI ext (stabilizer ↥S x) (ρ.comp S.subtype))) :
    qDual S x ((dualRepG (WI ext (stabilizer ↥S x) (ρ.comp S.subtype))).ρ g f) =
      (dualRepG (Rep.res S.subtype (Rep.of (permRep ρ Δ)))).ρ g (qDual S x f) :=
  qDual_equivariant ρ S x g f

variable (ext) in
/-- The inclusion of the orbit component on the classes with vanishing radical restriction. -/
def jKer : (twoCohomologyRestriction ext.inl (WI ext (stabilizer ↥S x) (ρ.comp S.subtype))).ker →ₗ[ℂ]
    (twoCohomologyRestriction ext.inl (Rep.res S.subtype (Rep.of (permRep ρ Δ)))).ker :=
  isoKer (W₁ := WI ext (stabilizer ↥S x) (ρ.comp S.subtype)) (W₂ := Rep.res S.subtype (Rep.of (permRep ρ Δ)))
    (ext' := ext) (MonoidHom.id ↥S) (fun _ => rfl) (jL S x) (jL_equivariant ρ S x)

variable (ext) in
/-- The transposed orbit projection on the classes with vanishing radical restriction (coefficients `V^*`). -/
def qKerD : (twoCohomologyRestriction ext.inl (dualRepG (WI ext (stabilizer ↥S x) (ρ.comp S.subtype)))).ker →ₗ[ℂ]
    (twoCohomologyRestriction ext.inl (dualRepG (Rep.res S.subtype (Rep.of (permRep ρ Δ))))).ker :=
  isoKerD (W₁ := WI ext (stabilizer ↥S x) (ρ.comp S.subtype)) (W₂ := Rep.res S.subtype (Rep.of (permRep ρ Δ)))
    (ext' := ext) (MonoidHom.id ↥S) (fun _ => rfl) (qDual S x) (qDual_equivariant' ρ S x)

instance : Fintype (YN ext (stabilizer ↥S x)) := inferInstanceAs (Fintype (↥S ⧸ stabilizer ↥S x))

instance : FiniteDimensional ℂ (Rep.of (permRep ρ Δ)) := Module.Finite.pi

include hc hM hdet' in
/-- **The canonical face pairing of the orbit components, constant `1`.** -/
theorem mackey_edge
    (a : (twoCohomologyRestriction ext.inl (WI ext (stabilizer ↥S x) (ρ.comp S.subtype))).ker)
    (b : (twoCohomologyRestriction ext.inl (dualRepG (WI ext (stabilizer ↥S x) (ρ.comp S.subtype)))).ker)
    (ha : splitCohomologyEdge s (WI ext (stabilizer ↥S x) (ρ.comp S.subtype)) a ∈
      cuspidalSubspace (Gamma N) (splitRadicalH1Representation s (WI ext (stabilizer ↥S x) (ρ.comp S.subtype))))
    (hb : splitCohomologyEdge s (dualRepG (WI ext (stabilizer ↥S x) (ρ.comp S.subtype))) b ∈
      cuspidalSubspace (Gamma N) (splitRadicalH1Representation s (dualRepG (WI ext (stabilizer ↥S x) (ρ.comp S.subtype)))))
    (h1 : splitCohomologyEdge s (Rep.res S.subtype (Rep.of (permRep ρ Δ))) (jKer ρ S x ext a) ∈
      cuspidalSubspace (Gamma N) (splitRadicalH1Representation s (Rep.res S.subtype (Rep.of (permRep ρ Δ)))))
    (h2 : splitCohomologyEdge s (dualRepG (Rep.res S.subtype (Rep.of (permRep ρ Δ)))) (qKerD ρ S x ext b) ∈
      cuspidalSubspace (Gamma N) (splitRadicalH1Representation s (dualRepG (Rep.res S.subtype (Rep.of (permRep ρ Δ)))))) :
    facePairingCan hN.out s hc.det (Rep.res S.subtype (Rep.of (permRep ρ Δ)))
        ⟨splitCohomologyEdge s (Rep.res S.subtype (Rep.of (permRep ρ Δ))) (jKer ρ S x ext a), h1⟩
        ⟨splitCohomologyEdge s (dualRepG (Rep.res S.subtype (Rep.of (permRep ρ Δ)))) (qKerD ρ S x ext b), h2⟩ =
      facePairingCan hM s' hdet' (AS (stabilizer ↥S x).subtype (ρ.comp S.subtype))
        ⟨splitCohomologyEdge s' (AS (stabilizer ↥S x).subtype (ρ.comp S.subtype)) (kerMapW hc (ρ.comp S.subtype) a),
          edge_kerMapW_mem hc (ρ.comp S.subtype) hM a ha⟩
        ⟨splitCohomologyEdge s' (dualRepG (AS (stabilizer ↥S x).subtype (ρ.comp S.subtype))) (kerMapWD hc (ρ.comp S.subtype) b),
          edge_kerMapWD_mem hc (ρ.comp S.subtype) hM b hb⟩ := by
  have e := facePairingCan_iso_edge (s := s) (s' := s) (W₁ := WI ext (stabilizer ↥S x) (ρ.comp S.subtype))
    (W₂ := Rep.res S.subtype (Rep.of (permRep ρ Δ))) (ext' := ext) (MonoidHom.id ↥S) (fun _ => rfl) (fun _ => rfl)
    (jL S x) (qDual S x) (jL_equivariant ρ S x) (qDual_equivariant' ρ S x) (fun a b => qDual_jL S x b a)
    hc.det hc.det a b ha hb h1 h2
  exact e.symm.trans (facePairingCan_ind_edge hc (ρ.comp S.subtype) hM hdet' a b ha hb)

end Mackey

end TernaryPeriodPolynomials.Argument.RadicalInduction
