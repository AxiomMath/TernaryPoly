module

public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.MackeyEdge
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Line.Pairing1

@[expose] public section


/-!
# The classes of the orbit components: projection, coordinates

Formalized by Claude Sonnet 5.5.

For the orbit `o` of `S` on `G/Δ` (representative `x = out o`): `qKer`, `jKerD` (the orbit projection `q` on classes and the transpose `jᵀ` of the orbit inclusion, on the classes with vanishing radical
restriction), the identities `jKer ∘ qKer = id` on the classes of the form `j_* y₀` (`jKer_qKer`) and `qKerD ∘ jKerD = id` on the classes in the dual component (`qKerD_jKerD`), and the identification of
the evaluation maps `kerMapW`, `kerMapWD` with the Shapiro coordinate `PhiH` (`kerMapW_val`, `kerMapWD_val`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.RadicalInduction

open CongruenceSubgroup
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.CuspidalInduction
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
open MulAction
open scoped Classical

theorem h2Map_comp_id {H : Type} [Group H] (A B C : Rep ℂ H) (T₁ : A →ₗ[ℂ] B) (hT₁ : ∀ (g : H) (v : A), T₁ (A.ρ ((MonoidHom.id H) g) v) = B.ρ g (T₁ v))
    (T₂ : B →ₗ[ℂ] C) (hT₂ : ∀ (g : H) (v : B), T₂ (B.ρ ((MonoidHom.id H) g) v) = C.ρ g (T₂ v))
    (hT : ∀ (g : H) (v : A), (T₂ ∘ₗ T₁) (A.ρ ((MonoidHom.id H) g) v) = C.ρ g ((T₂ ∘ₗ T₁) v)) (x : groupCohomology.H2 A) :
    EdgeNat.h2Map (MonoidHom.id H) B C T₂ hT₂ (EdgeNat.h2Map (MonoidHom.id H) A B T₁ hT₁ x) =
      EdgeNat.h2Map (MonoidHom.id H) A C (T₂ ∘ₗ T₁) hT x :=
  (h2Map_comp (MonoidHom.id H) (MonoidHom.id H) A B C T₁ hT₁ T₂ hT₂ x).trans
    (h2Map_congr rfl A C _ hT rfl x)

theorem h2Map_comp_idem {H : Type} [Group H] (A B : Rep ℂ H) (j : A →ₗ[ℂ] B)
    (hj : ∀ (g : H) (v : A), j (A.ρ ((MonoidHom.id H) g) v) = B.ρ g (j v)) (q : B →ₗ[ℂ] A)
    (hq : ∀ (g : H) (v : B), q (B.ρ ((MonoidHom.id H) g) v) = A.ρ g (q v)) (e : A →ₗ[ℂ] A)
    (he : ∀ (k : H) (v : A), e (A.ρ k v) = A.ρ k (e v)) (hqj : q ∘ₗ j = e) (x : groupCohomology.H2 A) :
    EdgeNat.h2Map (MonoidHom.id H) B A q hq (EdgeNat.h2Map (MonoidHom.id H) A B j hj x) = h2E A e he x := by
  subst hqj
  exact h2Map_comp_id A B A j hj q hq (fun g v => he g v) x

theorem dualPair_single {G E : Type} [Group G] [AddCommGroup E] [Module ℂ E] (Δ' : Subgroup G) [Fintype (G ⧸ Δ')] (dec : DecidableEq (G ⧸ Δ'))
    (φ : (G ⧸ Δ') → Module.Dual ℂ E) (y : G ⧸ Δ') (a : E) :
    dualPairEquiv Δ' φ (@Pi.single (G ⧸ Δ') (fun _ => E) _ dec y a) = φ y a := by
  change ∑ z, φ z ((@Pi.single (G ⧸ Δ') (fun _ => E) _ dec y a : (G ⧸ Δ') → E) z) = φ y a
  rw [Finset.sum_eq_single y]
  · simp
  · intro z _ hz
    simp [Pi.single_eq_of_ne hz]
  · intro h
    exact absurd (Finset.mem_univ _) h

section MC

variable {G E : Type} [Group G] [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] (ρ : Representation ℂ G E)
  {Δ : Subgroup G} (S : Subgroup G) (x : G ⧸ Δ) [Fintype (G ⧸ Δ)]
  [Fintype (↥S ⧸ stabilizer ↥S x)]
  {N : ℕ} {ext : GroupExtension RadicalLattice ↥S (Gamma N)}

omit [FiniteDimensional ℂ E] [Fintype (G ⧸ Δ)] [Fintype (↥S ⧸ stabilizer ↥S x)] in
theorem qL_equivariant (g : ↥S) (v : Rep.res S.subtype (Rep.of (permRep ρ Δ))) :
    qL S x ((Rep.res S.subtype (Rep.of (permRep ρ Δ))).ρ g v) =
      (WI ext (stabilizer ↥S x) (ρ.comp S.subtype)).ρ g (qL S x v) :=
  Rep.hom_comm_apply (qRep ρ S x) g v

variable (ext) in
/-- The orbit projection on the classes with vanishing radical restriction. -/
def qKer : (twoCohomologyRestriction ext.inl (Rep.res S.subtype (Rep.of (permRep ρ Δ)))).ker →ₗ[ℂ]
    (twoCohomologyRestriction ext.inl (WI ext (stabilizer ↥S x) (ρ.comp S.subtype))).ker :=
  isoKer (W₁ := Rep.res S.subtype (Rep.of (permRep ρ Δ)))
    (W₂ := WI ext (stabilizer ↥S x) (ρ.comp S.subtype)) (ext' := ext) (MonoidHom.id ↥S)
    (fun _ => rfl) (qL S x) (qL_equivariant ρ S x)

omit [FiniteDimensional ℂ E] [Fintype (G ⧸ Δ)] [Fintype (↥S ⧸ stabilizer ↥S x)] in
theorem jDual_equivariant' (g : ↥S) (f : dualRepG (Rep.res S.subtype (Rep.of (permRep ρ Δ)))) :
    jDual S x ((dualRepG (Rep.res S.subtype (Rep.of (permRep ρ Δ)))).ρ g f) =
      (dualRepG (WI ext (stabilizer ↥S x) (ρ.comp S.subtype))).ρ g
        (jDual S x f) :=
  jDual_equivariant ρ S x g f

variable (ext) in
/-- The transpose of the orbit inclusion on the classes with vanishing radical restriction (dual coefficients). -/
def jKerD : (twoCohomologyRestriction ext.inl (dualRepG (Rep.res S.subtype (Rep.of (permRep ρ Δ))))).ker →ₗ[ℂ]
    (twoCohomologyRestriction ext.inl (dualRepG (WI ext (stabilizer ↥S x) (ρ.comp S.subtype)))).ker :=
  isoKerD (W₁ := Rep.res S.subtype (Rep.of (permRep ρ Δ)))
    (W₂ := WI ext (stabilizer ↥S x) (ρ.comp S.subtype)) (ext' := ext) (MonoidHom.id ↥S)
    (fun _ => rfl) (jDual S x) (jDual_equivariant' ρ S x)

omit [FiniteDimensional ℂ E] [Fintype (G ⧸ Δ)] [Fintype (↥S ⧸ stabilizer ↥S x)] in
theorem jKer_qKer (y : (twoCohomologyRestriction ext.inl (Rep.res S.subtype (Rep.of (permRep ρ Δ)))).ker)
    (h : y.1 = h2Hom (jRep ρ S x) (h2Hom (qRep ρ S x) y.1)) :
    jKer ρ S x ext (qKer ρ S x ext y) = y := by
  apply Subtype.ext
  refine Eq.trans ?_ h.symm
  rw [h2Hom_eq_h2Map, h2Hom_eq_h2Map]
  rfl

omit [FiniteDimensional ℂ E] [Fintype (G ⧸ Δ)] in
theorem qKerD_jKerD (o : orbitRel.Quotient ↥S (G ⧸ Δ)) (hx : x = Quotient.out o)
    (y : (twoCohomologyRestriction ext.inl (dualRepG (Rep.res S.subtype (Rep.of (permRep ρ Δ))))).ker)
    (hS : ∀ (k : ↥S) (v : Module.Dual ℂ ((G ⧸ Δ) → E)),
      (eO Δ S o).dualMap ((Rep.res S.subtype (Rep.of (permRep ρ Δ).dual)).ρ k v) =
        (Rep.res S.subtype (Rep.of (permRep ρ Δ).dual)).ρ k ((eO Δ S o).dualMap v))
    (h : y.1 = h2E (Rep.res S.subtype (Rep.of (permRep ρ Δ).dual)) (eO Δ S o).dualMap hS y.1) :
    qKerD ρ S x ext (jKerD ρ S x ext y) = y := by
  subst hx
  apply Subtype.ext
  have e := h2Map_comp_idem (dualRepG (Rep.res S.subtype (Rep.of (permRep ρ Δ))))
    (dualRepG (WI ext (stabilizer ↥S (Quotient.out o : G ⧸ Δ)) (ρ.comp S.subtype)))
    (jDual S (Quotient.out o : G ⧸ Δ)) (fun g f => jDual_equivariant' ρ S (Quotient.out o : G ⧸ Δ) g f)
    (qDual S (Quotient.out o : G ⧸ Δ)) (fun g f => qDual_equivariant' ρ S (Quotient.out o : G ⧸ Δ) g f)
    (eO Δ S o).dualMap (fun k v => hS k v) rfl y.1
  exact e.trans h.symm

omit [FiniteDimensional ℂ E] [Fintype (G ⧸ Δ)] [Fintype (↥S ⧸ stabilizer ↥S x)] in
theorem h2Map_stab_eq_PhiH (z : groupCohomology.H2 (Rep.of (permRep (ρ.comp S.subtype) (stabilizer ↥S x)))) :
    EdgeNat.h2Map (stabilizer ↥S x).subtype (WI ext (stabilizer ↥S x) (ρ.comp S.subtype))
      (AS (stabilizer ↥S x).subtype (ρ.comp S.subtype)) (evT ext (stabilizer ↥S x) (stabilizer ↥S x).subtype (ρ.comp S.subtype))
      (evT_hT (stabilizer ↥S x).subtype (fun g => g.2) (ρ.comp S.subtype)) z =
      PhiH (ρ.comp S.subtype) (stabilizer ↥S x) z := by
  unfold PhiH coordH
  rw [LinearMap.comp_apply, twoCohomologyRestriction_eq_h2Map, h2Map_comp]
  exact h2Map_congr (by ext; rfl) _ _ _ _ (LinearMap.ext fun v => rfl) z

omit [FiniteDimensional ℂ E] in
theorem jDual_dualPairEquiv_jL (φ : (↥S ⧸ stabilizer ↥S x) → Module.Dual ℂ E) :
    jDual S x (dualPairEquiv Δ (jL S x φ)) = dualPairEquiv (stabilizer ↥S x) φ := by
  refine LinearMap.ext fun ψ => ?_
  rw [jDual_apply, dualPair_jL, qL_jL]

/-- `jᵀ` as a morphism of representations. -/
def jDualRep : Rep.res S.subtype (Rep.of (permRep ρ Δ).dual) ⟶
    Rep.of (permRep (ρ.comp S.subtype) (stabilizer ↥S x)).dual :=
  Rep.ofHom ⟨jDual S x, fun g => LinearMap.ext fun f => jDual_equivariant ρ S x g f⟩

omit [FiniteDimensional ℂ E] [Fintype (G ⧸ Δ)] in
/-- `jᵀ` carries the dual of the orbit inclusion of `E^*`-valued functions to the dual identification on `S/Stab`. -/
theorem jDual_dualPush [Fintype (G ⧸ Δ)] (z : groupCohomology.H2 (Rep.of (permRep (ρ.dual.comp S.subtype) (stabilizer ↥S x)))) :
    EdgeNat.h2Map (MonoidHom.id ↥S) (dualRepG (Rep.res S.subtype (Rep.of (permRep ρ Δ))))
      (dualRepG (WI ext (stabilizer ↥S x) (ρ.comp S.subtype))) (jDual S x) (fun g f => jDual_equivariant' ρ S x g f)
      (dualPushG ρ Δ S (h2Hom (jRep ρ.dual S x) z)) =
    h2Hom (dualRepHom (ρ.comp S.subtype) (stabilizer ↥S x)) z := by
  have e : h2Hom (jDualRep ρ S x) (dualPushG ρ Δ S (h2Hom (jRep ρ.dual S x) z)) =
      h2Hom (dualRepHom (ρ.comp S.subtype) (stabilizer ↥S x)) z := by
    unfold dualPushG
    rw [← h2Hom_comp, ← h2Hom_comp]
    refine congrArg (fun f => h2Hom f z) ?_
    exact Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun φ => jDual_dualPairEquiv_jL S x φ))
  exact e

omit [FiniteDimensional ℂ E] [Fintype (G ⧸ Δ)] in
theorem h2Map_stab_dual_eq_PhiH (z' : groupCohomology.H2 (Rep.of (permRep (Representation.dual (ρ.comp S.subtype)) (stabilizer ↥S x)))) :
    EdgeNat.h2Map (stabilizer ↥S x).subtype (dualRepG (WI ext (stabilizer ↥S x) (ρ.comp S.subtype)))
      (dualRepG (AS (stabilizer ↥S x).subtype (ρ.comp S.subtype)))
      (evTD ext (stabilizer ↥S x) (stabilizer ↥S x).subtype (ρ.comp S.subtype))
      (evTD_hT (fun g => g.2) (ρ.comp S.subtype))
      (h2Hom (dualRepHom (ρ.comp S.subtype) (stabilizer ↥S x)) z') =
      PhiH (Representation.dual (ρ.comp S.subtype)) (stabilizer ↥S x) z' := by
  rw [h2Hom_eq_h2Map]
  refine (h2Map_comp (MonoidHom.id ↥S) (stabilizer ↥S x).subtype _ _ _ _ _ _ _ z').trans ?_
  unfold PhiH coordH
  rw [LinearMap.comp_apply, twoCohomologyRestriction_eq_h2Map, h2Map_comp]
  refine h2Map_congr (by ext; rfl) _ _ _ _ ?_ z'
  refine LinearMap.ext fun φ => LinearMap.ext fun a => ?_
  exact (evTD_apply (ext := ext) (Stab := stabilizer ↥S x) (α := (stabilizer ↥S x).subtype) (ρ.comp S.subtype)
    (dualPairEquiv (stabilizer ↥S x) φ) a).trans
    (dualPair_single (stabilizer ↥S x) (fun a b => Classical.propDecidable (a = b)) φ (y0 ext (stabilizer ↥S x)) a)

omit [FiniteDimensional ℂ E] [Fintype (G ⧸ Δ)] [Fintype (↥S ⧸ stabilizer ↥S x)] in
theorem qKer_edge_mem [hN : Fact (3 ≤ N)] {s : ext.Splitting}
    (y : (twoCohomologyRestriction ext.inl (Rep.res S.subtype (Rep.of (permRep ρ Δ)))).ker)
    (hy : splitCohomologyEdge s (Rep.res S.subtype (Rep.of (permRep ρ Δ))) y ∈
      cuspidalSubspace (Gamma N) (splitRadicalH1Representation s (Rep.res S.subtype (Rep.of (permRep ρ Δ))))) :
    splitCohomologyEdge s (WI ext (stabilizer ↥S x) (ρ.comp S.subtype)) (qKer ρ S x ext y) ∈
      cuspidalSubspace (Gamma N) (splitRadicalH1Representation s (WI ext (stabilizer ↥S x) (ρ.comp S.subtype))) :=
  isoKer_edge_mem (s := s) (s' := s) (ext' := ext) (W₁ := Rep.res S.subtype (Rep.of (permRep ρ Δ)))
    (W₂ := WI ext (stabilizer ↥S x) (ρ.comp S.subtype)) (MonoidHom.id ↥S) (fun _ => rfl) (fun _ => rfl) (qL S x)
    (qL_equivariant ρ S x) y hy

omit [FiniteDimensional ℂ E] [Fintype (G ⧸ Δ)] [Fintype (↥S ⧸ stabilizer ↥S x)] in
theorem jKerD_edge_mem [hN : Fact (3 ≤ N)] {s : ext.Splitting}
    (y : (twoCohomologyRestriction ext.inl (dualRepG (Rep.res S.subtype (Rep.of (permRep ρ Δ))))).ker)
    (hy : splitCohomologyEdge s (dualRepG (Rep.res S.subtype (Rep.of (permRep ρ Δ)))) y ∈
      cuspidalSubspace (Gamma N) (splitRadicalH1Representation s (dualRepG (Rep.res S.subtype (Rep.of (permRep ρ Δ)))))) :
    splitCohomologyEdge s (dualRepG (WI ext (stabilizer ↥S x) (ρ.comp S.subtype))) (jKerD ρ S x ext y) ∈
      cuspidalSubspace (Gamma N) (splitRadicalH1Representation s (dualRepG (WI ext (stabilizer ↥S x) (ρ.comp S.subtype)))) :=
  isoKerD_edge_mem (s := s) (s' := s) (ext' := ext) (W₁ := Rep.res S.subtype (Rep.of (permRep ρ Δ)))
    (W₂ := WI ext (stabilizer ↥S x) (ρ.comp S.subtype)) (MonoidHom.id ↥S) (fun _ => rfl) (fun _ => rfl) (jDual S x)
    (jDual_equivariant' ρ S x) y hy

end MC

end TernaryPeriodPolynomials.Argument.RadicalInduction
