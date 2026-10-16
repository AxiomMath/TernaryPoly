module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.PermCoind

@[expose] public section


/-!
# Trees with a free action of a quotient: the exact sequence `0 → A → Fun(V, A) → Anti(E, A) → 0` of `G`-modules

Formalized by Claude Sonnet 5.5.

`TreeData Q` packages a tree on which `Q` acts freely (connected, with potentials of antisymmetric edge functions over `ℚ`-vector spaces); for a group `G` acting through `π : G →* Q`
the sequence `treeSES` is a short exact sequence of `G`-representations (`treeSES_shortExact`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open CategoryTheory CategoryTheory.Limits



/-- A tree with a free action of `Q` on its vertices and oriented edges, with the two properties giving the exact sequence
`0 → A → Fun(Vt, A) → Anti(Et, A) → 0`: connectedness and existence of potentials of antisymmetric edge functions. -/
structure TreeData (Q : Type) [Group Q] where
  Vt : Type
  Et : Type
  [mulV : MulAction Q Vt]
  [mulE : MulAction Q Et]
  swap : Et → Et
  src : Et → Vt
  tgt : Et → Vt
  src_smul : ∀ (q : Q) (e : Et), src (q • e) = q • src e
  tgt_smul : ∀ (q : Q) (e : Et), tgt (q • e) = q • tgt e
  swap_smul : ∀ (q : Q) (e : Et), swap (q • e) = q • swap e
  src_swap : ∀ e, src (swap e) = tgt e
  swap_swap : ∀ e, swap (swap e) = e
  free_v : ∀ (q : Q) (v : Vt), q • v = v → q = 1
  free_e : ∀ (q : Q) (e : Et), q • e = e → q = 1
  nonempty_v : Nonempty Vt
  conn : ∀ (A : Type) [AddCommGroup A] (P : Vt → A), (∀ e, P (tgt e) = P (src e)) → ∀ v w, P v = P w
  pot : ∀ (A : Type) [AddCommGroup A] [Module ℚ A] (F : Et → A), (∀ e, F (swap e) = -F e) →
    ∃ P : Vt → A, ∀ e, P (tgt e) - P (src e) = F e

attribute [instance] TreeData.mulV TreeData.mulE

namespace TreeData

variable {Q : Type} [Group Q] (T : TreeData Q)

theorem tgt_swap (e : T.Et) : T.tgt (T.swap e) = T.src e := by
  rw [← T.src_swap (T.swap e), T.swap_swap]

/-- The antisymmetric functions on the oriented edges. -/
def antiSub (k : Type) [CommRing k] (A : Type) [AddCommGroup A] [Module k A] : Submodule k (T.Et → A) where
  carrier := {F | ∀ e, F (T.swap e) = -F e}
  add_mem' := fun {F F'} hF hF' e => by simp [hF e, hF' e, add_comm]
  zero_mem' := fun e => by simp
  smul_mem' := fun c F hF e => by simp [hF e]

end TreeData

section SES

variable {k : Type} [CommRing k] {G Q : Type} [Group G] [Group Q] (π : G →* Q) (T : TreeData Q)
  (A : Type) [AddCommGroup A] [Module k A]

/-- The representation of `G` on the antisymmetric edge functions. -/
def antiRep : Representation k G (T.antiSub k A) where
  toFun g := (permRep (k := k) π T.Et A g).restrict (fun F hF e => by
    have h1 : T.swap ((π g)⁻¹ • e) = (π g)⁻¹ • T.swap e := T.swap_smul _ e
    change F ((π g)⁻¹ • T.swap e) = -F ((π g)⁻¹ • e)
    rw [← h1]
    exact hF _)
  map_one' := by
    ext F e
    simp
  map_mul' g h := by
    ext F e
    show F.1 ((π (g * h))⁻¹ • e) = F.1 ((π h)⁻¹ • (π g)⁻¹ • e)
    rw [map_mul, mul_inv_rev, mul_smul]

/-- The constants as a morphism of representations. -/
def constHom : Rep.trivial k G A ⟶ Rep.of (permRep (k := k) π T.Vt A) :=
  Rep.ofHom
    { toFun := fun a _ => a
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      isIntertwining' := fun g => by
        ext a v
        simp [permRep_apply] }

/-- The coboundary `P ↦ (e ↦ P (tgt e) - P (src e))` as a morphism of representations. -/
def edgeHom : Rep.of (permRep (k := k) π T.Vt A) ⟶ Rep.of (antiRep (k := k) π T A) :=
  Rep.ofHom
    { toFun := fun P => ⟨fun e => P (T.tgt e) - P (T.src e), fun e => by
        simp [T.src_swap, T.tgt_swap]⟩
      map_add' := fun P P' => by
        apply Subtype.ext
        funext e
        simp only [Pi.add_apply, Submodule.coe_add]
        abel
      map_smul' := fun c P => by
        apply Subtype.ext
        funext e
        simp [smul_sub]
      isIntertwining' := fun g => by
        ext P e
        show P ((π g)⁻¹ • T.tgt e) - P ((π g)⁻¹ • T.src e) =
          P (T.tgt ((π g)⁻¹ • e)) - P (T.src ((π g)⁻¹ • e))
        rw [T.tgt_smul, T.src_smul] }

/-- The short complex `0 → A → Fun(Vt, A) → Anti(Et, A) → 0` of `G`-representations. -/
def treeSES : ShortComplex (Rep.{0} k G) where
  X₁ := Rep.trivial k G A
  X₂ := Rep.of (permRep (k := k) π T.Vt A)
  X₃ := Rep.of (antiRep (k := k) π T A)
  f := constHom π T A
  g := edgeHom π T A
  zero := by
    apply Rep.hom_ext
    ext a e
    simp [constHom, edgeHom]

theorem treeSES_shortExact [Module ℚ A] : (treeSES (k := k) π T A).ShortExact where
  exact := by
    refine (ShortComplex.exact_map_iff_of_faithful (treeSES (k := k) π T A)
      (forget₂ (Rep.{0} k G) (ModuleCat.{0} k))).1 ?_
    rw [ShortComplex.moduleCat_exact_iff]
    intro P hP
    have h0 : ∀ e, P (T.tgt e) = P (T.src e) := by
      intro e
      have := congrArg (fun F : T.antiSub k A => F.1 e) hP
      simp only [ShortComplex.map_g, treeSES] at this
      exact sub_eq_zero.mp this
    obtain ⟨v₀⟩ := T.nonempty_v
    refine ⟨P v₀, ?_⟩
    funext v
    exact T.conn A P h0 v₀ v
  mono_f := by
    rw [Rep.mono_iff_injective]
    obtain ⟨v₀⟩ := T.nonempty_v
    intro a b hab
    exact congrFun hab v₀
  epi_g := by
    rw [Rep.epi_iff_surjective]
    intro F
    obtain ⟨P, hP⟩ := T.pot A F.1 F.2
    exact ⟨P, Subtype.ext (funext hP)⟩

end SES


end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
