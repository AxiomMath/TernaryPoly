module

public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.RadPer
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.RadicalFacePairing

@[expose] public section


/-!
# The contragredient of `Fun(S/Stab, E)`

Formalized by Claude Sonnet 5.5.

`kapDual : Dual(Fun(Y, E)) → Fun(Y, Dual E)`, `f ↦ (y ↦ f ∘ single y)`, is `S`-equivariant (`kapDual_equivariant`) and turns the evaluation pairing `Module.Dual.eval` of `Fun(Y, E)` with its
literal contragredient into the summed pairing `eindQ` of `Fun(Y, E) × Fun(Y, Dual E)` (`eval_eq`).  Hence the radical identity of `phiC_ind` holds for the literal contragredient (`phiC_ind_dual`) with the comparison
`T' f = f ∘ single y₀`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.RadicalInduction

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.CuspidalInduction
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open scoped Classical

variable {S L L' : Type} [Group S] [Group L] [Group L'] {ext : GroupExtension RadicalLattice S L} {s : ext.Splitting}
  {Stab : Subgroup S} {E₂ : Type} [Group E₂] {α : E₂ →* S} {ext' : GroupExtension RadicalLattice E₂ L'} {s' : ext'.Splitting}
  {ιL : L' →* L} {m0 : ℕ} {Lsub : Subgroup L} {E : Type} [AddCommGroup E] [Module ℂ E]

variable (ext Stab) in
/-- `Dual(Fun(Y, E)) → Fun(Y, Dual E)`, `f ↦ (y ↦ f ∘ single y)`. -/
def kapDual (E : Type) [AddCommGroup E] [Module ℂ E] :
    Module.Dual ℂ (YN ext Stab → E) →ₗ[ℂ] (YN ext Stab → Module.Dual ℂ E) where
  toFun f y := f ∘ₗ LinearMap.single ℂ (fun _ : YN ext Stab => E) y
  map_add' f g := by funext y; ext a; simp
  map_smul' c f := by funext y; ext a; simp

theorem kapDual_apply (f : Module.Dual ℂ (YN ext Stab → E)) (y : YN ext Stab) (a : E) :
    kapDual ext Stab E f y a = f (Pi.single y a) := rfl

theorem single_equivariant (ρ : Representation ℂ S E) (g : S) (y : YN ext Stab) (a : E) :
    indRepQ (Q := YN ext Stab) ρ g (Pi.single y a) = Pi.single (g • y) (ρ g a) := by
  funext z
  rw [indRepQ_apply, Pi.single_apply, Pi.single_apply]
  have : g⁻¹ • z = y ↔ z = g • y := inv_smul_eq_iff
  by_cases h : z = g • y
  · rw [ite_eq_left (this.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (this.mp h')), ite_eq_right h, map_zero]

theorem kapDual_equivariant (ρ : Representation ℂ S E) (g : S) (f : Module.Dual ℂ (YN ext Stab → E)) :
    kapDual ext Stab E ((indRepQ (Q := YN ext Stab) ρ).dual g f) =
      indRepQ (Q := YN ext Stab) ρ.dual g (kapDual ext Stab E f) := by
  funext y
  ext a
  rw [kapDual_apply, indRepQ_apply]
  change f (indRepQ (Q := YN ext Stab) ρ g⁻¹ (Pi.single y a)) = (ρ.dual g) (kapDual ext Stab E f (g⁻¹ • y)) a
  rw [single_equivariant]
  rfl

theorem eval_eq [Fintype (YN ext Stab)] (f : Module.Dual ℂ (YN ext Stab → E)) (F : YN ext Stab → E) :
    f F = eindQ (Module.Dual.eval ℂ E) F (kapDual ext Stab E f) := by
  rw [eindQ_apply]
  conv_lhs => rw [← Finset.univ_sum_single F]
  rw [map_sum]
  rfl

variable (ext Stab) in
/-- The transfer of a radical cocycle with values in the literal contragredient of `Fun(Y, E)` to `Fun(Y, Dual E)`. -/
def kcoc (ρ : Representation ℂ S E) :
    groupCohomology.cocycles₁ (Rep.res ext.inl (dualRepG (WI ext Stab ρ))) →ₗ[ℂ]
      groupCohomology.cocycles₁ (Rep.res ext.inl (WI ext Stab ρ.dual)) :=
  oneCocyclePullback (Rep.res ext.inl (dualRepG (WI ext Stab ρ))) (Rep.res ext.inl (WI ext Stab ρ.dual))
    (MonoidHom.id RadicalLattice) (kapDual ext Stab E) (by
      intro r
      apply LinearMap.ext
      intro f
      exact (kapDual_equivariant ρ (ext.inl r) f).symm)

theorem kcoc_apply (ρ : Representation ℂ S E) (c : groupCohomology.cocycles₁ (Rep.res ext.inl (dualRepG (WI ext Stab ρ)))) (r : RadicalLattice) :
    (kcoc ext Stab ρ c).1 r = kapDual ext Stab E (c.1 r) := rfl

variable [Fintype (YN ext Stab)] in
theorem eval_term (ρ : Representation ℂ S E) (r : RadicalLattice) (F : YN ext Stab → E)
    (f : Module.Dual ℂ (YN ext Stab → E)) :
    ((indRepQ (Q := YN ext Stab) ρ).dual (ext.inl r) f) F =
      eindQ (Module.Dual.eval ℂ E) F (indRepQ (Q := YN ext Stab) ρ.dual (ext.inl r) (kapDual ext Stab E f)) := by
  rw [← kapDual_equivariant ρ (ext.inl r) f, ← eval_eq]

variable [Fintype (YN ext Stab)] in
theorem phiC_dual_eq (ρ : Representation ℂ S E) (c : groupCohomology.cocycles₁ (Rep.res ext.inl (WI ext Stab ρ)))
    (c' : groupCohomology.cocycles₁ (Rep.res ext.inl (dualRepG (WI ext Stab ρ)))) :
    PhiC (Rep.res ext.inl (WI ext Stab ρ)) (Rep.res ext.inl (dualRepG (WI ext Stab ρ))) (Module.Dual.eval ℂ (WI ext Stab ρ)) c c' =
      PhiC (Rep.res ext.inl (WI ext Stab ρ)) (Rep.res ext.inl (WI ext Stab ρ.dual)) (eW ρ ρ.dual (Module.Dual.eval ℂ E)) c (kcoc ext Stab ρ c') := by
  rw [PhiC_apply, PhiC_apply]
  exact congrArg₂ (· - ·) (eval_term ρ rl1 (c.1 rl1) (c'.1 rl2)) (eval_term ρ rl2 (c.1 rl2) (c'.1 rl1))

section Cocycle

variable (ext Stab α) in
/-- The comparison `Dual(Fun(Y, E)) → Dual E`, `f ↦ f ∘ single y₀`. -/
def evTD (ρ : Representation ℂ S E) : dualRepG (WI ext Stab ρ) →ₗ[ℂ] dualRepG (AS α ρ) :=
  (evT ext Stab α ρ.dual).comp (kapDual ext Stab E)

theorem evTD_apply (ρ : Representation ℂ S E) (f : Module.Dual ℂ (YN ext Stab → E)) (a : E) :
    evTD ext Stab α ρ f a = f (Pi.single (y0 ext Stab) a) := rfl

theorem evTD_hT (hα : ∀ g, α g ∈ Stab) (ρ : Representation ℂ S E) (g : E₂) (f : dualRepG (WI ext Stab ρ)) :
    evTD ext Stab α ρ ((dualRepG (WI ext Stab ρ)).ρ (α g) f) = (dualRepG (AS α ρ)).ρ g (evTD ext Stab α ρ f) := by
  have h := evT_hT (ext := ext) (Stab := Stab) α hα ρ.dual g (kapDual ext Stab E f)
  have h2 := kapDual_equivariant (ext := ext) (Stab := Stab) ρ (α g) f
  change evT ext Stab α ρ.dual (kapDual ext Stab E ((indRepQ (Q := YN ext Stab) ρ).dual (α g) f)) = _
  rw [h2]
  refine h.trans ?_
  change ρ.dual (α g) (kapDual ext Stab E f (y0 ext Stab)) = (Representation.dual (ρ.comp α) g) (kapDual ext Stab E f (y0 ext Stab))
  simp [Representation.dual, map_inv]

section IndDual

variable (hc : Compat ext s Stab α ext' s' ιL m0) (ρ : Representation ℂ S E)

/-- `evTD` as a map of the restrictions to the radical lattices. -/
def evTD' : Rep.res ext.inl (dualRepG (WI ext Stab ρ)) →ₗ[ℂ] Rep.res ext'.inl (dualRepG (AS α ρ)) :=
  evTD ext Stab α ρ

include hc in
/-- The cocycle pullback along `r ↦ r^{m₀}` and `T' f = f ∘ single y₀` for the contragredient. -/
def pbCocD : groupCohomology.cocycles₁ (Rep.res ext.inl (dualRepG (WI ext Stab ρ))) →ₗ[ℂ]
    groupCohomology.cocycles₁ (Rep.res ext'.inl (dualRepG (AS α ρ))) :=
  oneCocyclePullback (Rep.res ext.inl (dualRepG (WI ext Stab ρ))) (Rep.res ext'.inl (dualRepG (AS α ρ)))
    (powMonoidHom m0) (evTD' ρ) (by
      intro r
      apply LinearMap.ext
      intro f
      have h := evTD_hT hc.mem_stab ρ (ext'.inl r) f
      rw [hc.inl_eq] at h
      exact h.symm)

include hc in
/-- The cocycle map attached to the Levi coset `x`, for the contragredient. -/
def acocD (x : L ⧸ Lsub) : groupCohomology.cocycles₁ (Rep.res ext.inl (dualRepG (WI ext Stab ρ))) →ₗ[ℂ]
    groupCohomology.cocycles₁ (Rep.res ext'.inl (dualRepG (AS α ρ))) :=
  (pbCocD hc ρ).comp (splitRadicalCocycleAction s (dualRepG (WI ext Stab ρ)) (Quotient.out x)⁻¹)

include hc in
theorem acoc_kcoc (x : L ⧸ Lsub) (c' : groupCohomology.cocycles₁ (Rep.res ext.inl (dualRepG (WI ext Stab ρ)))) (r : RadicalLattice) :
    (acoc (s := s) (Lsub := Lsub) hc ρ.dual x (kcoc ext Stab ρ c')).1 r = (acocD (s := s) (Lsub := Lsub) hc ρ x c').1 r := by
  change evT ext Stab α ρ.dual (indRepQ (Q := YN ext Stab) ρ.dual (s (Quotient.out x)⁻¹)
      (kapDual ext Stab E (c'.1 (splitRadicalInput s (Quotient.out x)⁻¹ (r ^ m0))))) =
    evT ext Stab α ρ.dual (kapDual ext Stab E
      ((indRepQ (Q := YN ext Stab) ρ).dual (s (Quotient.out x)⁻¹) (c'.1 (splitRadicalInput s (Quotient.out x)⁻¹ (r ^ m0)))))
  exact congrArg (evT ext Stab α ρ.dual) (kapDual_equivariant (Stab := Stab) ρ (s (Quotient.out x)⁻¹) _).symm

theorem phiC_dualA_congr (d : groupCohomology.cocycles₁ (Rep.res ext'.inl (AS α ρ)))
    (d2 : groupCohomology.cocycles₁ (Rep.res ext'.inl (AS α ρ.dual)))
    (d3 : groupCohomology.cocycles₁ (Rep.res ext'.inl (dualRepG (AS α ρ)))) (h : ∀ r, d2.1 r = d3.1 r) :
    PhiC (Rep.res ext'.inl (AS α ρ)) (Rep.res ext'.inl (AS α ρ.dual)) (Module.Dual.eval ℂ E) d d2 =
      PhiC (Rep.res ext'.inl (AS α ρ)) (Rep.res ext'.inl (dualRepG (AS α ρ))) (Module.Dual.eval ℂ (AS α ρ)) d d3 := by
  have hact : ∀ (r : RadicalLattice) (v : Module.Dual ℂ E), (Rep.res ext'.inl (AS α ρ.dual)).ρ r v =
      (Rep.res ext'.inl (dualRepG (AS α ρ))).ρ r v := by
    intro r v
    change ρ.dual (α (ext'.inl r)) v = (Representation.dual (ρ.comp α) (ext'.inl r)) v
    simp [Representation.dual, map_inv]
  rw [PhiC_apply, PhiC_apply]
  refine congrArg₂ (· - ·) ?_ ?_
  · exact congrArg (fun v => (Module.Dual.eval ℂ E) (d.1 rl1) v) ((hact rl1 _).trans (congrArg _ (h rl2)))
  · exact congrArg (fun v => (Module.Dual.eval ℂ E) (d.1 rl2) v) ((hact rl2 _).trans (congrArg _ (h rl1)))

section Main

variable (hr : ιL.range = Lsub) [NeZero m0] [Fintype (YN ext Stab)] [Fintype (L ⧸ Lsub)]

include hc hr in
/-- **The radical identity for the literal contragredient** (scalar exactly `1`). -/
theorem phiC_ind_dual (c : groupCohomology.cocycles₁ (Rep.res ext.inl (WI ext Stab ρ)))
    (c' : groupCohomology.cocycles₁ (Rep.res ext.inl (dualRepG (WI ext Stab ρ)))) :
    PhiC (Rep.res ext.inl (WI ext Stab ρ)) (Rep.res ext.inl (dualRepG (WI ext Stab ρ))) (Module.Dual.eval ℂ (WI ext Stab ρ)) c c' =
      ∑ x : L ⧸ Lsub, PhiC (Rep.res ext'.inl (AS α ρ)) (Rep.res ext'.inl (dualRepG (AS α ρ))) (Module.Dual.eval ℂ (AS α ρ))
        (acoc (s := s) (Lsub := Lsub) hc ρ x c) (acocD (s := s) (Lsub := Lsub) hc ρ x c') := by
  rw [phiC_dual_eq]
  have he : ∀ (g : S) (a : E) (b : Module.Dual ℂ E), Module.Dual.eval ℂ E (ρ g a) (ρ.dual g b) = Module.Dual.eval ℂ E a b :=
    fun g a b => by
      change ((dualRepG (Rep.of ρ)).ρ g b) ((Rep.of ρ).ρ g a) = b a
      rw [dualRepG_inv, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [phiC_ind hc ρ ρ.dual (Module.Dual.eval ℂ E) he hr c (kcoc ext Stab ρ c')]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  exact phiC_dualA_congr ρ _ _ _ (fun r => acoc_kcoc hc ρ x c' r)

end Main

end IndDual

end Cocycle

end TernaryPeriodPolynomials.Argument.RadicalInduction
