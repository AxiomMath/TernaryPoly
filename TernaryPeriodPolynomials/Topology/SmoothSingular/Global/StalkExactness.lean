module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SingularSheaf

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Limits Opposite TopologicalSpace Set
open TopCat.Presheaf
open SymmetricSpaceCovering

/-- Actual local section lifting proves exactness on stalks; the local hypothesis is discharged
by the genuine quotient Poincaré lemma in the smooth application. -/
theorem stalk_exact_of_local_lifting
    (S : ShortComplex (TopCat.Presheaf (ModuleCat ℝ) (TopCat.of OrbitSpace)))
    (hlocal : ∀ (U : Opens (TopCat.of OrbitSpace)) (q : OrbitSpace) (_ : q ∈ U)
      (w : S.X₂.obj (op U)), S.g.app (op U) w = 0 →
        ∃ (V : Opens (TopCat.of OrbitSpace)) (_hqV : q ∈ V) (i : V ⟶ U)
          (z : S.X₁.obj (op V)), S.f.app (op V) z = S.X₂.map i.op w)
    (q : OrbitSpace) : (S.map (stalkFunctor (ModuleCat ℝ) q)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro w hw
  obtain ⟨U, hqU, u, rfl⟩ := exists_germ_eq S.X₂ w
  change (stalkFunctor (ModuleCat ℝ) q).map S.g (S.X₂.germ U q hqU u) = 0 at hw
  rw [stalkFunctor_map_germ_apply] at hw
  change S.X₃.germ U q hqU (S.g.app (op U) u) = (0 : S.X₃.stalk q) at hw
  have hzero : S.X₃.germ U q hqU (S.g.app (op U) u) = S.X₃.germ U q hqU 0 := by
    simpa only [map_zero] using hw
  obtain ⟨W, hqW, iWU, _, he⟩ := germ_eq S.X₃ q hqU hqU _ _ hzero
  have hz : S.g.app (op W) (S.X₂.map iWU.op u) = 0 := by
    have hn := congrArg (fun k => k u) (S.g.naturality iWU.op)
    exact hn.trans (he.trans (map_zero _))
  obtain ⟨V, hqV, iVW, z, hprim⟩ := hlocal W q hqW (S.X₂.map iWU.op u) hz
  refine ⟨S.X₁.germ V q hqV z, ?_⟩
  change (stalkFunctor (ModuleCat ℝ) q).map S.f (S.X₁.germ V q hqV z) = _
  rw [stalkFunctor_map_germ_apply, hprim]
  rw [germ_res_apply, germ_res_apply]

end TernaryPoly.SmoothSingularGlobal
