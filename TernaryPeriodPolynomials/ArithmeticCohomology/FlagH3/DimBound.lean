module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.StabCd

@[expose] public section


/-!
# `H³` of an extension of `ℤ` by `ℤ²` has rational dimension `≤ 1`

Formalized by Claude Sonnet 5.5.

Bass-Serre dimension shifting along `ℤ` using the tree machinery (`treeSES_shortExact`, `permCoindIso`): for `π : G →* ℤ` onto with `cd (ker π) ≤ n`, the connecting map
`H^n(G, Anti(E, ℚ)) → H^{n+1}(G, ℚ)` is onto and `H^n(G, Anti(E, ℚ)) ≅ H^n(ker π, ℚ)` (`antiCohIso`, as the antisymmetric edge functions of the line are the permutation module of
the vertices).  Hence `dim H^{n+1}(G, ℚ) ≤ dim H^n(ker π, ℚ)` (`finrank_succ_le`); applied three times (`H1_int`, `H2_int2`, `H3_ext_le`) it gives `dim H³(B, ℚ) ≤ 1` for every group
extension of `ℤ` by `ℤ²`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FlagH3

open CategoryTheory CategoryTheory.Limits
open TernaryPeriodPolynomials.Argument.GammaNFaceFactor

variable {G : Type} [Group G] (π : G →* Multiplicative ℤ)

/-- The antisymmetric edge functions of the line are the functions on the vertices. -/
def antiPermEquiv : (lineTree.antiSub ℚ ℚ) ≃ₗ[ℚ] (lineTree.Vt → ℚ) where
  toFun F n := F.1 (n, false)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun P := ⟨fun e => if e.2 then -P e.1 else P e.1, fun e => by
    rcases e with ⟨n, b⟩
    cases b <;> simp [lineTree]⟩
  left_inv F := by
    apply Subtype.ext
    funext e
    rcases e with ⟨n, b⟩
    cases b
    · rfl
    · have h : F.1 (n, !true) = -F.1 (n, true) := F.2 (n, true)
      simp only [Bool.not_true] at h
      show -F.1 (n, false) = F.1 (n, true)
      rw [h, neg_neg]
  right_inv P := by
    funext n
    rfl

/-- … equivariantly. -/
def antiPermIso : Rep.of (antiRep (k := ℚ) π lineTree ℚ) ≅ Rep.of (permRep (k := ℚ) π lineTree.Vt ℚ) :=
  Rep.mkIso (Representation.Equiv.mk antiPermEquiv (fun g => by
    ext F n
    rfl))


/-- The vertices of the line form the free `ℤ`-set `ℤ × Unit`. -/
def vertEquiv : lineTree.Vt ≃ Multiplicative ℤ × Unit where
  toFun n := (Multiplicative.ofAdd (id n : ℤ), ())
  invFun p := Multiplicative.toAdd p.1
  left_inv n := rfl
  right_inv p := by rcases p with ⟨a, ⟨⟩⟩; rfl

theorem vertEquiv_smul (q : Multiplicative ℤ) (x : lineTree.Vt) :
    vertEquiv (q • x) = (q * (vertEquiv x).1, (vertEquiv x).2) := by
  show (Multiplicative.ofAdd ((id x : ℤ) + Multiplicative.toAdd q), ()) = (q * Multiplicative.ofAdd (id x : ℤ), ())
  rw [Prod.mk.injEq]
  refine ⟨?_, rfl⟩
  rw [ofAdd_add, ofAdd_toAdd]
  exact mul_comm _ _

/-- `H^n` of the antisymmetric edge functions is `H^n` of the kernel with trivial coefficients. -/
def antiCohIso (hπ : Function.Surjective π) (n : ℕ) :
    groupCohomology (Rep.of (antiRep (k := ℚ) π lineTree ℚ)) n ≃ₗ[ℚ] groupCohomology (Rep.trivial ℚ π.ker ℚ) n :=
  let i1 := (groupCohomology.functor ℚ G n).mapIso
    (antiPermIso π ≪≫ permCoindIso π lineTree.Vt ℚ vertEquiv vertEquiv_smul hπ)
  let i2 := groupCohomology.coindIso (Rep.trivial ℚ π.ker (Unit → ℚ)) n
  let i3 := groupCohomology.mapIso (MulEquiv.refl π.ker) (B := Rep.trivial ℚ π.ker (Unit → ℚ))
    (A := Rep.trivial ℚ π.ker ℚ) (LinearEquiv.funUnique Unit ℚ ℚ) (fun g => by ext; rfl) n
  (i1 ≪≫ i2 ≪≫ i3).toLinearEquiv


/-- **Connecting map onto the next degree**: if the kernel of `π : G →* ℤ` has cohomological dimension `≤ n`, the connecting map
`H^n(G, Anti(E, ℚ)) → H^{n+1}(G, ℚ)` of the line tree is surjective. -/
theorem delta_surjective (hπ : Function.Surjective π) (n : ℕ) (hK : CdLe ℚ π.ker n) :
    Function.Surjective (groupCohomology.δ (treeSES_shortExact (k := ℚ) π lineTree ℚ) n (n + 1) rfl).hom := by
  have hSES := treeSES_shortExact (k := ℚ) π lineTree ℚ
  obtain ⟨Iv, ev, hev⟩ := exists_free_decomp (Multiplicative ℤ) lineTree.Vt lineTree.free_v
  have hV : IsZero (groupCohomology (treeSES (k := ℚ) π lineTree ℚ).X₂ (n + 1)) :=
    isZero_perm π lineTree.Vt ℚ ev hev hπ hK (n + 1) (by omega)
  have hepi : Epi (groupCohomology.δ hSES n (n + 1) rfl) := groupCohomology.epi_δ_of_isZero hSES n hV
  exact (ModuleCat.epi_iff_surjective _).1 hepi

/-- **Dimension shifting along `ℤ`.**  If `π : G →* ℤ` is onto and `ker π` has cohomological dimension `≤ n` with `H^n(ker π, ℚ)` finite
dimensional, then `H^{n+1}(G, ℚ)` is finite dimensional of dimension at most that of `H^n(ker π, ℚ)`. -/
theorem finrank_succ_le (hπ : Function.Surjective π) (n : ℕ) (hK : CdLe ℚ π.ker n)
    [Module.Finite ℚ (groupCohomology (Rep.trivial ℚ π.ker ℚ) n)] :
    Module.Finite ℚ (groupCohomology (Rep.trivial ℚ G ℚ) (n + 1)) ∧
      Module.finrank ℚ (groupCohomology (Rep.trivial ℚ G ℚ) (n + 1)) ≤
        Module.finrank ℚ (groupCohomology (Rep.trivial ℚ π.ker ℚ) n) := by
  have hs := delta_surjective π hπ n hK
  let e := antiCohIso π hπ n
  have : Module.Finite ℚ (groupCohomology (Rep.of (antiRep (k := ℚ) π lineTree ℚ)) n) :=
    Module.Finite.equiv e.symm
  let f : groupCohomology (Rep.of (antiRep (k := ℚ) π lineTree ℚ)) n →ₗ[ℚ] groupCohomology (Rep.trivial ℚ G ℚ) (n + 1) :=
    (groupCohomology.δ (treeSES_shortExact (k := ℚ) π lineTree ℚ) n (n + 1) rfl).hom
  have hf : Function.Surjective f := hs
  refine ⟨Module.Finite.of_surjective f hf, ?_⟩
  calc _ ≤ Module.finrank ℚ (groupCohomology (Rep.of (antiRep (k := ℚ) π lineTree ℚ)) n) :=
        LinearMap.finrank_le_finrank_of_surjective hf
    _ = _ := e.finrank_eq


/-- Cohomology with trivial coefficients is invariant under isomorphism of groups. -/
def cohEquivOfMulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G') (n : ℕ) :
    groupCohomology (Rep.trivial ℚ G ℚ) n ≃ₗ[ℚ] groupCohomology (Rep.trivial ℚ G' ℚ) n :=
  (groupCohomology.mapIso e (B := Rep.trivial ℚ G ℚ) (A := Rep.trivial ℚ G' ℚ) (LinearEquiv.refl ℚ ℚ)
    (fun g => by ext; rfl) n).toLinearEquiv

/-- `H^0(G, ℚ)` is one-dimensional. -/
theorem H0_trivial (G : Type) [Group G] :
    Module.Finite ℚ (groupCohomology (Rep.trivial ℚ G ℚ) 0) ∧ Module.finrank ℚ (groupCohomology (Rep.trivial ℚ G ℚ) 0) = 1 := by
  let e := (groupCohomology.H0IsoOfIsTrivial (Rep.trivial ℚ G ℚ)).toLinearEquiv
  exact ⟨Module.Finite.equiv e.symm, by rw [e.finrank_eq]; simp⟩

/-- `H^1(ℤ, ℚ)` has dimension `≤ 1`. -/
theorem H1_int : Module.Finite ℚ (groupCohomology (Rep.trivial ℚ (Multiplicative ℤ) ℚ) 1) ∧
    Module.finrank ℚ (groupCohomology (Rep.trivial ℚ (Multiplicative ℤ) ℚ) 1) ≤ 1 := by
  have hsub : Subsingleton (MonoidHom.id (Multiplicative ℤ)).ker :=
    ⟨fun a b => Subtype.ext (by
      have ha := MonoidHom.mem_ker.mp a.2
      have hb := MonoidHom.mem_ker.mp b.2
      exact ha.trans hb.symm)⟩
  have h0 : CdLe ℚ (MonoidHom.id (Multiplicative ℤ)).ker 0 := cdLe_zero_of_subsingleton _
  have := (H0_trivial (MonoidHom.id (Multiplicative ℤ)).ker).1
  obtain ⟨h1, h2⟩ := finrank_succ_le (MonoidHom.id (Multiplicative ℤ)) (fun x => ⟨x, rfl⟩) 0 h0
  exact ⟨h1, h2.trans (H0_trivial _).2.le⟩

/-- `H^2(ℤ², ℚ)` has dimension `≤ 1`. -/
theorem H2_int2 : Module.Finite ℚ (groupCohomology (Rep.trivial ℚ (Multiplicative (ℤ × ℤ)) ℚ) 2) ∧
    Module.finrank ℚ (groupCohomology (Rep.trivial ℚ (Multiplicative (ℤ × ℤ)) ℚ) 2) ≤ 1 := by
  have h1 : CdLe ℚ projFst.ker 1 := CdLe.of_mulEquiv projFstKer.symm cdLe_int
  let e := cohEquivOfMulEquiv projFstKer 1
  have : Module.Finite ℚ (groupCohomology (Rep.trivial ℚ projFst.ker ℚ) 1) :=
    have := H1_int.1
    Module.Finite.equiv e.symm
  obtain ⟨h2, h3⟩ := finrank_succ_le projFst (fun m => ⟨Multiplicative.ofAdd (Multiplicative.toAdd m, 0), rfl⟩) 1 h1
  refine ⟨h2, h3.trans ?_⟩
  rw [e.finrank_eq]
  exact H1_int.2

/-- **`H^3` of an extension of `ℤ` by `ℤ²` has dimension `≤ 1` (rational coefficients).** -/
theorem H3_ext_le {B : Type} [Group B] (X : GroupExtension (Multiplicative (ℤ × ℤ)) B (Multiplicative ℤ)) :
    Module.Finite ℚ (groupCohomology (Rep.trivial ℚ B ℚ) 3) ∧
      Module.finrank ℚ (groupCohomology (Rep.trivial ℚ B ℚ) 3) ≤ 1 := by
  let eK : (Multiplicative (ℤ × ℤ)) ≃* X.rightHom.ker :=
    (MonoidHom.ofInjective X.inl_injective).trans (MulEquiv.subgroupCongr X.range_inl_eq_ker_rightHom)
  have h2 : CdLe ℚ X.rightHom.ker 2 := CdLe.of_mulEquiv eK cdLe_int2
  let e := cohEquivOfMulEquiv eK 2
  have : Module.Finite ℚ (groupCohomology (Rep.trivial ℚ X.rightHom.ker ℚ) 2) :=
    have := H2_int2.1
    Module.Finite.equiv e
  obtain ⟨h3, h4⟩ := finrank_succ_le X.rightHom X.rightHom_surjective 2 h2
  refine ⟨h3, h4.trans ?_⟩
  rw [← e.finrank_eq]
  exact H2_int2.2



end TernaryPeriodPolynomials.Argument.FlagH3
