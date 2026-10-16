module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.Push.ConeLeibniz
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.Push.ConeStrata
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.PairingComparison

@[expose] public section


/-!
# The cone diagonal pairing of two degree-two cone cochains, in coordinates

For a pushout cone `K` of `a : A ⟶ L`, `b : A ⟶ P`, cochains `b̃, ã : K.X 2 ⟶ W` and an invariant pairing `π`, the
pairing `π ∘ (b̃ ⊗ ã) ∘ Δ_{2,2}` on `K.X 4` is, on the three coordinates of `v`, the sum of the line pairing on `v_L`, the
plane pairing on `v_P` and the two corner terms `c_b ⌣ (a^* l_a)` and `(b^* p_b) ⌣ c_a` on `v_A`.  If the line (plane)
pairing is the coboundary of a primitive `γ_L` (`γ_P`) and `v` is a coinvariant cycle, the primitives contribute
`-a^* γ_L + b^* γ_P` on the corner (`pair_cycle`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

variable {Γ : Type} [Group Γ]
  {A L P K : ChainComplex (Rep.{0} ℚ Γ) ℕ} {a : A ⟶ L} {b : A ⟶ P}

namespace PushCone

variable (𝒞 : PushCone A L P K a b) (SA : DiagSystem A) (SL : DiagSystem L) (SP : DiagSystem P)
  {W W' T : Rep.{0} ℚ Γ} (π : W ⊗ W' ⟶ T) (bt : K.X 2 ⟶ W) (at' : K.X 2 ⟶ W')

theorem iL_pair : 𝒞.iL 4 ≫ 𝒞.Δ SA SL SP 2 2 4 rfl ≫ (bt ⊗ₘ at') ≫ π =
    SL.Δ 2 2 4 rfl ≫ ((𝒞.iL 2 ≫ bt) ⊗ₘ (𝒞.iL 2 ≫ at')) ≫ π := by
  rw [← Category.assoc, iL_Δ']
  simp only [Category.assoc]
  rw [← Category.assoc (𝒞.iL 2 ⊗ₘ 𝒞.iL 2), MonoidalCategory.tensorHom_comp_tensorHom]

theorem iP_pair : 𝒞.iP 4 ≫ 𝒞.Δ SA SL SP 2 2 4 rfl ≫ (bt ⊗ₘ at') ≫ π =
    SP.Δ 2 2 4 rfl ≫ ((𝒞.iP 2 ≫ bt) ⊗ₘ (𝒞.iP 2 ≫ at')) ≫ π := by
  rw [← Category.assoc, iP_Δ']
  simp only [Category.assoc]
  rw [← Category.assoc (𝒞.iP 2 ⊗ₘ 𝒞.iP 2), MonoidalCategory.tensorHom_comp_tensorHom]

theorem iA_pair : 𝒞.iA 3 ≫ 𝒞.Δ SA SL SP 2 2 4 rfl ≫ (bt ⊗ₘ at') ≫ π =
    SA.Δ 1 2 3 rfl ≫ ((𝒞.iA 1 ≫ bt) ⊗ₘ (a.f 2 ≫ 𝒞.iL 2 ≫ at')) ≫ π +
    SA.Δ 2 1 3 rfl ≫ ((b.f 2 ≫ 𝒞.iP 2 ≫ bt) ⊗ₘ (𝒞.iA 1 ≫ at')) ≫ π := by
  rw [← Category.assoc, iA_Δ]
  have e : 𝒞.aPart SA 2 2 3 rfl = 𝒞.tI SA 1 2 3 rfl + 𝒞.tII SA 2 1 3 rfl := by
    simp [aPart, tIc, tIIc]
  rw [e, Preadditive.add_comp]
  unfold tI tII
  simp only [Category.assoc]
  rw [← Category.assoc (𝒞.iA 1 ⊗ₘ (a.f 2 ≫ 𝒞.iL 2)), MonoidalCategory.tensorHom_comp_tensorHom,
    ← Category.assoc ((b.f 2 ≫ 𝒞.iP 2) ⊗ₘ 𝒞.iA 1), MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Category.assoc]

/-- **The pairing of two degree-two cone cochains on a coinvariant cycle.**  If the line and plane pairings are the
coboundaries of primitives `γL`, `γP`, the pairing of `v` reduces to the corner value of `v_A`. -/
theorem pair_cycle (π0 : W ⊗ W' ⟶ 𝟙_ (Rep.{0} ℚ Γ)) (v : K.X 4) (hv : IsCoinvCycle v)
    (γL : L.X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ)) (γP : P.X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ))
    (hL : L.d 4 3 ≫ γL = SL.Δ 2 2 4 rfl ≫ ((𝒞.iL 2 ≫ bt) ⊗ₘ (𝒞.iL 2 ≫ at')) ≫ π0)
    (hP : P.d 4 3 ≫ γP = SP.Δ 2 2 4 rfl ≫ ((𝒞.iP 2 ≫ bt) ⊗ₘ (𝒞.iP 2 ≫ at')) ≫ π0) :
    (𝒞.Δ SA SL SP 2 2 4 rfl ≫ (bt ⊗ₘ at') ≫ π0).hom v =
      ((SA.Δ 1 2 3 rfl ≫ ((𝒞.iA 1 ≫ bt) ⊗ₘ (a.f 2 ≫ 𝒞.iL 2 ≫ at')) ≫ π0 +
          SA.Δ 2 1 3 rfl ≫ ((b.f 2 ≫ 𝒞.iP 2 ≫ bt) ⊗ₘ (𝒞.iA 1 ≫ at')) ≫ π0) - a.f 3 ≫ γL + b.f 3 ≫ γP).hom
        ((𝒞.pA 3).hom v) := by
  have hdec := 𝒞.decomp_succ 3 v
  generalize (𝒞.pA 3).hom v = x at hdec ⊢
  generalize (𝒞.pL 3).hom v = l at hdec
  generalize (𝒞.pP 3).hom v = p at hdec
  subst hdec
  have hA : (𝒞.iA 3 ≫ 𝒞.Δ SA SL SP 2 2 4 rfl ≫ (bt ⊗ₘ at') ≫ π0).hom x =
      (SA.Δ 1 2 3 rfl ≫ ((𝒞.iA 1 ≫ bt) ⊗ₘ (a.f 2 ≫ 𝒞.iL 2 ≫ at')) ≫ π0 +
        SA.Δ 2 1 3 rfl ≫ ((b.f 2 ≫ 𝒞.iP 2 ≫ bt) ⊗ₘ (𝒞.iA 1 ≫ at')) ≫ π0).hom x :=
    congrArg (fun m => m.hom x) (𝒞.iA_pair SA SL SP π0 bt at')
  have hLp : (𝒞.iL 4 ≫ 𝒞.Δ SA SL SP 2 2 4 rfl ≫ (bt ⊗ₘ at') ≫ π0).hom l =
      (SL.Δ 2 2 4 rfl ≫ ((𝒞.iL 2 ≫ bt) ⊗ₘ (𝒞.iL 2 ≫ at')) ≫ π0).hom l :=
    congrArg (fun m => m.hom l) (𝒞.iL_pair SA SL SP π0 bt at')
  have hPp : (𝒞.iP 4 ≫ 𝒞.Δ SA SL SP 2 2 4 rfl ≫ (bt ⊗ₘ at') ≫ π0).hom p =
      (SP.Δ 2 2 4 rfl ≫ ((𝒞.iP 2 ≫ bt) ⊗ₘ (𝒞.iP 2 ≫ at')) ≫ π0).hom p :=
    congrArg (fun m => m.hom p) (𝒞.iP_pair SA SL SP π0 bt at')
  have hLc : (L.d 4 3 ≫ γL).hom l =
      (SL.Δ 2 2 4 rfl ≫ ((𝒞.iL 2 ≫ bt) ⊗ₘ (𝒞.iL 2 ≫ at')) ≫ π0).hom l :=
    congrArg (fun m => m.hom l) hL
  have hPc : (P.d 4 3 ≫ γP).hom p =
      (SP.Δ 2 2 4 rfl ≫ ((𝒞.iP 2 ≫ bt) ⊗ₘ (𝒞.iP 2 ≫ at')) ≫ π0).hom p :=
    congrArg (fun m => m.hom p) hP
  have hd : (K.d 4 3).hom ((𝒞.iA 3).hom x + (𝒞.iL 4).hom l + (𝒞.iP 4).hom p) =
      (-(𝒞.iA 2).hom ((A.d 3 2).hom x) + (𝒞.iL 3).hom ((a.f 3).hom x) - (𝒞.iP 3).hom ((b.f 3).hom x)) +
        (𝒞.iL 3).hom ((L.d 4 3).hom l) + (𝒞.iP 3).hom ((P.d 4 3).hom p) := by
    rw [map_add, map_add]
    exact congrArg₂ (· + ·) (congrArg₂ (· + ·) (𝒞.d_iA_succ 2 x) (𝒞.d_iL 3 l)) (𝒞.d_iP 3 p)
  have cL : γL.hom ((𝒞.pL 2).hom ((K.d 4 3).hom ((𝒞.iA 3).hom x + (𝒞.iL 4).hom l + (𝒞.iP 4).hom p))) = 0 :=
    hv (𝒞.pL 2 ≫ γL)
  have cP : γP.hom ((𝒞.pP 2).hom ((K.d 4 3).hom ((𝒞.iA 3).hom x + (𝒞.iL 4).hom l + (𝒞.iP 4).hom p))) = 0 :=
    hv (𝒞.pP 2 ≫ γP)
  rw [hd] at cL cP
  simp only [map_add, map_sub, map_neg, 𝒞.pL_iA, 𝒞.pL_iL, 𝒞.pL_iP,
    𝒞.pP_iA, 𝒞.pP_iL, 𝒞.pP_iP, neg_zero, zero_add, add_zero, zero_sub, sub_zero] at cL cP
  have e1 : γL.hom ((L.d 4 3).hom l) = - γL.hom ((a.f 3).hom x) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact cL
  have e2 : γP.hom ((P.d 4 3).hom p) = γP.hom ((b.f 3).hom x) := by
    rw [← sub_eq_zero]; rw [← cP]; abel
  rw [map_add, map_add]
  erw [hA, hLp, hPp, ← hLc, ← hPc]
  have e3 : (Rep.Hom.hom (L.d 4 3 ≫ γL)) l = γL.hom ((L.d 4 3).hom l) := rfl
  have e4 : (Rep.Hom.hom (P.d 4 3 ≫ γP)) p = γP.hom ((P.d 4 3).hom p) := rfl
  rw [e3, e4, e1, e2]
  simp only [Rep.add_hom, Rep.sub_hom, Representation.IntertwiningMap.coe_add,
    Representation.IntertwiningMap.coe_sub, Pi.add_apply, Pi.sub_apply]
  have e5 : (Rep.Hom.hom (a.f 3 ≫ γL)) x = γL.hom ((a.f 3).hom x) := rfl
  have e6 : (Rep.Hom.hom (b.f 3 ≫ γP)) x = γP.hom ((b.f 3).hom x) := rfl
  rw [e5, e6]
  abel

end PushCone

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
