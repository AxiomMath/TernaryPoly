module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.NFTAlg

@[expose] public section


/-!
# Normal-form transfer, algebraic core: the plane flag cochain

Formalized by Claude Sonnet 5.5.

With the notation of `NFTAlg` (`zb = zx + dκ`, `zb' = zy + dκ'`, `dd3T gb = cup22 zb zb'`), and a primitive `w̄'` of `zb' ∘ ι` on a group `H` with `ι : H → E`, the plane flag cochain
`cup21 (zb ∘ ι) (-w̄') + gb ∘ ι` differs by a coboundary `dd2T χ` from `cup21 (zx ∘ ι) (-(w̄' - κ' ∘ ι)) + (γ - dd2T ε) ∘ ι`, where `γ = nfGamma0 ... gb` is the same normal-form primitive as for lines (`nfThetaP_eq`).
`nf_primitiveP`: `w̄' - κ' ∘ ι` is a primitive of `zy ∘ ι`; `nfThetaP_dd3T`: the transferred plane flag cochain is a cocycle.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

section NFP

variable {E : Type} [Group E] {V W : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
  {ρ : Representation ℚ E V} {ρ' : Representation ℚ E W} {e : V →ₗ[ℚ] W →ₗ[ℚ] ℚ}
  {H : Type} [Group H] (ι : H →* E) {ρH : Representation ℚ H V} {ρH' : Representation ℚ H W}

/-- The primitive `wb' - κ' ∘ ι` of `zy ∘ ι`. -/
theorem nf_primitiveP (hρ' : ∀ (s : H) (w : W), ρ' (ι s) w = ρH' s w)
    (zy zb' : E → E → W) (κ' : E → W) (h2 : zb' = zy + dd1 ρ' κ')
    (wb' : H → W) (hw : dd1 ρH' wb' = fun s t => zb' (ι s) (ι t)) :
    dd1 ρH' (wb' - fun s => κ' (ι s)) = fun s t => zy (ι s) (ι t) := by
  have hk := dd1_pull ι hρ' κ'
  funext s t
  have h3 := congrFun (congrFun hw s) t
  have h4 := congrFun (congrFun hk s) t
  have h5 := congrFun (congrFun h2 (ι s)) (ι t)
  simp only [dd1, Pi.add_apply, Pi.sub_apply, map_sub, ι.map_mul, hρ'] at h3 h4 h5 ⊢
  linear_combination (norm := module) h3 + h5

/-- **The plane flag cochain of `H` changes by a coboundary under the normal-form transfer.** -/
theorem nfThetaP_eq (hρ : ∀ (s : H) (v : V), ρ (ι s) v = ρH s v) (hρ' : ∀ (s : H) (w : W), ρ' (ι s) w = ρH' s w)
    (he : ∀ (g : E) (v : V) (w : W), e (ρ g v) (ρ' g w) = e v w)
    (zx zb : E → E → V) (zy zb' : E → E → W) (κ : E → V) (κ' : E → W) (gb : E → E → E → ℚ) (ε : E → E → ℚ)
    (h1 : zb = zx + dd1 ρ κ) (h2 : zb' = zy + dd1 ρ' κ')
    (wb' : H → W) (hw : dd1 ρH' wb' = fun s t => zb' (ι s) (ι t)) :
    (fun a b c : H => cup21 ρH' e (fun s t => zb (ι s) (ι t)) (-wb') a b c + gb (ι a) (ι b) (ι c)) =
      (fun a b c : H => cup21 ρH' e (fun s t => zx (ι s) (ι t)) (-(wb' - fun s => κ' (ι s))) a b c +
        (nfGamma0 ρ' e zb κ κ' zy gb - dd2T ε) (ι a) (ι b) (ι c)) +
      dd2T ((fun s t : H => ε (ι s) (ι t)) - cup11 ρH' e (fun s => κ (ι s)) (wb' - fun s => κ' (ι s))) := by
  have heH := pull_inv ι hρ hρ' he
  have hprim := nf_primitiveP ι hρ' zy zb' κ' h2 wb' hw
  have hl := leibniz11 heH (fun s => κ (ι s)) (wb' - fun s => κ' (ι s))
  rw [hprim, dd1_pull ι hρ κ] at hl
  have f3 : ∀ (a b : H) (w : W), ρ' (ι a * ι b) w = ρH' (a * b) w := by
    intro a b w
    rw [← ι.map_mul]
    exact hρ' _ _
  funext a b c
  have hl' := congrFun (congrFun (congrFun hl a) b) c
  have h1' := congrFun (congrFun h1 (ι a)) (ι b)
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, nfGamma0, dd2T, cup12, cup21, cup11, dd1, ι.map_mul, f3, hρ',
    map_add, map_sub, map_neg] at hl' h1' ⊢
  rw [h1']
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply] at hl' ⊢
  linear_combination (norm := module) hl'

/-- **The transferred plane flag cochain is a cocycle.** -/
theorem nfThetaP_dd3T (hρ : ∀ (s : H) (v : V), ρ (ι s) v = ρH s v) (hρ' : ∀ (s : H) (w : W), ρ' (ι s) w = ρH' s w)
    (heH : ∀ (g : H) (v : V) (w : W), e (ρH g v) (ρH' g w) = e v w)
    (zx : E → E → V) (zy : E → E → W) (gn : E → E → E → ℚ) (hzx : dd2 ρ zx = 0)
    (hγ : dd3T gn = cup22 ρ' e zx zy) (wn : H → W) (hwn : dd1 ρH' wn = fun s t => zy (ι s) (ι t)) :
    dd3T (fun a b c : H => cup21 ρH' e (fun s t => zx (ι s) (ι t)) (-wn) a b c + gn (ι a) (ι b) (ι c)) = 0 := by
  have hz : dd2 ρH (fun s t => zx (ι s) (ι t)) = 0 := by
    funext a b c
    have := congrFun (congrFun (congrFun hzx (ι a)) (ι b)) (ι c)
    simp only [dd2, map_mul, hρ, Pi.zero_apply] at this ⊢
    exact this
  have h0 : dd3T (fun a b c : H => cup21 ρH' e (fun s t => zx (ι s) (ι t)) (-wn) a b c + gn (ι a) (ι b) (ι c)) =
      dd3T (cup21 ρH' e (fun s t => zx (ι s) (ι t)) (-wn)) + dd3T (fun a b c : H => gn (ι a) (ι b) (ι c)) := by
    funext g1 g2 g3 g4
    simp only [dd3T, Pi.add_apply]
    ring
  have hd1 : dd1 ρH' (-wn) = fun s t => -zy (ι s) (ι t) := by
    funext s t
    have := congrFun (congrFun hwn s) t
    simp only [dd1, Pi.neg_apply, map_neg] at this ⊢
    rw [← sub_eq_zero] at this ⊢
    rw [← neg_eq_zero]
    rw [← this]
    abel
  rw [h0, leibniz21 heH _ hz, hd1, dd3T_pull, hγ]
  funext a b c d
  simp only [Pi.add_apply, Pi.zero_apply, cup22, map_neg, ← ι.map_mul, hρ']
  ring

end NFP

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
