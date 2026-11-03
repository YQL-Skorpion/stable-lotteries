import OptimalG.TailContact
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen

/-! A cap upper bound at the delayed rank and the exact affine head make a
mixed-test envelope convex in the initial split. Its two endpoint checks
therefore control the whole cap-shift region. -/
namespace OptimalG
open Set Variational

noncomputable def capHeadEnvelope (lam S shift phi0 slope A B K q : ℝ) : ℝ :=
  A+B*q+K*(cap lam S (shift+q)-phi0*q-slope*q^2/2)

theorem capHeadEnvelope_convex {lam S shift phi0 slope A B K a b : ℝ}
    (hK : 0≤K) (harg : shift+b<1)
    (hcap : ∀ u∈Icc a b,∀ v∈Icc a b,u≤v→
      slope*(v-u)≤capScore lam S (shift+v)-capScore lam S (shift+u)) :
    ConvexOn ℝ (Icc a b) (capHeadEnvelope lam S shift phi0 slope A B K) := by
  have hd (q : ℝ) (hq : q∈Icc a b) :
      HasDerivAt (capHeadEnvelope lam S shift phi0 slope A B K)
        (B+K*(capScore lam S (shift+q)-phi0-slope*q)) q := by
    have hcapd := (cap_hasDerivAt lam S (shift+q)
      (ne_of_lt (by linarith only [hq.2,harg]))).comp q
      ((hasDerivAt_id q).const_add shift)
    have hhead := ((hasDerivAt_id q).const_mul phi0).add
      (((hasDerivAt_id q).pow 2).const_mul (slope/2))
    have hh := (((hasDerivAt_id q).const_mul B).const_add A).add
      ((hcapd.sub hhead).const_mul K)
    convert! hh using 1
    · funext x
      dsimp [capHeadEnvelope,Function.comp_def]
      ring
    · simp only [id_eq,mul_one,Nat.cast_ofNat,Nat.reduceSub,pow_one]
      ring
  have hcont : ContinuousOn (capHeadEnvelope lam S shift phi0 slope A B K) (Icc a b) :=
    fun q hq => (hd q hq).continuousAt.continuousWithinAt
  apply MonotoneOn.convexOn_of_deriv (convex_Icc a b) hcont
    (fun q hq => (hd q (interior_subset hq)).differentiableAt.differentiableWithinAt)
  intro u hu v hv huv
  rw [(hd u (interior_subset hu)).deriv,(hd v (interior_subset hv)).deriv]
  have hh := hcap u (interior_subset hu) v (interior_subset hv) huv
  have hm := mul_le_mul_of_nonneg_left hh hK
  nlinarith only [hm]

theorem capHeadEnvelope_le_endpoints {lam S shift phi0 slope A B K a b : ℝ}
    (hK : 0≤K) (hab : a≤b) (harg : shift+b<1)
    (hcap : ∀ u∈Icc a b,∀ v∈Icc a b,u≤v→
      slope*(v-u)≤capScore lam S (shift+v)-capScore lam S (shift+u))
    (ha : capHeadEnvelope lam S shift phi0 slope A B K a≤0)
    (hb : capHeadEnvelope lam S shift phi0 slope A B K b≤0) :
    ∀ q∈Icc a b,capHeadEnvelope lam S shift phi0 slope A B K q≤0 := by
  intro q hq
  have hh := (capHeadEnvelope_convex (phi0:=phi0) (A:=A) (B:=B) hK harg hcap).le_max_of_mem_Icc
    (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hq
  exact hh.trans (max_le ha hb)

end OptimalG
