import OptimalG.ThreeClassProfile
import OptimalG.TwoClassLimit

/-! # Positive auxiliary weights correct rounded class balances exactly -/

namespace OptimalG
open Set Filter
open scoped Topology

/-- Two positive auxiliary classes, with scores P and -R, remove any vanishing
class-balance error. Their common strictly negative reference score creates a
strict margin, while an arbitrarily small total weight preserves cost excess. -/
theorem exists_eventually_positive_auxiliary_correction
    (lam R P A B S : ℝ) (hlam : 0 ≤ lam) (hR : 0 < R) (hP : 0 < P)
    (hA : A ≤ 0) (hB : 0 < B) (hS : S < 0)
    (rn pn en an bn sn : ℕ → ℝ)
    (hr : Tendsto rn atTop (𝓝 R)) (hp : Tendsto pn atTop (𝓝 P))
    (he : Tendsto en atTop (𝓝 0)) (ha : Tendsto an atTop (𝓝 A))
    (hb : Tendsto bn atTop (𝓝 B)) (hs : Tendsto sn atTop (𝓝 S)) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ᶠ n in atTop,
      let u := eps * rn n - en n / (pn n + rn n)
      let v := eps * pn n + en n / (pn n + rn n)
      0 < u ∧ 0 < v ∧ en n + u * pn n - v * rn n = 0 ∧
        an n + (u + v) * sn n < 0 ∧ 0 < bn n - 2 * lam * (u + v) := by
  let eps := B / (4 * (lam + 1) * (R + P))
  have hden : 0 < 4 * (lam + 1) * (R + P) := by positivity
  have heps : 0 < eps := div_pos hB hden
  have hsum : 0 < R + P := add_pos hR hP
  have hsum' : P + R ≠ 0 := ne_of_gt (add_pos hP hR)
  have hprod : eps * (4 * (lam + 1) * (R + P)) = B := div_mul_cancel₀ B (ne_of_gt hden)
  have hlimitB : 0 < B - 2 * lam * (eps * R + eps * P) := by
    have hpos : 0 < eps * (R + P) := mul_pos heps hsum
    have hnonneg : 0 ≤ lam * (eps * (R + P)) := mul_nonneg hlam hpos.le
    nlinarith only [hprod, hpos, hnonneg]
  have hlimitA : A + (eps * R + eps * P) * S < 0 := by
    have hneg : (eps * R + eps * P) * S < 0 := mul_neg_of_pos_of_neg (add_pos (mul_pos heps hR) (mul_pos heps hP)) hS
    linarith
  let u := fun n => eps * rn n - en n / (pn n + rn n)
  let v := fun n => eps * pn n + en n / (pn n + rn n)
  have hquot : Tendsto (fun n => en n / (pn n + rn n)) atTop (𝓝 0) := by
    have hq := he.div (hp.add hr) hsum'
    change Tendsto (fun n => en n / (pn n + rn n)) atTop (𝓝 (0 / (P + R))) at hq
    simpa only [zero_div] using hq
  have hu : Tendsto u atTop (𝓝 (eps * R)) := by
    simpa only [sub_zero] using (tendsto_const_nhds.mul hr).sub hquot
  have hv : Tendsto v atTop (𝓝 (eps * P)) := by
    simpa only [add_zero] using (tendsto_const_nhds.mul hp).add hquot
  have hreference := (ha.add ((hu.add hv).mul hs)).eventually_lt_const hlimitA
  have hcost := (hb.sub (tendsto_const_nhds.mul (hu.add hv))).eventually_const_lt hlimitB
  refine ⟨eps, heps, ?_⟩
  filter_upwards [hu.eventually_const_lt (mul_pos heps hR), hv.eventually_const_lt (mul_pos heps hP),
    (hp.add hr).eventually_ne hsum', hreference, hcost] with n hnu hnv hnDen hnA hnB
  refine ⟨hnu, hnv, ?_, hnA, hnB⟩
  field_simp
  ring

end OptimalG
