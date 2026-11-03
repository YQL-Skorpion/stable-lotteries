import OptimalG.SigmaIntegralBounds

/-! Exact elimination of the unknown intermediate score in C.17 and C.19,
and connection to the actual slack integrals. -/
namespace OptimalG
open Set MeasureTheory

/-- Eliminating the intermediate height between the prefix and tail cone bounds
produces the difference of two positive-part squares. -/
theorem sigma_area_elimination {E v s k d : ℝ} (hk : 0<k) (hs : 0≤s)
    (hv : 0≤v) (hvs : v≤s)
    (h1 : v^2≤2*k*E) (h2 : 2*k*s*d-2*s*v+v^2≤2*k*E) :
    k/2*((max d 0)^2-(max (d-s/k) 0)^2)≤E := by
  have hE : 0≤E := by nlinarith [sq_nonneg v]
  have hsk : 0≤s/k := div_nonneg hs hk.le
  by_cases hd : d≤0
  · rw [max_eq_right hd,max_eq_right (by linarith : d-s/k≤0)]
    simpa using hE
  · have hd0 : 0≤d := (lt_of_not_ge hd).le
    rw [max_eq_left hd0]
    by_cases hds : s/k≤d
    · rw [max_eq_left (sub_nonneg.mpr hds)]
      have he : 2*k*(k/2*(d^2-(d-s/k)^2))=2*k*s*d-s^2 := by
        field_simp
        ring
      apply (mul_le_mul_iff_right₀ (show 0<2*k by positivity)).mp
      rw [he]
      nlinarith [sq_nonneg (s-v)]
    · rw [max_eq_right (by linarith : d-s/k≤0)]
      have hkd : k*d≤s := by
        have hh := (lt_div_iff₀ hk).mp (lt_of_not_ge hds)
        nlinarith
      apply (mul_le_mul_iff_right₀ (show 0<2*k by positivity)).mp
      by_cases hkv : k*d≤v
      · have hh := mul_nonneg (sub_nonneg.mpr hkv) (show 0≤v+k*d by positivity)
        nlinarith
      · have hh := mul_nonneg (show 0≤k*d-v by linarith)
          (show 0≤2*s-v-k*d by linarith)
        nlinarith

/-- The actual C.17 integral bound, with x0 determined by the total slack area. -/
theorem sigma_integral_lower {sigma : ℝ → ℝ} {c t q k : ℝ}
    (hq : q ∈ Icc c t) (hk : 0<k) (hs : 0<sigma c)
    (hc : ContinuousOn sigma (Icc c t)) (hn : ∀ r ∈ Icc c t,0≤sigma r)
    (ha : AntitoneOn sigma (Icc c t)) (ht : sigma t=0)
    (hslope : ∀ a ∈ Icc c t,∀ b ∈ Icc c t,a≤b → sigma a-sigma b≤k*(b-a)) :
    let x0 := c+(∫ r in c..t,sigma r)/sigma c+sigma c/(2*k)
    k/2*((max (x0-q) 0)^2-(max (x0-sigma c/k-q) 0)^2)≤∫ r in q..t,sigma r := by
  dsimp only
  let s := sigma c
  let v := sigma q
  let E := ∫ r in q..t,sigma r
  let Ec := ∫ r in c..t,sigma r
  let x0 := c+Ec/s+s/(2*k)
  have hi1 := (hc.mono (Icc_subset_Icc le_rfl hq.2)).intervalIntegrable_of_Icc (μ := volume) hq.1
  have hi2 := (hc.mono (Icc_subset_Icc hq.1 le_rfl)).intervalIntegrable_of_Icc (μ := volume) hq.2
  have hsum : (∫ r in c..q,sigma r)+E=Ec :=
    intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have hpre := sigma_prefix_upper hq.1 hk (hc.mono (Icc_subset_Icc le_rfl hq.2))
    (ha.mono (Icc_subset_Icc le_rfl hq.2))
    (fun r hr => hslope r ⟨hr.1,hr.2.trans hq.2⟩ q hq hr.2)
  have htail := sigma_tail_lower hq.2 hk (hc.mono (Icc_subset_Icc hq.1 le_rfl))
    (fun r hr => hn r ⟨hq.1.trans hr.1,hr.2⟩) ht
    (fun r hr => hslope q hq r ⟨hq.1.trans hr.1,hr.2⟩ hr.1)
  have h1 : v^2≤2*k*E := by
    simpa only [mul_comm] using (div_le_iff₀ (show 0<2*k by positivity)).mp htail
  have hpre' : 2*k*(∫ r in c..q,sigma r)≤2*k*s*(q-c)-(s-v)^2 := by
    calc
      _≤2*k*(sigma c*(q-c)-(sigma c-sigma q)^2/(2*k)) :=
        mul_le_mul_of_nonneg_left hpre (by positivity)
      _= _ := by dsimp [s,v]; field_simp <;> ring
  have hx : 2*k*s*(x0-c)=2*k*Ec+s^2 := by
    dsimp [x0,s]
    field_simp
    ring
  have hsum' := congrArg (fun u : ℝ => 2*k*u) hsum
  have h2 : 2*k*s*(x0-q)-2*s*v+v^2≤2*k*E := by nlinarith
  have hh := sigma_area_elimination hk hs.le (hn q hq)
    (ha ⟨le_rfl,hq.1.trans hq.2⟩ hq hq.1) h1 h2
  have he : x0-q-s/k=x0-s/k-q := by ring
  rw [he] at hh
  exact hh

/-- The C.19 pointwise bound comes from the prefix cone and the remaining
endpoint rectangle; its denominator is positive on the whole closed interval. -/
theorem sigma_pointwise_lower {sigma : ℝ → ℝ} {c t q k : ℝ}
    (hq : q ∈ Icc c t) (hk : 0<k) (hs : 0<sigma c)
    (hc : ContinuousOn sigma (Icc c t)) (hn : 0≤sigma q)
    (ha : AntitoneOn sigma (Icc c t))
    (hslope : ∀ r ∈ Icc c q,sigma r-sigma q≤k*(q-r)) :
    let x0 := c+(∫ r in c..t,sigma r)/sigma c+sigma c/(2*k)
    sigma c*max (x0-q) 0/(sigma c/k+t-q)≤sigma q := by
  dsimp only
  let s := sigma c
  let v := sigma q
  let Ec := ∫ r in c..t,sigma r
  let x0 := c+Ec/s+s/(2*k)
  have hden : 0<s/k+t-q := by have hh := div_pos hs hk; linarith [hq.2]
  have hi1 := (hc.mono (Icc_subset_Icc le_rfl hq.2)).intervalIntegrable_of_Icc (μ := volume) hq.1
  have hi2 := (hc.mono (Icc_subset_Icc hq.1 le_rfl)).intervalIntegrable_of_Icc (μ := volume) hq.2
  have hsum : (∫ r in c..q,sigma r)+(∫ r in q..t,sigma r)=Ec :=
    intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have hpre := sigma_prefix_upper hq.1 hk (hc.mono (Icc_subset_Icc le_rfl hq.2))
    (ha.mono (Icc_subset_Icc le_rfl hq.2)) hslope
  have htail := sigma_tail_upper hq.2 (hc.mono (Icc_subset_Icc hq.1 le_rfl))
    (ha.mono (Icc_subset_Icc hq.1 le_rfl))
  change s*max (x0-q) 0/(s/k+t-q)≤v
  apply (div_le_iff₀ hden).mpr
  by_cases hxq : x0≤q
  · rw [max_eq_right (by linarith),mul_zero]
    exact mul_nonneg hn hden.le
  · rw [max_eq_left (by linarith)]
    have hpre' : 2*k*(∫ r in c..q,sigma r)≤2*k*s*(q-c)-(s-v)^2 := by
      calc
        _≤2*k*(sigma c*(q-c)-(sigma c-sigma q)^2/(2*k)) :=
          mul_le_mul_of_nonneg_left hpre (by positivity)
        _= _ := by dsimp [s,v]; field_simp <;> ring
    have htail' : 2*k*(∫ r in q..t,sigma r)≤2*k*v*(t-q) := by
      have hh := mul_le_mul_of_nonneg_left htail (show 0≤2*k by positivity)
      nlinarith
    have hx : 2*k*s*(x0-c)=2*k*Ec+s^2 := by
      dsimp [x0,s]
      field_simp
      ring
    have hdiv : k*(s/k)=s := mul_div_cancel₀ _ hk.ne'
    have hdiv' := congrArg (fun u : ℝ => 2*v*u) hdiv
    have hsum' := congrArg (fun u : ℝ => 2*k*u) hsum
    apply (mul_le_mul_iff_right₀ (show 0<2*k by positivity)).mp
    nlinarith [sq_nonneg v]

end OptimalG
