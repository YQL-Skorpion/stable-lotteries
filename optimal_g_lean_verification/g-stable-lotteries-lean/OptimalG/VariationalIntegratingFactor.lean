import OptimalG.VariationalTransportODE

/-! An actual normalized integrating factor for an integrable reference
coefficient, with its absolute continuity and almost-everywhere derivative. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter Real
open scoped Topology NNReal

 theorem absolutelyContinuous_comp_lipschitz {a b : ℝ} {f g : ℝ → ℝ} {s : Set ℝ} {K : ℝ≥0}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : LipschitzOnWith K g s)
    (hmap : MapsTo f (uIcc a b) s) : AbsolutelyContinuousOnInterval (fun r => g (f r)) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro eps heps
  obtain ⟨delta,hdelta,hworks⟩ := hf (eps/(K+1)) (by positivity)
  refine ⟨delta,hdelta,?_⟩
  rintro ⟨n,I⟩ hI hlen
  have hsmall := hworks (n,I) hI hlen
  calc
    (∑ i ∈ Finset.range n, dist (g (f (I i).1)) (g (f (I i).2))) ≤
        ∑ i ∈ Finset.range n, (K:ℝ)*dist (f (I i).1) (f (I i).2) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hg.dist_le_mul _ (hmap (hI.left i hi).left) _ (hmap (hI.left i hi).right)
    _ = (K:ℝ)*∑ i ∈ Finset.range n, dist (f (I i).1) (f (I i).2) := by rw [Finset.mul_sum]
    _ ≤ (K:ℝ)*(eps/(K+1)) := mul_le_mul_of_nonneg_left hsmall.le K.coe_nonneg
    _ < ((K:ℝ)+1)*(eps/(K+1)) := by gcongr; linarith
    _ = eps := by field_simp

 theorem absolutelyContinuous_exp {a b : ℝ} {f : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun r => exp (f r)) a b := by
  obtain ⟨M,hM⟩ := hf.exists_bound
  have hExp : ContDiffOn ℝ 1 exp (Icc (-M) M) := contDiff_exp.contDiffOn
  obtain ⟨K,hK⟩ := hExp.exists_lipschitzOnWith (by decide) (convex_Icc _ _) isCompact_Icc
  apply absolutelyContinuous_comp_lipschitz hf hK
  intro r hr
  exact abs_le.mp (by simpa only [Real.norm_eq_abs] using hM r hr)

noncomputable def referenceIntegratingFactor (a b : ℝ) (B : ℝ → ℝ) (t : ℝ) : ℝ :=
  exp ((∫ s in a..t, B s)-(∫ s in a..b, B s))

 theorem referenceIntegratingFactor_pos (a b : ℝ) (B : ℝ → ℝ) (t : ℝ) :
    0 < referenceIntegratingFactor a b B t := exp_pos _

 theorem referenceIntegratingFactor_terminal (a b : ℝ) (B : ℝ → ℝ) :
    referenceIntegratingFactor a b B b = 1 := by simp [referenceIntegratingFactor]

 theorem referenceIntegratingFactor_AC {a b : ℝ} {B : ℝ → ℝ}
    (hB : IntervalIntegrable B volume a b) :
    AbsolutelyContinuousOnInterval (referenceIntegratingFactor a b B) a b := by
  have hi := hB.absolutelyContinuousOnInterval_intervalIntegral (show a ∈ uIcc a b by simp)
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => ∫ s in a..b, B s) a b :=
    (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
  exact absolutelyContinuous_exp (hi.sub hc)

 theorem referenceIntegratingFactor_deriv_ae {a b : ℝ} {B : ℝ → ℝ}
    (hB : IntervalIntegrable B volume a b) :
    ∀ᵐ t ∂volume, t ∈ uIcc a b →
      deriv (referenceIntegratingFactor a b B) t = B t*referenceIntegratingFactor a b B t := by
  filter_upwards [hB.ae_hasDerivAt_integral] with t ht htab
  have hi := ht htab a (by simp)
  have hh := (hi.sub_const (∫ s in a..b, B s)).exp
  change HasDerivAt (referenceIntegratingFactor a b B)
    (exp ((∫ s in a..t,B s)-(∫ s in a..b,B s))*B t) t at hh
  simpa only [referenceIntegratingFactor,mul_comm] using hh.deriv

 theorem actual_integrating_factor_entropy {a b : ℝ} {d B G : ℝ → ℝ}
    (hab : a ≤ b) (hB : IntervalIntegrable B volume a b)
    (hd : AbsolutelyContinuousOnInterval d a b)
    (hdd : ∀ᵐ t ∂volume.restrict (Icc a b), -B t*d t+G t ≤ deriv d t)
    (hG : IntervalIntegrable (fun t => referenceIntegratingFactor a b B t*G t) volume a b) :
    referenceIntegratingFactor a b B a*d a+
      (∫ t in a..b, referenceIntegratingFactor a b B t*G t) ≤ d b := by
  apply integrating_factor_entropy hab (referenceIntegratingFactor_AC hB) hd
    (Eventually.of_forall (fun t => (referenceIntegratingFactor_pos a b B t).le)) _ hdd hG
    (referenceIntegratingFactor_terminal a b B)
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  simpa only [uIcc_of_le hab] using referenceIntegratingFactor_deriv_ae hB

end OptimalG.Variational
