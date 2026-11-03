import OptimalG.VariationalFeatureReplacement
import OptimalG.VariationalCapReplacement

/-! Every cap-replaced control can be moved into the original essential score
graph by finitely many rightward rank replacements. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology NNReal

theorem select_original_x {lam c z u A B : ℝ} {d d' : LowRankData}
    (hd : Admissible lam d) (hd' : Admissible lam d') (hS : d'.S = d.S)
    (hc : c ∈ Icc ell tEnd) (hcx : c ≤ xHi)
    (hcontact : lowPrimitive lam d c = cap lam d.S c)
    {v : Control} (hv : v ∈ controlDomain) (hz : z ∈ Icc zStart zEnd)
    (huLow : quadratic lam z-quadratic lam 1 ≤ u) (huHigh : u ≤ quadratic lam z-d'.S)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hsource : (v.2.1,A) ∈ rankScoreSupport d.phi ∨
      (v.2.1 < c ∧ A = capScore lam d.S v.2.1)) :
    ∃ w ∈ rankScoreSupport d.phi,
      featureH hd' z u ((v.1,w.1,v.2.2),w.2,B) ≤ featureH hd' z u (v,A,B) := by
  rcases hsource with hsource | ⟨hrc,hscore⟩
  · exact ⟨(v.2.1,A),hsource,le_rfl⟩
  · have htheta := hd'.cap_coordinate_theta_lower hv hA0 hB0
      (Or.inl (by rw [hS]; exact hscore))
    have htheta' : (13:ℝ)/100 < featureTheta lam d' (v,A,B) := by linarith
    obtain ⟨w,hw,hwr,hi⟩ := hd.exists_affine_improvement_at_contact hc hcx hcontact hv.2.1 hrc htheta'
    have hs : A+featureTheta lam d' (v,A,B)*v.2.1 ≤ w.2+featureTheta lam d' (v,A,B)*w.1 := by
      simpa only [hscore] using hi.le
    exact ⟨w,hw,(hd'.feature_x_replacement hv hz huLow huHigh (hd.rankScoreSupport_bounds hw).1 hs).1⟩

theorem select_original_y {lam c z u A B : ℝ} {d d' : LowRankData}
    (hd : Admissible lam d) (hd' : Admissible lam d') (hS : d'.S = d.S)
    (hc : c ∈ Icc ell tEnd) (hcx : c ≤ xHi)
    (hcontact : lowPrimitive lam d c = cap lam d.S c)
    {v : Control} (hv : v ∈ controlDomain) (hz : z ∈ Icc zStart zEnd)
    (huLow : quadratic lam z-quadratic lam 1 ≤ u) (huHigh : u ≤ quadratic lam z-d'.S)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hsource : (v.2.2,B) ∈ rankScoreSupport d.phi ∨
      (v.2.2 < c ∧ B = capScore lam d.S v.2.2)) :
    ∃ w ∈ rankScoreSupport d.phi, v.1 ≤ w.1 ∧
      featureH hd' z u ((v.1,v.2.1,w.1),A,w.2) ≤ featureH hd' z u (v,A,B) := by
  have hp : v.1 ≤ v.2.2 := (le_max_right _ _).trans hv.2.2.1
  rcases hsource with hsource | ⟨hrc,hscore⟩
  · exact ⟨(v.2.2,B),hsource,hp,le_rfl⟩
  · have htheta := hd'.cap_coordinate_theta_lower hv hA0 hB0
      (Or.inr (by rw [hS]; exact hscore))
    have htheta' : (13:ℝ)/100 < featureTheta lam d' (v,A,B) := by linarith
    have hyr : v.2.2 ∈ Icc xLo xHi := ⟨(le_max_left _ _).trans hv.2.2.1,hv.2.2.2⟩
    obtain ⟨w,hw,hwr,hi⟩ := hd.exists_affine_improvement_at_contact hc hcx hcontact hyr hrc htheta'
    have hpw : v.1 ≤ w.1 := hp.trans hwr.1
    have hs : B+featureTheta lam d' (v,A,B)*v.2.2 ≤ w.2+featureTheta lam d' (v,A,B)*w.1 := by
      simpa only [hscore] using hi.le
    exact ⟨w,hw,hpw,(hd'.feature_y_replacement hv hz huLow huHigh (hd.rankScoreSupport_bounds hw).1 hpw hs).1⟩

theorem select_original_feature {lam c z u A B : ℝ} {d d' : LowRankData}
    (hd : Admissible lam d) (hd' : Admissible lam d') (hS : d'.S = d.S)
    (hc : c ∈ Icc ell tEnd) (hcx : c ≤ xHi)
    (hcontact : lowPrimitive lam d c = cap lam d.S c)
    {v : Control} (hv : v ∈ controlDomain) (hz : z ∈ Icc zStart zEnd)
    (huLow : quadratic lam z-quadratic lam 1 ≤ u) (huHigh : u ≤ quadratic lam z-d'.S)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hsourceA : (v.2.1,A) ∈ rankScoreSupport d.phi ∨ (v.2.1 < c ∧ A = capScore lam d.S v.2.1))
    (hsourceB : (v.2.2,B) ∈ rankScoreSupport d.phi ∨ (v.2.2 < c ∧ B = capScore lam d.S v.2.2)) :
    ∃ w ∈ controlFeatureSupport d, w.1.1 = v.1 ∧ featureH hd' z u w ≤ featureH hd' z u (v,A,B) := by
  obtain ⟨wx,hwx,hx⟩ := select_original_x hd hd' hS hc hcx hcontact hv hz huLow huHigh hA0 hB0 hsourceA
  have hxB := hd.rankScoreSupport_bounds hwx
  have hv' : (v.1,wx.1,v.2.2) ∈ controlDomain := ⟨hv.1,hxB.1,hv.2.2⟩
  obtain ⟨wy,hwy,hpwy,hy⟩ := select_original_y hd hd' hS hc hcx hcontact hv' hz huLow huHigh hxB.2.1 hB0 hsourceB
  refine ⟨((v.1,wx.1,wy.1),wx.2,wy.2),hd.feature_mem_support_of_rankScores hv.1 hwx hwy hpwy,rfl,?_⟩
  exact hy.trans hx

theorem primitive_le_capReplacement {lam c p : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hc : c ∈ Icc ell tEnd)
    (hcontact : lowPrimitive lam d c = cap lam d.S c) (hp : p ∈ Icc pLo pHi) :
    primitive lam d p ≤ primitive lam (capReplacement lam d c) p := by
  unfold primitive
  split_ifs with hpe hpt
  · exact le_rfl
  · exact lowPrimitive_le_capReplacement hd hc hcontact ⟨(lt_of_not_ge hpe).le,hpt⟩
  · exact le_rfl

end OptimalG.Variational
