import OptimalG.Certificates.StaticBinaryLateAreaBounds.HeadHead
import OptimalG.Certificates.StaticBinaryLateAreaBounds.HeadCap
import OptimalG.Certificates.StaticBinaryLateAreaBounds.HeadConeLeft
import OptimalG.Certificates.StaticBinaryLateAreaBounds.HeadConeRight
import OptimalG.Certificates.StaticBinaryLateAreaBounds.CapHead
import OptimalG.Certificates.StaticBinaryLateAreaBounds.CapCap
import OptimalG.Certificates.StaticBinaryLateAreaBounds.CapConeLeft
import OptimalG.Certificates.StaticBinaryLateAreaBounds.CapConeRight
import OptimalG.Certificates.StaticBinaryLateAreaBounds.ConeLinearHead
import OptimalG.Certificates.StaticBinaryLateAreaBounds.ConeLinearCap
import OptimalG.Certificates.StaticBinaryLateAreaBounds.ConeLinearConeLeft
import OptimalG.Certificates.StaticBinaryLateAreaBounds.ConeLinearConeRight
import OptimalG.Certificates.StaticBinaryLateAreaBounds.ConeQuadraticHead
import OptimalG.Certificates.StaticBinaryLateAreaBounds.ConeQuadraticCap
import OptimalG.Certificates.StaticBinaryLateAreaBounds.ConeQuadraticConeLeft
import OptimalG.Certificates.StaticBinaryLateAreaBounds.ConeQuadraticConeRight

namespace OptimalG.Certificates.StaticBinaryLateArea
open Set StaticBinaryCentralExpressions StaticBinaryLateExpressions StaticBinaryLateScalars
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem Head {d q : ℝ} (hd : d∈Icc (1/50:ℝ) (7/80))
    (hq : q∈Icc (0:ℝ) (337/1000)) (hr : q∈Icc (0:ℝ) (527/2000:ℝ)) :
    d^2*((B-C*d)/(1-d)*(L-q)-1/2)≤lower q-upper (q+d) := by
  have hlower : lower q=areaHead q := lower_head hr.2
  have hqb : q∈Icc 0 (527/2000) := by
    have hh := hr
    norm_num [cutoff2,cutoff,binaryAreaCutoff,L,S,c,StaticLow.lam,StaticLow.slack,StaticLow.leftContact,UpperProfileData.leftContact,Variational.capDeficit,Variational.capSlack,Variational.cap,Variational.capScore,Variational.quadratic] at hh ⊢
    exact hh
  by_cases hhead : q+d≤527/2000
  · have hupper := (upper_head hhead).le
    exact StaticBinaryLateAreaBounds.HeadHead.bound hd hqb
      ⟨by linarith only [hq.1,hd.1],hhead⟩ hq hlower hupper
  by_cases hcap : q+d≤c
  · have hh : q+d∈Icc (527/2000:ℝ) c := ⟨(lt_of_not_ge hhead).le,hcap⟩
    have hupper := (upper_cap hh).le
    apply StaticBinaryLateAreaBounds.HeadCap.bound hd hqb ?_ hq hlower hupper
    simpa [c,StaticLow.leftContact,UpperProfileData.leftContact] using hh
  by_cases hleft : q+d≤348541/1000000
  · have hh : q+d∈Icc c (348541/1000000) := ⟨(lt_of_not_ge hcap).le,hleft⟩
    have hupper := upper_left hh
    apply StaticBinaryLateAreaBounds.HeadConeLeft.bound hd hqb ?_ hq hlower hupper
    simpa [c,StaticLow.leftContact,UpperProfileData.leftContact] using hh
  · have hupper := (upper_right (lt_of_not_ge hleft).le).le
    exact StaticBinaryLateAreaBounds.HeadConeRight.bound hd hqb
      ⟨(lt_of_not_ge hleft).le,by linarith only [hq.2,hd.2]⟩ hq hlower hupper

private theorem Cap {d q : ℝ} (hd : d∈Icc (1/50:ℝ) (7/80))
    (hq : q∈Icc (0:ℝ) (337/1000)) (hr : q∈Icc (527/2000:ℝ) (c:ℝ)) :
    d^2*((B-C*d)/(1-d)*(L-q)-1/2)≤lower q-upper (q+d) := by
  have hlower : lower q=areaCap q := lower_cap hr
  have hqb : q∈Icc (527/2000) (2950935005377889/10000000000000000) := by
    have hh := hr
    norm_num [cutoff2,cutoff,binaryAreaCutoff,L,S,c,StaticLow.lam,StaticLow.slack,StaticLow.leftContact,UpperProfileData.leftContact,Variational.capDeficit,Variational.capSlack,Variational.cap,Variational.capScore,Variational.quadratic] at hh ⊢
    exact hh
  by_cases hhead : q+d≤527/2000
  · have hupper := (upper_head hhead).le
    exact StaticBinaryLateAreaBounds.CapHead.bound hd hqb
      ⟨by linarith only [hq.1,hd.1],hhead⟩ hq hlower hupper
  by_cases hcap : q+d≤c
  · have hh : q+d∈Icc (527/2000:ℝ) c := ⟨(lt_of_not_ge hhead).le,hcap⟩
    have hupper := (upper_cap hh).le
    apply StaticBinaryLateAreaBounds.CapCap.bound hd hqb ?_ hq hlower hupper
    simpa [c,StaticLow.leftContact,UpperProfileData.leftContact] using hh
  by_cases hleft : q+d≤348541/1000000
  · have hh : q+d∈Icc c (348541/1000000) := ⟨(lt_of_not_ge hcap).le,hleft⟩
    have hupper := upper_left hh
    apply StaticBinaryLateAreaBounds.CapConeLeft.bound hd hqb ?_ hq hlower hupper
    simpa [c,StaticLow.leftContact,UpperProfileData.leftContact] using hh
  · have hupper := (upper_right (lt_of_not_ge hleft).le).le
    exact StaticBinaryLateAreaBounds.CapConeRight.bound hd hqb
      ⟨(lt_of_not_ge hleft).le,by linarith only [hq.2,hd.2]⟩ hq hlower hupper

private theorem ConeLinear {d q : ℝ} (hd : d∈Icc (1/50:ℝ) (7/80))
    (hq : q∈Icc (0:ℝ) (337/1000)) (hr : q∈Icc (c:ℝ) (cutoff2:ℝ)) :
    d^2*((B-C*d)/(1-d)*(L-q)-1/2)≤lower q-upper (q+d) := by
  have hlower : lower q=areaLinear q := lower_linear hr
  have hqb : q∈Icc (2950935005377889/10000000000000000) (9764675264432828020717332009213874188106300418835385927801144446371126129006862927848715177742693160316714351616160693891/32715759564676520860721298708061938005633151811116999343755125914557013109886958424402492555434660728700380000000000000000) := by
    have hh := hr
    norm_num [cutoff2,cutoff,binaryAreaCutoff,L,S,c,StaticLow.lam,StaticLow.slack,StaticLow.leftContact,UpperProfileData.leftContact,Variational.capDeficit,Variational.capSlack,Variational.cap,Variational.capScore,Variational.quadratic] at hh ⊢
    exact hh
  by_cases hhead : q+d≤527/2000
  · have hupper := (upper_head hhead).le
    exact StaticBinaryLateAreaBounds.ConeLinearHead.bound hd hqb
      ⟨by linarith only [hq.1,hd.1],hhead⟩ hq hlower hupper
  by_cases hcap : q+d≤c
  · have hh : q+d∈Icc (527/2000:ℝ) c := ⟨(lt_of_not_ge hhead).le,hcap⟩
    have hupper := (upper_cap hh).le
    apply StaticBinaryLateAreaBounds.ConeLinearCap.bound hd hqb ?_ hq hlower hupper
    simpa [c,StaticLow.leftContact,UpperProfileData.leftContact] using hh
  by_cases hleft : q+d≤348541/1000000
  · have hh : q+d∈Icc c (348541/1000000) := ⟨(lt_of_not_ge hcap).le,hleft⟩
    have hupper := upper_left hh
    apply StaticBinaryLateAreaBounds.ConeLinearConeLeft.bound hd hqb ?_ hq hlower hupper
    simpa [c,StaticLow.leftContact,UpperProfileData.leftContact] using hh
  · have hupper := (upper_right (lt_of_not_ge hleft).le).le
    exact StaticBinaryLateAreaBounds.ConeLinearConeRight.bound hd hqb
      ⟨(lt_of_not_ge hleft).le,by linarith only [hq.2,hd.2]⟩ hq hlower hupper

private theorem ConeQuadratic {d q : ℝ} (hd : d∈Icc (1/50:ℝ) (7/80))
    (hq : q∈Icc (0:ℝ) (337/1000)) (hr : q∈Icc (cutoff2:ℝ) (337/1000:ℝ)) :
    d^2*((B-C*d)/(1-d)*(L-q)-1/2)≤lower q-upper (q+d) := by
  have hlower : lower q=areaQuadratic q := lower_quadratic hr
  have hqb : q∈Icc (9764675264432828020717332009213874188106300418835385927801144446371126129006862927848715177742693160316714351616160693891/32715759564676520860721298708061938005633151811116999343755125914557013109886958424402492555434660728700380000000000000000) (337/1000) := by
    have hh := hr
    norm_num [cutoff2,cutoff,binaryAreaCutoff,L,S,c,StaticLow.lam,StaticLow.slack,StaticLow.leftContact,UpperProfileData.leftContact,Variational.capDeficit,Variational.capSlack,Variational.cap,Variational.capScore,Variational.quadratic] at hh ⊢
    exact hh
  by_cases hhead : q+d≤527/2000
  · have hupper := (upper_head hhead).le
    exact StaticBinaryLateAreaBounds.ConeQuadraticHead.bound hd hqb
      ⟨by linarith only [hq.1,hd.1],hhead⟩ hq hlower hupper
  by_cases hcap : q+d≤c
  · have hh : q+d∈Icc (527/2000:ℝ) c := ⟨(lt_of_not_ge hhead).le,hcap⟩
    have hupper := (upper_cap hh).le
    apply StaticBinaryLateAreaBounds.ConeQuadraticCap.bound hd hqb ?_ hq hlower hupper
    simpa [c,StaticLow.leftContact,UpperProfileData.leftContact] using hh
  by_cases hleft : q+d≤348541/1000000
  · have hh : q+d∈Icc c (348541/1000000) := ⟨(lt_of_not_ge hcap).le,hleft⟩
    have hupper := upper_left hh
    apply StaticBinaryLateAreaBounds.ConeQuadraticConeLeft.bound hd hqb ?_ hq hlower hupper
    simpa [c,StaticLow.leftContact,UpperProfileData.leftContact] using hh
  · have hupper := (upper_right (lt_of_not_ge hleft).le).le
    exact StaticBinaryLateAreaBounds.ConeQuadraticConeRight.bound hd hqb
      ⟨(lt_of_not_ge hleft).le,by linarith only [hq.2,hd.2]⟩ hq hlower hupper

theorem bound {d q : ℝ} (hd : d∈Icc (1/50:ℝ) (7/80))
    (hq : q∈Icc (0:ℝ) (337/1000)) :
    d^2*((B-C*d)/(1-d)*(L-q)-1/2)≤lower q-upper (q+d) := by
  by_cases hh : q≤527/2000
  · exact Head hd hq ⟨hq.1,hh⟩
  by_cases hc : q≤c
  · exact Cap hd hq ⟨(lt_of_not_ge hh).le,hc⟩
  by_cases hl : q≤cutoff2
  · exact ConeLinear hd hq ⟨(lt_of_not_ge hc).le,hl⟩
  · exact ConeQuadratic hd hq ⟨(lt_of_not_ge hl).le,hq.2⟩

end OptimalG.Certificates.StaticBinaryLateArea
