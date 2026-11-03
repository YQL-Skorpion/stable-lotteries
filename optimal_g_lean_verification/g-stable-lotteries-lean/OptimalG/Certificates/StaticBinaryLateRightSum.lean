import OptimalG.Certificates.StaticBinaryLateSumBounds.Interval000
import OptimalG.Certificates.StaticBinaryLateSumBounds.Interval001
import OptimalG.Certificates.StaticBinaryLateSumBounds.Interval002
import OptimalG.Certificates.StaticBinaryLateSumBounds.Interval003
import OptimalG.Certificates.StaticBinaryLateSumBounds.Interval004
import OptimalG.Certificates.StaticBinaryLateSumBounds.Interval005
import OptimalG.Certificates.StaticBinaryLateSumBounds.Interval006
import OptimalG.Certificates.StaticBinaryLateSumBounds.Interval007
import OptimalG.Certificates.StaticBinaryLateSumBounds.Interval008

namespace OptimalG.Certificates.StaticBinaryLateRightSum
open Set StaticBinaryLateExpressions
theorem nonneg {q : ℝ} (hq : q∈Icc (1/4:ℝ) (337/1000)) : 0≤rightSum q := by
  by_cases h0 : q≤(1501/6000)
  · exact StaticBinaryLateSumBounds.Interval000.bound ⟨by linarith only [hq.1],h0⟩
  by_cases h1 : q≤(1541/6000)
  · exact StaticBinaryLateSumBounds.Interval001.bound ⟨by linarith only [hq.1 ,h0],h1⟩
  by_cases h2 : q≤(2750935005377889/10000000000000000)
  · exact StaticBinaryLateSumBounds.Interval002.bound ⟨by linarith only [hq.1 ,h1],h2⟩
  by_cases h3 : q≤(8452805016133667/30000000000000000)
  · exact StaticBinaryLateSumBounds.Interval003.bound ⟨by linarith only [hq.1 ,h2],h3⟩
  by_cases h4 : q≤(8652805016133667/30000000000000000)
  · exact StaticBinaryLateSumBounds.Interval004.bound ⟨by linarith only [hq.1 ,h3],h4⟩
  by_cases h5 : q≤(10395848796186841646603236307354207299655183079759224261720018193160081900315912026656070581952701238282841191774815095891/32715759564676520860721298708061938005633151811116999343755125914557013109886958424402492555434660728700380000000000000000)
  · exact StaticBinaryLateSumBounds.Interval005.bound ⟨by linarith only [hq.1 ,h4],h5⟩
  by_cases h6 : q≤(3537984619983783928558237210691540073230912475055556974670573010863487329238386138717362399662977436602503463924938365297/10905253188225506953573766236020646001877717270372333114585041971519004369962319474800830851811553576233460000000000000000)
  · exact StaticBinaryLateSumBounds.Interval006.bound ⟨by linarith only [hq.1 ,h5],h6⟩
  by_cases h7 : q≤(10832058923715861924746186956795033139730291770574117586303419872020842075114404805648103816025163381332179591774815095891/32715759564676520860721298708061938005633151811116999343755125914557013109886958424402492555434660728700380000000000000000)
  · exact StaticBinaryLateSumBounds.Interval007.bound ⟨by linarith only [hq.1 ,h6],h7⟩
  exact StaticBinaryLateSumBounds.Interval008.bound ⟨by linarith only [h7],hq.2⟩
end OptimalG.Certificates.StaticBinaryLateRightSum
