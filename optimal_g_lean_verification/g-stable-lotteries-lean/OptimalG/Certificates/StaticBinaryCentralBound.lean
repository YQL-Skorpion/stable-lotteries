import OptimalG.Certificates.StaticBinaryCentralCoverage
import OptimalG.Certificates.StaticBinaryCentralSemantics.Cap
import OptimalG.Certificates.StaticBinaryCentralSemantics.ConeRight
import OptimalG.Certificates.StaticBinaryCentralSemantics.Factor
import OptimalG.Certificates.StaticBinaryCentralSemantics.Middle
import OptimalG.Certificates.StaticBinaryData.Central.Leaf000
import OptimalG.Certificates.StaticBinaryData.Central.Leaf001
import OptimalG.Certificates.StaticBinaryData.Central.Leaf002
import OptimalG.Certificates.StaticBinaryData.Central.Leaf003
import OptimalG.Certificates.StaticBinaryData.Central.Leaf004
import OptimalG.Certificates.StaticBinaryData.Central.Leaf005
import OptimalG.Certificates.StaticBinaryData.Central.Leaf006
import OptimalG.Certificates.StaticBinaryData.Central.Leaf007
import OptimalG.Certificates.StaticBinaryData.Central.Leaf008
import OptimalG.Certificates.StaticBinaryData.Central.Leaf009
import OptimalG.Certificates.StaticBinaryData.Central.Leaf010
import OptimalG.Certificates.StaticBinaryData.Central.Leaf011
import OptimalG.Certificates.StaticBinaryData.Central.Leaf012
import OptimalG.Certificates.StaticBinaryData.Central.Leaf013
import OptimalG.Certificates.StaticBinaryData.Central.Leaf014
import OptimalG.Certificates.StaticBinaryData.Central.Leaf015
import OptimalG.Certificates.StaticBinaryData.Central.Leaf016
import OptimalG.Certificates.StaticBinaryData.Central.Leaf017
import OptimalG.Certificates.StaticBinaryData.Central.Leaf018
import OptimalG.Certificates.StaticBinaryData.Central.Leaf019
import OptimalG.Certificates.StaticBinaryData.Central.Leaf020
import OptimalG.Certificates.StaticBinaryData.Central.Leaf021
import OptimalG.Certificates.StaticBinaryData.Central.Leaf022
import OptimalG.Certificates.StaticBinaryData.Central.Leaf023
import OptimalG.Certificates.StaticBinaryData.Central.Leaf024
import OptimalG.Certificates.StaticBinaryData.Central.Leaf025
import OptimalG.Certificates.StaticBinaryData.Central.Leaf026

namespace OptimalG.Certificates.StaticBinaryCentralBound
open Set StaticBinaryCentralExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
theorem bound {p q : ℝ}
    (hp : p∈Icc (13/20:ℝ) (31/40)) (hq : q∈Icc (0:ℝ) (9/50))
    (he : actualError p q≤0) : q*base p q+p*actualError p q≤0 := by
  have hpq : 0<p-q := by linarith only [hp.1,hq.2]
  have hp0 : 0≤p := by linarith only [hp.1]
  have hx : ∀ i,(StaticBinaryCentralCoverage.rootBox i).Contains (![p,q] i) := by
    intro i
    fin_cases i
    · simpa [StaticBinaryCentralCoverage.rootBox,RatInterval.Contains] using hp
    · simpa [StaticBinaryCentralCoverage.rootBox,RatInterval.Contains] using hq
  obtain ⟨j,hj⟩ := StaticBinaryCentralCoverage.covered ![p,q] hx
  fin_cases j
  · have hbp : p∈Icc (13/20) (109/160) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc 0 (9/200) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryData.Central.Leaf000.numerator p q 0 := StaticBinaryData.Central.Leaf000.numerator_pos (u:=0) hbp hbq (by constructor <;> norm_num)
    have hb := StaticBinaryCentralSemantics.Cap.nonpos hpq hn
    have hrc : c≤q+1-p := by
      norm_num [c,StaticLow.leftContact,UpperProfileData.leftContact]
      linarith only [hbp.2,hbq.1]
    have hh := mul_le_mul_of_nonneg_left (cap_envelope hrc) hp0
    linarith only [hb,hh]
  · have hbp : p∈Icc (109/160) (223/320) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc 0 (9/400) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryData.Central.Leaf000.numerator p q 0 := StaticBinaryData.Central.Leaf001.numerator_pos (u:=0) hbp hbq (by constructor <;> norm_num)
    have hb := StaticBinaryCentralSemantics.Cap.nonpos hpq hn
    have hrc : c≤q+1-p := by
      norm_num [c,StaticLow.leftContact,UpperProfileData.leftContact]
      linarith only [hbp.2,hbq.1]
    have hh := mul_le_mul_of_nonneg_left (cap_envelope hrc) hp0
    linarith only [hb,hh]
  · have hbp : p∈Icc (223/320) (451/640) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc 0 (9/800) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryData.Central.Leaf000.numerator p q 0 := StaticBinaryData.Central.Leaf002.numerator_pos (u:=0) hbp hbq (by constructor <;> norm_num)
    have hb := StaticBinaryCentralSemantics.Cap.nonpos hpq hn
    have hrc : c≤q+1-p := by
      norm_num [c,StaticLow.leftContact,UpperProfileData.leftContact]
      linarith only [hbp.2,hbq.1]
    have hh := mul_le_mul_of_nonneg_left (cap_envelope hrc) hp0
    linarith only [hb,hh]
  · have hbp : p∈Icc (451/640) (57/80) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc 0 (9/800) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryData.Central.Leaf003.numerator p q 0 := StaticBinaryData.Central.Leaf003.numerator_pos (u:=0) hbp hbq (by constructor <;> norm_num)
    have hb := StaticBinaryCentralSemantics.Factor.nonpos hpq hn
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hq.1 hb) (mul_nonpos_of_nonneg_of_nonpos hp0 he)
  · have hbp : p∈Icc (223/320) (57/80) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (9/800) (9/400) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryData.Central.Leaf000.numerator p q 0 := StaticBinaryData.Central.Leaf004.numerator_pos (u:=0) hbp hbq (by constructor <;> norm_num)
    have hb := StaticBinaryCentralSemantics.Cap.nonpos hpq hn
    have hrc : c≤q+1-p := by
      norm_num [c,StaticLow.leftContact,UpperProfileData.leftContact]
      linarith only [hbp.2,hbq.1]
    have hh := mul_le_mul_of_nonneg_left (cap_envelope hrc) hp0
    linarith only [hb,hh]
  · have hbp : p∈Icc (109/160) (57/80) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (9/400) (9/200) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryData.Central.Leaf000.numerator p q 0 := StaticBinaryData.Central.Leaf005.numerator_pos (u:=0) hbp hbq (by constructor <;> norm_num)
    have hb := StaticBinaryCentralSemantics.Cap.nonpos hpq hn
    have hrc : c≤q+1-p := by
      norm_num [c,StaticLow.leftContact,UpperProfileData.leftContact]
      linarith only [hbp.2,hbq.1]
    have hh := mul_le_mul_of_nonneg_left (cap_envelope hrc) hp0
    linarith only [hb,hh]
  · have hbp : p∈Icc (13/20) (57/80) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (9/200) (9/100) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryData.Central.Leaf000.numerator p q 0 := StaticBinaryData.Central.Leaf006.numerator_pos (u:=0) hbp hbq (by constructor <;> norm_num)
    have hb := StaticBinaryCentralSemantics.Cap.nonpos hpq hn
    have hrc : c≤q+1-p := by
      norm_num [c,StaticLow.leftContact,UpperProfileData.leftContact]
      linarith only [hbp.2,hbq.1]
    have hh := mul_le_mul_of_nonneg_left (cap_envelope hrc) hp0
    linarith only [hb,hh]
  · have hbp : p∈Icc (57/80) (119/160) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc 0 (9/400) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryData.Central.Leaf003.numerator p q 0 := StaticBinaryData.Central.Leaf007.numerator_pos (u:=0) hbp hbq (by constructor <;> norm_num)
    have hb := StaticBinaryCentralSemantics.Factor.nonpos hpq hn
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hq.1 hb) (mul_nonpos_of_nonneg_of_nonpos hp0 he)
  · have hbp : p∈Icc (57/80) (461/640) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (9/400) (27/800) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryData.Central.Leaf000.numerator p q 0 := StaticBinaryData.Central.Leaf008.numerator_pos (u:=0) hbp hbq (by constructor <;> norm_num)
    have hb := StaticBinaryCentralSemantics.Cap.nonpos hpq hn
    have hrc : c≤q+1-p := by
      norm_num [c,StaticLow.leftContact,UpperProfileData.leftContact]
      linarith only [hbp.2,hbq.1]
    have hh := mul_le_mul_of_nonneg_left (cap_envelope hrc) hp0
    linarith only [hb,hh]
  · have hbp : p∈Icc (461/640) (233/320) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (9/400) (27/800) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryData.Central.Leaf003.numerator p q 0 := StaticBinaryData.Central.Leaf009.numerator_pos (u:=0) hbp hbq (by constructor <;> norm_num)
    have hb := StaticBinaryCentralSemantics.Factor.nonpos hpq hn
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hq.1 hb) (mul_nonpos_of_nonneg_of_nonpos hp0 he)
  · have hbp : p∈Icc (57/80) (233/320) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (27/800) (9/200) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryData.Central.Leaf000.numerator p q 0 := StaticBinaryData.Central.Leaf010.numerator_pos (u:=0) hbp hbq (by constructor <;> norm_num)
    have hb := StaticBinaryCentralSemantics.Cap.nonpos hpq hn
    have hrc : c≤q+1-p := by
      norm_num [c,StaticLow.leftContact,UpperProfileData.leftContact]
      linarith only [hbp.2,hbq.1]
    have hh := mul_le_mul_of_nonneg_left (cap_envelope hrc) hp0
    linarith only [hb,hh]
  · have hbp : p∈Icc (233/320) (119/160) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (9/400) (9/200) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryData.Central.Leaf003.numerator p q 0 := StaticBinaryData.Central.Leaf011.numerator_pos (u:=0) hbp hbq (by constructor <;> norm_num)
    have hb := StaticBinaryCentralSemantics.Factor.nonpos hpq hn
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hq.1 hb) (mul_nonpos_of_nonneg_of_nonpos hp0 he)
  · have hbp : p∈Icc (119/160) (31/40) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc 0 (9/200) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryData.Central.Leaf003.numerator p q 0 := StaticBinaryData.Central.Leaf012.numerator_pos (u:=0) hbp hbq (by constructor <;> norm_num)
    have hb := StaticBinaryCentralSemantics.Factor.nonpos hpq hn
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hq.1 hb) (mul_nonpos_of_nonneg_of_nonpos hp0 he)
  · have hbp : p∈Icc (57/80) (119/160) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (9/200) (9/100) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryData.Central.Leaf000.numerator p q 0 := StaticBinaryData.Central.Leaf013.numerator_pos (u:=0) hbp hbq (by constructor <;> norm_num)
    have hb := StaticBinaryCentralSemantics.Cap.nonpos hpq hn
    have hrc : c≤q+1-p := by
      norm_num [c,StaticLow.leftContact,UpperProfileData.leftContact]
      linarith only [hbp.2,hbq.1]
    have hh := mul_le_mul_of_nonneg_left (cap_envelope hrc) hp0
    linarith only [hb,hh]
  · have hbp : p∈Icc (119/160) (243/320) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (9/200) (9/160) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryData.Central.Leaf003.numerator p q 0 := StaticBinaryData.Central.Leaf014.numerator_pos (u:=0) hbp hbq (by constructor <;> norm_num)
    have hb := StaticBinaryCentralSemantics.Factor.nonpos hpq hn
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hq.1 hb) (mul_nonpos_of_nonneg_of_nonpos hp0 he)
  · have hbp : p∈Icc (119/160) (243/320) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (9/160) (27/400) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryData.Central.Leaf000.numerator p q 0 := StaticBinaryData.Central.Leaf015.numerator_pos (u:=0) hbp hbq (by constructor <;> norm_num)
    have hb := StaticBinaryCentralSemantics.Cap.nonpos hpq hn
    have hrc : c≤q+1-p := by
      norm_num [c,StaticLow.leftContact,UpperProfileData.leftContact]
      linarith only [hbp.2,hbq.1]
    have hh := mul_le_mul_of_nonneg_left (cap_envelope hrc) hp0
    linarith only [hb,hh]
  · have hbp : p∈Icc (243/320) (31/40) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (9/200) (27/400) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryData.Central.Leaf003.numerator p q 0 := StaticBinaryData.Central.Leaf016.numerator_pos (u:=0) hbp hbq (by constructor <;> norm_num)
    have hb := StaticBinaryCentralSemantics.Factor.nonpos hpq hn
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hq.1 hb) (mul_nonpos_of_nonneg_of_nonpos hp0 he)
  · have hbp : p∈Icc (119/160) (243/320) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (27/400) (9/100) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryData.Central.Leaf000.numerator p q 0 := StaticBinaryData.Central.Leaf017.numerator_pos (u:=0) hbp hbq (by constructor <;> norm_num)
    have hb := StaticBinaryCentralSemantics.Cap.nonpos hpq hn
    have hrc : c≤q+1-p := by
      norm_num [c,StaticLow.leftContact,UpperProfileData.leftContact]
      linarith only [hbp.2,hbq.1]
    have hh := mul_le_mul_of_nonneg_left (cap_envelope hrc) hp0
    linarith only [hb,hh]
  · have hbp : p∈Icc (243/320) (31/40) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (27/400) (63/800) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryData.Central.Leaf003.numerator p q 0 := StaticBinaryData.Central.Leaf018.numerator_pos (u:=0) hbp hbq (by constructor <;> norm_num)
    have hb := StaticBinaryCentralSemantics.Factor.nonpos hpq hn
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hq.1 hb) (mul_nonpos_of_nonneg_of_nonpos hp0 he)
  · have hbp : p∈Icc (243/320) (31/40) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (63/800) (9/100) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryData.Central.Leaf000.numerator p q 0 := StaticBinaryData.Central.Leaf019.numerator_pos (u:=0) hbp hbq (by constructor <;> norm_num)
    have hb := StaticBinaryCentralSemantics.Cap.nonpos hpq hn
    have hrc : c≤q+1-p := by
      norm_num [c,StaticLow.leftContact,UpperProfileData.leftContact]
      linarith only [hbp.2,hbq.1]
    have hh := mul_le_mul_of_nonneg_left (cap_envelope hrc) hp0
    linarith only [hb,hh]
  · have hbp : p∈Icc (13/20) (57/80) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (9/100) (9/50) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryData.Central.Leaf020.numerator p q 0 := StaticBinaryData.Central.Leaf020.numerator_pos (u:=0) hbp hbq (by constructor <;> norm_num)
    have hb := StaticBinaryCentralSemantics.Middle.nonpos hpq hn
    rw [middle_envelope (by linarith only [hbp.2,hbq.1])]
    exact hb
  · have hbp : p∈Icc (57/80) (119/160) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (9/100) (27/200) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryData.Central.Leaf000.numerator p q 0 := StaticBinaryData.Central.Leaf021.numerator_pos (u:=0) hbp hbq (by constructor <;> norm_num)
    have hb := StaticBinaryCentralSemantics.Cap.nonpos hpq hn
    have hrc : c≤q+1-p := by
      norm_num [c,StaticLow.leftContact,UpperProfileData.leftContact]
      linarith only [hbp.2,hbq.1]
    have hh := mul_le_mul_of_nonneg_left (cap_envelope hrc) hp0
    linarith only [hb,hh]
  · have hbp : p∈Icc (119/160) (31/40) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (9/100) (9/80) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryData.Central.Leaf000.numerator p q 0 := StaticBinaryData.Central.Leaf022.numerator_pos (u:=0) hbp hbq (by constructor <;> norm_num)
    have hb := StaticBinaryCentralSemantics.Cap.nonpos hpq hn
    have hrc : c≤q+1-p := by
      norm_num [c,StaticLow.leftContact,UpperProfileData.leftContact]
      linarith only [hbp.2,hbq.1]
    have hh := mul_le_mul_of_nonneg_left (cap_envelope hrc) hp0
    linarith only [hb,hh]
  · have hbp : p∈Icc (119/160) (243/320) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (9/80) (27/200) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryData.Central.Leaf023.numerator p q 0 := StaticBinaryData.Central.Leaf023.numerator_pos (u:=0) hbp hbq (by constructor <;> norm_num)
    have hb := StaticBinaryCentralSemantics.ConeRight.nonpos hpq hn
    have hrc : c≤q+1-p := by
      norm_num [c,StaticLow.leftContact,UpperProfileData.leftContact]
      linarith only [hbp.2,hbq.1]
    have hr : (348541/1000000:ℝ)≤q+1-p := by linarith only [hbp.2,hbq.1]
    have hh := mul_le_mul_of_nonneg_left (right_envelope hrc hr) hp0
    linarith only [hb,hh]
  · have hbp : p∈Icc (243/320) (31/40) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (9/80) (99/800) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryData.Central.Leaf000.numerator p q 0 := StaticBinaryData.Central.Leaf024.numerator_pos (u:=0) hbp hbq (by constructor <;> norm_num)
    have hb := StaticBinaryCentralSemantics.Cap.nonpos hpq hn
    have hrc : c≤q+1-p := by
      norm_num [c,StaticLow.leftContact,UpperProfileData.leftContact]
      linarith only [hbp.2,hbq.1]
    have hh := mul_le_mul_of_nonneg_left (cap_envelope hrc) hp0
    linarith only [hb,hh]
  · have hbp : p∈Icc (243/320) (31/40) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (99/800) (27/200) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryData.Central.Leaf023.numerator p q 0 := StaticBinaryData.Central.Leaf025.numerator_pos (u:=0) hbp hbq (by constructor <;> norm_num)
    have hb := StaticBinaryCentralSemantics.ConeRight.nonpos hpq hn
    have hrc : c≤q+1-p := by
      norm_num [c,StaticLow.leftContact,UpperProfileData.leftContact]
      linarith only [hbp.2,hbq.1]
    have hr : (348541/1000000:ℝ)≤q+1-p := by linarith only [hbp.2,hbq.1]
    have hh := mul_le_mul_of_nonneg_left (right_envelope hrc hr) hp0
    linarith only [hb,hh]
  · have hbp : p∈Icc (57/80) (31/40) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (27/200) (9/50) := by
      simpa [StaticBinaryCentralCoverage.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryData.Central.Leaf020.numerator p q 0 := StaticBinaryData.Central.Leaf026.numerator_pos (u:=0) hbp hbq (by constructor <;> norm_num)
    have hb := StaticBinaryCentralSemantics.Middle.nonpos hpq hn
    rw [middle_envelope (by linarith only [hbp.2,hbq.1])]
    exact hb
end OptimalG.Certificates.StaticBinaryCentralBound
