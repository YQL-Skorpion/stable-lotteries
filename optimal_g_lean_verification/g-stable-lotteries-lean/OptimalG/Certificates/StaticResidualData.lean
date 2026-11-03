import OptimalG.Certificates.StaticResidualData.Batch000
import OptimalG.Certificates.StaticResidualData.Batch001
import OptimalG.Certificates.StaticResidualData.Batch002
import OptimalG.Certificates.StaticResidualData.Batch003
import OptimalG.Certificates.StaticResidualData.Batch004
import OptimalG.Certificates.StaticResidualData.Batch005
import OptimalG.Certificates.StaticResidualData.Batch006
import OptimalG.Certificates.StaticResidualData.Batch007
import OptimalG.Certificates.StaticResidualData.Batch008
import OptimalG.Certificates.StaticResidualData.Bundle0009_0012
import OptimalG.Certificates.StaticResidualData.Bundle0013_0016
import OptimalG.Certificates.StaticResidualData.Bundle0017_0019
import OptimalG.Certificates.StaticHighControl
namespace OptimalG.Certificates.StaticResidualData
open StaticHighData
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem all_checked : StaticHighData.pieces.all (prefixResidualCheck StaticSegmentData.tree)=true := by
  have h0 : prefixResidualCheck StaticSegmentData.tree piece0=true := by
    have hs : ¬StaticHigh.contact≤piece0.lo := by norm_num [StaticHigh.contact,piece0]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch000.residual0_checked
  have h1 : prefixResidualCheck StaticSegmentData.tree piece1=true := by
    have hs : ¬StaticHigh.contact≤piece1.lo := by norm_num [StaticHigh.contact,piece1]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch000.residual1_checked
  have h2 : prefixResidualCheck StaticSegmentData.tree piece2=true := by
    have hs : ¬StaticHigh.contact≤piece2.lo := by norm_num [StaticHigh.contact,piece2]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch000.residual2_checked
  have h3 : prefixResidualCheck StaticSegmentData.tree piece3=true := by
    have hs : ¬StaticHigh.contact≤piece3.lo := by norm_num [StaticHigh.contact,piece3]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch000.residual3_checked
  have h4 : prefixResidualCheck StaticSegmentData.tree piece4=true := by
    have hs : ¬StaticHigh.contact≤piece4.lo := by norm_num [StaticHigh.contact,piece4]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch000.residual4_checked
  have h5 : prefixResidualCheck StaticSegmentData.tree piece5=true := by
    have hs : ¬StaticHigh.contact≤piece5.lo := by norm_num [StaticHigh.contact,piece5]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch000.residual5_checked
  have h6 : prefixResidualCheck StaticSegmentData.tree piece6=true := by
    have hs : ¬StaticHigh.contact≤piece6.lo := by norm_num [StaticHigh.contact,piece6]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch000.residual6_checked
  have h7 : prefixResidualCheck StaticSegmentData.tree piece7=true := by
    have hs : ¬StaticHigh.contact≤piece7.lo := by norm_num [StaticHigh.contact,piece7]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch000.residual7_checked
  have h8 : prefixResidualCheck StaticSegmentData.tree piece8=true := by
    have hs : ¬StaticHigh.contact≤piece8.lo := by norm_num [StaticHigh.contact,piece8]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch001.residual8_checked
  have h9 : prefixResidualCheck StaticSegmentData.tree piece9=true := by
    have hs : ¬StaticHigh.contact≤piece9.lo := by norm_num [StaticHigh.contact,piece9]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch001.residual9_checked
  have h10 : prefixResidualCheck StaticSegmentData.tree piece10=true := by
    have hs : ¬StaticHigh.contact≤piece10.lo := by norm_num [StaticHigh.contact,piece10]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch001.residual10_checked
  have h11 : prefixResidualCheck StaticSegmentData.tree piece11=true := by
    have hs : ¬StaticHigh.contact≤piece11.lo := by norm_num [StaticHigh.contact,piece11]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch001.residual11_checked
  have h12 : prefixResidualCheck StaticSegmentData.tree piece12=true := by
    have hs : ¬StaticHigh.contact≤piece12.lo := by norm_num [StaticHigh.contact,piece12]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch001.residual12_checked
  have h13 : prefixResidualCheck StaticSegmentData.tree piece13=true := by
    have hs : ¬StaticHigh.contact≤piece13.lo := by norm_num [StaticHigh.contact,piece13]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch001.residual13_checked
  have h14 : prefixResidualCheck StaticSegmentData.tree piece14=true := by
    have hs : ¬StaticHigh.contact≤piece14.lo := by norm_num [StaticHigh.contact,piece14]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch001.residual14_checked
  have h15 : prefixResidualCheck StaticSegmentData.tree piece15=true := by
    have hs : ¬StaticHigh.contact≤piece15.lo := by norm_num [StaticHigh.contact,piece15]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch001.residual15_checked
  have h16 : prefixResidualCheck StaticSegmentData.tree piece16=true := by
    have hs : ¬StaticHigh.contact≤piece16.lo := by norm_num [StaticHigh.contact,piece16]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch002.residual16_checked
  have h17 : prefixResidualCheck StaticSegmentData.tree piece17=true := by
    have hs : ¬StaticHigh.contact≤piece17.lo := by norm_num [StaticHigh.contact,piece17]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch002.residual17_checked
  have h18 : prefixResidualCheck StaticSegmentData.tree piece18=true := by
    have hs : ¬StaticHigh.contact≤piece18.lo := by norm_num [StaticHigh.contact,piece18]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch002.residual18_checked
  have h19 : prefixResidualCheck StaticSegmentData.tree piece19=true := by
    have hs : ¬StaticHigh.contact≤piece19.lo := by norm_num [StaticHigh.contact,piece19]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch002.residual19_checked
  have h20 : prefixResidualCheck StaticSegmentData.tree piece20=true := by
    have hs : ¬StaticHigh.contact≤piece20.lo := by norm_num [StaticHigh.contact,piece20]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch002.residual20_checked
  have h21 : prefixResidualCheck StaticSegmentData.tree piece21=true := by
    have hs : ¬StaticHigh.contact≤piece21.lo := by norm_num [StaticHigh.contact,piece21]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch002.residual21_checked
  have h22 : prefixResidualCheck StaticSegmentData.tree piece22=true := by
    have hs : ¬StaticHigh.contact≤piece22.lo := by norm_num [StaticHigh.contact,piece22]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch002.residual22_checked
  have h23 : prefixResidualCheck StaticSegmentData.tree piece23=true := by
    have hs : ¬StaticHigh.contact≤piece23.lo := by norm_num [StaticHigh.contact,piece23]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch002.residual23_checked
  have h24 : prefixResidualCheck StaticSegmentData.tree piece24=true := by
    have hs : ¬StaticHigh.contact≤piece24.lo := by norm_num [StaticHigh.contact,piece24]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch003.residual24_checked
  have h25 : prefixResidualCheck StaticSegmentData.tree piece25=true := by
    have hs : ¬StaticHigh.contact≤piece25.lo := by norm_num [StaticHigh.contact,piece25]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch003.residual25_checked
  have h26 : prefixResidualCheck StaticSegmentData.tree piece26=true := by
    have hs : ¬StaticHigh.contact≤piece26.lo := by norm_num [StaticHigh.contact,piece26]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch003.residual26_checked
  have h27 : prefixResidualCheck StaticSegmentData.tree piece27=true := by
    have hs : ¬StaticHigh.contact≤piece27.lo := by norm_num [StaticHigh.contact,piece27]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch003.residual27_checked
  have h28 : prefixResidualCheck StaticSegmentData.tree piece28=true := by
    have hs : ¬StaticHigh.contact≤piece28.lo := by norm_num [StaticHigh.contact,piece28]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch003.residual28_checked
  have h29 : prefixResidualCheck StaticSegmentData.tree piece29=true := by
    have hs : ¬StaticHigh.contact≤piece29.lo := by norm_num [StaticHigh.contact,piece29]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch003.residual29_checked
  have h30 : prefixResidualCheck StaticSegmentData.tree piece30=true := by
    have hs : ¬StaticHigh.contact≤piece30.lo := by norm_num [StaticHigh.contact,piece30]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch003.residual30_checked
  have h31 : prefixResidualCheck StaticSegmentData.tree piece31=true := by
    have hs : ¬StaticHigh.contact≤piece31.lo := by norm_num [StaticHigh.contact,piece31]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch003.residual31_checked
  have h32 : prefixResidualCheck StaticSegmentData.tree piece32=true := by
    have hs : ¬StaticHigh.contact≤piece32.lo := by norm_num [StaticHigh.contact,piece32]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch004.residual32_checked
  have h33 : prefixResidualCheck StaticSegmentData.tree piece33=true := by
    have hs : ¬StaticHigh.contact≤piece33.lo := by norm_num [StaticHigh.contact,piece33]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch004.residual33_checked
  have h34 : prefixResidualCheck StaticSegmentData.tree piece34=true := by
    have hs : ¬StaticHigh.contact≤piece34.lo := by norm_num [StaticHigh.contact,piece34]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch004.residual34_checked
  have h35 : prefixResidualCheck StaticSegmentData.tree piece35=true := by
    have hs : ¬StaticHigh.contact≤piece35.lo := by norm_num [StaticHigh.contact,piece35]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch004.residual35_checked
  have h36 : prefixResidualCheck StaticSegmentData.tree piece36=true := by
    have hs : ¬StaticHigh.contact≤piece36.lo := by norm_num [StaticHigh.contact,piece36]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch004.residual36_checked
  have h37 : prefixResidualCheck StaticSegmentData.tree piece37=true := by
    have hs : ¬StaticHigh.contact≤piece37.lo := by norm_num [StaticHigh.contact,piece37]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch004.residual37_checked
  have h38 : prefixResidualCheck StaticSegmentData.tree piece38=true := by
    have hs : ¬StaticHigh.contact≤piece38.lo := by norm_num [StaticHigh.contact,piece38]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch004.residual38_checked
  have h39 : prefixResidualCheck StaticSegmentData.tree piece39=true := by
    have hs : ¬StaticHigh.contact≤piece39.lo := by norm_num [StaticHigh.contact,piece39]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch004.residual39_checked
  have h40 : prefixResidualCheck StaticSegmentData.tree piece40=true := by
    have hs : ¬StaticHigh.contact≤piece40.lo := by norm_num [StaticHigh.contact,piece40]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch005.residual40_checked
  have h41 : prefixResidualCheck StaticSegmentData.tree piece41=true := by
    have hs : ¬StaticHigh.contact≤piece41.lo := by norm_num [StaticHigh.contact,piece41]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch005.residual41_checked
  have h42 : prefixResidualCheck StaticSegmentData.tree piece42=true := by
    have hs : ¬StaticHigh.contact≤piece42.lo := by norm_num [StaticHigh.contact,piece42]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch005.residual42_checked
  have h43 : prefixResidualCheck StaticSegmentData.tree piece43=true := by
    have hs : ¬StaticHigh.contact≤piece43.lo := by norm_num [StaticHigh.contact,piece43]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch005.residual43_checked
  have h44 : prefixResidualCheck StaticSegmentData.tree piece44=true := by
    have hs : ¬StaticHigh.contact≤piece44.lo := by norm_num [StaticHigh.contact,piece44]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch005.residual44_checked
  have h45 : prefixResidualCheck StaticSegmentData.tree piece45=true := by
    have hs : ¬StaticHigh.contact≤piece45.lo := by norm_num [StaticHigh.contact,piece45]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch005.residual45_checked
  have h46 : prefixResidualCheck StaticSegmentData.tree piece46=true := by
    have hs : ¬StaticHigh.contact≤piece46.lo := by norm_num [StaticHigh.contact,piece46]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch005.residual46_checked
  have h47 : prefixResidualCheck StaticSegmentData.tree piece47=true := by
    have hs : ¬StaticHigh.contact≤piece47.lo := by norm_num [StaticHigh.contact,piece47]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch005.residual47_checked
  have h48 : prefixResidualCheck StaticSegmentData.tree piece48=true := by
    have hs : ¬StaticHigh.contact≤piece48.lo := by norm_num [StaticHigh.contact,piece48]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch006.residual48_checked
  have h49 : prefixResidualCheck StaticSegmentData.tree piece49=true := by
    have hs : ¬StaticHigh.contact≤piece49.lo := by norm_num [StaticHigh.contact,piece49]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch006.residual49_checked
  have h50 : prefixResidualCheck StaticSegmentData.tree piece50=true := by
    have hs : ¬StaticHigh.contact≤piece50.lo := by norm_num [StaticHigh.contact,piece50]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch006.residual50_checked
  have h51 : prefixResidualCheck StaticSegmentData.tree piece51=true := by
    have hs : ¬StaticHigh.contact≤piece51.lo := by norm_num [StaticHigh.contact,piece51]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch006.residual51_checked
  have h52 : prefixResidualCheck StaticSegmentData.tree piece52=true := by
    have hs : ¬StaticHigh.contact≤piece52.lo := by norm_num [StaticHigh.contact,piece52]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch006.residual52_checked
  have h53 : prefixResidualCheck StaticSegmentData.tree piece53=true := by
    have hs : ¬StaticHigh.contact≤piece53.lo := by norm_num [StaticHigh.contact,piece53]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch006.residual53_checked
  have h54 : prefixResidualCheck StaticSegmentData.tree piece54=true := by
    have hs : ¬StaticHigh.contact≤piece54.lo := by norm_num [StaticHigh.contact,piece54]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch006.residual54_checked
  have h55 : prefixResidualCheck StaticSegmentData.tree piece55=true := by
    have hs : ¬StaticHigh.contact≤piece55.lo := by norm_num [StaticHigh.contact,piece55]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch006.residual55_checked
  have h56 : prefixResidualCheck StaticSegmentData.tree piece56=true := by
    have hs : ¬StaticHigh.contact≤piece56.lo := by norm_num [StaticHigh.contact,piece56]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch007.residual56_checked
  have h57 : prefixResidualCheck StaticSegmentData.tree piece57=true := by
    have hs : ¬StaticHigh.contact≤piece57.lo := by norm_num [StaticHigh.contact,piece57]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch007.residual57_checked
  have h58 : prefixResidualCheck StaticSegmentData.tree piece58=true := by
    have hs : ¬StaticHigh.contact≤piece58.lo := by norm_num [StaticHigh.contact,piece58]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch007.residual58_checked
  have h59 : prefixResidualCheck StaticSegmentData.tree piece59=true := by
    have hs : ¬StaticHigh.contact≤piece59.lo := by norm_num [StaticHigh.contact,piece59]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch007.residual59_checked
  have h60 : prefixResidualCheck StaticSegmentData.tree piece60=true := by
    have hs : ¬StaticHigh.contact≤piece60.lo := by norm_num [StaticHigh.contact,piece60]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch007.residual60_checked
  have h61 : prefixResidualCheck StaticSegmentData.tree piece61=true := by
    have hs : ¬StaticHigh.contact≤piece61.lo := by norm_num [StaticHigh.contact,piece61]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch007.residual61_checked
  have h62 : prefixResidualCheck StaticSegmentData.tree piece62=true := by
    have hs : ¬StaticHigh.contact≤piece62.lo := by norm_num [StaticHigh.contact,piece62]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch007.residual62_checked
  have h63 : prefixResidualCheck StaticSegmentData.tree piece63=true := by
    have hs : ¬StaticHigh.contact≤piece63.lo := by norm_num [StaticHigh.contact,piece63]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch007.residual63_checked
  have h64 : prefixResidualCheck StaticSegmentData.tree piece64=true := by
    have hs : ¬StaticHigh.contact≤piece64.lo := by norm_num [StaticHigh.contact,piece64]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch008.residual64_checked
  have h65 : prefixResidualCheck StaticSegmentData.tree piece65=true := by
    have hs : ¬StaticHigh.contact≤piece65.lo := by norm_num [StaticHigh.contact,piece65]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch008.residual65_checked
  have h66 : prefixResidualCheck StaticSegmentData.tree piece66=true := by
    have hs : ¬StaticHigh.contact≤piece66.lo := by norm_num [StaticHigh.contact,piece66]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch008.residual66_checked
  have h67 : prefixResidualCheck StaticSegmentData.tree piece67=true := by
    have hs : ¬StaticHigh.contact≤piece67.lo := by norm_num [StaticHigh.contact,piece67]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch008.residual67_checked
  have h68 : prefixResidualCheck StaticSegmentData.tree piece68=true := by
    have hs : ¬StaticHigh.contact≤piece68.lo := by norm_num [StaticHigh.contact,piece68]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch008.residual68_checked
  have h69 : prefixResidualCheck StaticSegmentData.tree piece69=true := by
    have hs : ¬StaticHigh.contact≤piece69.lo := by norm_num [StaticHigh.contact,piece69]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch008.residual69_checked
  have h70 : prefixResidualCheck StaticSegmentData.tree piece70=true := by
    have hs : ¬StaticHigh.contact≤piece70.lo := by norm_num [StaticHigh.contact,piece70]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch008.residual70_checked
  have h71 : prefixResidualCheck StaticSegmentData.tree piece71=true := by
    have hs : ¬StaticHigh.contact≤piece71.lo := by norm_num [StaticHigh.contact,piece71]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch008.residual71_checked
  have h72 : prefixResidualCheck StaticSegmentData.tree piece72=true := by
    have hs : ¬StaticHigh.contact≤piece72.lo := by norm_num [StaticHigh.contact,piece72]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch009.residual72_checked
  have h73 : prefixResidualCheck StaticSegmentData.tree piece73=true := by
    have hs : ¬StaticHigh.contact≤piece73.lo := by norm_num [StaticHigh.contact,piece73]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch009.residual73_checked
  have h74 : prefixResidualCheck StaticSegmentData.tree piece74=true := by
    have hs : ¬StaticHigh.contact≤piece74.lo := by norm_num [StaticHigh.contact,piece74]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch009.residual74_checked
  have h75 : prefixResidualCheck StaticSegmentData.tree piece75=true := by
    have hs : ¬StaticHigh.contact≤piece75.lo := by norm_num [StaticHigh.contact,piece75]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch009.residual75_checked
  have h76 : prefixResidualCheck StaticSegmentData.tree piece76=true := by
    have hs : ¬StaticHigh.contact≤piece76.lo := by norm_num [StaticHigh.contact,piece76]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch009.residual76_checked
  have h77 : prefixResidualCheck StaticSegmentData.tree piece77=true := by
    have hs : ¬StaticHigh.contact≤piece77.lo := by norm_num [StaticHigh.contact,piece77]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch009.residual77_checked
  have h78 : prefixResidualCheck StaticSegmentData.tree piece78=true := by
    have hs : ¬StaticHigh.contact≤piece78.lo := by norm_num [StaticHigh.contact,piece78]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch009.residual78_checked
  have h79 : prefixResidualCheck StaticSegmentData.tree piece79=true := by
    have hs : ¬StaticHigh.contact≤piece79.lo := by norm_num [StaticHigh.contact,piece79]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch009.residual79_checked
  have h80 : prefixResidualCheck StaticSegmentData.tree piece80=true := by
    have hs : ¬StaticHigh.contact≤piece80.lo := by norm_num [StaticHigh.contact,piece80]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch010.residual80_checked
  have h81 : prefixResidualCheck StaticSegmentData.tree piece81=true := by
    have hs : ¬StaticHigh.contact≤piece81.lo := by norm_num [StaticHigh.contact,piece81]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch010.residual81_checked
  have h82 : prefixResidualCheck StaticSegmentData.tree piece82=true := by
    have hs : ¬StaticHigh.contact≤piece82.lo := by norm_num [StaticHigh.contact,piece82]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch010.residual82_checked
  have h83 : prefixResidualCheck StaticSegmentData.tree piece83=true := by
    have hs : ¬StaticHigh.contact≤piece83.lo := by norm_num [StaticHigh.contact,piece83]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch010.residual83_checked
  have h84 : prefixResidualCheck StaticSegmentData.tree piece84=true := by
    have hs : ¬StaticHigh.contact≤piece84.lo := by norm_num [StaticHigh.contact,piece84]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch010.residual84_checked
  have h85 : prefixResidualCheck StaticSegmentData.tree piece85=true := by
    have hs : ¬StaticHigh.contact≤piece85.lo := by norm_num [StaticHigh.contact,piece85]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch010.residual85_checked
  have h86 : prefixResidualCheck StaticSegmentData.tree piece86=true := by
    have hs : ¬StaticHigh.contact≤piece86.lo := by norm_num [StaticHigh.contact,piece86]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch010.residual86_checked
  have h87 : prefixResidualCheck StaticSegmentData.tree piece87=true := by
    have hs : ¬StaticHigh.contact≤piece87.lo := by norm_num [StaticHigh.contact,piece87]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch010.residual87_checked
  have h88 : prefixResidualCheck StaticSegmentData.tree piece88=true := by
    have hs : ¬StaticHigh.contact≤piece88.lo := by norm_num [StaticHigh.contact,piece88]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch011.residual88_checked
  have h89 : prefixResidualCheck StaticSegmentData.tree piece89=true := by
    have hs : ¬StaticHigh.contact≤piece89.lo := by norm_num [StaticHigh.contact,piece89]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch011.residual89_checked
  have h90 : prefixResidualCheck StaticSegmentData.tree piece90=true := by
    have hs : ¬StaticHigh.contact≤piece90.lo := by norm_num [StaticHigh.contact,piece90]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch011.residual90_checked
  have h91 : prefixResidualCheck StaticSegmentData.tree piece91=true := by
    have hs : ¬StaticHigh.contact≤piece91.lo := by norm_num [StaticHigh.contact,piece91]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch011.residual91_checked
  have h92 : prefixResidualCheck StaticSegmentData.tree piece92=true := by
    have hs : ¬StaticHigh.contact≤piece92.lo := by norm_num [StaticHigh.contact,piece92]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch011.residual92_checked
  have h93 : prefixResidualCheck StaticSegmentData.tree piece93=true := by
    have hs : ¬StaticHigh.contact≤piece93.lo := by norm_num [StaticHigh.contact,piece93]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch011.residual93_checked
  have h94 : prefixResidualCheck StaticSegmentData.tree piece94=true := by
    have hs : ¬StaticHigh.contact≤piece94.lo := by norm_num [StaticHigh.contact,piece94]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch011.residual94_checked
  have h95 : prefixResidualCheck StaticSegmentData.tree piece95=true := by
    have hs : ¬StaticHigh.contact≤piece95.lo := by norm_num [StaticHigh.contact,piece95]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch011.residual95_checked
  have h96 : prefixResidualCheck StaticSegmentData.tree piece96=true := by
    have hs : ¬StaticHigh.contact≤piece96.lo := by norm_num [StaticHigh.contact,piece96]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch012.residual96_checked
  have h97 : prefixResidualCheck StaticSegmentData.tree piece97=true := by
    have hs : ¬StaticHigh.contact≤piece97.lo := by norm_num [StaticHigh.contact,piece97]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch012.residual97_checked
  have h98 : prefixResidualCheck StaticSegmentData.tree piece98=true := by
    have hs : ¬StaticHigh.contact≤piece98.lo := by norm_num [StaticHigh.contact,piece98]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch012.residual98_checked
  have h99 : prefixResidualCheck StaticSegmentData.tree piece99=true := by
    have hs : ¬StaticHigh.contact≤piece99.lo := by norm_num [StaticHigh.contact,piece99]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch012.residual99_checked
  have h100 : prefixResidualCheck StaticSegmentData.tree piece100=true := by
    have hs : ¬StaticHigh.contact≤piece100.lo := by norm_num [StaticHigh.contact,piece100]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch012.residual100_checked
  have h101 : prefixResidualCheck StaticSegmentData.tree piece101=true := by
    have hs : ¬StaticHigh.contact≤piece101.lo := by norm_num [StaticHigh.contact,piece101]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch012.residual101_checked
  have h102 : prefixResidualCheck StaticSegmentData.tree piece102=true := by
    have hs : ¬StaticHigh.contact≤piece102.lo := by norm_num [StaticHigh.contact,piece102]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch012.residual102_checked
  have h103 : prefixResidualCheck StaticSegmentData.tree piece103=true := by
    have hs : ¬StaticHigh.contact≤piece103.lo := by norm_num [StaticHigh.contact,piece103]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch012.residual103_checked
  have h104 : prefixResidualCheck StaticSegmentData.tree piece104=true := by
    have hs : ¬StaticHigh.contact≤piece104.lo := by norm_num [StaticHigh.contact,piece104]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch013.residual104_checked
  have h105 : prefixResidualCheck StaticSegmentData.tree piece105=true := by
    have hs : ¬StaticHigh.contact≤piece105.lo := by norm_num [StaticHigh.contact,piece105]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch013.residual105_checked
  have h106 : prefixResidualCheck StaticSegmentData.tree piece106=true := by
    have hs : ¬StaticHigh.contact≤piece106.lo := by norm_num [StaticHigh.contact,piece106]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch013.residual106_checked
  have h107 : prefixResidualCheck StaticSegmentData.tree piece107=true := by
    have hs : ¬StaticHigh.contact≤piece107.lo := by norm_num [StaticHigh.contact,piece107]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch013.residual107_checked
  have h108 : prefixResidualCheck StaticSegmentData.tree piece108=true := by
    have hs : ¬StaticHigh.contact≤piece108.lo := by norm_num [StaticHigh.contact,piece108]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch013.residual108_checked
  have h109 : prefixResidualCheck StaticSegmentData.tree piece109=true := by
    have hs : ¬StaticHigh.contact≤piece109.lo := by norm_num [StaticHigh.contact,piece109]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch013.residual109_checked
  have h110 : prefixResidualCheck StaticSegmentData.tree piece110=true := by
    have hs : ¬StaticHigh.contact≤piece110.lo := by norm_num [StaticHigh.contact,piece110]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch013.residual110_checked
  have h111 : prefixResidualCheck StaticSegmentData.tree piece111=true := by
    have hs : ¬StaticHigh.contact≤piece111.lo := by norm_num [StaticHigh.contact,piece111]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch013.residual111_checked
  have h112 : prefixResidualCheck StaticSegmentData.tree piece112=true := by
    have hs : ¬StaticHigh.contact≤piece112.lo := by norm_num [StaticHigh.contact,piece112]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch014.residual112_checked
  have h113 : prefixResidualCheck StaticSegmentData.tree piece113=true := by
    have hs : ¬StaticHigh.contact≤piece113.lo := by norm_num [StaticHigh.contact,piece113]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch014.residual113_checked
  have h114 : prefixResidualCheck StaticSegmentData.tree piece114=true := by
    have hs : ¬StaticHigh.contact≤piece114.lo := by norm_num [StaticHigh.contact,piece114]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch014.residual114_checked
  have h115 : prefixResidualCheck StaticSegmentData.tree piece115=true := by
    have hs : ¬StaticHigh.contact≤piece115.lo := by norm_num [StaticHigh.contact,piece115]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch014.residual115_checked
  have h116 : prefixResidualCheck StaticSegmentData.tree piece116=true := by
    have hs : ¬StaticHigh.contact≤piece116.lo := by norm_num [StaticHigh.contact,piece116]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch014.residual116_checked
  have h117 : prefixResidualCheck StaticSegmentData.tree piece117=true := by
    have hs : ¬StaticHigh.contact≤piece117.lo := by norm_num [StaticHigh.contact,piece117]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch014.residual117_checked
  have h118 : prefixResidualCheck StaticSegmentData.tree piece118=true := by
    have hs : ¬StaticHigh.contact≤piece118.lo := by norm_num [StaticHigh.contact,piece118]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch014.residual118_checked
  have h119 : prefixResidualCheck StaticSegmentData.tree piece119=true := by
    have hs : ¬StaticHigh.contact≤piece119.lo := by norm_num [StaticHigh.contact,piece119]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch014.residual119_checked
  have h120 : prefixResidualCheck StaticSegmentData.tree piece120=true := by
    have hs : ¬StaticHigh.contact≤piece120.lo := by norm_num [StaticHigh.contact,piece120]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch015.residual120_checked
  have h121 : prefixResidualCheck StaticSegmentData.tree piece121=true := by
    have hs : ¬StaticHigh.contact≤piece121.lo := by norm_num [StaticHigh.contact,piece121]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch015.residual121_checked
  have h122 : prefixResidualCheck StaticSegmentData.tree piece122=true := by
    have hs : ¬StaticHigh.contact≤piece122.lo := by norm_num [StaticHigh.contact,piece122]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch015.residual122_checked
  have h123 : prefixResidualCheck StaticSegmentData.tree piece123=true := by
    have hs : ¬StaticHigh.contact≤piece123.lo := by norm_num [StaticHigh.contact,piece123]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch015.residual123_checked
  have h124 : prefixResidualCheck StaticSegmentData.tree piece124=true := by
    have hs : ¬StaticHigh.contact≤piece124.lo := by norm_num [StaticHigh.contact,piece124]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch015.residual124_checked
  have h125 : prefixResidualCheck StaticSegmentData.tree piece125=true := by
    have hs : ¬StaticHigh.contact≤piece125.lo := by norm_num [StaticHigh.contact,piece125]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch015.residual125_checked
  have h126 : prefixResidualCheck StaticSegmentData.tree piece126=true := by
    have hs : ¬StaticHigh.contact≤piece126.lo := by norm_num [StaticHigh.contact,piece126]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch015.residual126_checked
  have h127 : prefixResidualCheck StaticSegmentData.tree piece127=true := by
    have hs : ¬StaticHigh.contact≤piece127.lo := by norm_num [StaticHigh.contact,piece127]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch015.residual127_checked
  have h128 : prefixResidualCheck StaticSegmentData.tree piece128=true := by
    have hs : ¬StaticHigh.contact≤piece128.lo := by norm_num [StaticHigh.contact,piece128]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch016.residual128_checked
  have h129 : prefixResidualCheck StaticSegmentData.tree piece129=true := by
    have hs : ¬StaticHigh.contact≤piece129.lo := by norm_num [StaticHigh.contact,piece129]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch016.residual129_checked
  have h130 : prefixResidualCheck StaticSegmentData.tree piece130=true := by
    have hs : ¬StaticHigh.contact≤piece130.lo := by norm_num [StaticHigh.contact,piece130]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch016.residual130_checked
  have h131 : prefixResidualCheck StaticSegmentData.tree piece131=true := by
    have hs : ¬StaticHigh.contact≤piece131.lo := by norm_num [StaticHigh.contact,piece131]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch016.residual131_checked
  have h132 : prefixResidualCheck StaticSegmentData.tree piece132=true := by
    have hs : ¬StaticHigh.contact≤piece132.lo := by norm_num [StaticHigh.contact,piece132]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch016.residual132_checked
  have h133 : prefixResidualCheck StaticSegmentData.tree piece133=true := by
    have hs : ¬StaticHigh.contact≤piece133.lo := by norm_num [StaticHigh.contact,piece133]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch016.residual133_checked
  have h134 : prefixResidualCheck StaticSegmentData.tree piece134=true := by
    have hs : ¬StaticHigh.contact≤piece134.lo := by norm_num [StaticHigh.contact,piece134]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch016.residual134_checked
  have h135 : prefixResidualCheck StaticSegmentData.tree piece135=true := by
    have hs : ¬StaticHigh.contact≤piece135.lo := by norm_num [StaticHigh.contact,piece135]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch016.residual135_checked
  have h136 : prefixResidualCheck StaticSegmentData.tree piece136=true := by
    have hs : ¬StaticHigh.contact≤piece136.lo := by norm_num [StaticHigh.contact,piece136]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch017.residual136_checked
  have h137 : prefixResidualCheck StaticSegmentData.tree piece137=true := by
    have hs : ¬StaticHigh.contact≤piece137.lo := by norm_num [StaticHigh.contact,piece137]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch017.residual137_checked
  have h138 : prefixResidualCheck StaticSegmentData.tree piece138=true := by
    have hs : ¬StaticHigh.contact≤piece138.lo := by norm_num [StaticHigh.contact,piece138]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch017.residual138_checked
  have h139 : prefixResidualCheck StaticSegmentData.tree piece139=true := by
    have hs : ¬StaticHigh.contact≤piece139.lo := by norm_num [StaticHigh.contact,piece139]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch017.residual139_checked
  have h140 : prefixResidualCheck StaticSegmentData.tree piece140=true := by
    have hs : ¬StaticHigh.contact≤piece140.lo := by norm_num [StaticHigh.contact,piece140]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch017.residual140_checked
  have h141 : prefixResidualCheck StaticSegmentData.tree piece141=true := by
    have hs : ¬StaticHigh.contact≤piece141.lo := by norm_num [StaticHigh.contact,piece141]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch017.residual141_checked
  have h142 : prefixResidualCheck StaticSegmentData.tree piece142=true := by
    have hs : ¬StaticHigh.contact≤piece142.lo := by norm_num [StaticHigh.contact,piece142]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch017.residual142_checked
  have h143 : prefixResidualCheck StaticSegmentData.tree piece143=true := by
    have hs : ¬StaticHigh.contact≤piece143.lo := by norm_num [StaticHigh.contact,piece143]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch017.residual143_checked
  have h144 : prefixResidualCheck StaticSegmentData.tree piece144=true := by
    have hs : ¬StaticHigh.contact≤piece144.lo := by norm_num [StaticHigh.contact,piece144]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch018.residual144_checked
  have h145 : prefixResidualCheck StaticSegmentData.tree piece145=true := by
    have hs : ¬StaticHigh.contact≤piece145.lo := by norm_num [StaticHigh.contact,piece145]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch018.residual145_checked
  have h146 : prefixResidualCheck StaticSegmentData.tree piece146=true := by
    have hs : ¬StaticHigh.contact≤piece146.lo := by norm_num [StaticHigh.contact,piece146]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch018.residual146_checked
  have h147 : prefixResidualCheck StaticSegmentData.tree piece147=true := by
    have hs : ¬StaticHigh.contact≤piece147.lo := by norm_num [StaticHigh.contact,piece147]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch018.residual147_checked
  have h148 : prefixResidualCheck StaticSegmentData.tree piece148=true := by
    have hs : ¬StaticHigh.contact≤piece148.lo := by norm_num [StaticHigh.contact,piece148]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch018.residual148_checked
  have h149 : prefixResidualCheck StaticSegmentData.tree piece149=true := by
    have hs : ¬StaticHigh.contact≤piece149.lo := by norm_num [StaticHigh.contact,piece149]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch018.residual149_checked
  have h150 : prefixResidualCheck StaticSegmentData.tree piece150=true := by
    have hs : ¬StaticHigh.contact≤piece150.lo := by norm_num [StaticHigh.contact,piece150]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch018.residual150_checked
  have h151 : prefixResidualCheck StaticSegmentData.tree piece151=true := by
    have hs : ¬StaticHigh.contact≤piece151.lo := by norm_num [StaticHigh.contact,piece151]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch018.residual151_checked
  have h152 : prefixResidualCheck StaticSegmentData.tree piece152=true := by
    have hs : ¬StaticHigh.contact≤piece152.lo := by norm_num [StaticHigh.contact,piece152]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch019.residual152_checked
  have h153 : prefixResidualCheck StaticSegmentData.tree piece153=true := by
    have hs : ¬StaticHigh.contact≤piece153.lo := by norm_num [StaticHigh.contact,piece153]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch019.residual153_checked
  have h154 : prefixResidualCheck StaticSegmentData.tree piece154=true := by
    have hs : ¬StaticHigh.contact≤piece154.lo := by norm_num [StaticHigh.contact,piece154]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch019.residual154_checked
  have h155 : prefixResidualCheck StaticSegmentData.tree piece155=true := by
    have hs : ¬StaticHigh.contact≤piece155.lo := by norm_num [StaticHigh.contact,piece155]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch019.residual155_checked
  have h156 : prefixResidualCheck StaticSegmentData.tree piece156=true := by
    have hs : ¬StaticHigh.contact≤piece156.lo := by norm_num [StaticHigh.contact,piece156]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch019.residual156_checked
  have h157 : prefixResidualCheck StaticSegmentData.tree piece157=true := by
    have hs : ¬StaticHigh.contact≤piece157.lo := by norm_num [StaticHigh.contact,piece157]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch019.residual157_checked
  have h158 : prefixResidualCheck StaticSegmentData.tree piece158=true := by
    have hs : ¬StaticHigh.contact≤piece158.lo := by norm_num [StaticHigh.contact,piece158]
    rw [prefixResidualCheck,if_neg hs]
    exact Batch019.residual158_checked
  have h159 : prefixResidualCheck StaticSegmentData.tree piece159=true := by
    unfold prefixResidualCheck
    have hs : StaticHigh.contact≤piece159.lo := by norm_num [StaticHigh.contact,piece159]
    rw [if_pos hs]
  simp only [StaticHighData.pieces,List.all_cons,List.all_nil,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41,h42,h43,h44,h45,h46,h47,h48,h49,h50,h51,h52,h53,h54,h55,h56,h57,h58,h59,h60,h61,h62,h63,h64,h65,h66,h67,h68,h69,h70,h71,h72,h73,h74,h75,h76,h77,h78,h79,h80,h81,h82,h83,h84,h85,h86,h87,h88,h89,h90,h91,h92,h93,h94,h95,h96,h97,h98,h99,h100,h101,h102,h103,h104,h105,h106,h107,h108,h109,h110,h111,h112,h113,h114,h115,h116,h117,h118,h119,h120,h121,h122,h123,h124,h125,h126,h127,h128,h129,h130,h131,h132,h133,h134,h135,h136,h137,h138,h139,h140,h141,h142,h143,h144,h145,h146,h147,h148,h149,h150,h151,h152,h153,h154,h155,h156,h157,h158,h159,Bool.true_and]
end OptimalG.Certificates.StaticResidualData
