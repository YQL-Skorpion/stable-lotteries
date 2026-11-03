import OptimalG.Certificates.StaticLayerFast
import OptimalG.Certificates.StaticLayerGeometry
import OptimalG.Certificates.StaticSegmentData
import OptimalG.Certificates.SegmentMembership
import OptimalG.Certificates.StaticLayerCover

set_option Elab.async false

namespace OptimalG.Certificates.StaticSupportData.Batch005
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(16203438840341 / 59595920187500), (2719 / 10000), (741593637402319 / 2500000000000000), (118656900739 / 400000000000), StaticNodes.Batch0000.node72, StaticNodes.Batch0000.node73, false, true, .cap, 6, 6⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(2719 / 10000), (1361 / 5000), (118656900739 / 400000000000), (1187065601123 / 4000000000000), StaticNodes.Batch0000.node73, StaticNodes.Batch0000.node74, false, true, .cap, 6, 6⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(1361 / 5000), (109 / 400), (1187065601123 / 4000000000000), (14844536906373 / 50000000000000), StaticNodes.Batch0000.node74, StaticNodes.Batch0000.node75, false, true, .cap, 6, 6⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(109 / 400), (1131167505101573 / 4150925062000000), (14844536906373 / 50000000000000), (2968947806981173 / 10000000000000000), StaticNodes.Batch0000.node75, StaticNodes.Batch0000.node76, false, true, .cap, 6, 6⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(1131167505101573 / 4150925062000000), (341 / 1250), (2968947806981173 / 10000000000000000), (7425381646983 / 25000000000000), StaticNodes.Batch0000.node75, StaticNodes.Batch0000.node76, false, true, .cap, 7, 7⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(341 / 1250), (2731 / 10000), (7425381646983 / 25000000000000), (14856999198999 / 50000000000000), StaticNodes.Batch0000.node76, StaticNodes.Batch0000.node77, false, true, .cap, 7, 7⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(2731 / 10000), (426453541298377 / 1561362439000000), (14856999198999 / 50000000000000), (185720066522067 / 625000000000000), StaticNodes.Batch0000.node77, StaticNodes.Batch0000.node78, false, true, .cap, 7, 7⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(426453541298377 / 1561362439000000), (1367 / 5000), (185720066522067 / 625000000000000), (2972648929751 / 10000000000000), StaticNodes.Batch0000.node77, StaticNodes.Batch0000.node78, false, true, .cap, 8, 8⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(1367 / 5000), (2737 / 10000), (2972648929751 / 10000000000000), (29738999326801 / 100000000000000), StaticNodes.Batch0000.node78, StaticNodes.Batch0000.node79, false, true, .cap, 8, 8⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(2737 / 10000), (34298301400297079 / 125292180230000000), (29738999326801 / 100000000000000), (29740943217249693 / 100000000000000000), StaticNodes.Batch0000.node79, StaticNodes.Batch0000.node80, false, true, .cap, 8, 8⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(34298301400297079 / 125292180230000000), (137 / 500), (29740943217249693 / 100000000000000000), (3718941068103 / 12500000000000), StaticNodes.Batch0000.node79, StaticNodes.Batch0000.node80, false, true, .cap, 9, 9⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(137 / 500), (2743 / 10000), (3718941068103 / 12500000000000), (595281539777 / 2000000000000), StaticNodes.Batch0000.node80, StaticNodes.Batch0000.node81, false, true, .cap, 9, 9⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(2743 / 10000), (3448108658528101 / 12567732475000000), (595281539777 / 2000000000000), (2976667579096867 / 10000000000000000), StaticNodes.Batch0000.node81, StaticNodes.Batch0000.node82, false, true, .cap, 9, 9⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(3448108658528101 / 12567732475000000), (1373 / 5000), (2976667579096867 / 10000000000000000), (1191065788853 / 4000000000000), StaticNodes.Batch0000.node81, StaticNodes.Batch0000.node82, false, true, .cap, 10, 10⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(1373 / 5000), (2749 / 10000), (1191065788853 / 4000000000000), (29789231777301 / 100000000000000), StaticNodes.Batch0000.node82, StaticNodes.Batch0000.node83, false, true, .cap, 10, 10⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(2749 / 10000), (722180128104041 / 2626342638750000), (29789231777301 / 100000000000000), (3724051045585957 / 12500000000000000), StaticNodes.Batch0000.node83, StaticNodes.Batch0000.node84, false, true, .cap, 10, 10⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (16203438840341 / 59595920187500) (722180128104041 / 2626342638750000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch005

namespace OptimalG.Certificates.StaticSupportData.Batch006
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(722180128104041 / 2626342638750000), (172 / 625), (3724051045585957 / 12500000000000000), (29801838221967 / 100000000000000), StaticNodes.Batch0000.node83, StaticNodes.Batch0000.node84, false, true, .cap, 11, 11⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(172 / 625), (551 / 2000), (29801838221967 / 100000000000000), (14907232044417 / 50000000000000), StaticNodes.Batch0000.node84, StaticNodes.Batch0000.node85, false, true, .cap, 11, 11⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(551 / 2000), (11616329143572623 / 42151188000000000), (14907232044417 / 50000000000000), (29818140938406623 / 100000000000000000), StaticNodes.Batch0000.node85, StaticNodes.Batch0000.node86, false, true, .cap, 11, 11⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(11616329143572623 / 42151188000000000), (1379 / 5000), (29818140938406623 / 100000000000000000), (14913554722617 / 50000000000000), StaticNodes.Batch0000.node85, StaticNodes.Batch0000.node86, false, true, .cap, 12, 12⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(1379 / 5000), (2761 / 10000), (14913554722617 / 50000000000000), (7459943580921 / 25000000000000), StaticNodes.Batch0000.node86, StaticNodes.Batch0000.node87, false, true, .cap, 12, 12⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(2761 / 10000), (3503411785758583 / 12684469501000000), (7459943580921 / 25000000000000), (2984387351212561 / 10000000000000000), StaticNodes.Batch0000.node87, StaticNodes.Batch0000.node88, false, true, .cap, 12, 12⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(3503411785758583 / 12684469501000000), (691 / 2500), (2984387351212561 / 10000000000000000), (5970491758637 / 20000000000000), StaticNodes.Batch0000.node87, StaticNodes.Batch0000.node88, false, true, .cap, 13, 13⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(691 / 2500), (2767 / 10000), (5970491758637 / 20000000000000), (29865162885679 / 100000000000000), StaticNodes.Batch0000.node88, StaticNodes.Batch0000.node89, false, true, .cap, 13, 13⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(2767 / 10000), (17610022451781379 / 63618928990000000), (29865162885679 / 100000000000000), (14934803042922293 / 50000000000000000), StaticNodes.Batch0000.node89, StaticNodes.Batch0000.node90, false, true, .cap, 13, 13⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(17610022451781379 / 63618928990000000), (277 / 1000), (14934803042922293 / 50000000000000000), (29877886671477 / 100000000000000), StaticNodes.Batch0000.node89, StaticNodes.Batch0000.node90, false, true, .cap, 14, 14⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(277 / 1000), (2773 / 10000), (29877886671477 / 100000000000000), (29890630182279 / 100000000000000), StaticNodes.Batch0000.node90, StaticNodes.Batch0000.node91, false, true, .cap, 14, 14⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(2773 / 10000), (8851694036927923 / 31908267865000000), (29890630182279 / 100000000000000), (7473834664890891 / 25000000000000000), StaticNodes.Batch0000.node91, StaticNodes.Batch0000.node92, false, true, .cap, 14, 14⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(8851694036927923 / 31908267865000000), (347 / 1250), (7473834664890891 / 25000000000000000), (1196135739577 / 4000000000000), StaticNodes.Batch0000.node91, StaticNodes.Batch0000.node92, false, true, .cap, 15, 15⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(347 / 1250), (2779 / 10000), (1196135739577 / 4000000000000), (14958088312311 / 50000000000000), StaticNodes.Batch0000.node92, StaticNodes.Batch0000.node93, false, true, .cap, 15, 15⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(2779 / 10000), (1779715961379631 / 6401517704500000), (14958088312311 / 50000000000000), (1496053561664127 / 5000000000000000), StaticNodes.Batch0000.node93, StaticNodes.Batch0000.node94, false, true, .cap, 15, 15⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(1779715961379631 / 6401517704500000), (1391 / 5000), (1496053561664127 / 5000000000000000), (29928979660031 / 100000000000000), StaticNodes.Batch0000.node93, StaticNodes.Batch0000.node94, false, true, .cap, 16, 16⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (722180128104041 / 2626342638750000) (1391 / 5000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch006

namespace OptimalG.Certificates.StaticSupportData.Batch007
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(1391 / 5000), (557 / 2000), (29928979660031 / 100000000000000), (14970901313779 / 50000000000000), StaticNodes.Batch0000.node94, StaticNodes.Batch0000.node95, false, true, .cap, 16, 16⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(557 / 2000), (3578268186171059 / 12842972468000000), (14970901313779 / 50000000000000), (2994680380700153 / 10000000000000000), StaticNodes.Batch0000.node95, StaticNodes.Batch0000.node96, false, true, .cap, 16, 16⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(3578268186171059 / 12842972468000000), (697 / 2500), (2994680380700153 / 10000000000000000), (14977322800013 / 50000000000000), StaticNodes.Batch0000.node95, StaticNodes.Batch0000.node96, false, true, .cap, 17, 17⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(697 / 2500), (2791 / 10000), (14977322800013 / 50000000000000), (3745938576211 / 12500000000000), StaticNodes.Batch0000.node96, StaticNodes.Batch0000.node97, false, true, .cap, 17, 17⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(2791 / 10000), (7194374371098103 / 25766240446000000), (3745938576211 / 12500000000000), (5994507276144101 / 20000000000000000), StaticNodes.Batch0000.node97, StaticNodes.Batch0000.node98, false, true, .cap, 17, 17⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(7194374371098103 / 25766240446000000), (1397 / 5000), (5994507276144101 / 20000000000000000), (29980391729911 / 100000000000000), StaticNodes.Batch0000.node97, StaticNodes.Batch0000.node98, false, true, .cap, 18, 18⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(1397 / 5000), (2797 / 10000), (29980391729911 / 100000000000000), (14996647496709 / 50000000000000), StaticNodes.Batch0000.node98, StaticNodes.Batch0000.node99, false, true, .cap, 18, 18⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(2797 / 10000), (113005928442767 / 403858768531250), (14996647496709 / 50000000000000), (749956723860987 / 2500000000000000), StaticNodes.Batch0000.node99, StaticNodes.Batch0000.node100, false, true, .cap, 18, 18⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(113005928442767 / 403858768531250), (7 / 25), (749956723860987 / 2500000000000000), (30006218474011 / 100000000000000), StaticNodes.Batch0000.node99, StaticNodes.Batch0000.node100, false, true, .cap, 19, 19⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(7 / 25), (2803 / 10000), (30006218474011 / 100000000000000), (1876197637813 / 6250000000000), StaticNodes.Batch0000.node100, StaticNodes.Batch0000.node101, false, true, .cap, 19, 19⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(2803 / 10000), (1817638277358169 / 6482027752000000), (1876197637813 / 6250000000000), (1501200076407923 / 5000000000000000), StaticNodes.Batch0000.node101, StaticNodes.Batch0000.node102, false, true, .cap, 19, 19⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(1817638277358169 / 6482027752000000), (1403 / 5000), (1501200076407923 / 5000000000000000), (938503945641 / 3125000000000), StaticNodes.Batch0000.node101, StaticNodes.Batch0000.node102, false, true, .cap, 20, 20⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(1403 / 5000), (2809 / 10000), (938503945641 / 3125000000000), (30045110674593 / 100000000000000), StaticNodes.Batch0000.node102, StaticNodes.Batch0000.node103, false, true, .cap, 20, 20⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(2809 / 10000), (18272242624617151 / 65024234545000000), (30045110674593 / 100000000000000), (15024867050938717 / 50000000000000000), StaticNodes.Batch0000.node103, StaticNodes.Batch0000.node104, false, true, .cap, 20, 20⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(18272242624617151 / 65024234545000000), (703 / 2500), (15024867050938717 / 50000000000000000), (15029057760751 / 50000000000000), StaticNodes.Batch0000.node103, StaticNodes.Batch0000.node104, false, true, .cap, 21, 21⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(703 / 2500), (563 / 2000), (15029057760751 / 50000000000000), (30071140836241 / 100000000000000), StaticNodes.Batch0000.node104, StaticNodes.Batch0000.node105, false, true, .cap, 21, 21⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (1391 / 5000) (563 / 2000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch007

namespace OptimalG.Certificates.StaticSupportData.Batch008
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(563 / 2000), (3673706434250623 / 13045856776000000), (30071140836241 / 100000000000000), (3007546667559641 / 10000000000000000), StaticNodes.Batch0000.node105, StaticNodes.Batch0000.node106, false, true, .cap, 21, 21⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(3673706434250623 / 13045856776000000), (1409 / 5000), (3007546667559641 / 10000000000000000), (30084186693017 / 100000000000000), StaticNodes.Batch0000.node105, StaticNodes.Batch0000.node106, false, true, .cap, 22, 22⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(1409 / 5000), (2821 / 10000), (30084186693017 / 100000000000000), (15048626564007 / 50000000000000), StaticNodes.Batch0000.node106, StaticNodes.Batch0000.node107, false, true, .cap, 22, 22⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(2821 / 10000), (1678659592945189 / 5948675950000000), (15048626564007 / 50000000000000), (15050599624657693 / 50000000000000000), StaticNodes.Batch0000.node107, StaticNodes.Batch0000.node108, false, true, .cap, 22, 22⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(1678659592945189 / 5948675950000000), (353 / 1250), (15050599624657693 / 50000000000000000), (470474065861 / 1562500000000), StaticNodes.Batch0000.node107, StaticNodes.Batch0000.node108, false, true, .cap, 23, 23⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(353 / 1250), (2827 / 10000), (470474065861 / 1562500000000), (6024689598397 / 20000000000000), StaticNodes.Batch0000.node108, StaticNodes.Batch0000.node109, false, true, .cap, 23, 23⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(2827 / 10000), (3712483366323311 / 13128539855000000), (6024689598397 / 20000000000000), (3012693182303437 / 10000000000000000), StaticNodes.Batch0000.node109, StaticNodes.Batch0000.node110, false, true, .cap, 23, 23⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(3712483366323311 / 13128539855000000), (283 / 1000), (3012693182303437 / 10000000000000000), (47088400831 / 156250000000), StaticNodes.Batch0000.node109, StaticNodes.Batch0000.node110, false, true, .cap, 24, 24⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(283 / 1000), (2833 / 10000), (47088400831 / 156250000000), (3014972587431 / 10000000000000), StaticNodes.Batch0000.node110, StaticNodes.Batch0000.node111, false, true, .cap, 24, 24⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(2833 / 10000), (746400812005961 / 2634043419200000), (3014972587431 / 10000000000000), (603053287935067 / 2000000000000000), StaticNodes.Batch0000.node111, StaticNodes.Batch0000.node112, false, true, .cap, 24, 24⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(746400812005961 / 2634043419200000), (709 / 2500), (603053287935067 / 2000000000000000), (15081448045703 / 50000000000000), StaticNodes.Batch0000.node111, StaticNodes.Batch0000.node112, false, true, .cap, 25, 25⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(709 / 2500), (2839 / 10000), (15081448045703 / 50000000000000), (30176087225277 / 100000000000000), StaticNodes.Batch0000.node112, StaticNodes.Batch0000.node113, false, true, .cap, 25, 25⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(2839 / 10000), (416846003715711 / 1468013428000000), (30176087225277 / 100000000000000), (3017839697047233 / 10000000000000000), StaticNodes.Batch0000.node113, StaticNodes.Batch0000.node114, false, true, .cap, 25, 25⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(416846003715711 / 1468013428000000), (1421 / 5000), (3017839697047233 / 10000000000000000), (30189299346129 / 100000000000000), StaticNodes.Batch0000.node113, StaticNodes.Batch0000.node114, false, true, .cap, 26, 26⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(1421 / 5000), (569 / 2000), (30189299346129 / 100000000000000), (30202532499331 / 100000000000000), StaticNodes.Batch0000.node114, StaticNodes.Batch0000.node115, false, true, .cap, 26, 26⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(569 / 2000), (125710471457903 / 441808439400000), (30202532499331 / 100000000000000), (302041295441913 / 1000000000000000), StaticNodes.Batch0000.node115, StaticNodes.Batch0000.node116, false, true, .cap, 26, 26⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (563 / 2000) (125710471457903 / 441808439400000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch008
