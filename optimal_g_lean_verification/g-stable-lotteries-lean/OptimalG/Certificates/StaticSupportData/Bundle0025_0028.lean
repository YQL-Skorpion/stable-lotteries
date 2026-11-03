import OptimalG.Certificates.StaticLayerFast
import OptimalG.Certificates.StaticLayerGeometry
import OptimalG.Certificates.StaticSegmentData
import OptimalG.Certificates.SegmentMembership
import OptimalG.Certificates.StaticLayerCover

set_option Elab.async false

namespace OptimalG.Certificates.StaticSupportData.Batch025
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(15618268912768457 / 50000000000000000), (780928004699053 / 2500000000000000), (116975896018160384225758577 / 375000000000000000000000000), (5848825912763945273420533 / 18750000000000000000000000), StaticNodes.Batch0001.node80, StaticNodes.Batch0001.node81, false, false, .piece 105, 74, 105⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(780928004699053 / 2500000000000000), (780942563759683 / 2500000000000000), (5848825912763945273420533 / 18750000000000000000000000), (5848857024619871015011963 / 18750000000000000000000000), StaticNodes.Batch0001.node80, StaticNodes.Batch0001.node81, false, false, .piece 106, 74, 106⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(780942563759683 / 2500000000000000), (3123828491281251 / 10000000000000000), (5848857024619871015011963 / 18750000000000000000000000), (7798517515301061629824137 / 25000000000000000000000000), StaticNodes.Batch0001.node80, StaticNodes.Batch0001.node81, false, false, .piece 107, 74, 107⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(3123828491281251 / 10000000000000000), (3906202752742853 / 12500000000000000), (7798517515301061629824137 / 25000000000000000000000000), (29247469024272395724272333 / 93750000000000000000000000), StaticNodes.Batch0001.node80, StaticNodes.Batch0001.node81, false, false, .piece 108, 74, 108⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(3906202752742853 / 12500000000000000), (1670005431443787 / 5342352902500000), (29247469024272395724272333 / 93750000000000000000000000), (3900022764792483 / 12500000000000000), StaticNodes.Batch0001.node80, StaticNodes.Batch0001.node81, false, false, .piece 109, 74, 109⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(1670005431443787 / 5342352902500000), (1563 / 5000), (3900022764792483 / 12500000000000000), (31200257243021 / 100000000000000), StaticNodes.Batch0001.node80, StaticNodes.Batch0001.node81, false, false, .piece 109, 75, 109⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(1563 / 5000), (625219182621463 / 2000000000000000), (31200257243021 / 100000000000000), (18720318255166333122232373 / 60000000000000000000000000), StaticNodes.Batch0001.node81, StaticNodes.Batch0001.node82, false, false, .piece 109, 75, 109⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(625219182621463 / 2000000000000000), (781807406005087 / 2500000000000000), (18720318255166333122232373 / 60000000000000000000000000), (23402819618077419610977677 / 75000000000000000000000000), StaticNodes.Batch0001.node81, StaticNodes.Batch0001.node82, false, false, .piece 110, 75, 110⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(781807406005087 / 2500000000000000), (6256726669866759 / 20000000000000000), (23402819618077419610977677 / 75000000000000000000000000), (62413977112525118973093463 / 200000000000000000000000000), StaticNodes.Batch0001.node81, StaticNodes.Batch0001.node82, false, false, .piece 111, 75, 111⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(6256726669866759 / 20000000000000000), (26730958295464479 / 85446795710000000), (62413977112525118973093463 / 200000000000000000000000000), (31207020561860493 / 100000000000000000), StaticNodes.Batch0001.node81, StaticNodes.Batch0001.node82, false, false, .piece 112, 75, 112⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(26730958295464479 / 85446795710000000), (15643123060768027 / 50000000000000000), (31207020561860493 / 100000000000000000), (468115990994568551876876417 / 1500000000000000000000000000), StaticNodes.Batch0001.node81, StaticNodes.Batch0001.node82, false, false, .piece 112, 76, 112⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(15643123060768027 / 50000000000000000), (668402873267079 / 2136169892750000), (468115990994568551876876417 / 1500000000000000000000000000), (195054621501667 / 625000000000000), StaticNodes.Batch0001.node81, StaticNodes.Batch0001.node82, false, false, .piece 113, 76, 113⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(668402873267079 / 2136169892750000), (3129 / 10000), (195054621501667 / 625000000000000), (975275060081 / 3125000000000), StaticNodes.Batch0001.node81, StaticNodes.Batch0001.node82, false, false, .piece 113, 77, 113⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(3129 / 10000), (3911350260878823 / 12500000000000000), (3901100240299 / 12500000000000), (9752821951959398294498821 / 31250000000000000000000000), StaticNodes.Batch0001.node82, StaticNodes.Batch0001.node83, false, false, .piece 113, 77, 113⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(3911350260878823 / 12500000000000000), (1564771286000299 / 5000000000000000), (9752821951959398294498821 / 31250000000000000000000000), (11703879907468660121037619 / 37500000000000000000000000), StaticNodes.Batch0001.node82, StaticNodes.Batch0001.node83, false, false, .piece 114, 77, 114⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(1564771286000299 / 5000000000000000), (668164116602937 / 2134966681000000), (11703879907468660121037619 / 37500000000000000000000000), (780264395432479 / 2500000000000000), StaticNodes.Batch0001.node82, StaticNodes.Batch0001.node83, false, false, .piece 115, 77, 115⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (15618268912768457 / 50000000000000000) (668164116602937 / 2134966681000000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch025

namespace OptimalG.Certificates.StaticSupportData.Batch026
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(668164116602937 / 2134966681000000), (3130199347121233 / 10000000000000000), (780264395432479 / 2500000000000000), (23409162007936785722637673 / 75000000000000000000000000), StaticNodes.Batch0001.node82, StaticNodes.Batch0001.node83, false, false, .piece 115, 78, 115⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(3130199347121233 / 10000000000000000), (13366161532064931 / 42699333620000000), (23409162007936785722637673 / 75000000000000000000000000), (15606247641984977 / 50000000000000000), StaticNodes.Batch0001.node82, StaticNodes.Batch0001.node83, false, false, .piece 116, 78, 116⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(13366161532064931 / 42699333620000000), (6261 / 20000), (15606247641984977 / 50000000000000000), (15606535927877 / 50000000000000), StaticNodes.Batch0001.node82, StaticNodes.Batch0001.node83, false, false, .piece 116, 79, 116⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(6261 / 20000), (890492961292249 / 2844103456000000), (15606535927877 / 50000000000000), (3121453559966849 / 10000000000000000), StaticNodes.Batch0001.node82, StaticNodes.Batch0001.node83, false, false, .piece 116, 79, 116⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(890492961292249 / 2844103456000000), (156555876191359 / 500000000000000), (3121453559966849 / 10000000000000000), (48773168995945382788647 / 156250000000000000000000), StaticNodes.Batch0001.node82, StaticNodes.Batch0001.node83, false, false, .piece 116, 80, 116⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(156555876191359 / 500000000000000), (2226376051020121 / 7110258640000000), (48773168995945382788647 / 156250000000000000000000), (7803777547706621 / 25000000000000000), StaticNodes.Batch0001.node82, StaticNodes.Batch0001.node83, false, false, .piece 117, 80, 117⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(2226376051020121 / 7110258640000000), (1781239927501941 / 5688206912000000), (7803777547706621 / 25000000000000000), (6243161124851141 / 20000000000000000), StaticNodes.Batch0001.node82, StaticNodes.Batch0001.node83, false, false, .piece 117, 81, 117⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(1781239927501941 / 5688206912000000), (1781393438058061 / 5688206912000000), (6243161124851141 / 20000000000000000), (6243314635407261 / 20000000000000000), StaticNodes.Batch0001.node82, StaticNodes.Batch0001.node83, false, false, .piece 117, 82, 117⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(1781393438058061 / 5688206912000000), (890704352693497 / 2844103456000000), (6243314635407261 / 20000000000000000), (3121664951368097 / 10000000000000000), StaticNodes.Batch0001.node82, StaticNodes.Batch0001.node83, false, false, .piece 117, 83, 117⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(890704352693497 / 2844103456000000), (890763819833463 / 2844103456000000), (3121664951368097 / 10000000000000000), (3121724418508063 / 10000000000000000), StaticNodes.Batch0001.node82, StaticNodes.Batch0001.node83, false, false, .piece 117, 84, 117⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(890763819833463 / 2844103456000000), (783 / 2500), (3121724418508063 / 10000000000000000), (15608669005469 / 50000000000000), StaticNodes.Batch0001.node82, StaticNodes.Batch0001.node83, false, false, .piece 117, 85, 117⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(783 / 2500), (1780741245810031 / 5685589248000000), (15608669005469 / 50000000000000), (6243482295524031 / 20000000000000000), StaticNodes.Batch0001.node83, StaticNodes.Batch0001.node84, false, false, .piece 117, 85, 117⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(1780741245810031 / 5685589248000000), (6264071401066249 / 20000000000000000), (6243482295524031 / 20000000000000000), (487772492190963129101917 / 1562500000000000000000000), StaticNodes.Batch0001.node83, StaticNodes.Batch0001.node84, false, false, .piece 117, 86, 117⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(6264071401066249 / 20000000000000000), (8903753291825887 / 28427946240000000), (487772492190963129101917 / 1562500000000000000000000), (31217458540395887 / 100000000000000000), StaticNodes.Batch0001.node83, StaticNodes.Batch0001.node84, false, false, .piece 118, 86, 118⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(8903753291825887 / 28427946240000000), (200451 / 640000), (31217458540395887 / 100000000000000000), (3902183908367 / 12500000000000), StaticNodes.Batch0001.node83, StaticNodes.Batch0001.node84, false, false, .piece 118, 87, 118⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(200451 / 640000), (17505274761819 / 55890841600000), (3902183908367 / 12500000000000), (312174717801669 / 1000000000000000), StaticNodes.Batch0001.node83, StaticNodes.Batch0001.node84, false, false, .piece 118, 87, 118⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (668164116602937 / 2134966681000000) (17505274761819 / 55890841600000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch026

namespace OptimalG.Certificates.StaticSupportData.Batch027
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(17505274761819 / 55890841600000), (455137454762241 / 1453161881600000), (312174717801669 / 1000000000000000), (624349539254987 / 2000000000000000), StaticNodes.Batch0001.node83, StaticNodes.Batch0001.node84, false, false, .piece 118, 88, 118⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(455137454762241 / 1453161881600000), (2275687980625701 / 7265809408000000), (624349539254987 / 2000000000000000), (3121747931879767 / 10000000000000000), StaticNodes.Batch0001.node83, StaticNodes.Batch0001.node84, false, false, .piece 118, 89, 118⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(2275687980625701 / 7265809408000000), (1137845175774009 / 3632904704000000), (3121747931879767 / 10000000000000000), (1560874361093603 / 5000000000000000), StaticNodes.Batch0001.node83, StaticNodes.Batch0001.node84, false, false, .piece 118, 90, 118⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(1137845175774009 / 3632904704000000), (801807 / 2560000), (1560874361093603 / 5000000000000000), (7804374912251 / 25000000000000), StaticNodes.Batch0001.node83, StaticNodes.Batch0001.node84, false, false, .piece 118, 91, 118⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(801807 / 2560000), (2171578700665167 / 6933370112000000), (7804374912251 / 25000000000000), (3121752150357489 / 10000000000000000), StaticNodes.Batch0001.node83, StaticNodes.Batch0001.node84, false, false, .piece 118, 91, 118⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(2171578700665167 / 6933370112000000), (80181 / 256000), (3121752150357489 / 10000000000000000), (31217526732481 / 100000000000000), StaticNodes.Batch0001.node83, StaticNodes.Batch0001.node84, false, false, .piece 118, 92, 118⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(80181 / 256000), (100227 / 320000), (31217526732481 / 100000000000000), (31217581865029 / 100000000000000), StaticNodes.Batch0001.node83, StaticNodes.Batch0001.node84, false, false, .piece 118, 92, 118⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(100227 / 320000), (2198694056250399 / 7019799680000000), (31217581865029 / 100000000000000), (3121767181787033 / 10000000000000000), StaticNodes.Batch0001.node83, StaticNodes.Batch0001.node84, false, false, .piece 118, 92, 118⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(2198694056250399 / 7019799680000000), (200457 / 640000), (3121767181787033 / 10000000000000000), (31217691549399 / 100000000000000), StaticNodes.Batch0001.node83, StaticNodes.Batch0001.node84, false, false, .piece 118, 93, 118⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(200457 / 640000), (10023 / 32000), (31217691549399 / 100000000000000), (15608898797763 / 50000000000000), StaticNodes.Batch0001.node83, StaticNodes.Batch0001.node84, false, false, .piece 118, 93, 118⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(10023 / 32000), (25059 / 80000), (15608898797763 / 50000000000000), (7804555147513 / 25000000000000), StaticNodes.Batch0001.node83, StaticNodes.Batch0001.node84, false, false, .piece 118, 93, 118⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(25059 / 80000), (7587951969240327 / 24223969600000000), (7804555147513 / 25000000000000), (31218316881712327 / 100000000000000000), StaticNodes.Batch0001.node83, StaticNodes.Batch0001.node84, false, false, .piece 118, 93, 118⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(7587951969240327 / 24223969600000000), (12531 / 40000), (31218316881712327 / 100000000000000000), (1951195561807 / 6250000000000), StaticNodes.Batch0001.node83, StaticNodes.Batch0001.node84, false, false, .piece 118, 94, 118⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(12531 / 40000), (578130315482727 / 1845433630000000), (1951195561807 / 6250000000000), (780478923070959 / 2500000000000000), StaticNodes.Batch0001.node83, StaticNodes.Batch0001.node84, false, false, .piece 118, 94, 118⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(578130315482727 / 1845433630000000), (6267 / 20000), (780478923070959 / 2500000000000000), (15610487211271 / 50000000000000), StaticNodes.Batch0001.node83, StaticNodes.Batch0001.node84, false, false, .piece 118, 95, 118⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(6267 / 20000), (484179469082541 / 1545125320000000), (15610487211271 / 50000000000000), (243915668933677 / 781250000000000), StaticNodes.Batch0001.node83, StaticNodes.Batch0001.node84, false, false, .piece 118, 95, 118⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (17505274761819 / 55890841600000) (484179469082541 / 1545125320000000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch027

namespace OptimalG.Certificates.StaticSupportData.Batch028
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(484179469082541 / 1545125320000000), (4011 / 12800), (243915668933677 / 781250000000000), (1561060309567 / 5000000000000), StaticNodes.Batch0001.node83, StaticNodes.Batch0001.node84, false, false, .piece 118, 96, 118⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(4011 / 12800), (50139 / 160000), (1561060309567 / 5000000000000), (3122140362061 / 10000000000000), StaticNodes.Batch0001.node83, StaticNodes.Batch0001.node84, false, false, .piece 118, 96, 118⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(50139 / 160000), (9888629400480471 / 31554209120000000), (3122140362061 / 10000000000000), (15610877254074157 / 50000000000000000), StaticNodes.Batch0001.node83, StaticNodes.Batch0001.node84, false, false, .piece 118, 96, 118⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(9888629400480471 / 31554209120000000), (25071 / 80000), (15610877254074157 / 50000000000000000), (975681189007 / 3125000000000), StaticNodes.Batch0001.node83, StaticNodes.Batch0001.node84, false, false, .piece 118, 97, 118⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(25071 / 80000), (489701269966569 / 1562500000000000), (975681189007 / 3125000000000), (60980948633792124608141 / 195312500000000000000000), StaticNodes.Batch0001.node83, StaticNodes.Batch0001.node84, false, false, .piece 118, 97, 118⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(489701269966569 / 1562500000000000), (1234333119837813 / 3938238350000000), (60980948633792124608141 / 195312500000000000000000), (487852131914099 / 1562500000000000), StaticNodes.Batch0001.node83, StaticNodes.Batch0001.node84, false, false, .piece 119, 97, 119⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(1234333119837813 / 3938238350000000), (12537 / 40000), (487852131914099 / 1562500000000000), (15611292847947 / 50000000000000), StaticNodes.Batch0001.node83, StaticNodes.Batch0001.node84, false, false, .piece 119, 98, 119⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(12537 / 40000), (627 / 2000), (15611292847947 / 50000000000000), (15612078171619 / 50000000000000), StaticNodes.Batch0001.node83, StaticNodes.Batch0001.node84, false, false, .piece 119, 98, 119⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(627 / 2000), (12543 / 40000), (15612078171619 / 50000000000000), (7806430231953 / 25000000000000), StaticNodes.Batch0001.node84, StaticNodes.Batch0001.node85, false, false, .piece 119, 98, 119⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(12543 / 40000), (9775720314321189 / 31174247620000000), (7806430231953 / 25000000000000), (15612945669532563 / 50000000000000000), StaticNodes.Batch0001.node84, StaticNodes.Batch0001.node85, false, false, .piece 119, 98, 119⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(9775720314321189 / 31174247620000000), (3136140555038959 / 10000000000000000), (15612945669532563 / 50000000000000000), (23419899458833687330651379 / 75000000000000000000000000), StaticNodes.Batch0001.node84, StaticNodes.Batch0001.node85, false, false, .piece 119, 99, 119⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(3136140555038959 / 10000000000000000), (6273 / 20000), (23419899458833687330651379 / 75000000000000000000000000), (31227279640193 / 100000000000000), StaticNodes.Batch0001.node84, StaticNodes.Batch0001.node85, false, false, .piece 120, 99, 120⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(6273 / 20000), (12549 / 40000), (31227279640193 / 100000000000000), (31228832769573 / 100000000000000), StaticNodes.Batch0001.node84, StaticNodes.Batch0001.node85, false, false, .piece 120, 99, 120⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(12549 / 40000), (1942300387121973 / 6190696780000000), (31228832769573 / 100000000000000), (3122924623562791 / 10000000000000000), StaticNodes.Batch0001.node84, StaticNodes.Batch0001.node85, false, false, .piece 120, 99, 120⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(1942300387121973 / 6190696780000000), (1569 / 5000), (3122924623562791 / 10000000000000000), (3903797555471 / 12500000000000), StaticNodes.Batch0001.node84, StaticNodes.Batch0001.node85, false, false, .piece 120, 100, 120⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(1569 / 5000), (5021108771667 / 16000000000000), (487974694437 / 1562500000000), (9993876030097467228303 / 32000000000000000000000), StaticNodes.Batch0001.node85, StaticNodes.Batch0001.node86, false, false, .piece 120, 100, 120⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (484179469082541 / 1545125320000000) (5021108771667 / 16000000000000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch028
