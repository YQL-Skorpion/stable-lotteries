import OptimalG.Certificates.StaticLayerFast
import OptimalG.Certificates.StaticLayerGeometry
import OptimalG.Certificates.StaticSegmentData
import OptimalG.Certificates.SegmentMembership
import OptimalG.Certificates.StaticLayerCover

set_option Elab.async false

namespace OptimalG.Certificates.StaticSupportData.Batch051
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(1719 / 5000), (6879 / 20000), (6487274611209 / 20000000000000), (8111367798569 / 25000000000000), StaticNodes.Batch0002.node57, StaticNodes.Batch0002.node58, false, false, .piece 229, 176, 229⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(6879 / 20000), (625791769490649 / 1819087675400000), (8111367798569 / 25000000000000), (324493566455033 / 1000000000000000), StaticNodes.Batch0002.node57, StaticNodes.Batch0002.node58, false, false, .piece 229, 176, 229⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(625791769490649 / 1819087675400000), (860175047368787 / 2500000000000000), (324493566455033 / 1000000000000000), (12169780760206483151738699 / 37500000000000000000000000), StaticNodes.Batch0002.node57, StaticNodes.Batch0002.node58, false, false, .piece 229, 177, 229⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(860175047368787 / 2500000000000000), (3441 / 10000), (12169780760206483151738699 / 37500000000000000000000000), (32454566632653 / 100000000000000), StaticNodes.Batch0002.node57, StaticNodes.Batch0002.node58, false, false, .piece 230, 177, 230⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(3441 / 10000), (1377 / 4000), (32454566632653 / 100000000000000), (32463659335819 / 100000000000000), StaticNodes.Batch0002.node58, StaticNodes.Batch0002.node59, false, false, .piece 230, 177, 230⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(1377 / 4000), (20867921804425623 / 60600426140000000), (32463659335819 / 100000000000000), (32469884441549623 / 100000000000000000), StaticNodes.Batch0002.node58, StaticNodes.Batch0002.node59, false, false, .piece 230, 177, 230⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(20867921804425623 / 60600426140000000), (861 / 2500), (32469884441549623 / 100000000000000000), (1623637469987 / 5000000000000), StaticNodes.Batch0002.node58, StaticNodes.Batch0002.node59, false, false, .piece 230, 178, 230⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(861 / 2500), (17222126200831747 / 50000000000000000), (1623637469987 / 5000000000000), (243564941983696814108549923 / 750000000000000000000000000), StaticNodes.Batch0002.node59, StaticNodes.Batch0002.node60, false, false, .piece 230, 178, 230⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(17222126200831747 / 50000000000000000), (6891 / 20000), (243564941983696814108549923 / 750000000000000000000000000), (32481836728349 / 100000000000000), StaticNodes.Batch0002.node59, StaticNodes.Batch0002.node60, false, false, .piece 231, 178, 231⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(6891 / 20000), (3447 / 10000), (32481836728349 / 100000000000000), (16245460691413 / 50000000000000), StaticNodes.Batch0002.node59, StaticNodes.Batch0002.node60, false, false, .piece 231, 178, 231⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(3447 / 10000), (6896300581715099 / 20000000000000000), (16245460691413 / 50000000000000), (3249788606270770106539499 / 10000000000000000000000000), StaticNodes.Batch0002.node60, StaticNodes.Batch0002.node61, false, false, .piece 231, 178, 231⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(6896300581715099 / 20000000000000000), (6897 / 20000), (3249788606270770106539499 / 10000000000000000000000000), (4062500431357 / 12500000000000), StaticNodes.Batch0002.node60, StaticNodes.Batch0002.node61, false, false, .piece 232, 178, 232⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(6897 / 20000), (1566081825233787 / 4539788650000000), (4062500431357 / 12500000000000), (812678656031829 / 2500000000000000), StaticNodes.Batch0002.node60, StaticNodes.Batch0002.node61, false, false, .piece 232, 178, 232⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(1566081825233787 / 4539788650000000), (69 / 200), (812678656031829 / 2500000000000000), (8127270757039 / 25000000000000), StaticNodes.Batch0002.node60, StaticNodes.Batch0002.node61, false, false, .piece 232, 179, 232⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(69 / 200), (6903 / 20000), (8127270757039 / 25000000000000), (32518160057503 / 100000000000000), StaticNodes.Batch0002.node61, StaticNodes.Batch0002.node62, false, false, .piece 232, 179, 232⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(6903 / 20000), (2761500273239 / 8000000000000), (32518160057503 / 100000000000000), (7804903375658401390387 / 24000000000000000000000), StaticNodes.Batch0002.node61, StaticNodes.Batch0002.node62, false, false, .piece 232, 179, 232⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (1719 / 5000) (2761500273239 / 8000000000000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch051

namespace OptimalG.Certificates.StaticSupportData.Batch052
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(2761500273239 / 8000000000000), (3453 / 10000), (7804903375658401390387 / 24000000000000000000000), (4065904311271 / 12500000000000), StaticNodes.Batch0002.node61, StaticNodes.Batch0002.node62, false, false, .piece 233, 179, 233⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(3453 / 10000), (6909 / 20000), (4065904311271 / 12500000000000), (8134076603107 / 25000000000000), StaticNodes.Batch0002.node62, StaticNodes.Batch0002.node63, false, false, .piece 233, 179, 233⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(6909 / 20000), (34556003922399503 / 100000000000000000), (8134076603107 / 25000000000000), (488144396170797273911357011 / 1500000000000000000000000000), StaticNodes.Batch0002.node62, StaticNodes.Batch0002.node63, false, false, .piece 233, 179, 233⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(34556003922399503 / 100000000000000000), (391783899922119 / 1133686479625000), (488144396170797273911357011 / 1500000000000000000000000000), (813610201024917 / 2500000000000000), StaticNodes.Batch0002.node62, StaticNodes.Batch0002.node63, false, false, .piece 234, 179, 234⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(391783899922119 / 1133686479625000), (216 / 625), (813610201024917 / 2500000000000000), (6509075180853 / 20000000000000), StaticNodes.Batch0002.node62, StaticNodes.Batch0002.node63, false, false, .piece 234, 180, 234⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(216 / 625), (1383 / 4000), (6509075180853 / 20000000000000), (1302177714211 / 4000000000000), StaticNodes.Batch0002.node63, StaticNodes.Batch0002.node64, false, false, .piece 234, 180, 234⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(1383 / 4000), (3459 / 10000), (1302177714211 / 4000000000000), (32563507286289 / 100000000000000), StaticNodes.Batch0002.node63, StaticNodes.Batch0002.node64, false, false, .piece 234, 180, 234⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(3459 / 10000), (3459325442931151 / 10000000000000000), (32563507286289 / 100000000000000), (16282736697379823029783953 / 50000000000000000000000000), StaticNodes.Batch0002.node64, StaticNodes.Batch0002.node65, false, false, .piece 234, 180, 234⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(3459325442931151 / 10000000000000000), (6921 / 20000), (16282736697379823029783953 / 50000000000000000000000000), (16286284641399 / 50000000000000), StaticNodes.Batch0002.node64, StaticNodes.Batch0002.node65, false, false, .piece 235, 180, 235⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(6921 / 20000), (1731 / 5000), (16286284641399 / 50000000000000), (16290814464993 / 50000000000000), StaticNodes.Batch0002.node64, StaticNodes.Batch0002.node65, false, false, .piece 235, 180, 235⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(1731 / 5000), (313562207172873 / 905723840300000), (16290814464993 / 50000000000000), (162908349203601 / 500000000000000), StaticNodes.Batch0002.node65, StaticNodes.Batch0002.node66, false, false, .piece 235, 180, 235⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(313562207172873 / 905723840300000), (8657626234055879 / 25000000000000000), (162908349203601 / 500000000000000), (122204894915393673726721237 / 375000000000000000000000000), StaticNodes.Batch0002.node65, StaticNodes.Batch0002.node66, false, false, .piece 235, 181, 235⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(8657626234055879 / 25000000000000000), (6927 / 20000), (122204894915393673726721237 / 375000000000000000000000000), (32590686168389 / 100000000000000), StaticNodes.Batch0002.node65, StaticNodes.Batch0002.node66, false, false, .piece 236, 181, 236⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(6927 / 20000), (693 / 2000), (32590686168389 / 100000000000000), (32599740980743 / 100000000000000), StaticNodes.Batch0002.node65, StaticNodes.Batch0002.node66, false, false, .piece 236, 181, 236⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(693 / 2000), (6933 / 20000), (32599740980743 / 100000000000000), (32608793451083 / 100000000000000), StaticNodes.Batch0002.node66, StaticNodes.Batch0002.node67, false, false, .piece 236, 181, 236⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(6933 / 20000), (34667755443135523 / 100000000000000000), (32608793451083 / 100000000000000), (489156839113280125691066407 / 1500000000000000000000000000), StaticNodes.Batch0002.node66, StaticNodes.Batch0002.node67, false, false, .piece 236, 181, 236⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (2761500273239 / 8000000000000) (34667755443135523 / 100000000000000000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch052

namespace OptimalG.Certificates.StaticSupportData.Batch053
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(34667755443135523 / 100000000000000000), (867 / 2500), (489156839113280125691066407 / 1500000000000000000000000000), (4077230457999 / 12500000000000), StaticNodes.Batch0002.node66, StaticNodes.Batch0002.node67, false, false, .piece 237, 181, 237⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(867 / 2500), (1901821881118157 / 5483630260000000), (4077230457999 / 12500000000000), (32618931640443727 / 100000000000000000), StaticNodes.Batch0002.node67, StaticNodes.Batch0002.node68, false, false, .piece 237, 181, 237⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(1901821881118157 / 5483630260000000), (6939 / 20000), (32618931640443727 / 100000000000000000), (32626891653921 / 100000000000000), StaticNodes.Batch0002.node67, StaticNodes.Batch0002.node68, false, false, .piece 237, 182, 237⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(6939 / 20000), (3470500595004753 / 10000000000000000), (32626891653921 / 100000000000000), (8158231418100929923861011 / 25000000000000000000000000), StaticNodes.Batch0002.node67, StaticNodes.Batch0002.node68, false, false, .piece 237, 182, 237⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(3470500595004753 / 10000000000000000), (3471 / 10000), (8158231418100929923861011 / 25000000000000000000000000), (32635937299443 / 100000000000000), StaticNodes.Batch0002.node67, StaticNodes.Batch0002.node68, false, false, .piece 238, 182, 238⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(3471 / 10000), (1389 / 4000), (32635937299443 / 100000000000000), (32644980674633 / 100000000000000), StaticNodes.Batch0002.node68, StaticNodes.Batch0002.node69, false, false, .piece 238, 182, 238⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(1389 / 4000), (1737 / 5000), (32644980674633 / 100000000000000), (32654021862447 / 100000000000000), StaticNodes.Batch0002.node68, StaticNodes.Batch0002.node69, false, false, .piece 238, 182, 238⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(1737 / 5000), (3474225645695953 / 10000000000000000), (32654021862447 / 100000000000000), (1632769080005142343766451 / 5000000000000000000000000), StaticNodes.Batch0002.node69, StaticNodes.Batch0002.node70, false, false, .piece 238, 182, 238⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(3474225645695953 / 10000000000000000), (20936506733801657 / 60259853400000000), (1632769080005142343766451 / 5000000000000000000000000), (32656255525088657 / 100000000000000000), StaticNodes.Batch0002.node69, StaticNodes.Batch0002.node70, false, false, .piece 239, 182, 239⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(20936506733801657 / 60259853400000000), (6951 / 20000), (32656255525088657 / 100000000000000000), (32663060840457 / 100000000000000), StaticNodes.Batch0002.node69, StaticNodes.Batch0002.node70, false, false, .piece 239, 183, 239⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(6951 / 20000), (3477 / 10000), (32663060840457 / 100000000000000), (32672097534887 / 100000000000000), StaticNodes.Batch0002.node69, StaticNodes.Batch0002.node70, false, false, .piece 239, 183, 239⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(3477 / 10000), (1738975348193577 / 5000000000000000), (32672097534887 / 100000000000000), (8169455894110005133113977 / 25000000000000000000000000), StaticNodes.Batch0002.node70, StaticNodes.Batch0002.node71, false, false, .piece 239, 183, 239⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(1738975348193577 / 5000000000000000), (6957 / 20000), (8169455894110005133113977 / 25000000000000000000000000), (3268113203049 / 10000000000000), StaticNodes.Batch0002.node70, StaticNodes.Batch0002.node71, false, false, .piece 240, 183, 240⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(6957 / 20000), (87 / 250), (3268113203049 / 10000000000000), (32690164409419 / 100000000000000), StaticNodes.Batch0002.node70, StaticNodes.Batch0002.node71, false, false, .piece 240, 183, 240⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(87 / 250), (1047682794899729 / 3010092083000000), (32690164409419 / 100000000000000), (1634678970486679 / 5000000000000000), StaticNodes.Batch0002.node71, StaticNodes.Batch0002.node72, false, false, .piece 240, 183, 240⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(1047682794899729 / 3010092083000000), (6963 / 20000), (1634678970486679 / 5000000000000000), (8174798671417 / 25000000000000), StaticNodes.Batch0002.node71, StaticNodes.Batch0002.node72, false, false, .piece 240, 184, 240⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (34667755443135523 / 100000000000000000) (6963 / 20000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch053

namespace OptimalG.Certificates.StaticSupportData.Batch054
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(6963 / 20000), (1740837873539177 / 5000000000000000), (8174798671417 / 25000000000000), (24525189344041694748893647 / 75000000000000000000000000), StaticNodes.Batch0002.node71, StaticNodes.Batch0002.node72, false, false, .piece 240, 184, 240⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(1740837873539177 / 5000000000000000), (3483 / 10000), (24525189344041694748893647 / 75000000000000000000000000), (32708222770779 / 100000000000000), StaticNodes.Batch0002.node71, StaticNodes.Batch0002.node72, false, false, .piece 241, 184, 241⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(3483 / 10000), (6970801595539109 / 20000000000000000), (32708222770979 / 100000000000000), (2045166758817 / 6250000000000), StaticNodes.Batch0002.node72, StaticNodes.Batch0002.node73, false, false, .piece 241, 184, 241⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(6970801595539109 / 20000000000000000), (12099166380621908461614891603 / 34688857528000000000000000000), (2045166758817 / 6250000000000), (6546208990435033 / 20000000000000000), StaticNodes.Batch0002.node73, StaticNodes.Batch0002.node74, false, false, .tail, 184, 242⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(12099166380621908461614891603 / 34688857528000000000000000000), (218 / 625), (6546208990435033 / 20000000000000000), (16365670177727 / 50000000000000), StaticNodes.Batch0002.node73, StaticNodes.Batch0002.node74, false, false, .tail, 185, 242⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(218 / 625), (3491 / 10000), (16365670177727 / 50000000000000), (8185352544037 / 25000000000000), StaticNodes.Batch0002.node74, StaticNodes.Batch0002.node75, false, false, .tail, 185, 242⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(3491 / 10000), (1747 / 5000), (8185352544037 / 25000000000000), (16375772477589 / 50000000000000), StaticNodes.Batch0002.node75, StaticNodes.Batch0002.node76, false, false, .tail, 185, 242⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(1747 / 5000), (3497 / 10000), (16375772477589 / 50000000000000), (32761745240689 / 100000000000000), StaticNodes.Batch0002.node76, StaticNodes.Batch0002.node77, false, false, .tail, 185, 242⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(3497 / 10000), (6997 / 20000), (32761745240489 / 100000000000000), (6553374024431 / 20000000000000), StaticNodes.Batch0002.node77, StaticNodes.Batch0002.node78, false, false, .tail, 185, 242⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(6997 / 20000), (13997 / 40000), (6553374024431 / 20000000000000), (16384719389269 / 50000000000000), StaticNodes.Batch0002.node77, StaticNodes.Batch0002.node78, false, false, .tail, 185, 242⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(13997 / 40000), (55991 / 160000), (16384719389269 / 50000000000000), (32770081591589 / 100000000000000), StaticNodes.Batch0002.node77, StaticNodes.Batch0002.node78, false, false, .tail, 185, 242⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(55991 / 160000), (22397 / 64000), (32770081591589 / 100000000000000), (16385201547777 / 50000000000000), StaticNodes.Batch0002.node77, StaticNodes.Batch0002.node78, false, false, .tail, 185, 242⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(22397 / 64000), (895883 / 2560000), (16385201547777 / 50000000000000), (32770443288119 / 100000000000000), StaticNodes.Batch0002.node77, StaticNodes.Batch0002.node78, false, false, .tail, 185, 242⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(895883 / 2560000), (716707 / 2048000), (32770443288119 / 100000000000000), (16385226668209 / 50000000000000), StaticNodes.Batch0002.node77, StaticNodes.Batch0002.node78, false, false, .tail, 185, 242⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(716707 / 2048000), (72017240181313 / 205790167040000), (16385226668209 / 50000000000000), (65540915566487 / 200000000000000), StaticNodes.Batch0002.node77, StaticNodes.Batch0002.node78, false, false, .tail, 185, 242⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(72017240181313 / 205790167040000), (7167073 / 20480000), (65540915566487 / 200000000000000), (2048153647537 / 6250000000000), StaticNodes.Batch0002.node77, StaticNodes.Batch0002.node78, false, false, .tail, 186, 242⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (6963 / 20000) (7167073 / 20480000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch054
