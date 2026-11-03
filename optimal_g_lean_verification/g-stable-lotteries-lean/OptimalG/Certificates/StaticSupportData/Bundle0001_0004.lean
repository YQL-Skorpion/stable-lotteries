import OptimalG.Certificates.StaticLayerFast
import OptimalG.Certificates.StaticLayerGeometry
import OptimalG.Certificates.StaticSegmentData
import OptimalG.Certificates.SegmentMembership
import OptimalG.Certificates.StaticLayerCover

set_option Elab.async false

namespace OptimalG.Certificates.StaticSupportData.Batch001
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(637 / 2500), (2551 / 10000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node16, StaticNodes.Batch0000.node17, true, true, .cap, 0, 0⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(2551 / 10000), (1277 / 5000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node17, StaticNodes.Batch0000.node18, true, true, .cap, 0, 0⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(1277 / 5000), (2557 / 10000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node18, StaticNodes.Batch0000.node19, true, true, .cap, 0, 0⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(2557 / 10000), (32 / 125), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node19, StaticNodes.Batch0000.node20, true, true, .cap, 0, 0⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(32 / 125), (2563 / 10000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node20, StaticNodes.Batch0000.node21, true, true, .cap, 0, 0⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(2563 / 10000), (1283 / 5000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node21, StaticNodes.Batch0000.node22, true, true, .cap, 0, 0⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(1283 / 5000), (2569 / 10000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node22, StaticNodes.Batch0000.node23, true, true, .cap, 0, 0⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(2569 / 10000), (643 / 2500), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node23, StaticNodes.Batch0000.node24, true, true, .cap, 0, 0⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(643 / 2500), (103 / 400), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node24, StaticNodes.Batch0000.node25, true, true, .cap, 0, 0⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(103 / 400), (1289 / 5000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node25, StaticNodes.Batch0000.node26, true, true, .cap, 0, 0⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(1289 / 5000), (2581 / 10000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node26, StaticNodes.Batch0000.node27, true, true, .cap, 0, 0⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(2581 / 10000), (323 / 1250), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node27, StaticNodes.Batch0000.node28, true, true, .cap, 0, 0⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(323 / 1250), (2587 / 10000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node28, StaticNodes.Batch0000.node29, true, true, .cap, 0, 0⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(2587 / 10000), (259 / 1000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node29, StaticNodes.Batch0000.node30, true, true, .cap, 0, 0⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(259 / 1000), (2593 / 10000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node30, StaticNodes.Batch0000.node31, true, true, .cap, 0, 0⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(2593 / 10000), (649 / 2500), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node31, StaticNodes.Batch0000.node32, true, true, .cap, 0, 0⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (637 / 2500) (649 / 2500) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch001

namespace OptimalG.Certificates.StaticSupportData.Batch002
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(649 / 2500), (2599 / 10000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node32, StaticNodes.Batch0000.node33, true, true, .cap, 0, 0⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(2599 / 10000), (1301 / 5000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node33, StaticNodes.Batch0000.node34, true, true, .cap, 0, 0⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(1301 / 5000), (521 / 2000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node34, StaticNodes.Batch0000.node35, true, true, .cap, 0, 0⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(521 / 2000), (163 / 625), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node35, StaticNodes.Batch0000.node36, true, true, .cap, 0, 0⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(163 / 625), (2611 / 10000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node36, StaticNodes.Batch0000.node37, true, true, .cap, 0, 0⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(2611 / 10000), (1307 / 5000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node37, StaticNodes.Batch0000.node38, true, true, .cap, 0, 0⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(1307 / 5000), (2617 / 10000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node38, StaticNodes.Batch0000.node39, true, true, .cap, 0, 0⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(2617 / 10000), (131 / 500), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node39, StaticNodes.Batch0000.node40, true, true, .cap, 0, 0⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(131 / 500), (2623 / 10000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node40, StaticNodes.Batch0000.node41, true, true, .cap, 0, 0⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(2623 / 10000), (1313 / 5000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node41, StaticNodes.Batch0000.node42, true, true, .cap, 0, 0⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(1313 / 5000), (2629 / 10000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node42, StaticNodes.Batch0000.node43, true, true, .cap, 0, 0⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(2629 / 10000), (329 / 1250), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node43, StaticNodes.Batch0000.node44, true, true, .cap, 0, 0⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(329 / 1250), (527 / 2000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node44, StaticNodes.Batch0000.node45, true, true, .cap, 0, 0⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(527 / 2000), (1319 / 5000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node45, StaticNodes.Batch0000.node46, true, true, .cap, 0, 0⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(1319 / 5000), (2641 / 10000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node46, StaticNodes.Batch0000.node47, true, true, .cap, 0, 0⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(2641 / 10000), (661 / 2500), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node47, StaticNodes.Batch0000.node48, true, true, .cap, 0, 0⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (649 / 2500) (661 / 2500) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch002

namespace OptimalG.Certificates.StaticSupportData.Batch003
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(661 / 2500), (2647 / 10000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node48, StaticNodes.Batch0000.node49, true, true, .cap, 0, 0⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(2647 / 10000), (53 / 200), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node49, StaticNodes.Batch0000.node50, true, true, .cap, 0, 0⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(53 / 200), (2653 / 10000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node50, StaticNodes.Batch0000.node51, true, true, .cap, 0, 0⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(2653 / 10000), (166 / 625), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node51, StaticNodes.Batch0000.node52, true, true, .cap, 0, 0⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(166 / 625), (2659 / 10000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node52, StaticNodes.Batch0000.node53, true, true, .cap, 0, 0⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(2659 / 10000), (1331 / 5000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node53, StaticNodes.Batch0000.node54, true, true, .cap, 0, 0⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(1331 / 5000), (533 / 2000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node54, StaticNodes.Batch0000.node55, true, true, .cap, 0, 0⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(533 / 2000), (667 / 2500), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node55, StaticNodes.Batch0000.node56, true, true, .cap, 0, 0⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(667 / 2500), (2671 / 10000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node56, StaticNodes.Batch0000.node57, true, true, .cap, 0, 0⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(2671 / 10000), (1337 / 5000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node57, StaticNodes.Batch0000.node58, true, true, .cap, 0, 0⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(1337 / 5000), (2677 / 10000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node58, StaticNodes.Batch0000.node59, true, true, .cap, 0, 0⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(2677 / 10000), (67 / 250), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node59, StaticNodes.Batch0000.node60, true, true, .cap, 0, 0⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(67 / 250), (89965726889 / 335544320000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node60, StaticNodes.Batch0000.node61, true, true, .cap, 0, 0⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(89965726889 / 335544320000), (22491431723 / 83886080000), (2950935105377889 / 10000000000000000), (2950935105377889 / 10000000000000000), StaticNodes.Batch0000.node60, StaticNodes.Batch0000.node61, false, true, .cap, 0, 0⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(22491431723 / 83886080000), (2683 / 10000), (14754675527051 / 50000000000000), (29516707301623 / 100000000000000), StaticNodes.Batch0000.node60, StaticNodes.Batch0000.node61, false, true, .cap, 0, 0⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(2683 / 10000), (1343 / 5000), (29516707301623 / 100000000000000), (7382224627789 / 25000000000000), StaticNodes.Batch0000.node61, StaticNodes.Batch0000.node62, false, true, .cap, 0, 0⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (661 / 2500) (1343 / 5000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch003

namespace OptimalG.Certificates.StaticSupportData.Batch004
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(1343 / 5000), (546892391056393 / 2034933675500000), (7382224627789 / 25000000000000), (1476754131374893 / 5000000000000000), StaticNodes.Batch0000.node62, StaticNodes.Batch0000.node63, false, true, .cap, 0, 0⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(546892391056393 / 2034933675500000), (2689 / 10000), (1476754131374893 / 5000000000000000), (29541108113209 / 100000000000000), StaticNodes.Batch0000.node62, StaticNodes.Batch0000.node63, false, true, .cap, 1, 1⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(2689 / 10000), (673 / 2500), (29541108113209 / 100000000000000), (1847083508237 / 6250000000000), StaticNodes.Batch0000.node63, StaticNodes.Batch0000.node64, false, true, .cap, 1, 1⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(673 / 2500), (219933471297137 / 816433469200000), (1847083508237 / 6250000000000), (591216304024337 / 2000000000000000), StaticNodes.Batch0000.node64, StaticNodes.Batch0000.node65, false, true, .cap, 1, 1⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(219933471297137 / 816433469200000), (539 / 2000), (591216304024337 / 2000000000000000), (2956558263383 / 10000000000000), StaticNodes.Batch0000.node64, StaticNodes.Batch0000.node65, false, true, .cap, 2, 2⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(539 / 2000), (1349 / 5000), (2956558263383 / 10000000000000), (1848615477793 / 6250000000000), StaticNodes.Batch0000.node65, StaticNodes.Batch0000.node66, false, true, .cap, 2, 2⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(1349 / 5000), (1658360671650773 / 6141792632000000), (1848615477793 / 6250000000000), (1479327388746791 / 5000000000000000), StaticNodes.Batch0000.node66, StaticNodes.Batch0000.node67, false, true, .cap, 2, 2⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(1658360671650773 / 6141792632000000), (2701 / 10000), (1479327388746791 / 5000000000000000), (115586450117 / 390625000000), StaticNodes.Batch0000.node66, StaticNodes.Batch0000.node67, false, true, .cap, 3, 3⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(2701 / 10000), (169 / 625), (115586450117 / 390625000000), (14801216708927 / 50000000000000), StaticNodes.Batch0000.node67, StaticNodes.Batch0000.node68, false, true, .cap, 3, 3⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(169 / 625), (33345128486050421 / 123208534370000000), (14801216708927 / 50000000000000), (29612280348654807 / 100000000000000000), StaticNodes.Batch0000.node68, StaticNodes.Batch0000.node69, false, true, .cap, 3, 3⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(33345128486050421 / 123208534370000000), (2707 / 10000), (29612280348654807 / 100000000000000000), (29614754271291 / 100000000000000), StaticNodes.Batch0000.node68, StaticNodes.Batch0000.node69, false, true, .cap, 4, 4⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(2707 / 10000), (271 / 1000), (29614754271291 / 100000000000000), (14813546911283 / 50000000000000), StaticNodes.Batch0000.node69, StaticNodes.Batch0000.node70, false, true, .cap, 4, 4⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(271 / 1000), (16761886313556661 / 61791541195000000), (14813546911283 / 50000000000000), (14819006461186887 / 50000000000000000), StaticNodes.Batch0000.node70, StaticNodes.Batch0000.node71, false, true, .cap, 4, 4⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(16761886313556661 / 61791541195000000), (2713 / 10000), (14819006461186887 / 50000000000000000), (5927890426161 / 20000000000000), StaticNodes.Batch0000.node70, StaticNodes.Batch0000.node71, false, true, .cap, 5, 5⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(2713 / 10000), (679 / 2500), (5927890426161 / 20000000000000), (29651829233351 / 100000000000000), StaticNodes.Batch0000.node71, StaticNodes.Batch0000.node72, false, true, .cap, 5, 5⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(679 / 2500), (16203438840341 / 59595920187500), (29651829233351 / 100000000000000), (741593637402319 / 2500000000000000), StaticNodes.Batch0000.node72, StaticNodes.Batch0000.node73, false, true, .cap, 5, 5⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (1343 / 5000) (16203438840341 / 59595920187500) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch004
