import OptimalG.Certificates.StaticLayerFast
import OptimalG.Certificates.StaticLayerGeometry
import OptimalG.Certificates.StaticSegmentData
import OptimalG.Certificates.SegmentMembership
import OptimalG.Certificates.StaticLayerCover

set_option Elab.async false

namespace OptimalG.Certificates.StaticSupportData.Batch055
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(7167073 / 20480000), (1791769 / 5120000), (2048153647537 / 6250000000000), (3277045908023 / 10000000000000), StaticNodes.Batch0002.node77, StaticNodes.Batch0002.node78, false, false, .tail, 186, 242⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(1791769 / 5120000), (447943 / 1280000), (3277045908023 / 10000000000000), (6554092075459 / 20000000000000), StaticNodes.Batch0002.node77, StaticNodes.Batch0002.node78, false, false, .tail, 186, 242⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(447943 / 1280000), (223973 / 640000), (6554092075459 / 20000000000000), (32770465565649 / 100000000000000), StaticNodes.Batch0002.node77, StaticNodes.Batch0002.node78, false, false, .tail, 186, 242⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(223973 / 640000), (27997 / 80000), (32770465565649 / 100000000000000), (32770475942823 / 100000000000000), StaticNodes.Batch0002.node77, StaticNodes.Batch0002.node78, false, false, .tail, 186, 242⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(27997 / 80000), (7 / 20), (32770475942823 / 100000000000000), (32770558982531 / 100000000000000), StaticNodes.Batch0002.node77, StaticNodes.Batch0002.node78, false, false, .tail, 186, 242⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(7 / 20), (3503 / 10000), (32770558982731 / 100000000000000), (32771224729227 / 100000000000000), StaticNodes.Batch0002.node78, StaticNodes.Batch0002.node79, false, false, .tail, 186, 242⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(3503 / 10000), (1753 / 5000), (32771224729227 / 100000000000000), (32771893017163 / 100000000000000), StaticNodes.Batch0002.node79, StaticNodes.Batch0002.node80, false, false, .tail, 186, 242⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(1753 / 5000), (3509 / 10000), (32771893017163 / 100000000000000), (1638628192419 / 5000000000000), StaticNodes.Batch0002.node80, StaticNodes.Batch0002.node81, false, false, .tail, 186, 242⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(3509 / 10000), (439 / 1250), (1638628192419 / 5000000000000), (6554647444949 / 20000000000000), StaticNodes.Batch0002.node81, StaticNodes.Batch0002.node82, false, false, .tail, 186, 242⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(439 / 1250), (703 / 2000), (6554647444949 / 20000000000000), (16386956574071 / 50000000000000), StaticNodes.Batch0002.node82, StaticNodes.Batch0002.node83, false, false, .tail, 186, 242⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(703 / 2000), (1759 / 5000), (16386956574071 / 50000000000000), (51210299407 / 156250000000), StaticNodes.Batch0002.node83, StaticNodes.Batch0002.node84, false, false, .tail, 186, 242⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(1759 / 5000), (3521 / 10000), (51210299407 / 156250000000), (32775272643687 / 100000000000000), StaticNodes.Batch0002.node84, StaticNodes.Batch0002.node85, false, false, .tail, 186, 242⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(3521 / 10000), (881 / 2500), (32775272643687 / 100000000000000), (32775956219713 / 100000000000000), StaticNodes.Batch0002.node85, StaticNodes.Batch0002.node86, false, false, .tail, 186, 242⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(881 / 2500), (3527 / 10000), (32775956219713 / 100000000000000), (3277664235053 / 10000000000000), StaticNodes.Batch0002.node86, StaticNodes.Batch0002.node87, false, false, .tail, 186, 242⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(3527 / 10000), (353 / 1000), (3277664235053 / 10000000000000), (32777331038129 / 100000000000000), StaticNodes.Batch0002.node87, StaticNodes.Batch0002.node88, false, false, .tail, 186, 242⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(353 / 1000), (3533 / 10000), (32777331038129 / 100000000000000), (1311120891381 / 4000000000000), StaticNodes.Batch0002.node88, StaticNodes.Batch0002.node89, false, false, .tail, 186, 242⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (7167073 / 20480000) (3533 / 10000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch055

namespace OptimalG.Certificates.StaticSupportData.Batch056
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(3533 / 10000), (221 / 625), (1311120891381 / 4000000000000), (32778716091753 / 100000000000000), StaticNodes.Batch0002.node89, StaticNodes.Batch0002.node90, false, false, .tail, 186, 242⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(221 / 625), (3539 / 10000), (32778716091753 / 100000000000000), (32779412461871 / 100000000000000), StaticNodes.Batch0002.node90, StaticNodes.Batch0002.node91, false, false, .tail, 186, 242⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(3539 / 10000), (1771 / 5000), (32779412461871 / 100000000000000), (8195027849239 / 25000000000000), StaticNodes.Batch0002.node91, StaticNodes.Batch0002.node92, false, false, .tail, 186, 242⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(1771 / 5000), (709 / 2000), (8195027849239 / 25000000000000), (32780812899107 / 100000000000000), StaticNodes.Batch0002.node92, StaticNodes.Batch0002.node93, false, false, .tail, 186, 242⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(709 / 2000), (887 / 2500), (32780812899107 / 100000000000000), (2048844810653 / 6250000000000), StaticNodes.Batch0002.node93, StaticNodes.Batch0002.node94, false, false, .tail, 186, 242⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(887 / 2500), (3551 / 10000), (2048844810653 / 6250000000000), (32782223613119 / 100000000000000), StaticNodes.Batch0002.node94, StaticNodes.Batch0002.node95, false, false, .tail, 186, 242⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(3551 / 10000), (1777 / 5000), (32782223613119 / 100000000000000), (6556586565857 / 20000000000000), StaticNodes.Batch0002.node95, StaticNodes.Batch0002.node96, false, false, .tail, 186, 242⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(1777 / 5000), (3557 / 10000), (6556586565857 / 20000000000000), (8195911155283 / 25000000000000), StaticNodes.Batch0002.node96, StaticNodes.Batch0002.node97, false, false, .tail, 186, 242⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(3557 / 10000), (89 / 250), (8195911155283 / 25000000000000), (32784358990867 / 100000000000000), StaticNodes.Batch0002.node97, StaticNodes.Batch0002.node98, false, false, .tail, 186, 242⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(89 / 250), (3563 / 10000), (32784358990867 / 100000000000000), (409813449259 / 1250000000000), StaticNodes.Batch0002.node98, StaticNodes.Batch0002.node99, false, false, .tail, 186, 242⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(3563 / 10000), (1783 / 5000), (409813449259 / 1250000000000), (1639289773647 / 5000000000000), StaticNodes.Batch0002.node99, StaticNodes.Batch0002.node100, false, false, .tail, 186, 242⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(1783 / 5000), (3569 / 10000), (1639289773647 / 5000000000000), (32786517589801 / 100000000000000), StaticNodes.Batch0002.node100, StaticNodes.Batch0002.node101, false, false, .tail, 186, 242⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(3569 / 10000), (893 / 2500), (32786517589801 / 100000000000000), (8196810573399 / 25000000000000), StaticNodes.Batch0002.node101, StaticNodes.Batch0002.node102, false, false, .tail, 186, 242⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(893 / 2500), (143 / 400), (8196810573399 / 25000000000000), (32787969586641 / 100000000000000), StaticNodes.Batch0002.node102, StaticNodes.Batch0002.node103, false, false, .tail, 186, 242⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(143 / 400), (1789 / 5000), (32787969586641 / 100000000000000), (32788699471273 / 100000000000000), StaticNodes.Batch0002.node103, StaticNodes.Batch0002.node104, false, false, .tail, 186, 242⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(1789 / 5000), (3581 / 10000), (32788699471273 / 100000000000000), (8197357987463 / 25000000000000), StaticNodes.Batch0002.node104, StaticNodes.Batch0002.node105, false, false, .tail, 186, 242⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (3533 / 10000) (3581 / 10000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch056

namespace OptimalG.Certificates.StaticSupportData.Batch057
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(3581 / 10000), (224 / 625), (8197357987463 / 25000000000000), (16395083512379 / 50000000000000), StaticNodes.Batch0002.node105, StaticNodes.Batch0002.node106, false, false, .tail, 186, 242⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(224 / 625), (3587 / 10000), (16395083512379 / 50000000000000), (16395452349197 / 50000000000000), StaticNodes.Batch0002.node106, StaticNodes.Batch0002.node107, false, false, .tail, 186, 242⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(3587 / 10000), (359 / 1000), (16395452349197 / 50000000000000), (16395822486593 / 50000000000000), StaticNodes.Batch0002.node107, StaticNodes.Batch0002.node108, false, false, .tail, 186, 242⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(359 / 1000), (3593 / 10000), (16395822486593 / 50000000000000), (32792387851579 / 100000000000000), StaticNodes.Batch0002.node108, StaticNodes.Batch0002.node109, false, false, .tail, 186, 242⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(3593 / 10000), (899 / 2500), (32792387851579 / 100000000000000), (32793133336043 / 100000000000000), StaticNodes.Batch0002.node109, StaticNodes.Batch0002.node110, false, false, .tail, 186, 242⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(899 / 2500), (3599 / 10000), (32793133336043 / 100000000000000), (8198470357267 / 25000000000000), StaticNodes.Batch0002.node110, StaticNodes.Batch0002.node111, false, false, .tail, 186, 242⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(3599 / 10000), (9 / 25), (8198470357267 / 25000000000000), (32794131373523 / 100000000000000), StaticNodes.Batch0002.node111, StaticNodes.Batch0002.node112, false, false, .tail, 186, 242⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (3581 / 10000) (9 / 25) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch057
