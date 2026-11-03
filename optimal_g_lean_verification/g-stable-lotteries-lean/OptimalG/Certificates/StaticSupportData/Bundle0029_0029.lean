import OptimalG.Certificates.StaticLayerFast
import OptimalG.Certificates.StaticLayerGeometry
import OptimalG.Certificates.StaticSegmentData
import OptimalG.Certificates.SegmentMembership
import OptimalG.Certificates.StaticLayerCover

set_option Elab.async false

namespace OptimalG.Certificates.StaticSupportData.Batch029
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(5021108771667 / 16000000000000), (470442224312097 / 1499049727000000), (9993876030097467228303 / 32000000000000000000000), (624621082205859 / 2000000000000000), StaticNodes.Batch0001.node85, StaticNodes.Batch0001.node86, false, false, .piece 121, 100, 121⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(470442224312097 / 1499049727000000), (117640984419309 / 374762431750000), (624621082205859 / 2000000000000000), (156165413331893 / 500000000000000), StaticNodes.Batch0001.node85, StaticNodes.Batch0001.node86, false, false, .piece 121, 101, 121⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(117640984419309 / 374762431750000), (336173930314209 / 1070749805000000), (156165413331893 / 500000000000000), (3123440874575621 / 10000000000000000), StaticNodes.Batch0001.node85, StaticNodes.Batch0001.node86, false, false, .piece 121, 102, 121⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(336173930314209 / 1070749805000000), (11768407637030571 / 37476243175000000), (3123440874575621 / 10000000000000000), (15617977731555857 / 50000000000000000), StaticNodes.Batch0001.node85, StaticNodes.Batch0001.node86, false, false, .piece 121, 103, 121⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(11768407637030571 / 37476243175000000), (3140245409544793 / 10000000000000000), (15617977731555857 / 50000000000000000), (18741594246945925140921511 / 60000000000000000000000000), StaticNodes.Batch0001.node85, StaticNodes.Batch0001.node86, false, false, .piece 121, 104, 121⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(3140245409544793 / 10000000000000000), (11769281180668371 / 37476243175000000), (18741594246945925140921511 / 60000000000000000000000000), (15618268912768457 / 50000000000000000), StaticNodes.Batch0001.node85, StaticNodes.Batch0001.node86, false, false, .piece 122, 104, 122⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(11769281180668371 / 37476243175000000), (588507736215309 / 1873812158750000), (15618268912768457 / 50000000000000000), (780928004699053 / 2500000000000000), StaticNodes.Batch0001.node85, StaticNodes.Batch0001.node86, false, false, .piece 122, 105, 122⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(588507736215309 / 1873812158750000), (84078773342457 / 267687451250000), (780928004699053 / 2500000000000000), (780942563759683 / 2500000000000000), StaticNodes.Batch0001.node85, StaticNodes.Batch0001.node86, false, false, .piece 122, 106, 122⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(84078773342457 / 267687451250000), (3141 / 10000), (780942563759683 / 2500000000000000), (31237875692603 / 100000000000000), StaticNodes.Batch0001.node85, StaticNodes.Batch0001.node86, false, false, .piece 122, 107, 122⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(3141 / 10000), (2699654049809553 / 8594496287000000), (31237875692603 / 100000000000000), (3123828491281251 / 10000000000000000), StaticNodes.Batch0001.node86, StaticNodes.Batch0001.node87, false, false, .piece 122, 107, 122⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(2699654049809553 / 8594496287000000), (6284595673595419 / 20000000000000000), (3123828491281251 / 10000000000000000), (187449562662696092535709253 / 600000000000000000000000000), StaticNodes.Batch0001.node86, StaticNodes.Batch0001.node87, false, false, .piece 122, 108, 122⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(6284595673595419 / 20000000000000000), (393 / 1250), (187449562662696092535709253 / 600000000000000000000000000), (3124647018889 / 10000000000000), StaticNodes.Batch0001.node86, StaticNodes.Batch0001.node87, false, false, .piece 123, 108, 123⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(393 / 1250), (15721751320253133 / 50000000000000000), (3124647018889 / 10000000000000), (4882419070542161875190167 / 15625000000000000000000000), StaticNodes.Batch0001.node87, StaticNodes.Batch0001.node88, false, false, .piece 123, 108, 123⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(15721751320253133 / 50000000000000000), (3407143752466809 / 10833211880000000), (4882419070542161875190167 / 15625000000000000000000000), (3906202752742853 / 12500000000000000), StaticNodes.Batch0001.node87, StaticNodes.Batch0001.node88, false, false, .piece 124, 108, 124⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(3407143752466809 / 10833211880000000), (15732013456517713 / 50000000000000000), (3906202752742853 / 12500000000000000), (14650036509038876297550761 / 46875000000000000000000000), StaticNodes.Batch0001.node87, StaticNodes.Batch0001.node88, false, false, .piece 124, 109, 124⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(15732013456517713 / 50000000000000000), (3147 / 10000), (14650036509038876297550761 / 46875000000000000000000000), (15627568379197 / 50000000000000), StaticNodes.Batch0001.node87, StaticNodes.Batch0001.node88, false, false, .piece 125, 109, 125⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (5021108771667 / 16000000000000) (3147 / 10000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch029
