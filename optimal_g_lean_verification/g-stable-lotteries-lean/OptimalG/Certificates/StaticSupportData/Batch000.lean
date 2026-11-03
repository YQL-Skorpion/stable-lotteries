import OptimalG.Certificates.StaticLayerFast
import OptimalG.Certificates.StaticLayerGeometry
import OptimalG.Certificates.StaticSegmentData
import OptimalG.Certificates.SegmentMembership
import OptimalG.Certificates.StaticLayerCover
namespace OptimalG.Certificates.StaticSupportData.Batch000
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(1 / 4), (2503 / 10000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node0, StaticNodes.Batch0000.node1, true, true, .cap, 0, 0⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(2503 / 10000), (1253 / 5000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node1, StaticNodes.Batch0000.node2, true, true, .cap, 0, 0⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(1253 / 5000), (2509 / 10000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node2, StaticNodes.Batch0000.node3, true, true, .cap, 0, 0⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(2509 / 10000), (157 / 625), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node3, StaticNodes.Batch0000.node4, true, true, .cap, 0, 0⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(157 / 625), (503 / 2000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node4, StaticNodes.Batch0000.node5, true, true, .cap, 0, 0⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(503 / 2000), (1259 / 5000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node5, StaticNodes.Batch0000.node6, true, true, .cap, 0, 0⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(1259 / 5000), (2521 / 10000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node6, StaticNodes.Batch0000.node7, true, true, .cap, 0, 0⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(2521 / 10000), (631 / 2500), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node7, StaticNodes.Batch0000.node8, true, true, .cap, 0, 0⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(631 / 2500), (2527 / 10000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node8, StaticNodes.Batch0000.node9, true, true, .cap, 0, 0⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(2527 / 10000), (253 / 1000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node9, StaticNodes.Batch0000.node10, true, true, .cap, 0, 0⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(253 / 1000), (2533 / 10000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node10, StaticNodes.Batch0000.node11, true, true, .cap, 0, 0⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(2533 / 10000), (317 / 1250), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node11, StaticNodes.Batch0000.node12, true, true, .cap, 0, 0⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(317 / 1250), (2539 / 10000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node12, StaticNodes.Batch0000.node13, true, true, .cap, 0, 0⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(2539 / 10000), (1271 / 5000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node13, StaticNodes.Batch0000.node14, true, true, .cap, 0, 0⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(1271 / 5000), (509 / 2000), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node14, StaticNodes.Batch0000.node15, true, true, .cap, 0, 0⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(509 / 2000), (637 / 2500), (2950935005377889 / 10000000000000000), (2950935005377889 / 10000000000000000), StaticNodes.Batch0000.node15, StaticNodes.Batch0000.node16, true, true, .cap, 0, 0⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (1 / 4) (637 / 2500) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch000
