import OptimalG.Certificates.StaticLayerFast
import OptimalG.Certificates.StaticLayerGeometry
import OptimalG.Certificates.StaticSegmentData
import OptimalG.Certificates.SegmentMembership
import OptimalG.Certificates.StaticLayerCover
namespace OptimalG.Certificates.StaticSupportData.Batch030
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(3147 / 10000), (6296910237112917 / 20000000000000000), (15627568379197 / 50000000000000), (15629687465074813603443097 / 50000000000000000000000000), StaticNodes.Batch0001.node88, StaticNodes.Batch0001.node89, false, false, .piece 125, 109, 125⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(6296910237112917 / 20000000000000000), (31487323067431067 / 100000000000000000), (15629687465074813603443097 / 50000000000000000000000000), (234451367004104795593436741 / 750000000000000000000000000), StaticNodes.Batch0001.node88, StaticNodes.Batch0001.node89, false, false, .piece 126, 109, 126⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(31487323067431067 / 100000000000000000), (550305624167229 / 1747557298400000), (234451367004104795593436741 / 750000000000000000000000000), (625219182621463 / 2000000000000000), StaticNodes.Batch0001.node88, StaticNodes.Batch0001.node89, false, false, .piece 127, 109, 127⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(550305624167229 / 1747557298400000), (15745054784278503 / 50000000000000000), (625219182621463 / 2000000000000000), (39076242327846556456615123 / 125000000000000000000000000), StaticNodes.Batch0001.node88, StaticNodes.Batch0001.node89, false, false, .piece 127, 110, 127⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(15745054784278503 / 50000000000000000), (629838393647379 / 2000000000000000), (39076242327846556456615123 / 125000000000000000000000000), (1563076053760553903117039 / 5000000000000000000000000), StaticNodes.Batch0001.node88, StaticNodes.Batch0001.node89, false, false, .piece 128, 110, 128⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(629838393647379 / 2000000000000000), (1574687220897507 / 5000000000000000), (1563076053760553903117039 / 5000000000000000000000000), (3907756568359354731756287 / 12500000000000000000000000), StaticNodes.Batch0001.node88, StaticNodes.Batch0001.node89, false, false, .piece 129, 110, 129⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(1574687220897507 / 5000000000000000), (63 / 200), (3907756568359354731756287 / 12500000000000000000000000), (15631937272443 / 50000000000000), StaticNodes.Batch0001.node88, StaticNodes.Batch0001.node89, false, false, .piece 130, 110, 130⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(63 / 200), (3938996708417547 / 12500000000000000), (15631937272443 / 50000000000000), (39084245139881615357527401 / 125000000000000000000000000), StaticNodes.Batch0001.node89, StaticNodes.Batch0001.node90, false, false, .piece 130, 110, 130⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(3938996708417547 / 12500000000000000), (231821622669187 / 735273270750000), (39084245139881615357527401 / 125000000000000000000000000), (781807406005087 / 2500000000000000), StaticNodes.Batch0001.node89, StaticNodes.Batch0001.node90, false, false, .piece 131, 110, 131⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(231821622669187 / 735273270750000), (3153 / 10000), (781807406005087 / 2500000000000000), (6254539564827 / 20000000000000), StaticNodes.Batch0001.node89, StaticNodes.Batch0001.node90, false, false, .piece 131, 111, 131⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(3153 / 10000), (6306040583346123 / 20000000000000000), (6254539564827 / 20000000000000), (12509103243434010937203231 / 40000000000000000000000000), StaticNodes.Batch0001.node90, StaticNodes.Batch0001.node91, false, false, .piece 131, 111, 131⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(6306040583346123 / 20000000000000000), (788710804153021 / 2500000000000000), (12509103243434010937203231 / 40000000000000000000000000), (1563908691448366282904137 / 5000000000000000000000000), StaticNodes.Batch0001.node90, StaticNodes.Batch0001.node91, false, false, .piece 132, 111, 132⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(788710804153021 / 2500000000000000), (789 / 2500), (1563908691448366282904137 / 5000000000000000000000000), (3128161051209 / 10000000000000), StaticNodes.Batch0001.node90, StaticNodes.Batch0001.node91, false, false, .piece 133, 111, 133⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(789 / 2500), (789166535387777 / 2500000000000000), (3128161051209 / 10000000000000), (293283836367097486962371 / 937500000000000000000000), StaticNodes.Batch0001.node91, StaticNodes.Batch0001.node92, false, false, .piece 133, 111, 133⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(789166535387777 / 2500000000000000), (5682797551754277 / 18002483680000000), (293283836367097486962371 / 937500000000000000000000), (6256726669866759 / 20000000000000000), StaticNodes.Batch0001.node91, StaticNodes.Batch0001.node92, false, false, .piece 134, 111, 134⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(5682797551754277 / 18002483680000000), (14210913037689081 / 45006209200000000), (6256726669866759 / 20000000000000000), (15643123060768027 / 50000000000000000), StaticNodes.Batch0001.node91, StaticNodes.Batch0001.node92, false, false, .piece 134, 112, 134⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (3147 / 10000) (14210913037689081 / 45006209200000000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch030
