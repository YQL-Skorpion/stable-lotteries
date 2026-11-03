import OptimalG.Certificates.StaticLayerFast
import OptimalG.Certificates.StaticLayerGeometry
import OptimalG.Certificates.StaticSegmentData
import OptimalG.Certificates.SegmentMembership
import OptimalG.Certificates.StaticLayerCover

set_option Elab.async false

namespace OptimalG.Certificates.StaticSupportData.Batch035
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(4017679963101043 / 12500000000000000), (201 / 625), (29417279220539335937442457 / 93750000000000000000000000), (784534151433 / 2500000000000), StaticNodes.Batch0001.node110, StaticNodes.Batch0001.node111, false, false, .piece 162, 120, 162⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(201 / 625), (3216196750085467 / 10000000000000000), (784534151433 / 2500000000000), (94145031035857953461601413 / 300000000000000000000000000), StaticNodes.Batch0001.node111, StaticNodes.Batch0001.node112, false, false, .piece 162, 120, 162⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(3216196750085467 / 10000000000000000), (60999679903281 / 189654585560000), (94145031035857953461601413 / 300000000000000000000000000), (5021108771667 / 16000000000000), StaticNodes.Batch0001.node111, StaticNodes.Batch0001.node112, false, false, .piece 163, 120, 163⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(60999679903281 / 189654585560000), (8045623824225251 / 25000000000000000), (5021108771667 / 16000000000000), (235386910031217556662299389 / 750000000000000000000000000), StaticNodes.Batch0001.node111, StaticNodes.Batch0001.node112, false, false, .piece 163, 121, 163⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(8045623824225251 / 25000000000000000), (3219 / 10000), (235386910031217556662299389 / 750000000000000000000000000), (31386107421959 / 100000000000000), StaticNodes.Batch0001.node111, StaticNodes.Batch0001.node112, false, false, .piece 164, 121, 164⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(3219 / 10000), (3220302309294733 / 10000000000000000), (31386107421959 / 100000000000000), (23541123502203456202761053 / 75000000000000000000000000), StaticNodes.Batch0001.node112, StaticNodes.Batch0001.node113, false, false, .piece 164, 121, 164⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(3220302309294733 / 10000000000000000), (1611 / 5000), (23541123502203456202761053 / 75000000000000000000000000), (31390846498123 / 100000000000000), StaticNodes.Batch0001.node112, StaticNodes.Batch0001.node113, false, false, .piece 165, 121, 165⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(1611 / 5000), (3222355088899367 / 10000000000000000), (31390846498123 / 100000000000000), (23543555371877038660716587 / 75000000000000000000000000), StaticNodes.Batch0001.node113, StaticNodes.Batch0001.node114, false, false, .piece 165, 121, 165⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(3222355088899367 / 10000000000000000), (2015254917814999 / 6250000000000000), (23543555371877038660716587 / 75000000000000000000000000), (14716241428191017816509339 / 46875000000000000000000000), StaticNodes.Batch0001.node113, StaticNodes.Batch0001.node114, false, false, .piece 166, 121, 166⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(2015254917814999 / 6250000000000000), (129 / 400), (14716241428191017816509339 / 46875000000000000000000000), (31395583320767 / 100000000000000), StaticNodes.Batch0001.node113, StaticNodes.Batch0001.node114, false, false, .piece 167, 121, 167⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(129 / 400), (3226460648108633 / 10000000000000000), (31395583320767 / 100000000000000), (9419366555356972158259813 / 30000000000000000000000000), StaticNodes.Batch0001.node114, StaticNodes.Batch0001.node115, false, false, .piece 167, 121, 167⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(3226460648108633 / 10000000000000000), (807 / 2500), (9419366555356972158259813 / 30000000000000000000000000), (31400317925377 / 100000000000000), StaticNodes.Batch0001.node114, StaticNodes.Batch0001.node115, false, false, .piece 168, 121, 168⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(807 / 2500), (16142567138566327 / 50000000000000000), (31400317925377 / 100000000000000), (471016917779279016857132483 / 1500000000000000000000000000), StaticNodes.Batch0001.node115, StaticNodes.Batch0001.node116, false, false, .piece 168, 121, 168⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(16142567138566327 / 50000000000000000), (1528281207982479 / 4732467029000000), (471016917779279016857132483 / 1500000000000000000000000000), (3140245409544793 / 10000000000000000), StaticNodes.Batch0001.node115, StaticNodes.Batch0001.node116, false, false, .piece 169, 121, 169⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(1528281207982479 / 4732467029000000), (3230566207317899 / 10000000000000000), (3140245409544793 / 10000000000000000), (94213098267652535539052071 / 300000000000000000000000000), StaticNodes.Batch0001.node115, StaticNodes.Batch0001.node116, false, false, .piece 169, 122, 169⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(3230566207317899 / 10000000000000000), (3231 / 10000), (94213098267652535539052071 / 300000000000000000000000000), (15702525196203 / 50000000000000), StaticNodes.Batch0001.node115, StaticNodes.Batch0001.node116, false, false, .piece 170, 122, 170⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (4017679963101043 / 12500000000000000) (3231 / 10000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch035

namespace OptimalG.Certificates.StaticSupportData.Batch036
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(3231 / 10000), (808154746730633 / 2500000000000000), (15702525196203 / 50000000000000), (23555702466947194874786017 / 75000000000000000000000000), StaticNodes.Batch0001.node116, StaticNodes.Batch0001.node117, false, false, .piece 170, 122, 170⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(808154746730633 / 2500000000000000), (1617 / 5000), (23555702466947194874786017 / 75000000000000000000000000), (6281956187491 / 20000000000000), StaticNodes.Batch0001.node116, StaticNodes.Batch0001.node117, false, false, .piece 171, 122, 171⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(1617 / 5000), (16173358832635823 / 50000000000000000), (6281956187491 / 20000000000000), (78527099481042122008090121 / 250000000000000000000000000), StaticNodes.Batch0001.node117, StaticNodes.Batch0001.node118, false, false, .piece 171, 122, 171⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(16173358832635823 / 50000000000000000), (1618362273065899 / 5000000000000000), (78527099481042122008090121 / 250000000000000000000000000), (7853518858559725085236973 / 25000000000000000000000000), StaticNodes.Batch0001.node117, StaticNodes.Batch0001.node118, false, false, .piece 172, 122, 172⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(1618362273065899 / 5000000000000000), (3237 / 10000), (7853518858559725085236973 / 25000000000000000000000000), (31414509611417 / 100000000000000), StaticNodes.Batch0001.node117, StaticNodes.Batch0001.node118, false, false, .piece 173, 122, 173⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(3237 / 10000), (8096943314341079 / 25000000000000000), (31414509611417 / 100000000000000), (235629824901419282066202419 / 750000000000000000000000000), StaticNodes.Batch0001.node118, StaticNodes.Batch0001.node119, false, false, .piece 173, 122, 173⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(8096943314341079 / 25000000000000000), (81 / 250), (235629824901419282066202419 / 750000000000000000000000000), (15709618223439 / 50000000000000), StaticNodes.Batch0001.node118, StaticNodes.Batch0001.node119, false, false, .piece 174, 122, 174⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(81 / 250), (405103763167633 / 1250000000000000), (15709618223439 / 50000000000000), (1472837994043836087887039 / 4687500000000000000000000), StaticNodes.Batch0001.node119, StaticNodes.Batch0001.node120, false, false, .piece 174, 122, 174⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(405103763167633 / 1250000000000000), (3064068910931457 / 9450073328000000), (1472837994043836087887039 / 4687500000000000000000000), (6284595673595419 / 20000000000000000), StaticNodes.Batch0001.node119, StaticNodes.Batch0001.node120, false, false, .piece 175, 122, 175⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(3064068910931457 / 9450073328000000), (8107207212364241 / 25000000000000000), (6284595673595419 / 20000000000000000), (29459790961781409105941503 / 93750000000000000000000000), StaticNodes.Batch0001.node119, StaticNodes.Batch0001.node120, false, false, .piece 175, 123, 175⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(8107207212364241 / 25000000000000000), (3243 / 10000), (29459790961781409105941503 / 93750000000000000000000000), (15711980741771 / 50000000000000), StaticNodes.Batch0001.node119, StaticNodes.Batch0001.node120, false, false, .piece 176, 123, 176⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(3243 / 10000), (324493566455033 / 1000000000000000), (15711980741771 / 50000000000000), (1885620548881272490152433 / 6000000000000000000000000), StaticNodes.Batch0001.node120, StaticNodes.Batch0001.node121, false, false, .piece 176, 123, 176⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(324493566455033 / 1000000000000000), (1623 / 5000), (1885620548881272490152433 / 6000000000000000000000000), (31428684922547 / 100000000000000), StaticNodes.Batch0001.node120, StaticNodes.Batch0001.node121, false, false, .piece 177, 123, 177⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(1623 / 5000), (32469884441549623 / 100000000000000000), (31428684922547 / 100000000000000), (314302407140747279477914977 / 1000000000000000000000000000), StaticNodes.Batch0001.node121, StaticNodes.Batch0001.node122, false, false, .piece 177, 123, 177⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(32469884441549623 / 100000000000000000), (3249 / 10000), (314302407140747279477914977 / 1000000000000000000000000000), (3929175857893 / 12500000000000), StaticNodes.Batch0001.node121, StaticNodes.Batch0001.node122, false, false, .piece 178, 123, 178⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(3249 / 10000), (812678656031829 / 2500000000000000), (3929175857893 / 12500000000000), (982378275258269172108259 / 3125000000000000000000000), StaticNodes.Batch0001.node122, StaticNodes.Batch0001.node123, false, false, .piece 178, 123, 178⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (3231 / 10000) (812678656031829 / 2500000000000000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch036

namespace OptimalG.Certificates.StaticSupportData.Batch037
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(812678656031829 / 2500000000000000), (813 / 2500), (982378275258269172108259 / 3125000000000000000000000), (1964882958453 / 6250000000000), StaticNodes.Batch0001.node122, StaticNodes.Batch0001.node123, false, false, .piece 179, 123, 179⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(813 / 2500), (813610201024917 / 2500000000000000), (1964882958453 / 6250000000000), (1965122921695695248245173 / 6250000000000000000000000), StaticNodes.Batch0001.node123, StaticNodes.Batch0001.node124, false, false, .piece 179, 123, 179⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(813610201024917 / 2500000000000000), (651 / 2000), (1965122921695695248245173 / 6250000000000000000000000), (7860711592119 / 25000000000000), StaticNodes.Batch0001.node123, StaticNodes.Batch0001.node124, false, false, .piece 180, 123, 180⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(651 / 2000), (7679067072727899 / 23588579615000000), (7860711592119 / 25000000000000), (15721751320253133 / 50000000000000000), StaticNodes.Batch0001.node124, StaticNodes.Batch0001.node125, false, false, .piece 180, 123, 180⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(7679067072727899 / 23588579615000000), (1629 / 5000), (15721751320253133 / 50000000000000000), (31447564084399 / 100000000000000), StaticNodes.Batch0001.node124, StaticNodes.Batch0001.node125, false, false, .piece 180, 124, 180⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(1629 / 5000), (162908349203601 / 500000000000000), (31447564084399 / 100000000000000), (62895653229865457714363 / 200000000000000000000000), StaticNodes.Batch0001.node125, StaticNodes.Batch0001.node126, false, false, .piece 180, 124, 180⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(162908349203601 / 500000000000000), (3261 / 10000), (62895653229865457714363 / 200000000000000000000000), (3931535081453 / 12500000000000), StaticNodes.Batch0001.node125, StaticNodes.Batch0001.node126, false, false, .piece 181, 124, 181⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(3261 / 10000), (32618931640443727 / 100000000000000000), (3931535081453 / 12500000000000), (314536845409961206997029959 / 1000000000000000000000000000), StaticNodes.Batch0001.node126, StaticNodes.Batch0001.node127, false, false, .piece 181, 124, 181⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(32618931640443727 / 100000000000000000), (204 / 625), (314536845409961206997029959 / 1000000000000000000000000000), (1258279843963 / 4000000000000), StaticNodes.Batch0001.node126, StaticNodes.Batch0001.node127, false, false, .piece 182, 124, 182⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(204 / 625), (32656255525088657 / 100000000000000000), (1258279843963 / 4000000000000), (943786517287432814841890807 / 3000000000000000000000000000), StaticNodes.Batch0001.node127, StaticNodes.Batch0002.node0, false, false, .piece 182, 124, 182⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(32656255525088657 / 100000000000000000), (3267 / 10000), (943786517287432814841890807 / 3000000000000000000000000000), (15730855227013 / 50000000000000), StaticNodes.Batch0001.node127, StaticNodes.Batch0002.node0, false, false, .piece 183, 124, 183⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(3267 / 10000), (7702677927972639 / 23566584755000000), (15730855227013 / 50000000000000), (15732013456517713 / 50000000000000000), StaticNodes.Batch0002.node0, StaticNodes.Batch0002.node1, false, false, .piece 183, 124, 183⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(7702677927972639 / 23566584755000000), (1634678970486679 / 5000000000000000), (15732013456517713 / 50000000000000000), (47198122542618592850395729 / 150000000000000000000000000), StaticNodes.Batch0002.node0, StaticNodes.Batch0002.node1, false, false, .piece 183, 125, 183⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(1634678970486679 / 5000000000000000), (327 / 1000), (47198122542618592850395729 / 150000000000000000000000000), (31466423770977 / 100000000000000), StaticNodes.Batch0002.node0, StaticNodes.Batch0002.node1, false, false, .piece 184, 125, 184⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(327 / 1000), (3273 / 10000), (31466423770977 / 100000000000000), (15735568128069 / 50000000000000), StaticNodes.Batch0002.node1, StaticNodes.Batch0002.node2, false, false, .piece 184, 125, 184⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(3273 / 10000), (6546208990435033 / 20000000000000000), (15735568128069 / 50000000000000), (94413901119690896378788249 / 300000000000000000000000000), StaticNodes.Batch0002.node2, StaticNodes.Batch0002.node3, false, false, .piece 184, 125, 184⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (812678656031829 / 2500000000000000) (6546208990435033 / 20000000000000000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch037

namespace OptimalG.Certificates.StaticSupportData.Batch038
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(6546208990435033 / 20000000000000000), (819 / 2500), (94413901119690896378788249 / 300000000000000000000000000), (7868961991811 / 25000000000000), StaticNodes.Batch0002.node2, StaticNodes.Batch0002.node3, false, false, .piece 185, 125, 185⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(819 / 2500), (65540915566487 / 200000000000000), (7868961991761 / 25000000000000), (944324697995274210300707 / 3000000000000000000000000), StaticNodes.Batch0002.node3, StaticNodes.Batch0002.node4, false, false, .piece 185, 125, 185⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(65540915566487 / 200000000000000), (1311 / 4000), (944324697995274210300707 / 3000000000000000000000000), (6295640620421 / 20000000000000), StaticNodes.Batch0002.node3, StaticNodes.Batch0002.node4, false, false, .piece 186, 125, 186⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(1311 / 4000), (13113 / 40000), (6295640620421 / 20000000000000), (15739689090901 / 50000000000000), StaticNodes.Batch0002.node3, StaticNodes.Batch0002.node4, false, false, .piece 186, 125, 186⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(13113 / 40000), (3279 / 10000), (15739689090901 / 50000000000000), (7870137709583 / 25000000000000), StaticNodes.Batch0002.node3, StaticNodes.Batch0002.node4, false, false, .piece 186, 125, 186⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(3279 / 10000), (13119 / 40000), (7870137709583 / 25000000000000), (7870430270017 / 25000000000000), StaticNodes.Batch0002.node4, StaticNodes.Batch0002.node5, false, false, .piece 186, 125, 186⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(13119 / 40000), (6561 / 20000), (7870430270017 / 25000000000000), (3935361114421 / 12500000000000), StaticNodes.Batch0002.node4, StaticNodes.Batch0002.node5, false, false, .piece 186, 125, 186⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(6561 / 20000), (3280555791071671 / 10000000000000000), (3935361114421 / 12500000000000), (5903057926879032521318629 / 18750000000000000000000000), StaticNodes.Batch0002.node4, StaticNodes.Batch0002.node5, false, false, .piece 186, 125, 186⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(3280555791071671 / 10000000000000000), (21 / 64), (5903057926879032521318629 / 18750000000000000000000000), (7871013588141 / 25000000000000), StaticNodes.Batch0002.node4, StaticNodes.Batch0002.node5, false, false, .piece 187, 125, 187⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(21 / 64), (3053324092425351 / 9304460168000000), (7871013588141 / 25000000000000), (6296910237112917 / 20000000000000000), StaticNodes.Batch0002.node4, StaticNodes.Batch0002.node5, false, false, .piece 187, 125, 187⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(3053324092425351 / 9304460168000000), (1641 / 5000), (6296910237112917 / 20000000000000000), (6297043482017 / 20000000000000), StaticNodes.Batch0002.node4, StaticNodes.Batch0002.node5, false, false, .piece 187, 126, 187⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(1641 / 5000), (13131 / 40000), (6297043482017 / 20000000000000), (31486378100411 / 100000000000000), StaticNodes.Batch0002.node5, StaticNodes.Batch0002.node6, false, false, .piece 187, 126, 187⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(13131 / 40000), (5070935522948067 / 15444339520000000), (31486378100411 / 100000000000000), (31487323067431067 / 100000000000000000), StaticNodes.Batch0002.node5, StaticNodes.Batch0002.node6, false, false, .piece 187, 126, 187⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(5070935522948067 / 15444339520000000), (6567 / 20000), (31487323067431067 / 100000000000000000), (251900291407 / 800000000000), StaticNodes.Batch0002.node5, StaticNodes.Batch0002.node6, false, false, .piece 187, 127, 187⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(6567 / 20000), (13137 / 40000), (251900291407 / 800000000000), (15744346196993 / 50000000000000), StaticNodes.Batch0002.node5, StaticNodes.Batch0002.node6, false, false, .piece 187, 127, 187⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(13137 / 40000), (256582849505143 / 781250000000000), (15744346196993 / 50000000000000), (1845041513914401782782931 / 5859375000000000000000000), StaticNodes.Batch0002.node5, StaticNodes.Batch0002.node6, false, false, .piece 187, 127, 187⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (6546208990435033 / 20000000000000000) (256582849505143 / 781250000000000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch038
