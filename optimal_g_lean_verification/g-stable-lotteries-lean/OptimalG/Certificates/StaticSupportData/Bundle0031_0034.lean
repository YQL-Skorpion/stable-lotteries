import OptimalG.Certificates.StaticLayerFast
import OptimalG.Certificates.StaticLayerGeometry
import OptimalG.Certificates.StaticSegmentData
import OptimalG.Certificates.SegmentMembership
import OptimalG.Certificates.StaticLayerCover

set_option Elab.async false

namespace OptimalG.Certificates.StaticSupportData.Batch031
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(14210913037689081 / 45006209200000000), (3158718921155741 / 10000000000000000), (15643123060768027 / 50000000000000000), (1173366315039208963067543 / 3750000000000000000000000), StaticNodes.Batch0001.node91, StaticNodes.Batch0001.node92, false, false, .piece 134, 113, 134⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(3158718921155741 / 10000000000000000), (3159 / 10000), (1173366315039208963067543 / 3750000000000000000000000), (3129061175393 / 10000000000000), StaticNodes.Batch0001.node91, StaticNodes.Batch0001.node92, false, false, .piece 135, 113, 135⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(3159 / 10000), (202179 / 640000), (3129061175373 / 10000000000000), (6258150618859 / 20000000000000), StaticNodes.Batch0001.node92, StaticNodes.Batch0001.node93, false, false, .piece 135, 113, 135⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(202179 / 640000), (808719 / 2560000), (6258150618859 / 20000000000000), (31290788432803 / 100000000000000), StaticNodes.Batch0001.node92, StaticNodes.Batch0001.node93, false, false, .piece 135, 113, 135⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(808719 / 2560000), (3234879 / 10240000), (31290788432803 / 100000000000000), (782269931691 / 2500000000000), StaticNodes.Batch0001.node92, StaticNodes.Batch0001.node93, false, false, .piece 135, 113, 135⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(3234879 / 10240000), (93782648382417 / 296868520000000), (782269931691 / 2500000000000), (3911350260878823 / 12500000000000000), StaticNodes.Batch0001.node92, StaticNodes.Batch0001.node93, false, false, .piece 135, 113, 135⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(93782648382417 / 296868520000000), (1617441 / 5120000), (3911350260878823 / 12500000000000000), (31290804689353 / 100000000000000), StaticNodes.Batch0001.node92, StaticNodes.Batch0001.node93, false, false, .piece 135, 114, 135⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(1617441 / 5120000), (404361 / 1280000), (31290804689353 / 100000000000000), (31290814078359 / 100000000000000), StaticNodes.Batch0001.node92, StaticNodes.Batch0001.node93, false, false, .piece 135, 114, 135⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(404361 / 1280000), (101091 / 320000), (31290814078359 / 100000000000000), (15645425817109 / 50000000000000), StaticNodes.Batch0001.node92, StaticNodes.Batch0001.node93, false, false, .piece 135, 114, 135⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(101091 / 320000), (50547 / 160000), (15645425817109 / 50000000000000), (31291001854993 / 100000000000000), StaticNodes.Batch0001.node92, StaticNodes.Batch0001.node93, false, false, .piece 135, 114, 135⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(50547 / 160000), (1011 / 3200), (31291001854993 / 100000000000000), (6258260456757 / 20000000000000), StaticNodes.Batch0001.node92, StaticNodes.Batch0001.node93, false, false, .piece 135, 114, 135⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(1011 / 3200), (12639 / 40000), (6258260456757 / 20000000000000), (15645951545193 / 50000000000000), StaticNodes.Batch0001.node92, StaticNodes.Batch0001.node93, false, false, .piece 135, 114, 135⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(12639 / 40000), (6321 / 20000), (15645951545193 / 50000000000000), (15646552250013 / 50000000000000), StaticNodes.Batch0001.node92, StaticNodes.Batch0001.node93, false, false, .piece 135, 114, 135⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(6321 / 20000), (1580385850380187 / 5000000000000000), (15646552250013 / 50000000000000), (7823384896208274833501887 / 25000000000000000000000000), StaticNodes.Batch0001.node92, StaticNodes.Batch0001.node93, false, false, .piece 135, 114, 135⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(1580385850380187 / 5000000000000000), (253167530370049 / 800669101000000), (7823384896208274833501887 / 25000000000000000000000000), (1564771286000299 / 5000000000000000), StaticNodes.Batch0001.node92, StaticNodes.Batch0001.node93, false, false, .piece 136, 114, 136⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(253167530370049 / 800669101000000), (1581 / 5000), (1564771286000299 / 5000000000000000), (31295506507329 / 100000000000000), StaticNodes.Batch0001.node92, StaticNodes.Batch0001.node93, false, false, .piece 136, 115, 136⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (14210913037689081 / 45006209200000000) (1581 / 5000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch031

namespace OptimalG.Certificates.StaticSupportData.Batch032
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(1581 / 5000), (15814122401825037 / 50000000000000000), (31295506507529 / 100000000000000), (78242064721546071730109943 / 250000000000000000000000000), StaticNodes.Batch0001.node93, StaticNodes.Batch0001.node94, false, false, .piece 136, 115, 136⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(15814122401825037 / 50000000000000000), (3164877259969641 / 10000000000000000), (78242064721546071730109943 / 250000000000000000000000000), (15650055432539418694231499 / 50000000000000000000000000), StaticNodes.Batch0001.node93, StaticNodes.Batch0001.node94, false, false, .piece 137, 115, 137⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(3164877259969641 / 10000000000000000), (633 / 2000), (15650055432539418694231499 / 50000000000000000000000000), (31300307280763 / 100000000000000), StaticNodes.Batch0001.node93, StaticNodes.Batch0001.node94, false, false, .piece 138, 115, 138⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(633 / 2000), (56245296888937 / 177651063000000), (31300307280763 / 100000000000000), (3130199347121233 / 10000000000000000), StaticNodes.Batch0001.node94, StaticNodes.Batch0001.node95, false, false, .piece 138, 115, 138⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(56245296888937 / 177651063000000), (1583465019787137 / 5000000000000000), (3130199347121233 / 10000000000000000), (15651696571500508295989679 / 50000000000000000000000000), StaticNodes.Batch0001.node94, StaticNodes.Batch0001.node95, false, false, .piece 138, 116, 138⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(1583465019787137 / 5000000000000000), (198 / 625), (15651696571500508295989679 / 50000000000000000000000000), (3913137982433 / 12500000000000), StaticNodes.Batch0001.node94, StaticNodes.Batch0001.node95, false, false, .piece 139, 116, 139⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(198 / 625), (15844914095894533 / 50000000000000000), (3913137982433 / 12500000000000), (9783335598596326451082299 / 31250000000000000000000000), StaticNodes.Batch0001.node95, StaticNodes.Batch0001.node96, false, false, .piece 139, 116, 139⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(15844914095894533 / 50000000000000000), (3171 / 10000), (9783335598596326451082299 / 31250000000000000000000000), (3913737045851 / 12500000000000), StaticNodes.Batch0001.node95, StaticNodes.Batch0001.node96, false, false, .piece 140, 116, 140⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(3171 / 10000), (3171035598783539 / 10000000000000000), (3913737045851 / 12500000000000), (18785971913263106469440147 / 60000000000000000000000000), StaticNodes.Batch0001.node96, StaticNodes.Batch0001.node97, false, false, .piece 140, 116, 140⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(3171035598783539 / 10000000000000000), (4746334241502 / 14964160515625), (18785971913263106469440147 / 60000000000000000000000000), (156555876191359 / 500000000000000), StaticNodes.Batch0001.node96, StaticNodes.Batch0001.node97, false, false, .piece 141, 116, 141⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(4746334241502 / 14964160515625), (3173088378388173 / 10000000000000000), (156555876191359 / 500000000000000), (6262645957722516970369743 / 20000000000000000000000000), StaticNodes.Batch0001.node96, StaticNodes.Batch0001.node97, false, false, .piece 141, 117, 141⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(3173088378388173 / 10000000000000000), (1587 / 5000), (6262645957722516970369743 / 20000000000000000000000000), (31314684898173 / 100000000000000), StaticNodes.Batch0001.node96, StaticNodes.Batch0001.node97, false, false, .piece 142, 117, 142⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(1587 / 5000), (635028231598561 / 2000000000000000), (31314684898173 / 100000000000000), (3757980589660506301567267 / 12000000000000000000000000), StaticNodes.Batch0001.node97, StaticNodes.Batch0001.node98, false, false, .piece 142, 117, 142⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(635028231598561 / 2000000000000000), (3177 / 10000), (3757980589660506301567267 / 12000000000000000000000000), (7829867388227 / 25000000000000), StaticNodes.Batch0001.node97, StaticNodes.Batch0001.node98, false, false, .piece 143, 117, 143⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(3177 / 10000), (1588596968798719 / 5000000000000000), (7829867388227 / 25000000000000), (5872458490414491414883123 / 18750000000000000000000000), StaticNodes.Batch0001.node98, StaticNodes.Batch0001.node99, false, false, .piece 143, 117, 143⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(1588596968798719 / 5000000000000000), (3038288968588347 / 9561713872000000), (5872458490414491414883123 / 18750000000000000000000000), (6264071401066249 / 20000000000000000), StaticNodes.Batch0001.node98, StaticNodes.Batch0001.node99, false, false, .piece 144, 117, 144⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (1581 / 5000) (3038288968588347 / 9561713872000000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch032

namespace OptimalG.Certificates.StaticSupportData.Batch033
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(3038288968588347 / 9561713872000000), (3179246717202071 / 10000000000000000), (6264071401066249 / 20000000000000000), (11746143736530343956739307 / 37500000000000000000000000), StaticNodes.Batch0001.node98, StaticNodes.Batch0001.node99, false, false, .piece 144, 118, 144⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(3179246717202071 / 10000000000000000), (159 / 500), (11746143736530343956739307 / 37500000000000000000000000), (7831062602461 / 25000000000000), StaticNodes.Batch0001.node98, StaticNodes.Batch0001.node99, false, false, .piece 145, 118, 145⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(159 / 500), (636259899361341 / 2000000000000000), (7831062602461 / 25000000000000), (1566315987980502003630687 / 5000000000000000000000000), StaticNodes.Batch0001.node99, StaticNodes.Batch0001.node100, false, false, .piece 145, 118, 145⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(636259899361341 / 2000000000000000), (3183 / 10000), (1566315987980502003630687 / 5000000000000000000000000), (3916128460191 / 12500000000000), StaticNodes.Batch0001.node99, StaticNodes.Batch0001.node100, false, false, .piece 146, 118, 146⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(3183 / 10000), (3183352276411337 / 10000000000000000), (3916128460191 / 12500000000000), (31329588240870477984853493 / 100000000000000000000000000), StaticNodes.Batch0001.node100, StaticNodes.Batch0001.node101, false, false, .piece 146, 118, 146⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(3183352276411337 / 10000000000000000), (31854050560159697 / 100000000000000000), (31329588240870477984853493 / 100000000000000000000000000), (313328547235198777465917533 / 1000000000000000000000000000), StaticNodes.Batch0001.node100, StaticNodes.Batch0001.node101, false, false, .piece 147, 118, 147⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(31854050560159697 / 100000000000000000), (1593 / 5000), (313328547235198777465917533 / 1000000000000000000000000000), (6266760285459 / 20000000000000), StaticNodes.Batch0001.node100, StaticNodes.Batch0001.node101, false, false, .piece 148, 118, 148⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(1593 / 5000), (6374915671241207 / 20000000000000000), (6266760285459 / 20000000000000), (94008358546095627585224639 / 300000000000000000000000000), StaticNodes.Batch0001.node101, StaticNodes.Batch0001.node102, false, false, .piece 148, 118, 148⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(6374915671241207 / 20000000000000000), (3189 / 10000), (94008358546095627585224639 / 300000000000000000000000000), (31338571693649 / 100000000000000), StaticNodes.Batch0001.node101, StaticNodes.Batch0001.node102, false, false, .piece 149, 118, 149⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(3189 / 10000), (31895106152252367 / 100000000000000000), (31338571693649 / 100000000000000), (313393830384322083897513743 / 1000000000000000000000000000), StaticNodes.Batch0001.node102, StaticNodes.Batch0001.node103, false, false, .piece 149, 118, 149⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(31895106152252367 / 100000000000000000), (158421504012263 / 496548540312500), (313393830384322083897513743 / 1000000000000000000000000000), (489701269966569 / 1562500000000000), StaticNodes.Batch0001.node102, StaticNodes.Batch0001.node103, false, false, .piece 150, 118, 150⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(158421504012263 / 496548540312500), (6383126789659741 / 20000000000000000), (489701269966569 / 1562500000000000), (62685289627048507558709789 / 200000000000000000000000000), StaticNodes.Batch0001.node102, StaticNodes.Batch0001.node103, false, false, .piece 150, 119, 150⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(6383126789659741 / 20000000000000000), (399 / 1250), (62685289627048507558709789 / 200000000000000000000000000), (7835834639909 / 25000000000000), StaticNodes.Batch0001.node102, StaticNodes.Batch0001.node103, false, false, .piece 151, 119, 151⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(399 / 1250), (399202021804313 / 1250000000000000), (7835834639909 / 25000000000000), (11754714331670689902985519 / 37500000000000000000000000), StaticNodes.Batch0001.node103, StaticNodes.Batch0001.node104, false, false, .piece 151, 119, 151⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(399202021804313 / 1250000000000000), (639 / 2000), (11754714331670689902985519 / 37500000000000000000000000), (31348102262299 / 100000000000000), StaticNodes.Batch0001.node103, StaticNodes.Batch0001.node104, false, false, .piece 152, 119, 152⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(639 / 2000), (7989172385097841 / 25000000000000000), (31348102262299 / 100000000000000), (235118728546321497840747023 / 750000000000000000000000000), StaticNodes.Batch0001.node104, StaticNodes.Batch0001.node105, false, false, .piece 152, 119, 152⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (3038288968588347 / 9561713872000000) (7989172385097841 / 25000000000000000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch033

namespace OptimalG.Certificates.StaticSupportData.Batch034
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(7989172385097841 / 25000000000000000), (399715216705471 / 1250000000000000), (235118728546321497840747023 / 750000000000000000000000000), (11757157988604136416574913 / 37500000000000000000000000), StaticNodes.Batch0001.node104, StaticNodes.Batch0001.node105, false, false, .piece 153, 119, 153⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(399715216705471 / 1250000000000000), (1599 / 5000), (11757157988604136416574913 / 37500000000000000000000000), (15676431437901 / 50000000000000), StaticNodes.Batch0001.node104, StaticNodes.Batch0001.node105, false, false, .piece 154, 119, 154⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(1599 / 5000), (31997745132484023 / 100000000000000000), (15676431437901 / 50000000000000), (313556769976410929775310333 / 1000000000000000000000000000), StaticNodes.Batch0001.node105, StaticNodes.Batch0001.node106, false, false, .piece 154, 119, 154⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(31997745132484023 / 100000000000000000), (3201 / 10000), (313556769976410929775310333 / 1000000000000000000000000000), (6271524088543 / 20000000000000), StaticNodes.Batch0001.node105, StaticNodes.Batch0001.node106, false, false, .piece 155, 119, 155⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(3201 / 10000), (640365458570607 / 2000000000000000), (6271524088543 / 20000000000000), (6271786316266292810436139 / 20000000000000000000000000), StaticNodes.Batch0001.node106, StaticNodes.Batch0001.node107, false, false, .piece 155, 119, 155⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(640365458570607 / 2000000000000000), (507690364835159 / 1584854277000000), (6271786316266292810436139 / 20000000000000000000000000), (3136140555038959 / 10000000000000000), StaticNodes.Batch0001.node106, StaticNodes.Batch0001.node107, false, false, .piece 156, 119, 156⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(507690364835159 / 1584854277000000), (3203880072457669 / 10000000000000000), (3136140555038959 / 10000000000000000), (31362184937867606616100313 / 100000000000000000000000000), StaticNodes.Batch0001.node106, StaticNodes.Batch0001.node107, false, false, .piece 156, 120, 156⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(3203880072457669 / 10000000000000000), (801 / 2500), (31362184937867606616100313 / 100000000000000000000000000), (15681187502773 / 50000000000000), StaticNodes.Batch0001.node106, StaticNodes.Batch0001.node107, false, false, .piece 157, 120, 157⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(801 / 2500), (3205932852062301 / 10000000000000000), (15681187502773 / 50000000000000), (31365436480040669400528813 / 100000000000000000000000000), StaticNodes.Batch0001.node107, StaticNodes.Batch0001.node108, false, false, .piece 157, 120, 157⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(3205932852062301 / 10000000000000000), (3207 / 10000), (31365436480040669400528813 / 100000000000000000000000000), (6273425350457 / 20000000000000), StaticNodes.Batch0001.node107, StaticNodes.Batch0001.node108, false, false, .piece 158, 120, 158⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(3207 / 10000), (641597126333387 / 2000000000000000), (6273425350457 / 20000000000000), (3136868702853691358747179 / 10000000000000000000000000), StaticNodes.Batch0001.node108, StaticNodes.Batch0001.node109, false, false, .piece 158, 120, 158⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(641597126333387 / 2000000000000000), (321 / 1000), (3136868702853691358747179 / 10000000000000000000000000), (31371875817187 / 100000000000000), StaticNodes.Batch0001.node108, StaticNodes.Batch0001.node109, false, false, .piece 159, 120, 159⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(321 / 1000), (200627400704473 / 625000000000000), (31371875817187 / 100000000000000), (5882238110479417542118801 / 18750000000000000000000000), StaticNodes.Batch0001.node109, StaticNodes.Batch0001.node110, false, false, .piece 159, 120, 159⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(200627400704473 / 625000000000000), (3212091190876201 / 10000000000000000), (5882238110479417542118801 / 18750000000000000000000000), (94125553126228492852861537 / 300000000000000000000000000), StaticNodes.Batch0001.node109, StaticNodes.Batch0001.node110, false, false, .piece 160, 120, 160⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(3212091190876201 / 10000000000000000), (3213 / 10000), (94125553126228492852861537 / 300000000000000000000000000), (7844155559831 / 25000000000000), StaticNodes.Batch0001.node109, StaticNodes.Batch0001.node110, false, false, .piece 161, 120, 161⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(3213 / 10000), (4017679963101043 / 12500000000000000), (7844155559831 / 25000000000000), (29417279220539335937442457 / 93750000000000000000000000), StaticNodes.Batch0001.node110, StaticNodes.Batch0001.node111, false, false, .piece 161, 120, 161⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (7989172385097841 / 25000000000000000) (4017679963101043 / 12500000000000000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch034
