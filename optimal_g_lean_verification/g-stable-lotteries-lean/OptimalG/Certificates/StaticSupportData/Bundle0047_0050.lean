import OptimalG.Certificates.StaticLayerFast
import OptimalG.Certificates.StaticLayerGeometry
import OptimalG.Certificates.StaticSegmentData
import OptimalG.Certificates.SegmentMembership
import OptimalG.Certificates.StaticLayerCover

set_option Elab.async false

namespace OptimalG.Certificates.StaticSupportData.Batch047
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(6237153750323703 / 18418811494000000), (3387 / 10000), (3212091190876201 / 10000000000000000), (32125237584409 / 100000000000000), StaticNodes.Batch0002.node39, StaticNodes.Batch0002.node40, false, false, .piece 215, 161, 215⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(3387 / 10000), (6777 / 20000), (32125237584409 / 100000000000000), (251050338903 / 781250000000), StaticNodes.Batch0002.node40, StaticNodes.Batch0002.node41, false, false, .piece 215, 161, 215⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(6777 / 20000), (16942747398991703 / 50000000000000000), (251050338903 / 781250000000), (48202120390850085489504193 / 150000000000000000000000000), StaticNodes.Batch0002.node40, StaticNodes.Batch0002.node41, false, false, .piece 215, 161, 215⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(16942747398991703 / 50000000000000000), (974751395923563 / 2875677860937500), (48202120390850085489504193 / 150000000000000000000000000), (4017679963101043 / 12500000000000000), StaticNodes.Batch0002.node40, StaticNodes.Batch0002.node41, false, false, .piece 216, 161, 216⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(974751395923563 / 2875677860937500), (339 / 1000), (4017679963101043 / 12500000000000000), (32143645548739 / 100000000000000), StaticNodes.Batch0002.node40, StaticNodes.Batch0002.node41, false, false, .piece 216, 162, 216⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(339 / 1000), (6783 / 20000), (32143645548739 / 100000000000000), (32152844154561 / 100000000000000), StaticNodes.Batch0002.node41, StaticNodes.Batch0002.node42, false, false, .piece 216, 162, 216⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(6783 / 20000), (3392274530489541 / 10000000000000000), (32152844154561 / 100000000000000), (8039398015976188902262679 / 25000000000000000000000000), StaticNodes.Batch0002.node41, StaticNodes.Batch0002.node42, false, false, .piece 216, 162, 216⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(3392274530489541 / 10000000000000000), (6239754690134301 / 18390145028000000), (8039398015976188902262679 / 25000000000000000000000000), (3216196750085467 / 10000000000000000), StaticNodes.Batch0002.node41, StaticNodes.Batch0002.node42, false, false, .piece 217, 162, 217⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(6239754690134301 / 18390145028000000), (3393 / 10000), (3216196750085467 / 10000000000000000), (1286481569083 / 4000000000000), StaticNodes.Batch0002.node41, StaticNodes.Batch0002.node42, false, false, .piece 217, 163, 217⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(3393 / 10000), (6789 / 20000), (1286481569083 / 4000000000000), (3217123071739 / 10000000000000), StaticNodes.Batch0002.node42, StaticNodes.Batch0002.node43, false, false, .piece 217, 163, 217⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(6789 / 20000), (16979997905903707 / 50000000000000000), (3217123071739 / 10000000000000), (241353121575564074074510063 / 750000000000000000000000000), StaticNodes.Batch0002.node42, StaticNodes.Batch0002.node43, false, false, .piece 217, 163, 217⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(16979997905903707 / 50000000000000000), (849 / 2500), (241353121575564074074510063 / 750000000000000000000000000), (32180418775499 / 100000000000000), StaticNodes.Batch0002.node42, StaticNodes.Batch0002.node43, false, false, .piece 218, 163, 218⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(849 / 2500), (1732982899242167 / 5102502520000000), (32180418775499 / 100000000000000), (8045623824225251 / 25000000000000000), StaticNodes.Batch0002.node43, StaticNodes.Batch0002.node44, false, false, .piece 218, 163, 218⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(1732982899242167 / 5102502520000000), (1359 / 4000), (8045623824225251 / 25000000000000000), (6437920656007 / 20000000000000), StaticNodes.Batch0002.node43, StaticNodes.Batch0002.node44, false, false, .piece 218, 164, 218⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(1359 / 4000), (3399 / 10000), (6437920656007 / 20000000000000), (32198784393337 / 100000000000000), StaticNodes.Batch0002.node43, StaticNodes.Batch0002.node44, false, false, .piece 218, 164, 218⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(3399 / 10000), (6240284284529499 / 18355435936000000), (32198784393337 / 100000000000000), (3220302309294733 / 10000000000000000), StaticNodes.Batch0002.node44, StaticNodes.Batch0002.node45, false, false, .piece 218, 164, 218⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (6237153750323703 / 18418811494000000) (6240284284529499 / 18355435936000000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch047

namespace OptimalG.Certificates.StaticSupportData.Batch048
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(6240284284529499 / 18355435936000000), (6799449263743883 / 20000000000000000), (3220302309294733 / 10000000000000000), (6038103382119600372449359 / 18750000000000000000000000), StaticNodes.Batch0002.node44, StaticNodes.Batch0002.node45, false, false, .piece 218, 165, 218⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(6799449263743883 / 20000000000000000), (6801 / 20000), (6038103382119600372449359 / 18750000000000000000000000), (6441592422261 / 20000000000000), StaticNodes.Batch0002.node44, StaticNodes.Batch0002.node45, false, false, .piece 219, 165, 219⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(6801 / 20000), (1701 / 5000), (6441592422261 / 20000000000000), (6443427282601 / 20000000000000), StaticNodes.Batch0002.node44, StaticNodes.Batch0002.node45, false, false, .piece 219, 165, 219⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(1701 / 5000), (6241887274779801 / 18342042716000000), (6443427282601 / 20000000000000), (3222355088899367 / 10000000000000000), StaticNodes.Batch0002.node45, StaticNodes.Batch0002.node46, false, false, .piece 219, 165, 219⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(6241887274779801 / 18342042716000000), (1701724841281571 / 5000000000000000), (3222355088899367 / 10000000000000000), (12084749922314098866396709 / 37500000000000000000000000), StaticNodes.Batch0002.node45, StaticNodes.Batch0002.node46, false, false, .piece 219, 166, 219⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(1701724841281571 / 5000000000000000), (6807 / 20000), (12084749922314098866396709 / 37500000000000000000000000), (32226307434363 / 100000000000000), StaticNodes.Batch0002.node45, StaticNodes.Batch0002.node46, false, false, .piece 220, 166, 220⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(6807 / 20000), (681 / 2000), (32226307434363 / 100000000000000), (1611773753153 / 5000000000000), StaticNodes.Batch0002.node45, StaticNodes.Batch0002.node46, false, false, .piece 220, 166, 220⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(681 / 2000), (975550764722343 / 2863869221562500), (1611773753153 / 5000000000000), (2015254917814999 / 6250000000000000), StaticNodes.Batch0002.node46, StaticNodes.Batch0002.node47, false, false, .piece 220, 166, 220⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(975550764722343 / 2863869221562500), (6813 / 20000), (2015254917814999 / 6250000000000000), (32244639444569 / 100000000000000), StaticNodes.Batch0002.node46, StaticNodes.Batch0002.node47, false, false, .piece 220, 167, 220⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(6813 / 20000), (17035873666271717 / 50000000000000000), (32244639444569 / 100000000000000), (8062190074943074199361853 / 25000000000000000000000000), StaticNodes.Batch0002.node46, StaticNodes.Batch0002.node47, false, false, .piece 220, 167, 220⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(17035873666271717 / 50000000000000000), (213 / 625), (8062190074943074199361853 / 25000000000000000000000000), (32253800520839 / 100000000000000), StaticNodes.Batch0002.node46, StaticNodes.Batch0002.node47, false, false, .piece 221, 167, 221⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(213 / 625), (6819 / 20000), (32253800520839 / 100000000000000), (32262958337927 / 100000000000000), StaticNodes.Batch0002.node47, StaticNodes.Batch0002.node48, false, false, .piece 221, 167, 221⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(6819 / 20000), (2081012342649633 / 6103087046000000), (32262958337927 / 100000000000000), (3226460648108633 / 10000000000000000), StaticNodes.Batch0002.node47, StaticNodes.Batch0002.node48, false, false, .piece 221, 167, 221⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(2081012342649633 / 6103087046000000), (17054498919727723 / 50000000000000000), (3226460648108633 / 10000000000000000), (80678753352980630044188129 / 250000000000000000000000000), StaticNodes.Batch0002.node47, StaticNodes.Batch0002.node48, false, false, .piece 221, 168, 221⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(17054498919727723 / 50000000000000000), (3411 / 10000), (80678753352980630044188129 / 250000000000000000000000000), (2017007060531 / 6250000000000), StaticNodes.Batch0002.node47, StaticNodes.Batch0002.node48, false, false, .piece 222, 168, 222⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(3411 / 10000), (273 / 800), (2017007060531 / 6250000000000), (1614063217021 / 5000000000000), StaticNodes.Batch0002.node48, StaticNodes.Batch0002.node49, false, false, .piece 222, 168, 222⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (6240284284529499 / 18355435936000000) (273 / 800) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch048

namespace OptimalG.Certificates.StaticSupportData.Batch049
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(273 / 800), (31224202491581481 / 91482483770000000), (1614063217021 / 5000000000000), (16142567138566327 / 50000000000000000), StaticNodes.Batch0002.node48, StaticNodes.Batch0002.node49, false, false, .piece 222, 168, 222⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(31224202491581481 / 91482483770000000), (1707 / 5000), (16142567138566327 / 50000000000000000), (32290412588797 / 100000000000000), StaticNodes.Batch0002.node48, StaticNodes.Batch0002.node49, false, false, .piece 222, 169, 222⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(1707 / 5000), (34146248346367447 / 100000000000000000), (32290412588797 / 100000000000000), (484413330253463751057013903 / 1500000000000000000000000000), StaticNodes.Batch0002.node49, StaticNodes.Batch0002.node50, false, false, .piece 222, 169, 222⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(34146248346367447 / 100000000000000000), (6831 / 20000), (484413330253463751057013903 / 1500000000000000000000000000), (16149778817923 / 50000000000000), StaticNodes.Batch0002.node49, StaticNodes.Batch0002.node50, false, false, .piece 223, 169, 223⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(6831 / 20000), (2082226686765999 / 6094616434000000), (16149778817923 / 50000000000000), (3230566207317899 / 10000000000000000), StaticNodes.Batch0002.node49, StaticNodes.Batch0002.node50, false, false, .piece 223, 169, 223⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(2082226686765999 / 6094616434000000), (3417 / 10000), (3230566207317899 / 10000000000000000), (32308699560497 / 100000000000000), StaticNodes.Batch0002.node49, StaticNodes.Batch0002.node50, false, false, .piece 223, 170, 223⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(3417 / 10000), (683669977065589 / 2000000000000000), (32308699560497 / 100000000000000), (9695077148348423102945243 / 30000000000000000000000000), StaticNodes.Batch0002.node50, StaticNodes.Batch0002.node51, false, false, .piece 223, 170, 223⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(683669977065589 / 2000000000000000), (6837 / 20000), (9695077148348423102945243 / 30000000000000000000000000), (504966225181 / 1562500000000), StaticNodes.Batch0002.node50, StaticNodes.Batch0002.node51, false, false, .piece 224, 170, 224⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(6837 / 20000), (390536433065931 / 1141962390625000), (504966225181 / 1562500000000), (808154746730633 / 2500000000000000), StaticNodes.Batch0002.node50, StaticNodes.Batch0002.node51, false, false, .piece 224, 170, 224⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(390536433065931 / 1141962390625000), (171 / 500), (808154746730633 / 2500000000000000), (32326974110709 / 100000000000000), StaticNodes.Batch0002.node50, StaticNodes.Batch0002.node51, false, false, .piece 224, 171, 224⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(171 / 500), (6843 / 20000), (32326974110709 / 100000000000000), (32336106879799 / 100000000000000), StaticNodes.Batch0002.node51, StaticNodes.Batch0002.node52, false, false, .piece 224, 171, 224⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(6843 / 20000), (6844149872038291 / 20000000000000000), (32336106879799 / 100000000000000), (97018818605296655416445879 / 300000000000000000000000000), StaticNodes.Batch0002.node51, StaticNodes.Batch0002.node52, false, false, .piece 224, 171, 224⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(6844149872038291 / 20000000000000000), (3423 / 10000), (97018818605296655416445879 / 300000000000000000000000000), (8086309140417 / 25000000000000), StaticNodes.Batch0002.node51, StaticNodes.Batch0002.node52, false, false, .piece 225, 171, 225⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(3423 / 10000), (10414345720789823 / 30422451560000000), (8086309140417 / 25000000000000), (16173358832635823 / 50000000000000000), StaticNodes.Batch0002.node52, StaticNodes.Batch0002.node53, false, false, .piece 225, 171, 225⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(10414345720789823 / 30422451560000000), (6849 / 20000), (16173358832635823 / 50000000000000000), (2022147706071 / 6250000000000), StaticNodes.Batch0002.node52, StaticNodes.Batch0002.node53, false, false, .piece 225, 172, 225⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(6849 / 20000), (685159997342069 / 2000000000000000), (2022147706071 / 6250000000000), (3236227046638747258538277 / 10000000000000000000000000), StaticNodes.Batch0002.node52, StaticNodes.Batch0002.node53, false, false, .piece 225, 172, 225⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (273 / 800) (685159997342069 / 2000000000000000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch049

namespace OptimalG.Certificates.StaticSupportData.Batch050
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(685159997342069 / 2000000000000000), (1713 / 5000), (3236227046638747258538277 / 10000000000000000000000000), (6472697409447 / 20000000000000), StaticNodes.Batch0002.node52, StaticNodes.Batch0002.node53, false, false, .piece 226, 172, 226⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(1713 / 5000), (1041784116419749 / 3040269106000000), (6472697409447 / 20000000000000), (1618362273065899 / 5000000000000000), StaticNodes.Batch0002.node53, StaticNodes.Batch0002.node54, false, false, .piece 226, 172, 226⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(1041784116419749 / 3040269106000000), (1371 / 4000), (1618362273065899 / 5000000000000000), (32372607854553 / 100000000000000), StaticNodes.Batch0002.node53, StaticNodes.Batch0002.node54, false, false, .piece 226, 173, 226⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(1371 / 4000), (3429 / 10000), (32372607854553 / 100000000000000), (8095431434857 / 25000000000000), StaticNodes.Batch0002.node53, StaticNodes.Batch0002.node54, false, false, .piece 226, 173, 226⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(3429 / 10000), (3429525037401547 / 10000000000000000), (8095431434857 / 25000000000000), (9715474865162105915243989 / 30000000000000000000000000), StaticNodes.Batch0002.node54, StaticNodes.Batch0002.node55, false, false, .piece 226, 173, 226⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(3429525037401547 / 10000000000000000), (15632205598759737 / 45575007175000000), (9715474865162105915243989 / 30000000000000000000000000), (8096943314341079 / 25000000000000000), StaticNodes.Batch0002.node54, StaticNodes.Batch0002.node55, false, false, .piece 227, 173, 227⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(15632205598759737 / 45575007175000000), (6861 / 20000), (8096943314341079 / 25000000000000000), (32390840740863 / 100000000000000), StaticNodes.Batch0002.node54, StaticNodes.Batch0002.node55, false, false, .piece 227, 174, 227⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(6861 / 20000), (429 / 1250), (32390840740863 / 100000000000000), (6479990565581 / 20000000000000), StaticNodes.Batch0002.node54, StaticNodes.Batch0002.node55, false, false, .piece 227, 174, 227⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(429 / 1250), (34332500880927463 / 100000000000000000), (6479990565581 / 20000000000000), (162037722299369825995982011 / 500000000000000000000000000), StaticNodes.Batch0002.node55, StaticNodes.Batch0002.node56, false, false, .piece 227, 174, 227⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(34332500880927463 / 100000000000000000), (521261603202841 / 1518219398500000), (162037722299369825995982011 / 500000000000000000000000000), (405103763167633 / 1250000000000000), StaticNodes.Batch0002.node55, StaticNodes.Batch0002.node56, false, false, .piece 228, 174, 228⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(521261603202841 / 1518219398500000), (6867 / 20000), (405103763167633 / 1250000000000000), (4051132768037 / 12500000000000), StaticNodes.Batch0002.node55, StaticNodes.Batch0002.node56, false, false, .piece 228, 175, 228⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(6867 / 20000), (687 / 2000), (4051132768037 / 12500000000000), (16209084255639 / 50000000000000), StaticNodes.Batch0002.node55, StaticNodes.Batch0002.node56, false, false, .piece 228, 175, 228⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(687 / 2000), (6873 / 20000), (16209084255639 / 50000000000000), (32427272194899 / 100000000000000), StaticNodes.Batch0002.node56, StaticNodes.Batch0002.node57, false, false, .piece 228, 175, 228⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(6873 / 20000), (5212907385010991 / 15168101910000000), (32427272194899 / 100000000000000), (8107207212364241 / 25000000000000000), StaticNodes.Batch0002.node56, StaticNodes.Batch0002.node57, false, false, .piece 228, 175, 228⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(5212907385010991 / 15168101910000000), (859243784695987 / 2500000000000000), (8107207212364241 / 25000000000000000), (2026884686018595418403517 / 6250000000000000000000000), StaticNodes.Batch0002.node56, StaticNodes.Batch0002.node57, false, false, .piece 228, 176, 228⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(859243784695987 / 2500000000000000), (1719 / 5000), (2026884686018595418403517 / 6250000000000000000000000), (6487274611209 / 20000000000000), StaticNodes.Batch0002.node56, StaticNodes.Batch0002.node57, false, false, .piece 229, 176, 229⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (685159997342069 / 2000000000000000) (1719 / 5000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch050
