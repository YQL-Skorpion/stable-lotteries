import OptimalG.Certificates.StaticLayerFast
import OptimalG.Certificates.StaticLayerGeometry
import OptimalG.Certificates.StaticSegmentData
import OptimalG.Certificates.SegmentMembership
import OptimalG.Certificates.StaticLayerCover

set_option Elab.async false

namespace OptimalG.Certificates.StaticSupportData.Batch039
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(256582849505143 / 781250000000000), (657 / 2000), (1845041513914401782782931 / 5859375000000000000000000), (31489846012503 / 100000000000000), StaticNodes.Batch0002.node5, StaticNodes.Batch0002.node6, false, false, .piece 188, 127, 188⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(657 / 2000), (9977683712552003 / 30373065250000000), (31489846012703 / 100000000000000), (15745054784278503 / 50000000000000000), StaticNodes.Batch0002.node6, StaticNodes.Batch0002.node7, false, false, .piece 188, 127, 188⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(9977683712552003 / 30373065250000000), (399143550778319 / 1214922610000000), (15745054784278503 / 50000000000000000), (629838393647379 / 2000000000000000), StaticNodes.Batch0002.node6, StaticNodes.Batch0002.node7, false, false, .piece 188, 128, 188⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(399143550778319 / 1214922610000000), (997950113724857 / 3037306525000000), (629838393647379 / 2000000000000000), (1574687220897507 / 5000000000000000), StaticNodes.Batch0002.node6, StaticNodes.Batch0002.node7, false, false, .piece 188, 129, 188⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(997950113724857 / 3037306525000000), (3287979317746479 / 10000000000000000), (1574687220897507 / 5000000000000000), (630158884303317158499019 / 2000000000000000000000000), StaticNodes.Batch0002.node6, StaticNodes.Batch0002.node7, false, false, .piece 188, 130, 188⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(3287979317746479 / 10000000000000000), (411 / 1250), (630158884303317158499019 / 2000000000000000000000000), (31508069851853 / 100000000000000), StaticNodes.Batch0002.node6, StaticNodes.Batch0002.node7, false, false, .piece 189, 130, 189⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(411 / 1250), (3912509953441383 / 11897135000000000), (31508069851653 / 100000000000000), (3938996708417547 / 12500000000000000), StaticNodes.Batch0002.node7, StaticNodes.Batch0002.node8, false, false, .piece 189, 130, 189⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(3912509953441383 / 11897135000000000), (6579 / 20000), (3938996708417547 / 12500000000000000), (31517587559653 / 100000000000000), StaticNodes.Batch0002.node7, StaticNodes.Batch0002.node8, false, false, .piece 189, 131, 189⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(6579 / 20000), (3291 / 10000), (31517587559653 / 100000000000000), (31527099333367 / 100000000000000), StaticNodes.Batch0002.node7, StaticNodes.Batch0002.node8, false, false, .piece 189, 131, 189⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(3291 / 10000), (12515256025889769 / 38023074676000000), (31527099333367 / 100000000000000), (6306040583346123 / 20000000000000000), StaticNodes.Batch0002.node8, StaticNodes.Batch0002.node9, false, false, .piece 189, 131, 189⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(12515256025889769 / 38023074676000000), (411462270228391 / 1250000000000000), (6306040583346123 / 20000000000000000), (5912160695609088142081579 / 18750000000000000000000000), StaticNodes.Batch0002.node8, StaticNodes.Batch0002.node9, false, false, .piece 189, 132, 189⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(411462270228391 / 1250000000000000), (1317 / 4000), (5912160695609088142081579 / 18750000000000000000000000), (7884151275509 / 25000000000000), StaticNodes.Batch0002.node8, StaticNodes.Batch0002.node9, false, false, .piece 190, 132, 190⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(1317 / 4000), (1647 / 5000), (7884151275509 / 25000000000000), (985815781349 / 3125000000000), StaticNodes.Batch0002.node8, StaticNodes.Batch0002.node9, false, false, .piece 190, 132, 190⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(1647 / 5000), (1563854694518763 / 4747055729500000), (985815781349 / 3125000000000), (788710804153021 / 2500000000000000), StaticNodes.Batch0002.node9, StaticNodes.Batch0002.node10, false, false, .piece 190, 132, 190⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(1563854694518763 / 4747055729500000), (411927901564791 / 1250000000000000), (788710804153021 / 2500000000000000), (1972194568459618754680023 / 6250000000000000000000000), StaticNodes.Batch0002.node9, StaticNodes.Batch0002.node10, false, false, .piece 190, 133, 190⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(411927901564791 / 1250000000000000), (6591 / 20000), (1972194568459618754680023 / 6250000000000000000000000), (31555599114627 / 100000000000000), StaticNodes.Batch0002.node9, StaticNodes.Batch0002.node10, false, false, .piece 191, 133, 191⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (256582849505143 / 781250000000000) (6591 / 20000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch039

namespace OptimalG.Certificates.StaticSupportData.Batch040
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(6591 / 20000), (3297 / 10000), (31555599114627 / 100000000000000), (986408977627 / 3125000000000), StaticNodes.Batch0002.node9, StaticNodes.Batch0002.node10, false, false, .piece 191, 133, 191⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(3297 / 10000), (1563310473141381 / 4741256940500000), (986408977627 / 3125000000000), (789166535387777 / 2500000000000000), StaticNodes.Batch0002.node10, StaticNodes.Batch0002.node11, false, false, .piece 191, 133, 191⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(1563310473141381 / 4741256940500000), (6597 / 20000), (789166535387777 / 2500000000000000), (6314913959589 / 20000000000000), StaticNodes.Batch0002.node10, StaticNodes.Batch0002.node11, false, false, .piece 191, 134, 191⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(6597 / 20000), (32991482632095287 / 100000000000000000), (6314913959589 / 20000000000000), (157893326787003323346586609 / 500000000000000000000000000), StaticNodes.Batch0002.node10, StaticNodes.Batch0002.node11, false, false, .piece 191, 134, 191⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(32991482632095287 / 100000000000000000), (33 / 100), (157893326787003323346586609 / 500000000000000000000000000), (15792023205183 / 50000000000000), StaticNodes.Batch0002.node10, StaticNodes.Batch0002.node11, false, false, .piece 192, 134, 192⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(33 / 100), (6251813284197423 / 18942031648000000), (15792023205183 / 50000000000000), (3158718921155741 / 10000000000000000), StaticNodes.Batch0002.node11, StaticNodes.Batch0002.node12, false, false, .piece 192, 134, 192⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(6251813284197423 / 18942031648000000), (6603 / 20000), (3158718921155741 / 10000000000000000), (3159351742619 / 10000000000000), StaticNodes.Batch0002.node11, StaticNodes.Batch0002.node12, false, false, .piece 192, 135, 192⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(6603 / 20000), (330287331390073 / 1000000000000000), (3159351742619 / 10000000000000), (4740327507318126880095599 / 15000000000000000000000000), StaticNodes.Batch0002.node11, StaticNodes.Batch0002.node12, false, false, .piece 192, 135, 192⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(330287331390073 / 1000000000000000), (3303 / 10000), (4740327507318126880095599 / 15000000000000000000000000), (31602982803253 / 100000000000000), StaticNodes.Batch0002.node11, StaticNodes.Batch0002.node12, false, false, .piece 193, 135, 193⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(3303 / 10000), (3125271651008811 / 9459768454000000), (31602982803253 / 100000000000000), (1580385850380187 / 5000000000000000), StaticNodes.Batch0002.node12, StaticNodes.Batch0002.node13, false, false, .piece 193, 135, 193⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(3125271651008811 / 9459768454000000), (6609 / 20000), (1580385850380187 / 5000000000000000), (31612442571707 / 100000000000000), StaticNodes.Batch0002.node12, StaticNodes.Batch0002.node13, false, false, .piece 193, 136, 193⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(6609 / 20000), (1653 / 5000), (31612442571707 / 100000000000000), (7905474201727 / 25000000000000), StaticNodes.Batch0002.node12, StaticNodes.Batch0002.node13, false, false, .piece 193, 136, 193⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(1653 / 5000), (16532991822959653 / 50000000000000000), (7905474201727 / 25000000000000), (29649061866833646379341323 / 93750000000000000000000000), StaticNodes.Batch0002.node13, StaticNodes.Batch0002.node14, false, false, .piece 193, 136, 193⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(16532991822959653 / 50000000000000000), (31246974208281111 / 94487151280000000), (29649061866833646379341323 / 93750000000000000000000000), (15814122401825037 / 50000000000000000), StaticNodes.Batch0002.node13, StaticNodes.Batch0002.node14, false, false, .piece 194, 136, 194⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(31246974208281111 / 94487151280000000), (1323 / 4000), (15814122401825037 / 50000000000000000), (7907836380509 / 25000000000000), StaticNodes.Batch0002.node13, StaticNodes.Batch0002.node14, false, false, .piece 194, 137, 194⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(1323 / 4000), (3309 / 10000), (7907836380509 / 25000000000000), (31640788710049 / 100000000000000), StaticNodes.Batch0002.node13, StaticNodes.Batch0002.node14, false, false, .piece 194, 137, 194⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (6591 / 20000) (3309 / 10000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch040

namespace OptimalG.Certificates.StaticSupportData.Batch041
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(3309 / 10000), (2082791370903941 / 6291909888000000), (31640788710049 / 100000000000000), (3164877259969641 / 10000000000000000), StaticNodes.Batch0002.node14, StaticNodes.Batch0002.node15, false, false, .piece 194, 137, 194⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(2082791370903941 / 6291909888000000), (33103234152831307 / 100000000000000000), (3164877259969641 / 10000000000000000), (1236293574990424233239311 / 3906250000000000000000000), StaticNodes.Batch0002.node14, StaticNodes.Batch0002.node15, false, false, .piece 194, 138, 194⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(33103234152831307 / 100000000000000000), (6621 / 20000), (1236293574990424233239311 / 3906250000000000000000000), (31650226574881 / 100000000000000), StaticNodes.Batch0002.node14, StaticNodes.Batch0002.node15, false, false, .piece 195, 138, 195⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(6621 / 20000), (207 / 625), (31650226574881 / 100000000000000), (49468217023 / 156250000000), StaticNodes.Batch0002.node14, StaticNodes.Batch0002.node15, false, false, .piece 195, 138, 195⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(207 / 625), (6627 / 20000), (49468217023 / 156250000000), (31669086048779 / 100000000000000), StaticNodes.Batch0002.node15, StaticNodes.Batch0002.node16, false, false, .piece 195, 138, 195⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(6627 / 20000), (3121930806154011 / 9421755407000000), (31669086048779 / 100000000000000), (1583465019787137 / 5000000000000000), StaticNodes.Batch0002.node15, StaticNodes.Batch0002.node16, false, false, .piece 195, 138, 195⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(3121930806154011 / 9421755407000000), (3314048465974331 / 10000000000000000), (1583465019787137 / 5000000000000000), (47508796585427708622457717 / 150000000000000000000000000), StaticNodes.Batch0002.node15, StaticNodes.Batch0002.node16, false, false, .piece 195, 139, 195⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(3314048465974331 / 10000000000000000), (663 / 2000), (47508796585427708622457717 / 150000000000000000000000000), (15839253902093 / 50000000000000), StaticNodes.Batch0002.node15, StaticNodes.Batch0002.node16, false, false, .piece 196, 139, 196⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(663 / 2000), (6633 / 20000), (15839253902093 / 50000000000000), (15843962171529 / 50000000000000), StaticNodes.Batch0002.node16, StaticNodes.Batch0002.node17, false, false, .piece 196, 139, 196⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(6633 / 20000), (31215567838098099 / 94113408910000000), (15843962171529 / 50000000000000), (15844914095894533 / 50000000000000000), StaticNodes.Batch0002.node16, StaticNodes.Batch0002.node17, false, false, .piece 196, 139, 196⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(31215567838098099 / 94113408910000000), (16588867583327657 / 50000000000000000), (15844914095894533 / 50000000000000000), (237719360070283428175322387 / 750000000000000000000000000), StaticNodes.Batch0002.node16, StaticNodes.Batch0002.node17, false, false, .piece 196, 140, 196⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(16588867583327657 / 50000000000000000), (1659 / 5000), (237719360070283428175322387 / 750000000000000000000000000), (31697335683949 / 100000000000000), StaticNodes.Batch0002.node16, StaticNodes.Batch0002.node17, false, false, .piece 197, 140, 197⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(1659 / 5000), (6639 / 20000), (31697335683949 / 100000000000000), (31706741774153 / 100000000000000), StaticNodes.Batch0002.node17, StaticNodes.Batch0002.node18, false, false, .piece 197, 140, 197⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(6639 / 20000), (6242414879453217 / 18802020230000000), (31706741774153 / 100000000000000), (3171035598783539 / 10000000000000000), StaticNodes.Batch0002.node17, StaticNodes.Batch0002.node18, false, false, .piece 197, 140, 197⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(6242414879453217 / 18802020230000000), (3321 / 10000), (3171035598783539 / 10000000000000000), (7929035696067 / 25000000000000), StaticNodes.Batch0002.node17, StaticNodes.Batch0002.node18, false, false, .piece 197, 141, 197⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(3321 / 10000), (830374641839183 / 2500000000000000), (7929035696067 / 25000000000000), (11894724654862684498404557 / 37500000000000000000000000), StaticNodes.Batch0002.node18, StaticNodes.Batch0002.node19, false, false, .piece 197, 141, 197⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (3309 / 10000) (830374641839183 / 2500000000000000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch041

namespace OptimalG.Certificates.StaticSupportData.Batch042
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(830374641839183 / 2500000000000000), (1329 / 4000), (11894724654862684498404557 / 37500000000000000000000000), (31725538592047 / 100000000000000), StaticNodes.Batch0002.node18, StaticNodes.Batch0002.node19, false, false, .piece 198, 141, 198⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(1329 / 4000), (6241763549641419 / 18781519916000000), (31725538592047 / 100000000000000), (3173088378388173 / 10000000000000000), StaticNodes.Batch0002.node18, StaticNodes.Batch0002.node19, false, false, .piece 198, 141, 198⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(6241763549641419 / 18781519916000000), (831 / 2500), (3173088378388173 / 10000000000000000), (6346985870401 / 20000000000000), StaticNodes.Batch0002.node18, StaticNodes.Batch0002.node19, false, false, .piece 198, 142, 198⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(831 / 2500), (831305904511983 / 2500000000000000), (6346985870401 / 20000000000000), (24798895085519040335089 / 78125000000000000000000), StaticNodes.Batch0002.node19, StaticNodes.Batch0002.node20, false, false, .piece 198, 142, 198⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(831305904511983 / 2500000000000000), (6651 / 20000), (24798895085519040335089 / 78125000000000000000000), (6348863014369 / 20000000000000), StaticNodes.Batch0002.node19, StaticNodes.Batch0002.node20, false, false, .piece 199, 142, 199⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(6651 / 20000), (1248240880665423 / 3752263088800000), (6348863014369 / 20000000000000), (635028231598561 / 2000000000000000), StaticNodes.Batch0002.node19, StaticNodes.Batch0002.node20, false, false, .piece 199, 142, 199⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(1248240880665423 / 3752263088800000), (3327 / 10000), (635028231598561 / 2000000000000000), (31753695729567 / 100000000000000), StaticNodes.Batch0002.node19, StaticNodes.Batch0002.node20, false, false, .piece 199, 143, 199⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(3327 / 10000), (6657 / 20000), (31753695729567 / 100000000000000), (31763071539577 / 100000000000000), StaticNodes.Batch0002.node20, StaticNodes.Batch0002.node21, false, false, .piece 199, 143, 199⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(6657 / 20000), (33289486687391323 / 100000000000000000), (31763071539577 / 100000000000000), (158829372373813403276524339 / 500000000000000000000000000), StaticNodes.Batch0002.node20, StaticNodes.Batch0002.node21, false, false, .piece 199, 143, 199⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(33289486687391323 / 100000000000000000), (1040138043109919 / 3123613193000000), (158829372373813403276524339 / 500000000000000000000000000), (1588596968798719 / 5000000000000000), StaticNodes.Batch0002.node20, StaticNodes.Batch0002.node21, false, false, .piece 200, 143, 200⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(1040138043109919 / 3123613193000000), (333 / 1000), (1588596968798719 / 5000000000000000), (7943110594789 / 25000000000000), StaticNodes.Batch0002.node20, StaticNodes.Batch0002.node21, false, false, .piece 200, 144, 200⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(333 / 1000), (6663 / 20000), (7943110594789 / 25000000000000), (7945452091371 / 25000000000000), StaticNodes.Batch0002.node21, StaticNodes.Batch0002.node22, false, false, .piece 200, 144, 200⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(6663 / 20000), (1666336859715167 / 5000000000000000), (7945452091371 / 25000000000000), (31789133289643580105353 / 100000000000000000000000), StaticNodes.Batch0002.node21, StaticNodes.Batch0002.node22, false, false, .piece 200, 144, 200⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(1666336859715167 / 5000000000000000), (3333 / 10000), (31789133289643580105353 / 100000000000000000000000), (15895584767367 / 50000000000000), StaticNodes.Batch0002.node21, StaticNodes.Batch0002.node22, false, false, .piece 201, 144, 201⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(3333 / 10000), (2079094794433871 / 6237518844000000), (15895584767367 / 50000000000000), (3179246717202071 / 10000000000000000), StaticNodes.Batch0002.node22, StaticNodes.Batch0002.node23, false, false, .piece 201, 144, 201⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(2079094794433871 / 6237518844000000), (6669 / 20000), (3179246717202071 / 10000000000000000), (31800525813 / 100000000000), StaticNodes.Batch0002.node22, StaticNodes.Batch0002.node23, false, false, .piece 201, 145, 201⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (830374641839183 / 2500000000000000) (6669 / 20000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch042
