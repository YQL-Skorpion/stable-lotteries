import OptimalG.Certificates.StaticLayerFast
import OptimalG.Certificates.StaticLayerGeometry
import OptimalG.Certificates.StaticSegmentData
import OptimalG.Certificates.SegmentMembership
import OptimalG.Certificates.StaticLayerCover

set_option Elab.async false

namespace OptimalG.Certificates.StaticSupportData.Batch043
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(6669 / 20000), (417 / 1250), (31800525813 / 100000000000), (31809877395389 / 100000000000000), StaticNodes.Batch0002.node22, StaticNodes.Batch0002.node23, false, false, .piece 201, 145, 201⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(417 / 1250), (4170498462651917 / 12500000000000000), (31809877395389 / 100000000000000), (3976545275668264188801713 / 12500000000000000000000000), StaticNodes.Batch0002.node23, StaticNodes.Batch0002.node24, false, false, .piece 201, 145, 201⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(4170498462651917 / 12500000000000000), (415806940594361 / 1246236778000000), (3976545275668264188801713 / 12500000000000000000000000), (636259899361341 / 2000000000000000), StaticNodes.Batch0002.node23, StaticNodes.Batch0002.node24, false, false, .piece 202, 145, 202⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(415806940594361 / 1246236778000000), (267 / 800), (636259899361341 / 2000000000000000), (3977403021403 / 12500000000000), StaticNodes.Batch0002.node23, StaticNodes.Batch0002.node24, false, false, .piece 202, 146, 202⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(267 / 800), (3339 / 10000), (3977403021403 / 12500000000000), (15914283138443 / 50000000000000), StaticNodes.Batch0002.node23, StaticNodes.Batch0002.node24, false, false, .piece 202, 146, 202⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(3339 / 10000), (6237083091993411 / 18675040868000000), (15914283138443 / 50000000000000), (3183352276411337 / 10000000000000000), StaticNodes.Batch0002.node24, StaticNodes.Batch0002.node25, false, false, .piece 202, 146, 202⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(6237083091993411 / 18675040868000000), (1670061910406367 / 5000000000000000), (3183352276411337 / 10000000000000000), (3979445259594338184367213 / 12500000000000000000000000), StaticNodes.Batch0002.node24, StaticNodes.Batch0002.node25, false, false, .piece 202, 147, 202⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(1670061910406367 / 5000000000000000), (6681 / 20000), (3979445259594338184367213 / 12500000000000000000000000), (795947594933 / 2500000000000), StaticNodes.Batch0002.node24, StaticNodes.Batch0002.node25, false, false, .piece 203, 147, 203⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(6681 / 20000), (1671 / 5000), (795947594933 / 2500000000000), (15923618316669 / 50000000000000), StaticNodes.Batch0002.node24, StaticNodes.Batch0002.node25, false, false, .piece 203, 147, 203⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(1671 / 5000), (62370968339657091 / 186566506760000000), (15923618316669 / 50000000000000), (31854050560159697 / 100000000000000000), StaticNodes.Batch0002.node25, StaticNodes.Batch0002.node26, false, false, .piece 203, 147, 203⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(62370968339657091 / 186566506760000000), (6687 / 20000), (31854050560159697 / 100000000000000000), (7964141239669 / 25000000000000), StaticNodes.Batch0002.node25, StaticNodes.Batch0002.node26, false, false, .piece 203, 148, 203⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(6687 / 20000), (668769774300787 / 2000000000000000), (7964141239669 / 25000000000000), (49779271059217027823527 / 156250000000000000000000), StaticNodes.Batch0002.node25, StaticNodes.Batch0002.node26, false, false, .piece 203, 148, 203⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(668769774300787 / 2000000000000000), (669 / 2000), (49779271059217027823527 / 156250000000000000000000), (7966472168677 / 25000000000000), StaticNodes.Batch0002.node25, StaticNodes.Batch0002.node26, false, false, .piece 204, 148, 204⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(669 / 2000), (12474314201206821 / 37276832264000000), (7966472168677 / 25000000000000), (6374915671241207 / 20000000000000000), StaticNodes.Batch0002.node26, StaticNodes.Batch0002.node27, false, false, .piece 204, 148, 204⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(12474314201206821 / 37276832264000000), (6693 / 20000), (6374915671241207 / 20000000000000000), (15937603941387 / 50000000000000), StaticNodes.Batch0002.node26, StaticNodes.Batch0002.node27, false, false, .piece 204, 149, 204⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(6693 / 20000), (52305842534299 / 156250000000000), (15937603941387 / 50000000000000), (747231486496508410717697 / 2343750000000000000000000), StaticNodes.Batch0002.node26, StaticNodes.Batch0002.node27, false, false, .piece 204, 149, 204⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (6669 / 20000) (52305842534299 / 156250000000000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch043

namespace OptimalG.Certificates.StaticSupportData.Batch044
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(52305842534299 / 156250000000000), (837 / 2500), (747231486496508410717697 / 2343750000000000000000000), (31884522627977 / 100000000000000), StaticNodes.Batch0002.node26, StaticNodes.Batch0002.node27, false, false, .piece 205, 149, 205⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(837 / 2500), (6699 / 20000), (31884522627977 / 100000000000000), (31893832833351 / 100000000000000), StaticNodes.Batch0002.node27, StaticNodes.Batch0002.node28, false, false, .piece 205, 149, 205⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(6699 / 20000), (62343959830177101 / 186117748540000000), (31893832833351 / 100000000000000), (31895106152252367 / 100000000000000000), StaticNodes.Batch0002.node27, StaticNodes.Batch0002.node28, false, false, .piece 205, 149, 205⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(62343959830177101 / 186117748540000000), (3351 / 10000), (31895106152252367 / 100000000000000000), (15951569360389 / 50000000000000), StaticNodes.Batch0002.node27, StaticNodes.Batch0002.node28, false, false, .piece 205, 150, 205⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(3351 / 10000), (670259794577267 / 2000000000000000), (15951569360389 / 50000000000000), (9571497787315086927342473 / 30000000000000000000000000), StaticNodes.Batch0002.node28, StaticNodes.Batch0002.node29, false, false, .piece 205, 150, 205⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(670259794577267 / 2000000000000000), (1341 / 4000), (9571497787315086927342473 / 30000000000000000000000000), (31912440083997 / 100000000000000), StaticNodes.Batch0002.node28, StaticNodes.Batch0002.node29, false, false, .piece 206, 150, 206⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(1341 / 4000), (161939234731299 / 482965988000000), (31912440083997 / 100000000000000), (6383126789659741 / 20000000000000000), StaticNodes.Batch0002.node28, StaticNodes.Batch0002.node29, false, false, .piece 206, 150, 206⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(161939234731299 / 482965988000000), (1677 / 5000), (6383126789659741 / 20000000000000000), (15960868589633 / 50000000000000), StaticNodes.Batch0002.node28, StaticNodes.Batch0002.node29, false, false, .piece 206, 151, 206⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(1677 / 5000), (52422250368399 / 156250000000000), (15960868589633 / 50000000000000), (124719067089955693064437 / 390625000000000000000000), StaticNodes.Batch0002.node29, StaticNodes.Batch0002.node30, false, false, .piece 206, 151, 206⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(52422250368399 / 156250000000000), (6711 / 20000), (124719067089955693064437 / 390625000000000000000000), (7982757481961 / 25000000000000), StaticNodes.Batch0002.node29, StaticNodes.Batch0002.node30, false, false, .piece 207, 151, 207⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(6711 / 20000), (779378660195589 / 2322116576000000), (7982757481961 / 25000000000000), (399202021804313 / 1250000000000000), StaticNodes.Batch0002.node29, StaticNodes.Batch0002.node30, false, false, .piece 207, 151, 207⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(779378660195589 / 2322116576000000), (3357 / 10000), (399202021804313 / 1250000000000000), (7985079598537 / 25000000000000), StaticNodes.Batch0002.node29, StaticNodes.Batch0002.node30, false, false, .piece 207, 152, 207⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(3357 / 10000), (6717 / 20000), (7985079598537 / 25000000000000), (31949602638899 / 100000000000000), StaticNodes.Batch0002.node30, StaticNodes.Batch0002.node31, false, false, .piece 207, 152, 207⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(6717 / 20000), (3358749074268737 / 10000000000000000), (31949602638899 / 100000000000000), (23963357685709771742830591 / 75000000000000000000000000), StaticNodes.Batch0002.node30, StaticNodes.Batch0002.node31, false, false, .piece 207, 152, 207⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(3358749074268737 / 10000000000000000), (15588781180984773 / 46400077430000000), (23963357685709771742830591 / 75000000000000000000000000), (7989172385097841 / 25000000000000000), StaticNodes.Batch0002.node30, StaticNodes.Batch0002.node31, false, false, .piece 208, 152, 208⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(15588781180984773 / 46400077430000000), (42 / 125), (7989172385097841 / 25000000000000000), (6391776530877 / 20000000000000), StaticNodes.Batch0002.node30, StaticNodes.Batch0002.node31, false, false, .piece 208, 153, 208⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (52305842534299 / 156250000000000) (42 / 125) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch044

namespace OptimalG.Certificates.StaticSupportData.Batch045
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(42 / 125), (6723 / 20000), (6391776530877 / 20000000000000), (31968158473471 / 100000000000000), StaticNodes.Batch0002.node31, StaticNodes.Batch0002.node32, false, false, .piece 208, 153, 208⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(6723 / 20000), (16812370624799683 / 50000000000000000), (31968158473471 / 100000000000000), (239806347616937202632185387 / 750000000000000000000000000), StaticNodes.Batch0002.node31, StaticNodes.Batch0002.node32, false, false, .piece 208, 153, 208⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(16812370624799683 / 50000000000000000), (194877954277647 / 579482455562500), (239806347616937202632185387 / 750000000000000000000000000), (399715216705471 / 1250000000000000), StaticNodes.Batch0002.node31, StaticNodes.Batch0002.node32, false, false, .piece 209, 153, 209⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(194877954277647 / 579482455562500), (3363 / 10000), (399715216705471 / 1250000000000000), (799435754819 / 2500000000000), StaticNodes.Batch0002.node31, StaticNodes.Batch0002.node32, false, false, .piece 209, 154, 209⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(3363 / 10000), (6729 / 20000), (799435754819 / 2500000000000), (31986697667861 / 100000000000000), StaticNodes.Batch0002.node32, StaticNodes.Batch0002.node33, false, false, .piece 209, 154, 209⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(6729 / 20000), (1683 / 5000), (31986697667861 / 100000000000000), (99987378643 / 312500000000), StaticNodes.Batch0002.node32, StaticNodes.Batch0002.node33, false, false, .piece 209, 154, 209⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(1683 / 5000), (4207748969563923 / 12500000000000000), (99987378643 / 312500000000), (999912208014698053652609 / 3125000000000000000000000), StaticNodes.Batch0002.node33, StaticNodes.Batch0002.node34, false, false, .piece 209, 154, 209⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(4207748969563923 / 12500000000000000), (1326367283096427 / 3940146800000000), (999912208014698053652609 / 3125000000000000000000000), (31997745132484023 / 100000000000000000), StaticNodes.Batch0002.node33, StaticNodes.Batch0002.node34, false, false, .piece 210, 154, 210⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(1326367283096427 / 3940146800000000), (1347 / 4000), (31997745132484023 / 100000000000000000), (1600261025537 / 5000000000000), StaticNodes.Batch0002.node33, StaticNodes.Batch0002.node34, false, false, .piece 210, 155, 210⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(1347 / 4000), (3369 / 10000), (1600261025537 / 5000000000000), (8003618972171 / 25000000000000), StaticNodes.Batch0002.node33, StaticNodes.Batch0002.node34, false, false, .piece 210, 155, 210⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(3369 / 10000), (33701312875233 / 100015302800000), (8003618972171 / 25000000000000), (640365458570607 / 2000000000000000), StaticNodes.Batch0002.node34, StaticNodes.Batch0002.node35, false, false, .piece 210, 155, 210⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(33701312875233 / 100015302800000), (1684962113171169 / 5000000000000000), (640365458570607 / 2000000000000000), (8005044039157222019420007 / 25000000000000000000000000), StaticNodes.Batch0002.node34, StaticNodes.Batch0002.node35, false, false, .piece 210, 156, 210⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(1684962113171169 / 5000000000000000), (6741 / 20000), (8005044039157222019420007 / 25000000000000000000000000), (32023727304193 / 100000000000000), StaticNodes.Batch0002.node34, StaticNodes.Batch0002.node35, false, false, .piece 211, 156, 211⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(6741 / 20000), (843 / 2500), (32023727304193 / 100000000000000), (32032974721277 / 100000000000000), StaticNodes.Batch0002.node34, StaticNodes.Batch0002.node35, false, false, .piece 211, 156, 211⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(843 / 2500), (6235594755356307 / 18487090612000000), (32032974721277 / 100000000000000), (3203880072457669 / 10000000000000000), StaticNodes.Batch0002.node35, StaticNodes.Batch0002.node36, false, false, .piece 211, 156, 211⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(6235594755356307 / 18487090612000000), (6747 / 20000), (3203880072457669 / 10000000000000000), (32042218266583 / 100000000000000), StaticNodes.Batch0002.node35, StaticNodes.Batch0002.node36, false, false, .piece 211, 157, 211⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (42 / 125) (6747 / 20000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch045

namespace OptimalG.Certificates.StaticSupportData.Batch046
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(6747 / 20000), (16868246385167693 / 50000000000000000), (32042218266583 / 100000000000000), (48064706658736229040052717 / 150000000000000000000000000), StaticNodes.Batch0002.node35, StaticNodes.Batch0002.node36, false, false, .piece 211, 157, 211⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(16868246385167693 / 50000000000000000), (27 / 80), (48064706658736229040052717 / 150000000000000000000000000), (8012864464607 / 25000000000000), StaticNodes.Batch0002.node35, StaticNodes.Batch0002.node36, false, false, .piece 212, 157, 212⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(27 / 80), (152109468561183 / 450524084000000), (8012864464607 / 25000000000000), (3205932852062301 / 10000000000000000), StaticNodes.Batch0002.node36, StaticNodes.Batch0002.node37, false, false, .piece 212, 157, 212⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(152109468561183 / 450524084000000), (6753 / 20000), (3205932852062301 / 10000000000000000), (641213872043 / 2000000000000), StaticNodes.Batch0002.node36, StaticNodes.Batch0002.node37, false, false, .piece 212, 158, 212⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(6753 / 20000), (1688687163862369 / 5000000000000000), (641213872043 / 2000000000000), (6012389013820946280741781 / 18750000000000000000000000), StaticNodes.Batch0002.node36, StaticNodes.Batch0002.node37, false, false, .piece 212, 158, 212⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(1688687163862369 / 5000000000000000), (1689 / 5000), (6012389013820946280741781 / 18750000000000000000000000), (16034962751773 / 50000000000000), StaticNodes.Batch0002.node36, StaticNodes.Batch0002.node37, false, false, .piece 213, 158, 213⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(1689 / 5000), (6759 / 20000), (16034962751773 / 50000000000000), (1603957676527 / 5000000000000), StaticNodes.Batch0002.node37, StaticNodes.Batch0002.node38, false, false, .piece 213, 158, 213⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(6759 / 20000), (1246986926105781 / 3689731495600000), (1603957676527 / 5000000000000), (641597126333387 / 2000000000000000), StaticNodes.Batch0002.node37, StaticNodes.Batch0002.node38, false, false, .piece 213, 158, 213⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(1246986926105781 / 3689731495600000), (3381 / 10000), (641597126333387 / 2000000000000000), (32088377859279 / 100000000000000), StaticNodes.Batch0002.node37, StaticNodes.Batch0002.node38, false, false, .piece 213, 159, 213⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(3381 / 10000), (8452748446039851 / 25000000000000000), (32088377859279 / 100000000000000), (2005561795949450017572009 / 6250000000000000000000000), StaticNodes.Batch0002.node38, StaticNodes.Batch0002.node39, false, false, .piece 213, 159, 213⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(8452748446039851 / 25000000000000000), (1353 / 4000), (2005561795949450017572009 / 6250000000000000000000000), (32097598310819 / 100000000000000), StaticNodes.Batch0002.node38, StaticNodes.Batch0002.node39, false, false, .piece 214, 159, 214⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(1353 / 4000), (194875262975547 / 576050690562500), (32097598310819 / 100000000000000), (200627400704473 / 625000000000000), StaticNodes.Batch0002.node38, StaticNodes.Batch0002.node39, false, false, .piece 214, 159, 214⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(194875262975547 / 576050690562500), (423 / 1250), (200627400704473 / 625000000000000), (8026703780467 / 25000000000000), StaticNodes.Batch0002.node38, StaticNodes.Batch0002.node39, false, false, .piece 214, 160, 214⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(423 / 1250), (6769648858214281 / 20000000000000000), (8026703780467 / 25000000000000), (48167818194988712137437557 / 150000000000000000000000000), StaticNodes.Batch0002.node39, StaticNodes.Batch0002.node40, false, false, .piece 214, 160, 214⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(6769648858214281 / 20000000000000000), (6771 / 20000), (48167818194988712137437557 / 150000000000000000000000000), (16058014089331 / 50000000000000), StaticNodes.Batch0002.node39, StaticNodes.Batch0002.node40, false, false, .piece 215, 160, 215⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(6771 / 20000), (6237153750323703 / 18418811494000000), (16058014089331 / 50000000000000), (3212091190876201 / 10000000000000000), StaticNodes.Batch0002.node39, StaticNodes.Batch0002.node40, false, false, .piece 215, 160, 215⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (6747 / 20000) (6237153750323703 / 18418811494000000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch046
