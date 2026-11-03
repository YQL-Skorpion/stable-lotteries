import OptimalG.Certificates.StaticLayerFast
import OptimalG.Certificates.StaticLayerGeometry
import OptimalG.Certificates.StaticSegmentData
import OptimalG.Certificates.SegmentMembership
import OptimalG.Certificates.StaticLayerCover

set_option Elab.async false

namespace OptimalG.Certificates.StaticSupportData.Batch009
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(125710471457903 / 441808439400000), (178 / 625), (302041295441913 / 1000000000000000), (30215786752513 / 100000000000000), StaticNodes.Batch0000.node115, StaticNodes.Batch0000.node116, false, true, .cap, 27, 27⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(178 / 625), (2851 / 10000), (30215786752513 / 100000000000000), (15114531077573 / 50000000000000), StaticNodes.Batch0000.node116, StaticNodes.Batch0000.node117, false, true, .cap, 27, 27⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(2851 / 10000), (18955526308736441 / 66483080900000000), (15114531077573 / 50000000000000), (15114931058955147 / 50000000000000000), StaticNodes.Batch0000.node117, StaticNodes.Batch0000.node118, false, true, .cap, 27, 27⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(18955526308736441 / 66483080900000000), (1427 / 5000), (15114931058955147 / 50000000000000000), (15121179385663 / 50000000000000), StaticNodes.Batch0000.node117, StaticNodes.Batch0000.node118, false, true, .cap, 28, 28⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(1427 / 5000), (3804894974147381 / 13317884366000000), (15121179385663 / 50000000000000), (3025559469162927 / 10000000000000000), StaticNodes.Batch0000.node118, StaticNodes.Batch0000.node119, false, true, .cap, 28, 28⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(3804894974147381 / 13317884366000000), (2857 / 10000), (3025559469162927 / 10000000000000000), (7563919163923 / 25000000000000), StaticNodes.Batch0000.node118, StaticNodes.Batch0000.node119, false, true, .cap, 29, 29⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(2857 / 10000), (143 / 500), (7563919163923 / 25000000000000), (3026901586763 / 10000000000000), StaticNodes.Batch0000.node119, StaticNodes.Batch0000.node120, false, true, .cap, 29, 29⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(143 / 500), (579518957097193 / 2024333385000000), (3026901586763 / 10000000000000), (15140663632674123 / 50000000000000000), StaticNodes.Batch0000.node120, StaticNodes.Batch0000.node121, false, true, .cap, 29, 29⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(579518957097193 / 2024333385000000), (2863 / 10000), (15140663632674123 / 50000000000000000), (30282376467971 / 100000000000000), StaticNodes.Batch0000.node120, StaticNodes.Batch0000.node121, false, true, .cap, 30, 30⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(2863 / 10000), (1433 / 5000), (30282376467971 / 100000000000000), (30295758510837 / 100000000000000), StaticNodes.Batch0000.node121, StaticNodes.Batch0000.node122, false, true, .cap, 30, 30⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(1433 / 5000), (274632039315319 / 957396608500000), (30295758510837 / 100000000000000), (1515352991953361 / 5000000000000000), StaticNodes.Batch0000.node122, StaticNodes.Batch0000.node123, false, true, .cap, 30, 30⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(274632039315319 / 957396608500000), (2869 / 10000), (1515352991953361 / 5000000000000000), (7577290515839 / 25000000000000), StaticNodes.Batch0000.node122, StaticNodes.Batch0000.node123, false, true, .cap, 31, 31⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(2869 / 10000), (359 / 1250), (7577290515839 / 25000000000000), (6064517434951 / 20000000000000), StaticNodes.Batch0000.node123, StaticNodes.Batch0000.node124, false, true, .cap, 31, 31⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(359 / 1250), (3864966178815763 / 13446743062000000), (6064517434951 / 20000000000000), (3033279241278621 / 10000000000000000), StaticNodes.Batch0000.node124, StaticNodes.Batch0000.node125, false, true, .cap, 31, 31⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(3864966178815763 / 13446743062000000), (23 / 80), (3033279241278621 / 10000000000000000), (30336033917817 / 100000000000000), StaticNodes.Batch0000.node124, StaticNodes.Batch0000.node125, false, true, .cap, 32, 32⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(23 / 80), (1439 / 5000), (30336033917817 / 100000000000000), (1517475116883 / 5000000000000), StaticNodes.Batch0000.node125, StaticNodes.Batch0000.node126, false, true, .cap, 32, 32⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (125710471457903 / 441808439400000) (1439 / 5000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch009

namespace OptimalG.Certificates.StaticSupportData.Batch010
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(1439 / 5000), (1942589456216677 / 6745087070500000), (1517475116883 / 5000000000000), (1517926249325259 / 5000000000000000), StaticNodes.Batch0000.node126, StaticNodes.Batch0000.node127, false, true, .cap, 32, 32⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(1942589456216677 / 6745087070500000), (2881 / 10000), (1517926249325259 / 5000000000000000), (30362992511801 / 100000000000000), StaticNodes.Batch0000.node126, StaticNodes.Batch0000.node127, false, true, .cap, 33, 33⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(2881 / 10000), (721 / 2500), (30362992511801 / 100000000000000), (6075300896469 / 20000000000000), StaticNodes.Batch0000.node127, StaticNodes.Batch0001.node0, false, true, .cap, 33, 33⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(721 / 2500), (976371918324337 / 3383461988500000), (6075300896469 / 20000000000000), (189901609751401 / 625000000000000), StaticNodes.Batch0001.node0, StaticNodes.Batch0001.node1, false, true, .cap, 33, 33⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(976371918324337 / 3383461988500000), (2887 / 10000), (189901609751401 / 625000000000000), (30390038330299 / 100000000000000), StaticNodes.Batch0001.node0, StaticNodes.Batch0001.node1, false, true, .cap, 34, 34⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(2887 / 10000), (289 / 1000), (30390038330299 / 100000000000000), (15201797048087 / 50000000000000), StaticNodes.Batch0001.node1, StaticNodes.Batch0001.node2, false, true, .cap, 34, 34⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(289 / 1000), (1962946696560871 / 6788883359500000), (15201797048087 / 50000000000000), (1520499506697157 / 5000000000000000), StaticNodes.Batch0001.node2, StaticNodes.Batch0001.node3, false, true, .cap, 34, 34⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(1962946696560871 / 6788883359500000), (2893 / 10000), (1520499506697157 / 5000000000000000), (30417171862893 / 100000000000000), StaticNodes.Batch0001.node2, StaticNodes.Batch0001.node3, false, true, .cap, 35, 35⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(2893 / 10000), (181 / 625), (30417171862893 / 100000000000000), (30430771671151 / 100000000000000), StaticNodes.Batch0001.node3, StaticNodes.Batch0001.node4, false, true, .cap, 35, 35⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(181 / 625), (164433209046189 / 567580528625000), (30430771671151 / 100000000000000), (760893067691553 / 2500000000000000), StaticNodes.Batch0001.node4, StaticNodes.Batch0001.node5, false, true, .cap, 35, 35⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(164433209046189 / 567580528625000), (2899 / 10000), (760893067691553 / 2500000000000000), (15222196801919 / 50000000000000), StaticNodes.Batch0001.node4, StaticNodes.Batch0001.node5, false, true, .cap, 36, 36⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(2899 / 10000), (1451 / 5000), (15222196801919 / 50000000000000), (30458037703981 / 100000000000000), StaticNodes.Batch0001.node5, StaticNodes.Batch0001.node6, false, true, .cap, 36, 36⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(1451 / 5000), (6611665828923053 / 22777246865000000), (30458037703981 / 100000000000000), (15230727640690553 / 50000000000000000), StaticNodes.Batch0001.node6, StaticNodes.Batch0001.node7, false, true, .cap, 36, 36⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(6611665828923053 / 22777246865000000), (581 / 2000), (15230727640690553 / 50000000000000000), (304717040521 / 1000000000000), StaticNodes.Batch0001.node6, StaticNodes.Batch0001.node7, false, true, .cap, 37, 37⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(581 / 2000), (727 / 2500), (304717040521 / 1000000000000), (15242696348057 / 50000000000000), StaticNodes.Batch0001.node7, StaticNodes.Batch0001.node8, false, true, .cap, 37, 37⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(727 / 2500), (9969254488704563 / 34277538237500000), (15242696348057 / 50000000000000), (7621796963775021 / 25000000000000000), StaticNodes.Batch0001.node8, StaticNodes.Batch0001.node9, false, true, .cap, 37, 37⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (1439 / 5000) (9969254488704563 / 34277538237500000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch010

namespace OptimalG.Certificates.StaticSupportData.Batch011
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(9969254488704563 / 34277538237500000), (2911 / 10000), (7621796963775021 / 25000000000000000), (30499103711409 / 100000000000000), StaticNodes.Batch0001.node8, StaticNodes.Batch0001.node9, false, true, .cap, 38, 38⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(2911 / 10000), (1457 / 5000), (30499103711409 / 100000000000000), (7628209288453 / 25000000000000), StaticNodes.Batch0001.node9, StaticNodes.Batch0001.node10, false, true, .cap, 38, 38⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(1457 / 5000), (40085048905495171 / 137559365410000000), (7628209288453 / 25000000000000), (30512920428819057 / 100000000000000000), StaticNodes.Batch0001.node10, StaticNodes.Batch0001.node11, false, true, .cap, 38, 38⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(40085048905495171 / 137559365410000000), (2917 / 10000), (30512920428819057 / 100000000000000000), (30526593090353 / 100000000000000), StaticNodes.Batch0001.node10, StaticNodes.Batch0001.node11, false, true, .cap, 39, 39⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(2917 / 10000), (31428168589654 / 107644508640625), (30526593090353 / 100000000000000), (763466325063451 / 2500000000000000), StaticNodes.Batch0001.node11, StaticNodes.Batch0001.node12, false, true, .cap, 39, 39⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(31428168589654 / 107644508640625), (73 / 250), (763466325063451 / 2500000000000000), (30540371587459 / 100000000000000), StaticNodes.Batch0001.node11, StaticNodes.Batch0001.node12, false, true, .cap, 40, 40⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(73 / 250), (2923 / 10000), (30540371587459 / 100000000000000), (30554172702427 / 100000000000000), StaticNodes.Batch0001.node12, StaticNodes.Batch0001.node13, false, true, .cap, 40, 40⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(2923 / 10000), (5054704272709 / 17279762042500), (30554172702427 / 100000000000000), (30564385576257 / 100000000000000), StaticNodes.Batch0001.node13, StaticNodes.Batch0001.node14, false, true, .cap, 40, 40⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(5054704272709 / 17279762042500), (1463 / 5000), (30564385576257 / 100000000000000), (30567996512061 / 100000000000000), StaticNodes.Batch0001.node13, StaticNodes.Batch0001.node14, false, true, .cap, 41, 41⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(1463 / 5000), (2929 / 10000), (30567996512061 / 100000000000000), (6116368613217 / 20000000000000), StaticNodes.Batch0001.node14, StaticNodes.Batch0001.node15, false, true, .cap, 41, 41⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(2929 / 10000), (4064824624562197 / 13869382381000000), (6116368613217 / 20000000000000), (3059011814997599 / 10000000000000000), StaticNodes.Batch0001.node15, StaticNodes.Batch0001.node16, false, true, .cap, 41, 41⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(4064824624562197 / 13869382381000000), (733 / 2500), (3059011814997599 / 10000000000000000), (15297856224233 / 50000000000000), StaticNodes.Batch0001.node15, StaticNodes.Batch0001.node16, false, true, .cap, 42, 42⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(733 / 2500), (587 / 2000), (15297856224233 / 50000000000000), (30609604704843 / 100000000000000), StaticNodes.Batch0001.node16, StaticNodes.Batch0001.node17, false, true, .cap, 42, 42⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(587 / 2000), (4085990208823591 / 13915217728000000), (30609604704843 / 100000000000000), (3061585072369497 / 10000000000000000), StaticNodes.Batch0001.node17, StaticNodes.Batch0001.node18, false, true, .cap, 42, 42⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(4085990208823591 / 13915217728000000), (1469 / 5000), (3061585072369497 / 10000000000000000), (30623519922571 / 100000000000000), StaticNodes.Batch0001.node17, StaticNodes.Batch0001.node18, false, true, .cap, 43, 43⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(1469 / 5000), (2941 / 10000), (30623519922571 / 100000000000000), (15318729073651 / 50000000000000), StaticNodes.Batch0001.node18, StaticNodes.Batch0001.node19, false, true, .cap, 43, 43⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (9969254488704563 / 34277538237500000) (2941 / 10000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch011

namespace OptimalG.Certificates.StaticSupportData.Batch012
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(2941 / 10000), (1026815304560597 / 3490329542000000), (15318729073651 / 50000000000000), (766039582435349 / 2500000000000000), StaticNodes.Batch0001.node19, StaticNodes.Batch0001.node20, false, true, .cap, 43, 43⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(1026815304560597 / 3490329542000000), (184 / 625), (766039582435349 / 2500000000000000), (3065141946547 / 10000000000000), StaticNodes.Batch0001.node19, StaticNodes.Batch0001.node20, false, true, .cap, 44, 44⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(184 / 625), (2947 / 10000), (3065141946547 / 10000000000000), (30665403927147 / 100000000000000), StaticNodes.Batch0001.node20, StaticNodes.Batch0001.node21, false, true, .cap, 44, 44⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(2947 / 10000), (6881133842652617 / 23346143720000000), (30665403927147 / 100000000000000), (15333727251942117 / 50000000000000000), StaticNodes.Batch0001.node21, StaticNodes.Batch0001.node22, false, true, .cap, 44, 44⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(6881133842652617 / 23346143720000000), (59 / 200), (15333727251942117 / 50000000000000000), (30679411613379 / 100000000000000), StaticNodes.Batch0001.node21, StaticNodes.Batch0001.node22, false, true, .cap, 45, 45⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(59 / 200), (2950935005377889 / 10000000000000000), (30679411613379 / 100000000000000), (767094601615917868255421 / 2500000000000000000000000), StaticNodes.Batch0001.node22, StaticNodes.Batch0001.node23, false, true, .cap, 45, 45⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(2950935005377889 / 10000000000000000), (369 / 1250), (767094601615917868255421 / 2500000000000000000000000), (30688764396499 / 100000000000000), StaticNodes.Batch0001.node22, StaticNodes.Batch0001.node23, false, true, .piece 0, 45, 45⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(369 / 1250), (10383804838079643 / 35163901940000000), (30688764396499 / 100000000000000), (7673331427588631 / 25000000000000000), StaticNodes.Batch0001.node23, StaticNodes.Batch0001.node24, false, true, .piece 0, 45, 45⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(10383804838079643 / 35163901940000000), (1476754131374893 / 5000000000000000), (7673331427588631 / 25000000000000000), (5755469234429393241499621 / 18750000000000000000000000), StaticNodes.Batch0001.node23, StaticNodes.Batch0001.node24, false, true, .piece 0, 46, 46⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(1476754131374893 / 5000000000000000), (591 / 2000), (5755469234429393241499621 / 18750000000000000000000000), (1228113198291 / 4000000000000), StaticNodes.Batch0001.node23, StaticNodes.Batch0001.node24, false, true, .piece 1, 46, 46⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(591 / 2000), (591216304024337 / 2000000000000000), (1228113198291 / 4000000000000), (3684950064094169730021619 / 12000000000000000000000000), StaticNodes.Batch0001.node24, StaticNodes.Batch0001.node25, false, true, .piece 1, 46, 46⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(591216304024337 / 2000000000000000), (1479 / 5000), (3684950064094169730021619 / 12000000000000000000000000), (3071694132721 / 10000000000000), StaticNodes.Batch0001.node24, StaticNodes.Batch0001.node25, false, true, .piece 2, 46, 46⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(1479 / 5000), (4188479044357233 / 14157455273000000), (3071694132721 / 10000000000000), (3071928724255611 / 10000000000000000), StaticNodes.Batch0001.node25, StaticNodes.Batch0001.node26, false, true, .piece 2, 46, 46⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(4188479044357233 / 14157455273000000), (1479327388746791 / 5000000000000000), (3071928724255611 / 10000000000000000), (46080046982354577104778943 / 150000000000000000000000000), StaticNodes.Batch0001.node25, StaticNodes.Batch0001.node26, false, true, .piece 2, 47, 47⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(1479327388746791 / 5000000000000000), (2961 / 10000), (46080046982354577104778943 / 150000000000000000000000000), (30731098782483 / 100000000000000), StaticNodes.Batch0001.node25, StaticNodes.Batch0001.node26, false, true, .piece 3, 47, 47⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(2961 / 10000), (29612280348654807 / 100000000000000000), (30731098782483 / 100000000000000), (307321784359185938759006139 / 1000000000000000000000000000), StaticNodes.Batch0001.node26, StaticNodes.Batch0001.node27, false, true, .piece 3, 47, 47⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (2941 / 10000) (29612280348654807 / 100000000000000000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch012
