import OptimalG.Certificates.StaticLayerFast
import OptimalG.Certificates.StaticLayerGeometry
import OptimalG.Certificates.StaticSegmentData
import OptimalG.Certificates.SegmentMembership
import OptimalG.Certificates.StaticLayerCover

set_option Elab.async false

namespace OptimalG.Certificates.StaticSupportData.Batch017
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(15140663632674123 / 50000000000000000), (6354282634947687 / 20980987712500000), (30923350841741837018125697 / 100000000000000000000000000), (7731158071176479 / 25000000000000000), StaticNodes.Batch0001.node48, StaticNodes.Batch0001.node49, false, true, .piece 30, 54, 54⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(6354282634947687 / 20980987712500000), (303 / 1000), (7731158071176479 / 25000000000000000), (30928574473959 / 100000000000000), StaticNodes.Batch0001.node48, StaticNodes.Batch0001.node49, false, true, .piece 30, 55, 55⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(303 / 1000), (1515352991953361 / 5000000000000000), (30928574473959 / 100000000000000), (15465275451912706899067467 / 50000000000000000000000000), StaticNodes.Batch0001.node49, StaticNodes.Batch0001.node50, false, true, .piece 30, 55, 55⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(1515352991953361 / 5000000000000000), (3033 / 10000), (15465275451912706899067467 / 50000000000000000000000000), (154684865463 / 500000000000), StaticNodes.Batch0001.node49, StaticNodes.Batch0001.node50, false, true, .piece 31, 55, 55⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(3033 / 10000), (3033279241278621 / 10000000000000000), (154684865463 / 500000000000), (30937755419336031362740029 / 100000000000000000000000000), StaticNodes.Batch0001.node50, StaticNodes.Batch0001.node51, false, true, .piece 31, 55, 55⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(3033279241278621 / 10000000000000000), (1517926249325259 / 5000000000000000), (30937755419336031362740029 / 100000000000000000000000000), (15472482348729021305378091 / 50000000000000000000000000), StaticNodes.Batch0001.node50, StaticNodes.Batch0001.node51, false, true, .piece 32, 55, 55⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(1517926249325259 / 5000000000000000), (759 / 2500), (15472482348729021305378091 / 50000000000000000000000000), (30945377939547 / 100000000000000), StaticNodes.Batch0001.node50, StaticNodes.Batch0001.node51, false, true, .piece 33, 55, 55⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(759 / 2500), (1596936315532953 / 5256922000000000), (30945377939547 / 100000000000000), (3868795439998677 / 12500000000000000), StaticNodes.Batch0001.node51, StaticNodes.Batch0001.node52, false, true, .piece 33, 55, 55⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(1596936315532953 / 5256922000000000), (189901609751401 / 625000000000000), (3868795439998677 / 12500000000000000), (1813604238964109255111 / 5859375000000000000000), StaticNodes.Batch0001.node51, StaticNodes.Batch0001.node52, false, true, .piece 33, 56, 56⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(189901609751401 / 625000000000000), (3039 / 10000), (1813604238964109255111 / 5859375000000000000000), (30953789014747 / 100000000000000), StaticNodes.Batch0001.node51, StaticNodes.Batch0001.node52, false, true, .piece 34, 56, 56⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(3039 / 10000), (1520499506697157 / 5000000000000000), (30953789014747 / 100000000000000), (46439096728736412732681911 / 150000000000000000000000000), StaticNodes.Batch0001.node52, StaticNodes.Batch0001.node53, false, true, .piece 34, 56, 56⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(1520499506697157 / 5000000000000000), (1521 / 5000), (46439096728736412732681911 / 150000000000000000000000000), (3096220637367 / 10000000000000), StaticNodes.Batch0001.node52, StaticNodes.Batch0001.node53, false, true, .piece 35, 56, 56⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(1521 / 5000), (760893067691553 / 2500000000000000), (3096220637367 / 10000000000000), (7741655281685568757083317 / 25000000000000000000000000), StaticNodes.Batch0001.node53, StaticNodes.Batch0001.node54, false, true, .piece 35, 56, 56⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(760893067691553 / 2500000000000000), (609 / 2000), (7741655281685568757083317 / 25000000000000000000000000), (30970630024037 / 100000000000000), StaticNodes.Batch0001.node53, StaticNodes.Batch0001.node54, false, true, .piece 36, 56, 56⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(609 / 2000), (15230727640690553 / 50000000000000000), (30970630024037 / 100000000000000), (154869244676092920573441613 / 500000000000000000000000000), StaticNodes.Batch0001.node54, StaticNodes.Batch0001.node55, false, true, .piece 36, 56, 56⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(15230727640690553 / 50000000000000000), (856185389518093 / 2809980021000000), (154869244676092920573441613 / 500000000000000000000000000), (3097609475527293 / 10000000000000000), StaticNodes.Batch0001.node54, StaticNodes.Batch0001.node55, false, true, .piece 37, 56, 56⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (15140663632674123 / 50000000000000000) (856185389518093 / 2809980021000000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch017

namespace OptimalG.Certificates.StaticSupportData.Batch018
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(856185389518093 / 2809980021000000), (381 / 1250), (3097609475527293 / 10000000000000000), (309790599641 / 1000000000000), StaticNodes.Batch0001.node54, StaticNodes.Batch0001.node55, false, true, .piece 37, 57, 57⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(381 / 1250), (7621796963775021 / 25000000000000000), (309790599641 / 1000000000000), (77452703142278101185510431 / 250000000000000000000000000), StaticNodes.Batch0001.node55, StaticNodes.Batch0001.node56, false, true, .piece 37, 57, 57⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(7621796963775021 / 25000000000000000), (3051 / 10000), (77452703142278101185510431 / 250000000000000000000000000), (30987496247733 / 100000000000000), StaticNodes.Batch0001.node55, StaticNodes.Batch0001.node56, false, true, .piece 38, 57, 57⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(3051 / 10000), (30512920428819057 / 100000000000000000), (30987496247733 / 100000000000000), (309883181184893444232876877 / 1000000000000000000000000000), StaticNodes.Batch0001.node56, StaticNodes.Batch0001.node57, false, true, .piece 38, 57, 57⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(30512920428819057 / 100000000000000000), (763466325063451 / 2500000000000000), (309883181184893444232876877 / 1000000000000000000000000000), (23246669858845351284969133 / 75000000000000000000000000), StaticNodes.Batch0001.node56, StaticNodes.Batch0001.node57, false, true, .piece 39, 57, 57⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(763466325063451 / 2500000000000000), (1527 / 5000), (23246669858845351284969133 / 75000000000000000000000000), (7748984721379 / 25000000000000), StaticNodes.Batch0001.node56, StaticNodes.Batch0001.node57, false, true, .piece 40, 57, 57⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(1527 / 5000), (1032834944324931 / 3379595585200000), (7748984721379 / 25000000000000), (1240073039622257 / 4000000000000000), StaticNodes.Batch0001.node57, StaticNodes.Batch0001.node58, false, true, .piece 40, 57, 57⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(1032834944324931 / 3379595585200000), (30564385576257 / 100000000000000), (1240073039622257 / 4000000000000000), (310028066676710595950497 / 1000000000000000000000000), StaticNodes.Batch0001.node57, StaticNodes.Batch0001.node58, false, true, .piece 40, 58, 58⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(30564385576257 / 100000000000000), (3057 / 10000), (310028066676710595950497 / 1000000000000000000000000), (31004387874479 / 100000000000000), StaticNodes.Batch0001.node57, StaticNodes.Batch0001.node58, false, true, .piece 41, 58, 58⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(3057 / 10000), (3059011814997599 / 10000000000000000), (31004387874479 / 100000000000000), (3876257262842131813475193 / 12500000000000000000000000), StaticNodes.Batch0001.node58, StaticNodes.Batch0001.node59, false, true, .piece 41, 58, 58⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(3059011814997599 / 10000000000000000), (153 / 500), (3876257262842131813475193 / 12500000000000000000000000), (31012843266647 / 100000000000000), StaticNodes.Batch0001.node58, StaticNodes.Batch0001.node59, false, true, .piece 42, 58, 58⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(153 / 500), (3061585072369497 / 10000000000000000), (31012843266647 / 100000000000000), (31017314126323146011025887 / 100000000000000000000000000), StaticNodes.Batch0001.node59, StaticNodes.Batch0001.node60, false, true, .piece 42, 58, 58⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(3061585072369497 / 10000000000000000), (3063 / 10000), (31017314126323146011025887 / 100000000000000000000000000), (1551065253763 / 5000000000000), StaticNodes.Batch0001.node59, StaticNodes.Batch0001.node60, false, true, .piece 43, 58, 58⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(3063 / 10000), (766039582435349 / 2500000000000000), (1551065253763 / 5000000000000), (775614368485728583475309 / 2500000000000000000000000), StaticNodes.Batch0001.node60, StaticNodes.Batch0001.node61, false, true, .piece 43, 58, 58⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(766039582435349 / 2500000000000000), (180256375550207 / 588070918750000), (775614368485728583475309 / 2500000000000000000000000), (484805581653749 / 1562500000000000), StaticNodes.Batch0001.node60, StaticNodes.Batch0001.node61, false, true, .piece 44, 58, 58⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(180256375550207 / 588070918750000), (1533 / 5000), (484805581653749 / 1562500000000000), (3102977329649 / 10000000000000), StaticNodes.Batch0001.node60, StaticNodes.Batch0001.node61, false, true, .piece 44, 59, 59⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (856185389518093 / 2809980021000000) (1533 / 5000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch018

namespace OptimalG.Certificates.StaticSupportData.Batch019
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(1533 / 5000), (15333727251942117 / 50000000000000000), (3102977329649 / 10000000000000), (77579697788265213880743181 / 250000000000000000000000000), StaticNodes.Batch0001.node61, StaticNodes.Batch0001.node62, false, true, .piece 44, 59, 59⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(15333727251942117 / 50000000000000000), (3069 / 10000), (77579697788265213880743181 / 250000000000000000000000000), (969945249389 / 3125000000000), StaticNodes.Batch0001.node61, StaticNodes.Batch0001.node62, false, true, .piece 45, 59, 59⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(3069 / 10000), (7673331427588631 / 25000000000000000), (969945249389 / 3125000000000), (116396955662839107145317019 / 375000000000000000000000000), StaticNodes.Batch0001.node62, StaticNodes.Batch0001.node63, false, true, .piece 45, 59, 59⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(7673331427588631 / 25000000000000000), (3071928724255611 / 10000000000000000), (116396955662839107145317019 / 375000000000000000000000000), (15523263821180321021359013 / 50000000000000000000000000), StaticNodes.Batch0001.node62, StaticNodes.Batch0001.node63, false, true, .piece 46, 59, 59⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(3071928724255611 / 10000000000000000), (192 / 625), (15523263821180321021359013 / 50000000000000000000000000), (15523364571373 / 50000000000000), StaticNodes.Batch0001.node62, StaticNodes.Batch0001.node63, false, true, .piece 47, 59, 59⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(192 / 625), (521874142823607 / 1697527941800000), (15523364571373 / 50000000000000), (621065769222469 / 2000000000000000), StaticNodes.Batch0001.node63, StaticNodes.Batch0001.node64, false, true, .piece 47, 59, 59⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(521874142823607 / 1697527941800000), (1537269352605891 / 5000000000000000), (621065769222469 / 2000000000000000), (15526955840567161026308573 / 50000000000000000000000000), StaticNodes.Batch0001.node63, StaticNodes.Batch0001.node64, false, true, .piece 47, 60, 60⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(1537269352605891 / 5000000000000000), (123 / 400), (15526955840567161026308573 / 50000000000000000000000000), (6211043356491 / 20000000000000), StaticNodes.Batch0001.node63, StaticNodes.Batch0001.node64, false, true, .piece 48, 60, 60⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(123 / 400), (769268776766493 / 2500000000000000), (6211043356491 / 20000000000000), (7765273053061659617250817 / 25000000000000000000000000), StaticNodes.Batch0001.node64, StaticNodes.Batch0001.node65, false, true, .piece 48, 60, 60⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(769268776766493 / 2500000000000000), (26137529755396419 / 84941590070000000), (7765273053061659617250817 / 25000000000000000000000000), (31061213718745473 / 100000000000000000), StaticNodes.Batch0001.node64, StaticNodes.Batch0001.node65, false, true, .piece 49, 60, 60⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(26137529755396419 / 84941590070000000), (1539 / 5000), (31061213718745473 / 100000000000000000), (15531855470731 / 50000000000000), StaticNodes.Batch0001.node64, StaticNodes.Batch0001.node65, false, true, .piece 49, 61, 61⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(1539 / 5000), (7699063339842381 / 25000000000000000), (15531855470731 / 50000000000000), (19417697773558295843634989 / 62500000000000000000000000), StaticNodes.Batch0001.node65, StaticNodes.Batch0001.node66, false, true, .piece 49, 61, 61⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(7699063339842381 / 25000000000000000), (52362860345001 / 170013944560000), (19417697773558295843634989 / 62500000000000000000000000), (12427655590547 / 40000000000000), StaticNodes.Batch0001.node65, StaticNodes.Batch0001.node66, false, true, .piece 50, 61, 61⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(52362860345001 / 170013944560000), (3081 / 10000), (12427655590547 / 40000000000000), (3107221163869 / 10000000000000), StaticNodes.Batch0001.node65, StaticNodes.Batch0001.node66, false, true, .piece 50, 62, 62⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(3081 / 10000), (15410922984556233 / 50000000000000000), (3107221163869 / 10000000000000), (155377854318391951371577913 / 500000000000000000000000000), StaticNodes.Batch0001.node66, StaticNodes.Batch0001.node67, false, true, .piece 50, 62, 62⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(15410922984556233 / 50000000000000000), (5245107041320017 / 17014521766000000), (155377854318391951371577913 / 500000000000000000000000000), (6215419956143139 / 20000000000000000), StaticNodes.Batch0001.node66, StaticNodes.Batch0001.node67, false, true, .piece 51, 62, 62⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (1533 / 5000) (5245107041320017 / 17014521766000000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch019

namespace OptimalG.Certificates.StaticSupportData.Batch020
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(5245107041320017 / 17014521766000000), (771 / 2500), (6215419956143139 / 20000000000000000), (31080718899573 / 100000000000000), StaticNodes.Batch0001.node66, StaticNodes.Batch0001.node67, false, true, .piece 51, 63, 63⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(771 / 2500), (154237192894277 / 500000000000000), (31080718899573 / 100000000000000), (1554141493085804614753783 / 5000000000000000000000000), StaticNodes.Batch0001.node67, StaticNodes.Batch0001.node68, false, true, .piece 51, 63, 63⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(154237192894277 / 500000000000000), (273637673992177 / 886830243437500), (1554141493085804614753783 / 5000000000000000000000000), (3885646770110833 / 12500000000000000), StaticNodes.Batch0001.node67, StaticNodes.Batch0001.node68, false, true, .piece 52, 63, 63⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(273637673992177 / 886830243437500), (3087 / 10000), (3885646770110833 / 12500000000000000), (3108923246991 / 10000000000000), StaticNodes.Batch0001.node67, StaticNodes.Batch0001.node68, false, true, .piece 52, 64, 64⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(3087 / 10000), (3087316981413891 / 10000000000000000), (3108923246991 / 10000000000000), (7772533122778539462404211 / 25000000000000000000000000), StaticNodes.Batch0001.node68, StaticNodes.Batch0001.node69, false, true, .piece 52, 64, 64⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(3087316981413891 / 10000000000000000), (1544945052471121 / 5000000000000000), (7772533122778539462404211 / 25000000000000000000000000), (3887179811202565454731041 / 12500000000000000000000000), StaticNodes.Batch0001.node68, StaticNodes.Batch0001.node69, false, true, .piece 53, 64, 64⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(1544945052471121 / 5000000000000000), (309 / 1000), (3887179811202565454731041 / 12500000000000000000000000), (15548875260081 / 50000000000000), StaticNodes.Batch0001.node68, StaticNodes.Batch0001.node69, false, true, .piece 54, 64, 64⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(309 / 1000), (1317440368569183 / 4261095272500000), (15548875260081 / 50000000000000), (1555141502463661 / 5000000000000000), StaticNodes.Batch0001.node69, StaticNodes.Batch0001.node70, false, true, .piece 54, 64, 64⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(1317440368569183 / 4261095272500000), (7731158071176479 / 25000000000000000), (1555141502463661 / 5000000000000000), (46657121831434125272038211 / 150000000000000000000000000), StaticNodes.Batch0001.node69, StaticNodes.Batch0001.node70, false, true, .piece 54, 65, 65⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(7731158071176479 / 25000000000000000), (3093 / 10000), (46657121831434125272038211 / 150000000000000000000000000), (31106272710707 / 100000000000000), StaticNodes.Batch0001.node69, StaticNodes.Batch0001.node70, false, true, .piece 55, 65, 65⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(3093 / 10000), (3868795439998677 / 12500000000000000), (31106272710707 / 100000000000000), (121531485339970348401579 / 390625000000000000000000), StaticNodes.Batch0001.node70, StaticNodes.Batch0001.node71, false, true, .piece 55, 65, 65⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(3868795439998677 / 12500000000000000), (387 / 1250), (121531485339970348401579 / 390625000000000000000000), (31114799040627 / 100000000000000), StaticNodes.Batch0001.node70, StaticNodes.Batch0001.node71, false, true, .piece 56, 65, 65⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(387 / 1250), (3097609475527293 / 10000000000000000), (31114799040627 / 100000000000000), (7779843891508278307814483 / 25000000000000000000000000), StaticNodes.Batch0001.node71, StaticNodes.Batch0001.node72, false, true, .piece 56, 65, 65⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(3097609475527293 / 10000000000000000), (2642772404922351 / 8530465972000000), (7779843891508278307814483 / 25000000000000000000000000), (3112059950726417 / 10000000000000000), StaticNodes.Batch0001.node71, StaticNodes.Batch0001.node72, false, true, .piece 57, 65, 65⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(2642772404922351 / 8530465972000000), (3099 / 10000), (3112059950726417 / 10000000000000000), (31123329506599 / 100000000000000), StaticNodes.Batch0001.node71, StaticNodes.Batch0001.node72, false, true, .piece 57, 66, 66⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(3099 / 10000), (1240073039622257 / 4000000000000000), (31123329506599 / 100000000000000), (1556334692196468693514599 / 5000000000000000000000000), StaticNodes.Batch0001.node72, StaticNodes.Batch0001.node73, false, true, .piece 57, 66, 66⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (5245107041320017 / 17014521766000000) (1240073039622257 / 4000000000000000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch020
