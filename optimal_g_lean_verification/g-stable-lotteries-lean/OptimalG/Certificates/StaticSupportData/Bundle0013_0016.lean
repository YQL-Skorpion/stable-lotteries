import OptimalG.Certificates.StaticLayerFast
import OptimalG.Certificates.StaticLayerGeometry
import OptimalG.Certificates.StaticSegmentData
import OptimalG.Certificates.SegmentMembership
import OptimalG.Certificates.StaticLayerCover

set_option Elab.async false

namespace OptimalG.Certificates.StaticSupportData.Batch013
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(29612280348654807 / 100000000000000000), (14819006461186887 / 50000000000000000), (307321784359185938759006139 / 1000000000000000000000000000), (153721808876616010327816299 / 500000000000000000000000000), StaticNodes.Batch0001.node26, StaticNodes.Batch0001.node27, false, true, .piece 4, 47, 47⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(14819006461186887 / 50000000000000000), (741 / 2500), (153721808876616010327816299 / 500000000000000000000000000), (15372651288357 / 50000000000000), StaticNodes.Batch0001.node26, StaticNodes.Batch0001.node27, false, true, .piece 5, 47, 47⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(741 / 2500), (758787 / 2560000), (15372651288257 / 50000000000000), (15372679075683 / 50000000000000), StaticNodes.Batch0001.node27, StaticNodes.Batch0001.node28, false, true, .piece 5, 47, 47⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(758787 / 2560000), (1517577 / 5120000), (15372679075683 / 50000000000000), (30745385939059 / 100000000000000), StaticNodes.Batch0001.node27, StaticNodes.Batch0001.node28, false, true, .piece 5, 47, 47⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(1517577 / 5120000), (430646523127741 / 1452914688000000), (30745385939059 / 100000000000000), (1537269352605891 / 5000000000000000), StaticNodes.Batch0001.node27, StaticNodes.Batch0001.node28, false, true, .piece 5, 47, 47⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(430646523127741 / 1452914688000000), (75879 / 256000), (1537269352605891 / 5000000000000000), (30745402965403 / 100000000000000), StaticNodes.Batch0001.node27, StaticNodes.Batch0001.node28, false, true, .piece 5, 48, 48⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(75879 / 256000), (189699 / 640000), (30745402965403 / 100000000000000), (30745467528279 / 100000000000000), StaticNodes.Batch0001.node27, StaticNodes.Batch0001.node28, false, true, .piece 5, 48, 48⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(189699 / 640000), (94851 / 320000), (30745467528279 / 100000000000000), (30745596655093 / 100000000000000), StaticNodes.Batch0001.node27, StaticNodes.Batch0001.node28, false, true, .piece 5, 48, 48⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(94851 / 320000), (47427 / 160000), (30745596655093 / 100000000000000), (30745854912961 / 100000000000000), StaticNodes.Batch0001.node27, StaticNodes.Batch0001.node28, false, true, .piece 5, 48, 48⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(47427 / 160000), (4743 / 16000), (30745854912961 / 100000000000000), (30746371445663 / 100000000000000), StaticNodes.Batch0001.node27, StaticNodes.Batch0001.node28, false, true, .piece 5, 48, 48⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(4743 / 16000), (11859 / 40000), (30746371445663 / 100000000000000), (30747404578923 / 100000000000000), StaticNodes.Batch0001.node27, StaticNodes.Batch0001.node28, false, true, .piece 5, 48, 48⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(11859 / 40000), (5931 / 20000), (30747404578923 / 100000000000000), (15374735558403 / 50000000000000), StaticNodes.Batch0001.node27, StaticNodes.Batch0001.node28, false, true, .piece 5, 48, 48⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(5931 / 20000), (741593637402319 / 2500000000000000), (15374735558403 / 50000000000000), (1921992591829399260942243 / 6250000000000000000000000), StaticNodes.Batch0001.node27, StaticNodes.Batch0001.node28, false, true, .piece 5, 48, 48⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(741593637402319 / 2500000000000000), (2967 / 10000), (1921992591829399260942243 / 6250000000000000000000000), (7688401319397 / 25000000000000), StaticNodes.Batch0001.node27, StaticNodes.Batch0001.node28, false, true, .piece 6, 48, 48⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(2967 / 10000), (2968947806981173 / 10000000000000000), (7688401319447 / 25000000000000), (92276929374507550963497283 / 300000000000000000000000000), StaticNodes.Batch0001.node28, StaticNodes.Batch0001.node29, false, true, .piece 6, 48, 48⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(2968947806981173 / 10000000000000000), (297 / 1000), (92276929374507550963497283 / 300000000000000000000000000), (30761877935859 / 100000000000000), StaticNodes.Batch0001.node28, StaticNodes.Batch0001.node29, false, true, .piece 7, 48, 48⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (29612280348654807 / 100000000000000000) (297 / 1000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch013

namespace OptimalG.Certificates.StaticSupportData.Batch014
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(297 / 1000), (185720066522067 / 625000000000000), (30761877935859 / 100000000000000), (1922879704945534289791279 / 6250000000000000000000000), StaticNodes.Batch0001.node29, StaticNodes.Batch0001.node30, false, true, .piece 7, 48, 48⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(185720066522067 / 625000000000000), (2973 / 10000), (1922879704945534289791279 / 6250000000000000000000000), (3077015636917 / 10000000000000), StaticNodes.Batch0001.node29, StaticNodes.Batch0001.node30, false, true, .piece 8, 48, 48⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(2973 / 10000), (51314222432117 / 172588313312500), (3077015636917 / 10000000000000), (769268776766493 / 2500000000000000), StaticNodes.Batch0001.node30, StaticNodes.Batch0001.node31, false, true, .piece 8, 48, 48⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(51314222432117 / 172588313312500), (29740943217249693 / 100000000000000000), (769268776766493 / 2500000000000000), (307731782434217388320455009 / 1000000000000000000000000000), StaticNodes.Batch0001.node30, StaticNodes.Batch0001.node31, false, true, .piece 8, 49, 49⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(29740943217249693 / 100000000000000000), (186 / 625), (307731782434217388320455009 / 1000000000000000000000000000), (30778440608209 / 100000000000000), StaticNodes.Batch0001.node30, StaticNodes.Batch0001.node31, false, true, .piece 9, 49, 49⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(186 / 625), (2976667579096867 / 10000000000000000), (30778440608209 / 100000000000000), (18468171222765994000400441 / 60000000000000000000000000), StaticNodes.Batch0001.node31, StaticNodes.Batch0001.node32, false, true, .piece 9, 49, 49⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(2976667579096867 / 10000000000000000), (2979 / 10000), (18468171222765994000400441 / 60000000000000000000000000), (1924170668489 / 6250000000000), StaticNodes.Batch0001.node31, StaticNodes.Batch0001.node32, false, true, .piece 10, 49, 49⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(2979 / 10000), (3724051045585957 / 12500000000000000), (1924170668489 / 6250000000000), (115452737561978578186503037 / 375000000000000000000000000), StaticNodes.Batch0001.node32, StaticNodes.Batch0001.node33, false, true, .piece 10, 49, 49⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(3724051045585957 / 12500000000000000), (29818140938406623 / 100000000000000000), (115452737561978578186503037 / 375000000000000000000000000), (923835376086003932968464743 / 3000000000000000000000000000), StaticNodes.Batch0001.node32, StaticNodes.Batch0001.node33, false, true, .piece 11, 49, 49⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(29818140938406623 / 100000000000000000), (1491 / 5000), (923835376086003932968464743 / 3000000000000000000000000000), (6159005324853 / 20000000000000), StaticNodes.Batch0001.node32, StaticNodes.Batch0001.node33, false, true, .piece 12, 49, 49⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(1491 / 5000), (687767472576377 / 2306053805000000), (6159005324853 / 20000000000000), (7699063339842381 / 25000000000000000), StaticNodes.Batch0001.node33, StaticNodes.Batch0001.node34, false, true, .piece 12, 49, 49⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(687767472576377 / 2306053805000000), (2984387351212561 / 10000000000000000), (7699063339842381 / 25000000000000000), (15400816528341058594706763 / 50000000000000000000000000), StaticNodes.Batch0001.node33, StaticNodes.Batch0001.node34, false, true, .piece 12, 50, 50⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(2984387351212561 / 10000000000000000), (597 / 2000), (15400816528341058594706763 / 50000000000000000000000000), (30803328417963 / 100000000000000), StaticNodes.Batch0001.node33, StaticNodes.Batch0001.node34, false, true, .piece 13, 50, 50⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(597 / 2000), (14934803042922293 / 50000000000000000), (30803328417963 / 100000000000000), (30808757805082157490613039 / 100000000000000000000000000), StaticNodes.Batch0001.node34, StaticNodes.Batch0001.node35, false, true, .piece 13, 50, 50⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(14934803042922293 / 50000000000000000), (747 / 2500), (30808757805082157490613039 / 100000000000000000000000000), (3851454515601 / 12500000000000), StaticNodes.Batch0001.node34, StaticNodes.Batch0001.node35, false, true, .piece 14, 50, 50⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(747 / 2500), (7473834664890891 / 25000000000000000), (3851454515601 / 12500000000000), (19259929238032698010543863 / 62500000000000000000000000), StaticNodes.Batch0001.node35, StaticNodes.Batch0001.node36, false, true, .piece 14, 50, 50⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (297 / 1000) (7473834664890891 / 25000000000000000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch014

namespace OptimalG.Certificates.StaticSupportData.Batch015
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(7473834664890891 / 25000000000000000), (2991 / 10000), (19259929238032698010543863 / 62500000000000000000000000), (7704987434481 / 25000000000000), StaticNodes.Batch0001.node35, StaticNodes.Batch0001.node36, false, true, .piece 15, 50, 50⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(2991 / 10000), (4148237827537233 / 13865896730000000), (7704987434481 / 25000000000000), (15410922984556233 / 50000000000000000), StaticNodes.Batch0001.node36, StaticNodes.Batch0001.node37, false, true, .piece 15, 50, 50⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(4148237827537233 / 13865896730000000), (1496053561664127 / 5000000000000000), (15410922984556233 / 50000000000000000), (7705754997367847192760471 / 25000000000000000000000000), StaticNodes.Batch0001.node36, StaticNodes.Batch0001.node37, false, true, .piece 15, 51, 51⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(1496053561664127 / 5000000000000000), (1497 / 5000), (7705754997367847192760471 / 25000000000000000000000000), (15414134637981 / 50000000000000), StaticNodes.Batch0001.node36, StaticNodes.Batch0001.node37, false, true, .piece 16, 51, 51⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(1497 / 5000), (2994680380700153 / 10000000000000000), (15414134637981 / 50000000000000), (5780654521718533146635581 / 18750000000000000000000000), StaticNodes.Batch0001.node37, StaticNodes.Batch0001.node38, false, true, .piece 16, 51, 51⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(2994680380700153 / 10000000000000000), (2997 / 10000), (5780654521718533146635581 / 18750000000000000000000000), (15418297395397 / 50000000000000), StaticNodes.Batch0001.node37, StaticNodes.Batch0001.node38, false, true, .piece 17, 51, 51⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(2997 / 10000), (5994507276144101 / 20000000000000000), (15418297395397 / 50000000000000), (5781993597154562252045243 / 18750000000000000000000000), StaticNodes.Batch0001.node38, StaticNodes.Batch0001.node39, false, true, .piece 17, 51, 51⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(5994507276144101 / 20000000000000000), (749956723860987 / 2500000000000000), (5781993597154562252045243 / 18750000000000000000000000), (240972230762224609752247 / 781250000000000000000000), StaticNodes.Batch0001.node38, StaticNodes.Batch0001.node39, false, true, .piece 18, 51, 51⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(749956723860987 / 2500000000000000), (3 / 10), (240972230762224609752247 / 781250000000000000000000), (3084492627697 / 10000000000000), StaticNodes.Batch0001.node38, StaticNodes.Batch0001.node39, false, true, .piece 19, 51, 51⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(3 / 10), (13899972474809 / 46319284350000), (3084492627697 / 10000000000000), (154237192894277 / 500000000000000), StaticNodes.Batch0001.node39, StaticNodes.Batch0001.node40, false, true, .piece 19, 51, 51⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(13899972474809 / 46319284350000), (1501200076407923 / 5000000000000000), (154237192894277 / 500000000000000), (15425798339307818721794303 / 50000000000000000000000000), StaticNodes.Batch0001.node39, StaticNodes.Batch0001.node40, false, true, .piece 19, 52, 52⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(1501200076407923 / 5000000000000000), (3003 / 10000), (15425798339307818721794303 / 50000000000000000000000000), (30853263748153 / 100000000000000), StaticNodes.Batch0001.node39, StaticNodes.Batch0001.node40, false, true, .piece 20, 52, 52⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(3003 / 10000), (15024867050938717 / 50000000000000000), (30853263748153 / 100000000000000), (46288128206925437001212813 / 150000000000000000000000000), StaticNodes.Batch0001.node40, StaticNodes.Batch0001.node41, false, true, .piece 20, 52, 52⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(15024867050938717 / 50000000000000000), (1503 / 5000), (46288128206925437001212813 / 150000000000000000000000000), (30861607259043 / 100000000000000), StaticNodes.Batch0001.node40, StaticNodes.Batch0001.node41, false, true, .piece 21, 52, 52⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(1503 / 5000), (3007546667559641 / 10000000000000000), (30861607259043 / 100000000000000), (30865911916885483730618863 / 100000000000000000000000000), StaticNodes.Batch0001.node41, StaticNodes.Batch0001.node42, false, true, .piece 21, 52, 52⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(3007546667559641 / 10000000000000000), (3009 / 10000), (30865911916885483730618863 / 100000000000000000000000000), (3858744600759 / 12500000000000), StaticNodes.Batch0001.node41, StaticNodes.Batch0001.node42, false, true, .piece 22, 52, 52⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (7473834664890891 / 25000000000000000) (3009 / 10000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch015

namespace OptimalG.Certificates.StaticSupportData.Batch016
open StaticSupport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def cell0 : StaticSupport.ContinuousLayerCell := ⟨(3009 / 10000), (15050599624657693 / 50000000000000000), (3858744600759 / 12500000000000), (92619228054244149084816613 / 300000000000000000000000000), StaticNodes.Batch0001.node42, StaticNodes.Batch0001.node43, false, true, .piece 22, 52, 52⟩
def cell1 : StaticSupport.ContinuousLayerCell := ⟨(15050599624657693 / 50000000000000000), (2515161596904573 / 8355592205000000), (92619228054244149084816613 / 300000000000000000000000000), (3087316981413891 / 10000000000000000), StaticNodes.Batch0001.node42, StaticNodes.Batch0001.node43, false, true, .piece 23, 52, 52⟩
def cell2 : StaticSupport.ContinuousLayerCell := ⟨(2515161596904573 / 8355592205000000), (753 / 2500), (3087316981413891 / 10000000000000000), (30878312398277 / 100000000000000), StaticNodes.Batch0001.node42, StaticNodes.Batch0001.node43, false, true, .piece 23, 53, 53⟩
def cell3 : StaticSupport.ContinuousLayerCell := ⟨(753 / 2500), (3012693182303437 / 10000000000000000), (30878312398277 / 100000000000000), (92640733373094884857161469 / 300000000000000000000000000), StaticNodes.Batch0001.node43, StaticNodes.Batch0001.node44, false, true, .piece 23, 53, 53⟩
def cell4 : StaticSupport.ContinuousLayerCell := ⟨(3012693182303437 / 10000000000000000), (603 / 2000), (92640733373094884857161469 / 300000000000000000000000000), (15443337046107 / 50000000000000), StaticNodes.Batch0001.node43, StaticNodes.Batch0001.node44, false, true, .piece 24, 53, 53⟩
def cell5 : StaticSupport.ContinuousLayerCell := ⟨(603 / 2000), (603053287935067 / 2000000000000000), (15443337046107 / 50000000000000), (617748345260807722419629 / 2000000000000000000000000), StaticNodes.Batch0001.node44, StaticNodes.Batch0001.node45, false, true, .piece 24, 53, 53⟩
def cell6 : StaticSupport.ContinuousLayerCell := ⟨(603053287935067 / 2000000000000000), (3017839697047233 / 10000000000000000), (617748345260807722419629 / 2000000000000000000000000), (3089459475942928973760471 / 10000000000000000000000000), StaticNodes.Batch0001.node44, StaticNodes.Batch0001.node45, false, true, .piece 25, 53, 53⟩
def cell7 : StaticSupport.ContinuousLayerCell := ⟨(3017839697047233 / 10000000000000000), (1509 / 5000), (3089459475942928973760471 / 10000000000000000000000000), (3861880235853 / 12500000000000), StaticNodes.Batch0001.node44, StaticNodes.Batch0001.node45, false, true, .piece 26, 53, 53⟩
def cell8 : StaticSupport.ContinuousLayerCell := ⟨(1509 / 5000), (421400152424821 / 1395650080500000), (3861880235853 / 12500000000000), (1544945052471121 / 5000000000000000), StaticNodes.Batch0001.node45, StaticNodes.Batch0001.node46, false, true, .piece 26, 53, 53⟩
def cell9 : StaticSupport.ContinuousLayerCell := ⟨(421400152424821 / 1395650080500000), (302041295441913 / 1000000000000000), (1544945052471121 / 5000000000000000), (3090177716688260323047993 / 10000000000000000000000000), StaticNodes.Batch0001.node45, StaticNodes.Batch0001.node46, false, true, .piece 26, 54, 54⟩
def cell10 : StaticSupport.ContinuousLayerCell := ⟨(302041295441913 / 1000000000000000), (3021 / 10000), (3090177716688260323047993 / 10000000000000000000000000), (30903415787307 / 100000000000000), StaticNodes.Batch0001.node45, StaticNodes.Batch0001.node46, false, true, .piece 27, 54, 54⟩
def cell11 : StaticSupport.ContinuousLayerCell := ⟨(3021 / 10000), (15114931058955147 / 50000000000000000), (30903415787307 / 100000000000000), (77272409952249458818888839 / 250000000000000000000000000), StaticNodes.Batch0001.node46, StaticNodes.Batch0001.node47, false, true, .piece 27, 54, 54⟩
def cell12 : StaticSupport.ContinuousLayerCell := ⟨(15114931058955147 / 50000000000000000), (189 / 625), (77272409952249458818888839 / 250000000000000000000000000), (30911795850729 / 100000000000000), StaticNodes.Batch0001.node46, StaticNodes.Batch0001.node47, false, true, .piece 28, 54, 54⟩
def cell13 : StaticSupport.ContinuousLayerCell := ⟨(189 / 625), (3025559469162927 / 10000000000000000), (30911795850729 / 100000000000000), (6183231041091493199865361 / 20000000000000000000000000), StaticNodes.Batch0001.node47, StaticNodes.Batch0001.node48, false, true, .piece 28, 54, 54⟩
def cell14 : StaticSupport.ContinuousLayerCell := ⟨(3025559469162927 / 10000000000000000), (3027 / 10000), (6183231041091493199865361 / 20000000000000000000000000), (15460091039437 / 50000000000000), StaticNodes.Batch0001.node47, StaticNodes.Batch0001.node48, false, true, .piece 29, 54, 54⟩
def cell15 : StaticSupport.ContinuousLayerCell := ⟨(3027 / 10000), (15140663632674123 / 50000000000000000), (15460091039437 / 50000000000000), (30923350841741837018125697 / 100000000000000000000000000), StaticNodes.Batch0001.node48, StaticNodes.Batch0001.node49, false, true, .piece 29, 54, 54⟩
def cells : List StaticSupport.ContinuousLayerCell := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15]
theorem numeric_checked : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true := by decide +kernel
theorem geometry_checked : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true := by decide +kernel
theorem membership_checked : cells.all (fun c=>StaticSegmentData.tree.nodeCheck c.left && StaticSegmentData.tree.nodeCheck c.right)=true := by decide +kernel
theorem cover_checked : StaticSupport.continuousCellCoverCheck (3009 / 10000) (15140663632674123 / 50000000000000000) cells=true := by decide +kernel
end OptimalG.Certificates.StaticSupportData.Batch016
