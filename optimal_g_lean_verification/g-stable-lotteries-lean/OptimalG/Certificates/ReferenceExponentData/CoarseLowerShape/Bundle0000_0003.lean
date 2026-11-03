import OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Parameters
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Batch0000
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0001_0004

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0000
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert0 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0000.cert0,⟨264981333674591985113409,264981340495315785746952⟩,⟨0,592622438341997372630⟩⟩
def cert1 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0000.cert1,⟨264389292240727166449876,264389299044762865949498⟩,⟨0,592621914468732285952⟩⟩
def cert2 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0000.cert2,⟨264028805632958695604174,264028812433242927648850⟩,⟨0,360701852288244417074⟩⟩
def cert3 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0000.cert3,⟨263668318978100280119817,263668325774637716206676⟩,⟨0,360702001448011931498⟩⟩
def cert4 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0000.cert4,⟨263153186567703304055739,263153193353316848558633⟩,⟨0,515572602337604185620⟩⟩
def cert5 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0000.cert5,⟨262638053838524397222950,262638060613233469893486⟩,⟨0,515573219471701204781⟩⟩
def cert6 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0000.cert6,⟨262174280895158417345659,262174287661932381166695⟩,⟨0,464130242718272156668⟩⟩
def cert7 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0000.cert7,⟨261710507492506995124922,261710514251358546711538⟩,⟨0,464130920011765910291⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert0,cert1,cert2,cert3,cert4,cert5,cert6,cert7]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0000.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell0,ReferenceCumulativeData.CoarseLowerShapeTime.cell1,ReferenceCumulativeData.CoarseLowerShapeTime.cell2,ReferenceCumulativeData.CoarseLowerShapeTime.cell3,ReferenceCumulativeData.CoarseLowerShapeTime.cell4,ReferenceCumulativeData.CoarseLowerShapeTime.cell5,ReferenceCumulativeData.CoarseLowerShapeTime.cell6,ReferenceCumulativeData.CoarseLowerShapeTime.cell7] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0000

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0001
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert8 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0001.cert8,⟨261143474132841099983115,261143480877236758399432⟩,⟨0,567568371933235948421⟩⟩
def cert9 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0001.cert9,⟨260576439771786414812732,260576446501754438091246⟩,⟨0,567569772504108719889⟩⟩
def cert10 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0001.cert10,⟨260060762175250276376713,260060768894399547416837⟩,⟨0,516120781542233477525⟩⟩
def cert11 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0001.cert11,⟨259545083478314193591260,259545090186663939395317⟩,⟨0,516122182640974532930⟩⟩
def cert12 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0001.cert12,⟨259080815155821994380849,259080821856312947119241⟩,⟨0,464628055458852007010⟩⟩
def cert13 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0001.cert13,⟨258616545742644962772075,258616552435289693484898⟩,⟨0,464629365873363587645⟩⟩
def cert14 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0001.cert14,⟨258098823856544101532609,258098830538329882971554⟩,⟨0,518169908900690311507⟩⟩
def cert15 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0001.cert15,⟨257581100367584445034118,257581107038530635824143⟩,⟨0,518171816952038977614⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert8,cert9,cert10,cert11,cert12,cert13,cert14,cert15]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0001.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell8,ReferenceCumulativeData.CoarseLowerShapeTime.cell9,ReferenceCumulativeData.CoarseLowerShapeTime.cell10,ReferenceCumulativeData.CoarseLowerShapeTime.cell11,ReferenceCumulativeData.CoarseLowerShapeTime.cell12,ReferenceCumulativeData.CoarseLowerShapeTime.cell13,ReferenceCumulativeData.CoarseLowerShapeTime.cell14,ReferenceCumulativeData.CoarseLowerShapeTime.cell15] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0001

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0002
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert16 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0002.cert16,⟨257014938278380340196116,257014944935182890941117⟩,⟨0,566698770025159228070⟩⟩
def cert17 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0002.cert17,⟨256448773948416355865035,256448780591102823208489⟩,⟨0,566701410611353343264⟩⟩
def cert18 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0002.cert18,⟨256087292831649106923601,256087299470675980846405⟩,⟨0,361700147988268279239⟩⟩
def cert19 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0002.cert19,⟨255725810688931076145399,255725817324302910400655⟩,⟨0,361701278095097107348⟩⟩
def cert20 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0002.cert20,⟨255209245889650354315461,255209252514365619891309⟩,⟨0,517012748206618722377⟩⟩
def cert21 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0002.cert21,⟨254692678778722741812351,254692685392800371535202⟩,⟨0,517015364328648958021⟩⟩
def cert22 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0002.cert22,⟨254227604548589223580435,254227611154925786404809⟩,⟨0,465437836716595859731⟩⟩
def cert23 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0002.cert23,⟨253762528249281577445180,253762534847889452750342⟩,⟨0,465440128390910736405⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert16,cert17,cert18,cert19,cert20,cert21,cert22,cert23]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0002.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell16,ReferenceCumulativeData.CoarseLowerShapeTime.cell17,ReferenceCumulativeData.CoarseLowerShapeTime.cell18,ReferenceCumulativeData.CoarseLowerShapeTime.cell19,ReferenceCumulativeData.CoarseLowerShapeTime.cell20,ReferenceCumulativeData.CoarseLowerShapeTime.cell21,ReferenceCumulativeData.CoarseLowerShapeTime.cell22,ReferenceCumulativeData.CoarseLowerShapeTime.cell23] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0002

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0003
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert24 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0003.cert24,⟨253297295514791618824402,253297302105680719330617⟩,⟨0,465597091463469117511⟩⟩
def cert25 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0003.cert25,⟨252832060525222756951574,252832067108405426026704⟩,⟨0,465599569583440714600⟩⟩
def cert26 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0003.cert26,⟨252314947895089577406551,252314954467710859337520⟩,⟨0,517563461595788716223⟩⟩
def cert27 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0003.cert27,⟨251797832239268313061600,251797838801346969802095⟩,⟨0,517566794068133440516⟩⟩
def cert28 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0003.cert28,⟨251332260508141752853870,251332267062548435833725⟩,⟨0,465937681626911604968⟩⟩
def cert29 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0003.cert29,⟨250866686130994653699439,250866692677741630967141⟩,⟨0,465940551841690299846⟩⟩
def cert30 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0003.cert30,⟨250279613475164485086521,250279620006578876339638⟩,⟨0,587655520035857622176⟩⟩
def cert31 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0003.cert31,⟨249692536284153812972680,249692542800266509450105⟩,⟨0,587660505586818990001⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert24,cert25,cert26,cert27,cert28,cert29,cert30,cert31]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0003.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell24,ReferenceCumulativeData.CoarseLowerShapeTime.cell25,ReferenceCumulativeData.CoarseLowerShapeTime.cell26,ReferenceCumulativeData.CoarseLowerShapeTime.cell27,ReferenceCumulativeData.CoarseLowerShapeTime.cell28,ReferenceCumulativeData.CoarseLowerShapeTime.cell29,ReferenceCumulativeData.CoarseLowerShapeTime.cell30,ReferenceCumulativeData.CoarseLowerShapeTime.cell31] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0003
