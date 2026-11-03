import OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Bundle0076_0079
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0077_0080
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0081_0084

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0080
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert640 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0080.cert640,⟨52786200458505998392417,52786201830565571573015⟩,⟨0,1176175866696569815816⟩⟩
def cert641 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0080.cert641,⟨51611595695269100627607,51611597023803946120408⟩,⟨0,1176226514421666267264⟩⟩
def cert642 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0080.cert642,⟨50493087126727892017232,50493088417749634995571⟩,⟨0,1119986079321950408318⟩⟩
def cert643 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0080.cert643,⟨49374534978991491672950,49374536232817044525833⟩,⟨0,1120031203188096265781⟩⟩
def cert644 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0080.cert644,⟨48569378975738802929445,48569380215781292426387⟩,⟨0,805925248171964033401⟩⟩
def cert645 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0080.cert645,⟨47764200710324066338907,47764201936669505124615⟩,⟨0,805948090258983564174⟩⟩
def cert646 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0080.cert646,⟨46694013250157278251305,46694014444218156033843⟩,⟨0,1071553029270085329606⟩⟩
def cert647 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0080.cert647,⟨45623787005564558753141,45623788167611654950645⟩,⟨0,1071593185108574553667⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert640,cert641,cert642,cert643,cert644,cert645,cert646,cert647]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0080.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell640,ReferenceCumulativeData.CoarseLowerShapeTime.cell641,ReferenceCumulativeData.CoarseLowerShapeTime.cell642,ReferenceCumulativeData.CoarseLowerShapeTime.cell643,ReferenceCumulativeData.CoarseLowerShapeTime.cell644,ReferenceCumulativeData.CoarseLowerShapeTime.cell645,ReferenceCumulativeData.CoarseLowerShapeTime.cell646,ReferenceCumulativeData.CoarseLowerShapeTime.cell647] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0080

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0081
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert648 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0081.cert648,⟨44876627985370421542663,44876629136601938842245⟩,⟨0,747827607956710190592⟩⟩
def cert649 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0081.cert649,⟨44129450316926885107652,44129451457407819562493⟩,⟨0,747846725752967457934⟩⟩
def cert650 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0081.cert650,⟨43032051243399627640238,43032052349635434614627⟩,⟨0,1098848295541435646551⟩⟩
def cert651 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0081.cert651,⟨41934612496357375749083,41934613568653016504049⟩,⟨0,1098889467363136482925⟩⟩
def cert652 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0081.cert652,⟨40840153025968036760528,40840154064655617096294⟩,⟨0,1095908937352242656662⟩⟩
def cert653 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0081.cert653,⟨39745654745474288255932,39745655750858894967664⟩,⟨0,1095949245519783434017⟩⟩
def cert654 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0081.cert654,⟨38705113876012177619257,38705114852861791079502⟩,⟨0,1041858105057076781598⟩⟩
def cert655 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0081.cert655,⟨37664538493657259809701,37664539442223914623647⟩,⟨0,1041893915199315219341⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert648,cert649,cert650,cert651,cert652,cert653,cert654,cert655]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0081.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell648,ReferenceCumulativeData.CoarseLowerShapeTime.cell649,ReferenceCumulativeData.CoarseLowerShapeTime.cell650,ReferenceCumulativeData.CoarseLowerShapeTime.cell651,ReferenceCumulativeData.CoarseLowerShapeTime.cell652,ReferenceCumulativeData.CoarseLowerShapeTime.cell653,ReferenceCumulativeData.CoarseLowerShapeTime.cell654,ReferenceCumulativeData.CoarseLowerShapeTime.cell655] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0081

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0082
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert656 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0082.cert656,⟨36874922334629526479568,36874923270922220175223⟩,⟨0,790378152186863553175⟩⟩
def cert657 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0082.cert657,⟨36085286578570962867584,36085287502674129216683⟩,⟨0,790398319682851347137⟩⟩
def cert658 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0082.cert658,⟨35393845643142991610640,35393846559091387560975⟩,⟨0,692027401420774765456⟩⟩
def cert659 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0082.cert659,⟨34702389851548809953112,34702390759392473778776⟩,⟨0,692042642637788687051⟩⟩
def cert660 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0082.cert660,⟨33690092009549623097222,33690092891843701714590⟩,⟨0,1013555576192258566929⟩⟩
def cert661 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0082.cert661,⟨32677762741775564481327,32677763598695268065839⟩,⟨0,1013588179960365088731⟩⟩
def cert662 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0082.cert662,⟨31373762305549788924854,31373763107921876688980⟩,⟨0,1306099893509292979561⟩⟩
def cert663 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0082.cert663,⟨30069710658265627247886,30069711406577496535402⟩,⟨0,1306153645344268651764⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert656,cert657,cert658,cert659,cert660,cert661,cert662,cert663]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0082.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell656,ReferenceCumulativeData.CoarseLowerShapeTime.cell657,ReferenceCumulativeData.CoarseLowerShapeTime.cell658,ReferenceCumulativeData.CoarseLowerShapeTime.cell659,ReferenceCumulativeData.CoarseLowerShapeTime.cell660,ReferenceCumulativeData.CoarseLowerShapeTime.cell661,ReferenceCumulativeData.CoarseLowerShapeTime.cell662,ReferenceCumulativeData.CoarseLowerShapeTime.cell663] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0082

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0083
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert664 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0083.cert664,⟨29160268167427014476502,29160268897555090107911⟩,⟨0,910469217372344928956⟩⟩
def cert665 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0083.cert665,⟨28250801199773636089695,28250801911834736847597⟩,⟨0,910494562760316077728⟩⟩
def cert666 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0083.cert666,⟨27473471487412322581833,27473472188227715861531⟩,⟨0,778082966620674377154⟩⟩
def cert667 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0083.cert667,⟨26696124132144723541722,26696124821777331233579⟩,⟨0,778101155231625142903⟩⟩
def cert668 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0083.cert668,⟨25276246566008452535900,25276247186583853661382⟩,⟨0,1422405416865833002361⟩⟩
def cert669 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0083.cert669,⟨23856311165813394721141,23856311718037670886078⟩,⟨0,1422466607145363319812⟩⟩
def cert670 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0083.cert670,⟨23084656927278602026935,23084657468694810534857⟩,⟨0,772404810787550733734⟩⟩
def cert671 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0083.cert671,⟨22312985909186566822186,22312986439857185002103⟩,⟨0,772422133033126356757⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert664,cert665,cert666,cert667,cert668,cert669,cert670,cert671]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0083.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell664,ReferenceCumulativeData.CoarseLowerShapeTime.cell665,ReferenceCumulativeData.CoarseLowerShapeTime.cell666,ReferenceCumulativeData.CoarseLowerShapeTime.cell667,ReferenceCumulativeData.CoarseLowerShapeTime.cell668,ReferenceCumulativeData.CoarseLowerShapeTime.cell669,ReferenceCumulativeData.CoarseLowerShapeTime.cell670,ReferenceCumulativeData.CoarseLowerShapeTime.cell671] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0083
