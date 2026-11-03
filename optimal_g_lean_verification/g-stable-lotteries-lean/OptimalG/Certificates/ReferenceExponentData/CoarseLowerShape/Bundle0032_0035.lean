import OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Bundle0028_0031
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0029_0032
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0033_0036

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0032
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert256 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0032.cert256,⟨172156665888801539181552,172156670933901323874914⟩,⟨0,185595513423199728110⟩⟩
def cert257 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0032.cert257,⟨171971155458742998314003,171971160501392442405707⟩,⟨0,185602297455299673355⟩⟩
def cert258 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0032.cert258,⟨171709571777992638062499,171709576813767080442666⟩,⟨0,261766514002086378687⟩⟩
def cert259 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0032.cert259,⟨171447974534505472171927,171447979563408076779257⟩,⟨0,261780174405143009553⟩⟩
def cert260 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0032.cert260,⟨171153213824737236917656,171153218843806027514904⟩,⟨0,294993195002377095816⟩⟩
def cert261 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0032.cert261,⟨170858435669565735285408,170858440678805765278221⟩,⟨0,295010780543493428538⟩⟩
def cert262 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0032.cert262,⟨170590563850816961550323,170590568852683328563112⟩,⟨0,268064078456539288057⟩⟩
def cert263 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0032.cert263,⟨170322677437438483545717,170322682431934555781943⟩,⟨0,268078778539850149578⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert256,cert257,cert258,cert259,cert260,cert261,cert262,cert263]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0032.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell256,ReferenceCumulativeData.CoarseLowerShapeTime.cell257,ReferenceCumulativeData.CoarseLowerShapeTime.cell258,ReferenceCumulativeData.CoarseLowerShapeTime.cell259,ReferenceCumulativeData.CoarseLowerShapeTime.cell260,ReferenceCumulativeData.CoarseLowerShapeTime.cell261,ReferenceCumulativeData.CoarseLowerShapeTime.cell262,ReferenceCumulativeData.CoarseLowerShapeTime.cell263] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0032

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0033
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert264 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0033.cert264,⟨170158001408255159490454,170158006401040846860400⟩,⟨0,164748751737954480684⟩⟩
def cert265 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0033.cert265,⟨169993319809212943706636,169993324800288724710948⟩,⟨0,164754346137467453120⟩⟩
def cert266 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0033.cert266,⟨169751449829333225091105,169751454814987565471195⟩,⟨0,242027042012516812430⟩⟩
def cert267 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0033.cert267,⟨169509567723590426965597,169509572703825532700066⟩,⟨0,242039245812485414312⟩⟩
def cert268 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0033.cert268,⟨169390212995781667607782,169390217975366449308406⟩,⟨0,119392895412242009454⟩⟩
def cert269 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0033.cert269,⟨169270855291501988766379,169270860270436576747287⟩,⟨0,119395881252010469502⟩⟩
def cert270 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0033.cert270,⟨169107035903956061807734,169107040881208825264635⟩,⟨0,163891346755933652761⟩⟩
def cert271 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0033.cert271,⟨168943210873944534619975,168943215849515932941213⟩,⟨0,163897013484427086998⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert264,cert265,cert266,cert267,cert268,cert269,cert270,cert271]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0033.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell264,ReferenceCumulativeData.CoarseLowerShapeTime.cell265,ReferenceCumulativeData.CoarseLowerShapeTime.cell266,ReferenceCumulativeData.CoarseLowerShapeTime.cell267,ReferenceCumulativeData.CoarseLowerShapeTime.cell268,ReferenceCumulativeData.CoarseLowerShapeTime.cell269,ReferenceCumulativeData.CoarseLowerShapeTime.cell270,ReferenceCumulativeData.CoarseLowerShapeTime.cell271] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0033

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0034
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert272 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0034.cert272,⟨168757951825359898276252,168757956798499333397637⟩,⟨0,185351158300457666070⟩⟩
def cert273 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0034.cert273,⟨168572685505384782337497,168572690476093000016388⟩,⟨0,185358464843630866246⟩⟩
def cert274 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0034.cert274,⟨168294849243729221058391,168294854206230030011121⟩,⟨0,278043703987206851028⟩⟩
def cert275 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0034.cert275,⟨168016996462205401965869,168017001416502530877618⟩,⟨0,278060342743055968594⟩⟩
def cert276 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0034.cert276,⟨167898559549516972824798,167898564503179714638293⟩,⟨0,118474633527426684123⟩⟩
def cert277 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0034.cert277,⟨167780119609331068963052,167780124562359546356021⟩,⟨0,118477670245486917442⟩⟩
def cert278 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0034.cert278,⟨167688771078697021863348,167688776031434565535423⟩,⟨0,91370981222033438293⟩⟩
def cert279 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0034.cert279,⟨167597420738950376873543,167597425691397030090775⟩,⟨0,91372794569367910423⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert272,cert273,cert274,cert275,cert276,cert277,cert278,cert279]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0034.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell272,ReferenceCumulativeData.CoarseLowerShapeTime.cell273,ReferenceCumulativeData.CoarseLowerShapeTime.cell274,ReferenceCumulativeData.CoarseLowerShapeTime.cell275,ReferenceCumulativeData.CoarseLowerShapeTime.cell276,ReferenceCumulativeData.CoarseLowerShapeTime.cell277,ReferenceCumulativeData.CoarseLowerShapeTime.cell278,ReferenceCumulativeData.CoarseLowerShapeTime.cell279] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0034

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0035
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert280 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0035.cert280,⟨167551412154028538847330,167551417106438051094827⟩,⟨0,46014280805091971821⟩⟩
def cert281 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0035.cert281,⟨167505403108885027665743,167505408061257401736796⟩,⟨0,46014741567934973874⟩⟩
def cert282 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0035.cert282,⟨167452349487551128688987,167452354439866549772731⟩,⟨0,53061197646428975589⟩⟩
def cert283 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0035.cert283,⟨167399295252941539945143,167399300205200012970418⟩,⟨0,53061811752456059892⟩⟩
def cert284 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0035.cert284,⟨167297275750510792408630,167297280702364139733394⟩,⟨0,102047531329381395026⟩⟩
def cert285 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0035.cert285,⟨167195253972860992302384,167195258924309281022720⟩,⟨0,102049812458454514032⟩⟩
def cert286 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0035.cert286,⟨167182320843627448116866,167182325795074912490522⟩,⟨0,12933579026650273732⟩⟩
def cert287 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0035.cert287,⟨167169387677743661440471,167169392629190301484774⟩,⟨0,12933615688927379687⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert280,cert281,cert282,cert283,cert284,cert285,cert286,cert287]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0035.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell280,ReferenceCumulativeData.CoarseLowerShapeTime.cell281,ReferenceCumulativeData.CoarseLowerShapeTime.cell282,ReferenceCumulativeData.CoarseLowerShapeTime.cell283,ReferenceCumulativeData.CoarseLowerShapeTime.cell284,ReferenceCumulativeData.CoarseLowerShapeTime.cell285,ReferenceCumulativeData.CoarseLowerShapeTime.cell286,ReferenceCumulativeData.CoarseLowerShapeTime.cell287] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0035
