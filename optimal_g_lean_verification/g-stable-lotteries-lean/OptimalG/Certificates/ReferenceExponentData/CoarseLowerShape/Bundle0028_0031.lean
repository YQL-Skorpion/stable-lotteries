import OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Bundle0024_0027
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0025_0028
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0029_0032

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0028
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert224 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0028.cert224,⟨177496633595051250939807,177496638741131199720688⟩,⟨0,227550767193541259006⟩⟩
def cert225 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0028.cert225,⟨177269211037339968105950,177269216178846934797597⟩,⟨0,227559704520216429321⟩⟩
def cert226 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0028.cert226,⟨177001890089131092832845,177001895223214145076761⟩,⟨0,267510566826059490519⟩⟩
def cert227 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0028.cert227,⟨176734556715810677034545,176734561842474666856066⟩,⟨0,267523093891797313713⟩⟩
def cert228 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0028.cert228,⟨176456225901791135623032,176456231020088454931162⟩,⟨0,278536600672655218967⟩⟩
def cert229 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0028.cert229,⟨176177881424390925581568,176177886534327244329137⟩,⟨0,278550379382260782681⟩⟩
def cert230 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0028.cert230,⟨176027227740380301639808,176027232848993412290983⟩,⟨0,150714013100811124927⟩⟩
def cert231 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0028.cert231,⟨175876570008857104158013,175876575116147490012876⟩,⟨0,150718078924375810183⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert224,cert225,cert226,cert227,cert228,cert229,cert230,cert231]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0028.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell224,ReferenceCumulativeData.CoarseLowerShapeTime.cell225,ReferenceCumulativeData.CoarseLowerShapeTime.cell226,ReferenceCumulativeData.CoarseLowerShapeTime.cell227,ReferenceCumulativeData.CoarseLowerShapeTime.cell228,ReferenceCumulativeData.CoarseLowerShapeTime.cell229,ReferenceCumulativeData.CoarseLowerShapeTime.cell230,ReferenceCumulativeData.CoarseLowerShapeTime.cell231] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0028

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0029
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert232 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0029.cert232,⟨175796771086068964225955,175796776193162993907141⟩,⟨0,79815853211625692257⟩⟩
def cert233 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0029.cert233,⟨175716971020994564190928,175716976127892275944203⟩,⟨0,79816998220188477016⟩⟩
def cert234 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0029.cert234,⟨175521858892944014519114,175521863996970363721086⟩,⟨0,195213426002684745251⟩⟩
def cert235 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0029.cert235,⟨175326739888162259913917,175326744989318612278168⟩,⟨0,195220342594997570579⟩⟩
def cert236 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0029.cert236,⟨175288341826309221716330,175288346927443741292725⟩,⟨0,38401971025063425305⟩⟩
def cert237 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0029.cert237,⟨175249943496555722971338,175249948597668411797699⟩,⟨0,38402239229182023601⟩⟩
def cert238 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0029.cert238,⟨175002460453117320660286,175002465548376353854593⟩,⟨0,247645599707243322623⟩⟩
def cert239 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0029.cert239,⟨174754966200874741071858,174754971290283637584075⟩,⟨0,247656889988394554435⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert232,cert233,cert234,cert235,cert236,cert237,cert238,cert239]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0029.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell232,ReferenceCumulativeData.CoarseLowerShapeTime.cell233,ReferenceCumulativeData.CoarseLowerShapeTime.cell234,ReferenceCumulativeData.CoarseLowerShapeTime.cell235,ReferenceCumulativeData.CoarseLowerShapeTime.cell236,ReferenceCumulativeData.CoarseLowerShapeTime.cell237,ReferenceCumulativeData.CoarseLowerShapeTime.cell238,ReferenceCumulativeData.CoarseLowerShapeTime.cell239] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0029

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0030
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert240 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0030.cert240,⟨174649891795480147404976,174649896884442223430364⟩,⟨0,105103720548307478582⟩⟩
def cert241 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0030.cert241,⟨174544815351927780830105,174544820440443149986955⟩,⟨0,105105764946618865269⟩⟩
def cert242 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0030.cert242,⟨174526136134410031367754,174526141222922893565099⟩,⟨0,18680143529992022682⟩⟩
def cert243 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0030.cert243,⟨174507456852285767551933,174507461940796122902921⟩,⟨0,18680208171563443247⟩⟩
def cert244 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0030.cert244,⟨174329249590816937409098,174329254677147841914939⟩,⟨0,178291610421832481804⟩⟩
def cert245 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0030.cert245,⟨174151036420320652108988,174151041504473043882007⟩,⟨0,178297549940468615522⟩⟩
def cert246 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0030.cert246,⟨174081719633444531590963,174081724717468906681775⟩,⟨0,69329547855339057033⟩⟩
def cert247 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0030.cert247,⟨174012401947176424932492,174012407031072799534806⟩,⟨0,69330449042140475678⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert240,cert241,cert242,cert243,cert244,cert245,cert246,cert247]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0030.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell240,ReferenceCumulativeData.CoarseLowerShapeTime.cell241,ReferenceCumulativeData.CoarseLowerShapeTime.cell242,ReferenceCumulativeData.CoarseLowerShapeTime.cell243,ReferenceCumulativeData.CoarseLowerShapeTime.cell244,ReferenceCumulativeData.CoarseLowerShapeTime.cell245,ReferenceCumulativeData.CoarseLowerShapeTime.cell246,ReferenceCumulativeData.CoarseLowerShapeTime.cell247] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0030

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0031
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert248 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0031.cert248,⟨173890397850399563878105,173890402933597481473830⟩,⟨0,122043661409986854479⟩⟩
def cert249 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0031.cert249,⟨173768390953712911697670,173768396036212527409001⟩,⟨0,122046471122795305794⟩⟩
def cert250 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0031.cert250,⟨173576032011138663161116,173576037090900730901055⟩,⟨0,192457335125672135982⟩⟩
def cert251 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0031.cert251,⟨173383666055531928104119,173383671132557402212391⟩,⟨0,192464386625990712316⟩⟩
def cert252 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0031.cert252,⟨173079385678882996437298,173079390745064793951173⟩,⟨0,304526954069753334290⟩⟩
def cert253 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0031.cert253,⟨172775087538940272283782,172775092594284332783268⟩,⟨0,304544870095789699932⟩⟩
def cert254 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0031.cert254,⟨172558633105282079620760,172558638156728822974640⟩,⟨0,216579350633661877279⟩⟩
def cert255 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0031.cert255,⟨172342169569572426692863,172342174617123357184852⟩,⟨0,216588507783590441016⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert248,cert249,cert250,cert251,cert252,cert253,cert254,cert255]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0031.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell248,ReferenceCumulativeData.CoarseLowerShapeTime.cell249,ReferenceCumulativeData.CoarseLowerShapeTime.cell250,ReferenceCumulativeData.CoarseLowerShapeTime.cell251,ReferenceCumulativeData.CoarseLowerShapeTime.cell252,ReferenceCumulativeData.CoarseLowerShapeTime.cell253,ReferenceCumulativeData.CoarseLowerShapeTime.cell254,ReferenceCumulativeData.CoarseLowerShapeTime.cell255] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0031
