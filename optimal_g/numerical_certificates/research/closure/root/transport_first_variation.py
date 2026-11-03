"""Enclose the explicit transported witness's full first variation.

This is a residual certificate, NOT stationarity or an optimality proof.
Uses the companion verifier's exact rational reference and interval algebra.
"""
import argparse
import json
import sys
from pathlib import Path
from fractions import Fraction as F
import numpy as np

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'global'))
from interval_warped_hessian import I,J,Reference,split_cells,prepare_flow,numerators
from flow_scalar_sensitivity import propagate_scalar_sensitivity

def run(subdivisions,path,certificate,retained_density):
    cert=json.loads(Path(certificate).read_text())
    assert cert['reference']==path
    assert cert['high_cells_verified']==cert['high_cells_total']
    scalar_coercivity=I(cert['scalar_margin_if_terminal_curvature_650'])/2
    positional_loss=I(cert['one_endpoint_rank_loss_upper'])
    assert scalar_coercivity.lo>0
    ref=Reference(path)
    cells=split_cells(ref,subdivisions)
    flow=prepare_flow(ref,cells)
    start=F(flow['z0']); end=F(flow['zend'])
    scalar=I(0)
    events={ref.c:[],ref.rc:[]}
    for cell in cells:
        left,right=cell['left'],cell['right']
        ri=I(I(left['r']).lo,I(right['r']).hi)
        ai=I(I(left['a']).lo,I(right['a']).hi)
        zi=I(I(left['z']).lo,I(right['z']).hi)
        S,r,a=J.var(I(ref.S),0),J.var(ri,1),J.var(ai,2)
        warp=-(zi-I(start))/I(end-start)
        dwarp=I(-1/(end-start))
        z=J(zi)+(S-I(ref.S))*warp
        R=J(cell['rdata']['F'])+(S-I(ref.S))*cell['rdata']['u']
        D,N=numerators(I(ref.L),I(F('.135')),cell['branch'],S,r,a,R,z)
        weights=cell['weights'];total=sum(weights,I(0))
        grad=-(D.g/D.v)*total
        for n,w in zip(N,weights):
            grad=grad+(n.g/n.v)*w
        datasets=([cell['adata']]*2 if cell['branch']=='early' else
                  [cell['rdata'],cell['adata'],cell['rdata'],cell['adata']])
        gs=grad.take(0)+total*dwarp
        for data,w in zip(datasets,weights):
            gs=gs+w*data['du']/data['phi']
        scalar=scalar+gs*I(cell['dz'])
        # Push both positional coefficients and the negative derivative
        # coefficient to rank. Scores below c have fixed transported ranks.
        fluxes=({'r':I(0),'a':total} if cell['branch']=='early' else
                {'r':weights[0]+weights[2],'a':weights[1]+weights[3]})
        for index,key in [(1,'r'),(2,'a')]:
            lo,hi=left[key],right[key]
            if hi<=ref.c:continue
            assert lo>=ref.c and hi<=ref.rc
            slope=I((hi-lo)/cell['dz'])
            positional=grad.take(index)/slope
            derivative=fluxes[key]/slope
            events.setdefault(lo,[]).append((1,positional,derivative))
            events.setdefault(hi,[]).append((-1,positional,derivative))

    # Terminal logarithmic barrier derivative includes dz/dS=-1.
    L,S,q,z=ref.L,ref.S,F(str(ref.raw['terminal_q'])),end
    Q=lambda t:L*t-t*t/2
    N=Q(1-z+q)-S-ref.rat_F(q)
    B=z*N/(L-q)
    Bs=z*(-1+L/(1-q))/(L-q)
    Bz=(N-z*(L-1+z-q))/(L-q)
    Zbar=F('.135')-S-B
    bprime=(-1-Bs+Bz)/Zbar
    scalar=scalar-I(bprime)
    scalar_adjoint=scalar
    sensitivity=propagate_scalar_sensitivity(ref,cells,flow)
    scalar_direct=I(*sensitivity['scalar_residual'])
    assert max(float(scalar.lo),float(scalar_direct.lo))<=min(float(scalar.hi),float(scalar_direct.hi))
    scalar=I(max(float(scalar.lo),float(scalar_direct.lo)),min(float(scalar.hi),float(scalar_direct.hi)))

    locations=sorted(events)
    rankcells=[]
    for lo,hi in zip(locations,locations[1:]):
        rankcells.append((lo,hi))
    active={}; records=[]
    for lo,hi in rankcells:
        for sign,p,w in events[lo]:
            key=(id(p),id(w))
            if sign>0: active[key]=(p,w)
            else: del active[key]
        pos=sum((pw[0] for pw in active.values()),I(0))
        der=sum((pw[1] for pw in active.values()),I(0))
        records.append({'lo':lo,'hi':hi,'pos':pos,'der':der})
    tail=I(0); residual=[]
    for record in reversed(records):
        width=I(record['hi']-record['lo'])
        extra=record['pos']*width
        inside=I(min(0,float(extra.lo)),max(0,float(extra.hi)))
        R=tail+inside-record['der']
        record['P']=tail+inside
        residual.append((record,R))
        tail=tail+extra
    rlo=min(float(x.lo) for _,x in residual)
    rhi=max(float(x.hi) for _,x in residual)
    center=min(0.,(rlo+rhi)/2)
    centered=I(rlo,rhi)-I(center)
    radius=max(abs(float(centered.lo)),abs(float(centered.hi)))
    ell=I(ref.rc-ref.c)
    A=I(max(abs(float(scalar.lo)),abs(float(scalar.hi))))
    Bdual=I(radius)*(2*ell).sqrt()
    # log(Z/Zbar)>=1-Zbar/Z. This is a one-sided lower bound on the
    # reference violation; its interval overestimation is retained.
    Zterm=I(*flow['Zterminal'])
    E_lower=I(1)-I(Zbar)/Zterm
    full_rank_coercivity=I(cert['covered_rank_margin_lower'])
    budget=I(max(0.,-float(E_lower.lo)))+A.square()/(4*scalar_coercivity)+Bdual.square()/(4*full_rank_coercivity)
    # Retain W0 times reciprocal entropy for coercivity; use the remainder
    # to absorb the nonstationary flux locally. For w=W-W0, a=P-k-W0>0,
    # w(ξ-1-log ξ)+(P-W-k)(ξ-1) >= -(w-a)^2/a.
    # Unlike a sup norm, its rank integral captures narrow interface defects.
    W0=I(F(retained_density))
    Wmin=min(float(rec['der'].lo) for rec,_ in residual)
    assert Wmin>float(F(retained_density))
    best=None
    RI=I(np.array([float(v.lo) for _,v in residual]),np.array([float(v.hi) for _,v in residual]))
    PI=I(np.array([float(rec['P'].lo) for rec,_ in residual]),np.array([float(rec['P'].hi) for rec,_ in residual]))
    widths=[I(rec['hi']-rec['lo']) for rec,_ in residual]
    WI=I(np.array([float(v.lo) for v in widths]),np.array([float(v.hi) for v in widths]))
    def flux_error(kk):
        k=I(float(kk));a=PI-k-W0
        if np.any(a.lo<=0):return None
        terms=(RI-k).square()/a*WI
        # All terms are positive. n binary64 additions have relative error
        # at most n*u/(1-n*u); the larger n*eps bound safely includes the
        # library reduction order. Division below encloses the exact sum.
        n=len(residual)
        error=I(0,float((I(float(np.sum(terms.hi)))/(I(1)-I(n)*I(F(1,2**52)))).hi))
        return error
    for kk in np.linspace(-80,-5,301):
        error=flux_error(kk)
        if error is not None and (best is None or error.hi<best[1].hi):best=(float(kk),error)
    assert best is not None
    step=.25
    for _ in range(4):
        for kk in np.linspace(best[0]-step,min(0,best[0]+step),21):
            error=flux_error(kk)
            if error is not None and error.hi<best[1].hi:best=(float(kk),error)
        step/=10
    assert best is not None
    rank_coercivity=I(F(8,9))*W0-positional_loss
    assert rank_coercivity.lo>0
    error=best[1]
    # Retain the sign of the reference violation for a global infeasibility
    # certificate. The localization radii below deliberately discard a
    # positive violation, but the completed-square lower bound need not.
    calibrated_lower=E_lower-error-A.square()/(4*scalar_coercivity)
    localization_budget=I(max(0.,-float(E_lower.lo)))+error+A.square()/(4*scalar_coercivity)
    Jupper=localization_budget/rank_coercivity
    Sradius=(A+(A.square()+4*scalar_coercivity*(I(max(0.,-float(E_lower.lo)))+error)).sqrt())/(2*scalar_coercivity)
    rankradius=(2*ell*Jupper).sqrt()
    answer={'status':'interval first-variation enclosure; not an optimum',
            'reference':path,'coefficient_certificate':certificate,'subdivisions':subdivisions,'cells':len(cells),
            'flow':flow,'terminal_Zbar':float(Zbar),'terminal_bprime':float(bprime),
            'scalar_residual':scalar.bounds(),'scalar_adjoint_enclosure':scalar_adjoint.bounds(),
            'scalar_direct_sensitivity':sensitivity,'flux_range':[rlo,rhi],
            'favorable_constant_flux':center,'flux_sup_residual':radius,
            'energy_dual_residual_upper':float(Bdual.hi),
            'reference_violation_lower':float(E_lower.lo),
            'completed_square_budget_upper':float(budget.hi),
            'entropy_flux_absorption':{
                'retained_entropy_density':retained_density,'reference_density_lower':Wmin,
                'favorable_constant_flux':best[0],'defect_integral_upper':float(error.hi),
                'remaining_rank_coercivity_lower':float(rank_coercivity.lo),
                'calibrated_global_lower':float(calibrated_lower.lo),
                'localization_budget_upper':float(localization_budget.hi),
                'S_distance_upper':float(Sradius.hi),'J_upper':float(Jupper.hi),
                'rank_sup_distance_upper':float(rankradius.hi)}}
    return answer

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--subdivisions',type=int,default=2)
    parser.add_argument('--reference',default='research/closure/global/warped_interval_reference_extended.json')
    parser.add_argument('--certificate',default='research/closure/global/warped_interval_certificate_extended.json')
    parser.add_argument('--retained-density',default='3')
    parser.add_argument('--output',default='research/closure/root/transport_first_variation.json')
    args=parser.parse_args()
    result=run(args.subdivisions,args.reference,args.certificate,args.retained_density)
    Path(args.output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
