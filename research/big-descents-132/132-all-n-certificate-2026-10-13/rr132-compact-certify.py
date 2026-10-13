"""Bounded exact dyadic interval proof probe; no polynomial sequence generation.
All arithmetic bounds are outward rounded. Floating point is only progress display.
"""
from fractions import Fraction as F
from math import isqrt
import json,time,sys
BITS=80;S=1<<BITS
class I:
 __slots__=('lo','hi')
 def __init__(self,x=0,y=None,raw=False):
  if raw:self.lo=x;self.hi=y;return
  x=F(x);y=x if y is None else F(y)
  self.lo=x.numerator*S//x.denominator;self.hi=-((-y.numerator*S)//y.denominator)
 def __add__(a,b):
  if not isinstance(b,I):b=I(b)
  return I(a.lo+b.lo,a.hi+b.hi,raw=True)
 __radd__=__add__
 def __neg__(a):return I(-a.hi,-a.lo,raw=True)
 def __sub__(a,b):return a+-cv(b)
 def __rsub__(a,b):return cv(b)+-a
 def __mul__(a,b):
  b=cv(b);v=[a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi]
  return I(min(v)//S,-((-max(v))//S),raw=True)
 __rmul__=__mul__
 def __truediv__(a,b):
  b=cv(b)
  if b.lo<=0<=b.hi:raise ZeroDivisionError
  v=[F(x*S,y) for x in (a.lo,a.hi) for y in (b.lo,b.hi)]
  lo=min(v);hi=max(v)
  return I(lo.numerator//lo.denominator,-((-hi.numerator)//hi.denominator),raw=True)
 def __rtruediv__(a,b):return cv(b)/a
 def __pow__(a,n):
  assert n>=0
  if n==0:return I(1)
  if n==2:
   vals=[a.lo*a.lo,a.hi*a.hi];lo=0 if a.lo<=0<=a.hi else min(vals)
   return I(lo//S,-((-max(vals))//S),raw=True)
  z=I(1);b=a
  while n:
   if n&1:z=z*b
   n//=2
   if n:b=b**2
  return z
 def sqrt(a):
  if a.lo<0:raise ValueError('negative sqrt')
  lo=isqrt(a.lo*S);hi=isqrt(a.hi*S)
  return I(lo,hi+(hi*hi<a.hi*S),raw=True)
 def serial(a):return [str(a.lo),str(a.hi)]
 def mid(a):return F(a.lo+a.hi,2*S)
 def __repr__(a):return f'[{a.lo/S:.6g},{a.hi/S:.6g}]'
def cv(x):return x if isinstance(x,I) else I(x)
class C:
 __slots__=('r','i')
 def __init__(self,r=0,i=0):self.r=cv(r);self.i=cv(i)
 def __add__(a,b):b=cc(b);return C(a.r+b.r,a.i+b.i)
 __radd__=__add__
 def __neg__(a):return C(-a.r,-a.i)
 def __sub__(a,b):return a+-cc(b)
 def __rsub__(a,b):return cc(b)+-a
 def __mul__(a,b):b=cc(b);return C(a.r*b.r-a.i*b.i,a.r*b.i+a.i*b.r)
 __rmul__=__mul__
 def norm(a):return a.r**2+a.i**2
 def __truediv__(a,b):b=cc(b);c=a*C(b.r,-b.i);d=b.norm();return C(c.r/d,c.i/d)
 def __rtruediv__(a,b):return cc(b)/a
 def __pow__(a,n):
  if n==2:return a*a
  z=C(1)
  for _ in range(n):z=z*a
  return z
def cc(x):return x if isinstance(x,C) else C(x)
def poly(q,x):return x**4+6*q*x*x+(4-4*q**3)*x-3*q*q
def roots(q):
 M=F(32)+16*F(q.hi,S)
 while poly(q,I(-M)).lo<=0 or poly(q,I(M)).lo<=0:M*=2
 # Separately obtain certified outer ends around the unique negative/positive root.
 out=[]
 for neg in [True,False]:
  lower=-M if neg else F(0);upper=F(0) if neg else M
  ends=[]
  for which in ['lo','hi']:
   l=lower;h=upper
   for _ in range(74):
    x=(l+h)/2;p=poly(q,I(x));before=(p.lo>0 if neg else p.hi<0) if which=='lo' else (not(p.hi<0) if neg else not(p.lo>0))
    if before:l=x
    else:h=x
   ends.append(l if which=='lo' else h)
  out.append(I(ends[0],ends[1]))
 return out

def setup(q):
 A,B=roots(q);U=-(A+B)/2;V2=6*q+3*A*A/4+A*B/2+3*B*B/4
 if V2.lo<=0:raise ValueError('V2')
 V=V2.sqrt();Z=C(U,V);lam=C(1)+C(q)*Z;s=1+q**3;a=1+q*A;b=1+q*B;r=lam.norm()
 da=Z-A;db=Z-B;dc=C(0,2*V);ds=Z-q*q
 D0=da*db*dc;S0=ds*ds
 return dict(A=A,B=B,U=U,V2=V2,lam=lam,s=s,a=a,b=b,r=r,da=da,db=db,dc=dc,ds=ds,D0=D0,S0=S0)
def kernel_cert(q,g,h0):
 # t=(1-u)/q, rectangular cover contains every needed (q,t).
 T=1/F(q.lo,S);queue=[(F(0),T)];leaves=[];work=0
 while queue:
  l,h=queue.pop();work+=1
  if work>12000:return None,work
  t=I(l,h);w=g['lam']*C(t)
  try:
   z=((g['da']-w)*(g['db']-w)*(g['dc']-w)*g['S0'])/(g['D0']*(g['ds']-w)**2)
   E=z.i**2+4*h0*h0*z.r-4*h0**4
  except (ZeroDivisionError,ValueError):E=I(-1)
  if E.lo>0:leaves.append([str(l),str(h),E.serial()]);continue
  if h-l<F(1,1<<22):return None,work
  mid=(l+h)/2;queue.append((l,mid));queue.append((mid,h))
 return leaves,work

def cert(ql,qh,N):
 q=I(ql,qh);h0=min(F(1,2),F(9,50)/(qh+F(1,5)))
 try:
  g=setup(q);a=g['a'];b=g['b'];s=g['s'];lam=g['lam'];r=g['r'];Da=(lam-a).norm();Db=(lam-b).norm();Ds=(lam-s).norm();V2actual=q*q*g['V2']
  D4=Db*(b-a)**2*Ds**2/(64*h0**4*Da*V2actual*r*b*b)
  rho2=b*b/r
  if rho2.hi>=S:return None,'rho'
  rho=I(rho2.hi, rho2.hi,raw=True).sqrt();ru=F(rho.hi,S)
  t=(3*ru-1)/(2*(1-ru));peak=max(N,-((-t.numerator)//t.denominator))
  bound=I(D4.hi,D4.hi,raw=True)*(2*peak+1)**4*I(ru)**(4*peak)
  if bound.hi>=S:return None,'moment'
  leaves,work=kernel_cert(q,g,h0)
  if leaves is None:return None,'kernel'
  return dict(q=[str(ql),str(qh)],h0=str(h0),roots=[g['A'].serial(),g['B'].serial()],peak=peak,D4=D4.serial(),rho_upper=str(ru),bound=bound.serial(),kernel=leaves,work=work),None
 except (ValueError,ZeroDivisionError):return None,'geometry'

if __name__=='__main__':
 N=int(sys.argv[1]) if len(sys.argv)>1 else 100
 left=F(sys.argv[2]) if len(sys.argv)>2 else F(1,200);right=F(sys.argv[3]) if len(sys.argv)>3 else F(8)
 queue=[];q=left
 while q<right:
  cand=q*F(101,100); grid=1<<32
  qn=min(right,F(-((-cand.numerator*grid)//cand.denominator),grid));queue.append((q,qn,0));q=qn
 queue.reverse();done=[];fail={};start=time.time();trials=0
 while queue:
  ql,qh,depth=queue.pop();trials+=1
  c,reason=cert(ql,qh,N)
  if c is not None:
   done.append(c)
   if len(done)%500==0:print('certified',len(done),'through',float(qh),'trials',trials,'seconds',round(time.time()-start,1),flush=True)
  else:
   fail[reason]=fail.get(reason,0)+1
   if depth>=18 or trials>30000:raise RuntimeError((ql,qh,reason,fail))
   mid=(ql+qh)/2;queue.append((mid,qh,depth+1));queue.append((ql,mid,depth+1))
  if time.time()-start>180:
   break
 path='/tmp/rr132-compact-certificate-full.json'
 json.dump(dict(status='partial' if queue else 'complete',bits=BITS,N=N,range=[str(left),str(right)],done=done,remaining=[[str(l),str(h),d] for l,h,d in queue],failures=fail,trials=trials),open(path,'w'))
 print('saved',path,'completed intervals',len(done),'remaining',len(queue),'failures',fail,'seconds',round(time.time()-start,1),flush=True)
