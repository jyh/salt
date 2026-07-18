import math

def sieve(n):
    pr=[True]*(n+1); pr[0]=pr[1]=False
    for i in range(2,int(n**.5)+1):
        if pr[i]:
            for j in range(i*i,n+1,i): pr[j]=False
    return [i for i in range(2,n+1) if pr[i]]

def mobius(d):
    m=1; x=d
    p=2
    while p*p<=x:
        if x%p==0:
            x//=p
            if x%p==0: return 0
            m=-m
        p+=1
    if x>1: m=-m
    return m

def theta(z,d):
    if d>z: return 0.0
    m=mobius(d)
    if m==0: return 0.0
    return m*math.log(z/d)/math.log(z)

def wsum(z,n):
    return sum(theta(z,d) for d in range(1,n+1) if n%d==0)

z=50
tests = {
 "n=7 (prime<=z)": (7, math.log(7)/math.log(z)),
 "n=49=7^2": (49, math.log(7)/math.log(z)),
 "n=343=7^3": (343, math.log(7)/math.log(z)),
 "n=6=2*3 (rad<=z)": (6, 0.0),
 "n=30=2*3*5": (30, 0.0),
 "n=12=2^2*3": (12, 0.0),
 "n=53 (prime>z)": (53, 1.0),
 "n=2809=53^2 (p>z)": (2809, 1.0),
 "n=159=3*53 (band)": (159, math.log(3)/math.log(z)),
}
print("== identity checks (z=50) ==")
for k,(n,pred) in tests.items():
    print(f"{k}: w={wsum(z,n):.6f} predicted={pred:.6f}")
print(f"n=35, z=6: w={wsum(6,35):.6f} pred(log5/log6)={math.log(5)/math.log(6):.6f}")
print(f"n=1001=7*11*13, z=10: w={wsum(10,1001):.6f} pred(1)={1.0}")
print(f"n=105=3*5*7>z^2, z=10: w={wsum(10,105):.6f} pred={-2+math.log(105)/math.log(10):.6f}  (NONZERO though n>z^2)")

print("\n== prime sum magnitudes (Mertens) ==")
for Z in [10**3, 10**5, 10**7]:
    ps=sieve(Z)
    s=sum(math.log(p)**2/p for p in ps)
    print(f"z={Z:.0e}: sum(logp)^2/p={s:.3f}  (logz)^2/2={math.log(Z)**2/2:.3f} ratio={s/(math.log(Z)**2/2):.4f}")

print("\n== worst-case prime piece (all chi(p)=1), 2 sum (logp/logz)^2 p^-b0 ==")
ps5=sieve(10**5)
for b0 in [1-1e-6, 1-1/(20*math.log(2e6))]:
    s=sum(2*(math.log(p)/math.log(10**5))**2*p**(-b0) for p in ps5)
    print(f"z=1e5, 1-b0={1-b0:.3e}: piece={s:.4f}")

print("\n== band primes z<p<=x, weight 1, dhA<=2: integral model 2*int_z^x t^(1-b0)/(t log t) ==")
def band(logz,logx,u1,steps=200000):
    h=(logx-logz)/steps; s=0.0
    for i in range(steps):
        u=logz+(i+0.5)*h
        s+=math.exp(u*u1)/u*h
    return 2*s
for b in [20,40]:
    lz=math.log(2e6); lx=b*lz
    print(f"x=X^{b}, 1-b0=1e-6: band-prime piece ~ {band(lz,lx,1e-6):.3f} (lower floor 2log(b)={2*math.log(b):.3f})")

print("\n== prime-power corrections (worst chi=1) z=1e5 b0~1 ==")
s=0.0
for p in ps5:
    w=(math.log(p)/math.log(10**5))**2
    a=2
    while True:
        t=(a+1)*w*p**(-a*(1-1e-6))
        s+=t
        if t<1e-18: break
        a+=1
print(f"sum = {s:.5f}")

print("\n== z=x^C variant worst-case bound x^(1-b0)/C^2 with x^(1-b0)<=5.7 ==")
for C in [2,3,5,6]:
    print(f"C={C}: 5.7/C^2 = {5.7/C**2:.3f}")

print("\n== sigma=9/10 direct: sum_{p<=x} 2(logp/logz)^2 p^-0.9 diverges like x^0.1; sample z=x=1e5 ==")
s=sum(2*(math.log(p)/math.log(10**5))**2*p**(-0.9) for p in ps5)
print(f"z=x=1e5, sigma=0.9: prime piece = {s:.2f}")
