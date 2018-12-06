#Example 1 (Section 7.5.1)
#Last updated: December 5, 2018

def find_Q(C,P):
    i = 0
    try:
        p = P[1].parent().prime()
    except AttributeError:
        p = P[1].parent().order()
    while True:
        try:
            Q = C.lift_x(ZZ(P[0]) + i*p)
            break
        except ValueError:
            i += 1
    try:
        if ZZ(Q[1][0]) != ZZ(P[1][0]):
            Q = C(Q[0],-Q[1])
    except TypeError:
        if ZZ(Q[1][0]) != ZZ(P[1]):
            Q = C(Q[0],-Q[1])
    return Q

def prune(D):
    newlist=[]
    p = D[-1][0].parent().order()
    GFp = GF(p)
    XD = D[0].parent()
    for x in D:
        if XD(x[0],-x[1]) not in newlist and XD(-x[0],x[1]) not in newlist and XD(-x[0],-x[1]) not in newlist:
            if x[2]!=0:
                newlist.append(x)
    return newlist

def F1_eval(z0,Jz0,Iz0,mI0):
    return Jz0[1] - Jz0[5] + 1/2*Iz0[0]*mI0[1]

def F2_eval(z0,Jz0,Iz0,mI0):
    return 2*(-Jz0[3] + a*Jz0[7] + 2*Jz0[9]) - 1/2*z0[0] - Iz0[0]*mI0[3]

def qc2(a, z0, p, prec):
    R.<x> = QQ['x']
    X = HyperellipticCurve(x^6 +a*x^4 + a*x^2 + 1)
    K = Qp(p,prec)
    H1K = HyperellipticCurve(x^3 + a*x^2 + a*x + 1).change_ring(K)
    XK = X.change_ring(K)
    b = XK(0,1)
    mb = XK(0,-1)
    mI0 =  XK.coleman_integrals_on_basis(mb,b)
    Jz0 = XK.double_integrals_on_basis(b,z0)
    Iz0 = XK.coleman_integrals_on_basis(b,z0)
    F1z0 = F1_eval(z0, Jz0,Iz0,mI0)
    F2z0 = F2_eval(z0, Jz0, Iz0, mI0)

    disks = X.change_ring(GF(p)).rational_points()
    disks=prune(disks)
    for D in disks:
        print 50*'-'
        if D[1] != 0 and D[2] != 0:
            print 'working in disk %s'%D
            Q = find_Q(XK,D)
            if D[0] == 0:
                Q = find_Q(XK,D)
            Dz = XK.double_integrals_on_basis_to_z(b, Q)
            Iz = XK.coleman_integrals_on_basis_to_z(b,Q)
            z = Dz.base_ring().gens()[0]
            xx,yy = XK.local_coord(Q,prec)
            xx = xx(z)
            F2z = 2*(-Dz[3] + a*Dz[7] + 2*Dz[9]) - 1/2*xx -Iz[0]*mI0[3]
            F1z = Dz[1] - Dz[5] +1/2*Iz[0]*mI0[1]
            rhoz = F1z*F2z0-F1z0*F2z
            val = min([x.valuation() for x in rhoz.list()])
            rhoz = rhoz*p**(-val)
            if rhoz.valuation() > 0:
                t = rhoz.parent().gen()
                try:
                    rhoz = (rhoz/t**rhoz.valuation()).power_series().polynomial()
                except AttributeError:
                    rhoz = (rhoz/t**rhoz.valuation()).polynomial()
                roots = gp.polrootspadic(rhoz,p,prec)
                roots_new = [(sage_eval('%s'%roots[i+1])).add_bigoh(prec-5) for i in range(len(roots))]
                roots_new = [0] + [x for x in roots_new if x.valuation() > 0]
            else:
                try:
                    roots = gp.polrootspadic(rhoz,p,prec-5)
                except TypeError:
                    try:
                        rhoz = rhoz.power_series().polynomial()
                    except AttributeError:
                        rhoz = rhoz.polynomial()
                    roots = gp.polrootspadic(rhoz,p,prec-5)
                roots_new = [(sage_eval('%s'%roots[i+1])).add_bigoh(prec-5) for i in range(len(roots))]
                roots_new = [x for x in roots_new if x.valuation() > 0]
            for r in roots_new:
                r = XK(xx(r),yy(r))
                print 'pt on XK: ', r
        elif D[1] == 0 or D[2] == 0:
            print 'passing on disk at %s'%D


a = 31
p = 3
prec = 15
R.<x> = QQ['x']
X = HyperellipticCurve(x^6 +a*x^4 + a*x^2 + 1)
K = Qp(p,prec)
XK = X.change_ring(K)
z0 = XK(-7,440)
qc2(a, z0, p, prec)
