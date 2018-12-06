"""
Hyperelliptic curves over a padic field.
"""
#*****************************************************************************
#  Copyright (C) 2007 Robert Bradshaw <robertwb@math.washington.edu>
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#*****************************************************************************
from __future__ import absolute_import
from six.moves import range

from . import hyperelliptic_generic

from sage.rings.all import PowerSeriesRing, PolynomialRing, ZZ, QQ, O, pAdicField, GF, RR, RationalField, Infinity
from sage.misc.functional import cyclotomic_polynomial
from sage.functions.all import log
from sage.modules.free_module import VectorSpace
from sage.matrix.constructor import matrix, identity_matrix
from sage.modules.all import vector
from sage.functions.other import binomial

class HyperellipticCurve_padic_field(hyperelliptic_generic.HyperellipticCurve_generic):

# The functions below were prototyped at the 2007 Arizona Winter School by
# Robert Bradshaw and Ralf Gerkmann, working with Miljan Brakovevic and
# Kiran Kedlaya
# All of the below is with respect to the Monsky Washnitzer cohomology.

    def local_analytic_interpolation(self, P, Q, prec = None):
        """
        For points $P$, $Q$ in the same residue disc,
        this constructs an interpolation from $P$ to $Q$ (in homogeneous coordinates)
        in a power series in the local parameter $t$, with precision equal
        to the $p$-adic precision of the underlying ring.


        INPUT:
            - P and Q points on self in the same residue disc

        OUTPUT:
            Returns a point $X(t) = ( x(t) : y(t) : z(t) )$ such that
            (1) $X(0) = P$ and $X(1) = Q$ if $P, Q$ are not in the infinite disc
            (2) $X(P[0]^g}/P[1]) = P$ and $X(Q[0]^g/Q[1]) = Q$ if $P, Q$ are in the infinite disc

        EXAMPLES:
            sage: R.<x> = QQ['x']
            sage: H = HyperellipticCurve(x^3-10*x+9)
            sage: K = Qp(5,8)
            sage: HK = H.change_ring(K)

        A non-Weierstrass disc:
            sage: P = HK(0,3)
            sage: Q = HK(5, 3 + 3*5^2 + 2*5^3 + 3*5^4 + 2*5^5 + 2*5^6 + 3*5^7 + O(5^8))
            sage: x,y,z, = HK.local_analytic_interpolation(P,Q)
            sage: x(0) == P[0], x(1) == Q[0], y(0) == P[1], y(1) == Q[1]
            (True, True, True, True)

        A finite Weierstrass disc
            sage: P = HK.lift_x(1 + 2*5^2)
            sage: Q = HK.lift_x(1 + 3*5^2)
            sage: x,y,z = HK.local_analytic_interpolation(P,Q)
            sage: x(0) == P[0], x(1) == Q[0], y(0) == P[1], y(1) == Q[1]
            (True, True, True, True)

        The infinite disc
            sage: P = HK.lift_x(5^-2)
            sage: Q = HK.lift_x(4*5^-2)
            sage: x,y,z = HK.local_analytic_interpolation(P,Q)
            sage: x = x/z
            sage: y = y/z
            sage: x(P[0]/P[1]) == P[0]
            True
            sage: x(Q[0]/Q[1]) == Q[0]
            True
            sage: y(P[0]/P[1]) == P[1]
            True
            sage: y(Q[0]/Q[1]) == Q[1]
            True

        An error if points are not in the same disc:
            sage: x,y,z = HK.local_analytic_interpolation(P,HK(1,0))
            Traceback (most recent call last):
            ...
            ValueError: (5^-2 + O(5^6) : 5^-3 + 4*5^2 + 5^3 + 3*5^4 + O(5^5) : 1 + O(5^8)) and (1 + O(5^8) : 0 : 1 + O(5^8)) are not in the same residue disc

        AUTHORS:
            - Robert Bradshaw (2007-03)
            - Jennifer Balakrishnan (2010-02)
        """
        prec = self.base_ring().precision_cap() + 2
        if self.is_same_disc(P,Q) == False:
            raise ValueError, "%s and %s are not in the same residue disk"%(P,Q)
        disc = self.residue_disc(P)
        t = PowerSeriesRing(self.base_ring(), 't', prec).gen(0)
        if disc == self.change_ring(self.base_ring().residue_field())(0,1,0):
            x,y = self.local_coordinates_at_infinity(2*prec)
            g = self.genus()
            return (x*t**(2*g+1),y*t**(2*g+1),t**(2*g+1))
        if disc[1] !=0:
            x = P[0]+t*(Q[0]-P[0])
            pts = self.lift_x(x, all=True)
            if pts[0][1][0] == P[1]:
                return pts[0]
            else:
                return pts[1]
        else:
            S = self.find_char_zero_weier_point(P)
            x,y = self.local_coord(S)
            a = P[1]
            b = Q[1] - P[1]
            y = a + b*t
            x = x(y)
            return (x, y, 1)

    def weierstrass_points(self):
        """
        Return the Weierstrass points of self defined over self.base_ring(),
        that is, the point at infinity and those points in the support
        of the divisor of `y`

        EXAMPLES::

            sage: K = pAdicField(11, 5)
            sage: x = polygen(K)
            sage: C = HyperellipticCurve(x^5 + 33/16*x^4 + 3/4*x^3 + 3/8*x^2 - 1/4*x + 1/16)
            sage: C.weierstrass_points()
            [(0 : 1 + O(11^5) : 0), (7 + 10*11 + 4*11^3 + O(11^5) : 0 : 1 + O(11^5))]
        """
        f, h = self.hyperelliptic_polynomials()
        if h != 0:
            raise NotImplementedError()
        return [self((0,1,0))] + [self((x, 0, 1)) for x in f.roots(multiplicities=False)]

    def is_in_weierstrass_disc(self,P):
        """
        Checks if `P` is in a Weierstrass disc

        EXAMPLES::

            sage: R.<x> = QQ['x']
            sage: H = HyperellipticCurve(x^3-10*x+9)
            sage: K = Qp(5,8)
            sage: HK = H.change_ring(K)
            sage: P = HK(0,3)
            sage: HK.is_in_weierstrass_disc(P)
            False
            sage: Q = HK(0,1,0)
            sage: HK.is_in_weierstrass_disc(Q)
            True
            sage: S = HK(1,0)
            sage: HK.is_in_weierstrass_disc(S)
            True
            sage: T = HK.lift_x(1+3*5^2); T
            (1 + 3*5^2 + O(5^8) : 2*5 + 4*5^3 + 3*5^4 + 5^5 + 3*5^6 + O(5^7) : 1 + O(5^8))
            sage: HK.is_in_weierstrass_disc(T)
            True

        AUTHOR:
           - Jennifer Balakrishnan (2010-02)
        """
        if (P[1].valuation() == 0 and P != self(0,1,0)):
            return False
        else:
            return True

    def is_weierstrass(self,P):
        """
        Checks if `P` is a Weierstrass point (i.e., fixed by the hyperelliptic involution)

        EXAMPLES::

            sage: R.<x> = QQ['x']
            sage: H = HyperellipticCurve(x^3-10*x+9)
            sage: K = Qp(5,8)
            sage: HK = H.change_ring(K)
            sage: P = HK(0,3)
            sage: HK.is_weierstrass(P)
            False
            sage: Q = HK(0,1,0)
            sage: HK.is_weierstrass(Q)
            True
            sage: S = HK(1,0)
            sage: HK.is_weierstrass(S)
            True
            sage: T = HK.lift_x(1+3*5^2); T
            (1 + 3*5^2 + O(5^8) : 2*5 + 4*5^3 + 3*5^4 + 5^5 + 3*5^6 + O(5^7) : 1 + O(5^8))
            sage: HK.is_weierstrass(T)
            False

        AUTHOR:
            - Jennifer Balakrishnan (2010-02)
        """
        if (P[1] == 0 or P[2] ==0):
            return True
        else:
            return False

    def find_char_zero_weier_point(self, Q):
        """
        Given `Q` a point on self in a Weierstrass disc, finds the
        center of the Weierstrass disc (if defined over self.base_ring())

        EXAMPLES::

            sage: R.<x> = QQ['x']
            sage: H = HyperellipticCurve(x^3-10*x+9)
            sage: K = Qp(5,8)
            sage: HK = H.change_ring(K)
            sage: P = HK.lift_x(1 + 2*5^2)
            sage: Q = HK.lift_x(5^-2)
            sage: S = HK(1,0)
            sage: T = HK(0,1,0)
            sage: HK.find_char_zero_weier_point(P)
            (1 + O(5^8) : 0 : 1 + O(5^8))
            sage: HK.find_char_zero_weier_point(Q)
            (0 : 1 + O(5^8) : 0)
            sage: HK.find_char_zero_weier_point(S)
            (1 + O(5^8) : 0 : 1 + O(5^8))
            sage: HK.find_char_zero_weier_point(T)
            (0 : 1 + O(5^8) : 0)

        AUTHOR:
            - Jennifer Balakrishnan
        """
        if not self.is_in_weierstrass_disc(Q):
            raise ValueError("%s is not in a Weierstrass disc"%Q)
        points = self.weierstrass_points()
        for P in points:
            if self.is_same_disc(P,Q):
                return P

    def residue_disc(self,P):
        """
        Gives the residue disc of `P`

        EXAMPLES::

            sage: R.<x> = QQ['x']
            sage: H = HyperellipticCurve(x^3-10*x+9)
            sage: K = Qp(5,8)
            sage: HK = H.change_ring(K)
            sage: P = HK.lift_x(1 + 2*5^2)
            sage: HK.residue_disc(P)
            (1 : 0 : 1)
            sage: Q = HK(0,3)
            sage: HK.residue_disc(Q)
            (0 : 3 : 1)
            sage: S = HK.lift_x(5^-2)
            sage: HK.residue_disc(S)
            (0 : 1 : 0)
            sage: T = HK(0,1,0)
            sage: HK.residue_disc(T)
            (0 : 1 : 0)

        AUTHOR:
            - Jennifer Balakrishnan
        """
        xPv = P[0].valuation()
        yPv = P[1].valuation()
        F = self.base_ring().residue_field()
        HF = self.change_ring(F)
        if P == self(0,1,0):
            return HF(0,1,0)
        elif yPv > 0:
            if xPv > 0:
                return HF(0,0,1)
            if xPv == 0:
                return HF(P[0].list()[0], 0,1)
        elif yPv ==0:
            if xPv > 0:
                return HF(0, P[1].list()[0],1)
            if xPv == 0:
                return HF(P[0].list()[0], P[1].list()[0],1)
        else:
            return HF(0,1,0)

    def is_same_disc(self,P,Q):
        """
        Checks if `P,Q` are in same residue disc

        EXAMPLES::

            sage: R.<x> = QQ['x']
            sage: H = HyperellipticCurve(x^3-10*x+9)
            sage: K = Qp(5,8)
            sage: HK = H.change_ring(K)
            sage: P = HK.lift_x(1 + 2*5^2)
            sage: Q = HK.lift_x(5^-2)
            sage: S = HK(1,0)
            sage: HK.is_same_disc(P,Q)
            False
            sage: HK.is_same_disc(P,S)
            True
            sage: HK.is_same_disc(Q,S)
            False
        """
        if self.residue_disc(P) == self.residue_disc(Q):
            return True
        else:
            return False

    def tiny_integrals(self, F, P, Q):
        r"""
        Evaluate the integrals of `f_i dx/2y` from `P` to `Q` for each `f_i` in `F`
        by formally integrating a power series in a local parameter `t`

        `P` and `Q` MUST be in the same residue disc for this result to make sense.

        INPUT:

        - F a list of functions `f_i`
        - P a point on self
        - Q a point on self (in the same residue disc as P)

        OUTPUT:

        The integrals `\int_P^Q f_i dx/2y`

        EXAMPLES::

            sage: K = pAdicField(17, 5)
            sage: E = EllipticCurve(K, [-31/3, -2501/108]) # 11a
            sage: P = E(K(14/3), K(11/2))
            sage: TP = E.teichmuller(P);
            sage: x,y = E.monsky_washnitzer_gens()
            sage: E.tiny_integrals([1,x],P, TP) == E.tiny_integrals_on_basis(P,TP)
            True

        ::

            sage: K = pAdicField(11, 5)
            sage: x = polygen(K)
            sage: C = HyperellipticCurve(x^5 + 33/16*x^4 + 3/4*x^3 + 3/8*x^2 - 1/4*x + 1/16)
            sage: P = C.lift_x(11^(-2))
            sage: Q = C.lift_x(3*11^(-2))
            sage: C.tiny_integrals([1],P,Q)
            (3*11^3 + 7*11^4 + 4*11^5 + 7*11^6 + 5*11^7 + O(11^8))

        Note that this fails if the points are not in the same residue disc::

            sage: S = C(0,1/4)
            sage: C.tiny_integrals([1,x,x^2,x^3],P,S)
            Traceback (most recent call last):
            ...
            ValueError: (11^-2 + O(11^3) : 11^-5 + 8*11^-2 + O(11^0) : 1 + O(11^5)) and (0 : 3 + 8*11 + 2*11^2 + 8*11^3 + 2*11^4 + O(11^5) : 1 + O(11^5)) are not in the same residue disc

        """
        x, y, z = self.local_analytic_interpolation(P, Q)  #homogeneous coordinates
        x = x/z
        y = y/z
        dt = x.derivative() / (2*y)
        integrals = []
        g = self.genus()
        for f in F:
            try:
                f_dt = f(x,y)*dt
            except TypeError:   #if f is a constant, not callable
                f_dt = f*dt
            if x.valuation() != -2:
                I = sum(f_dt[n]/(n+1) for n in range(f_dt.degree() + 1)) # \int_0^1 f dt
            else:
                If_dt = f_dt.integral().laurent_polynomial()
                I = If_dt(Q[0]**g/Q[1]) - If_dt(P[0]**g/P[1])
            integrals.append(I)
        return vector(integrals)

    def tiny_integrals_on_basis(self, P, Q):
        r"""
        Evaluate the integrals `\{\int_P^Q x^i dx/2y \}_{i=0}^{2g-1}`
        by formally integrating a power series in a local parameter `t`.
        `P` and `Q` MUST be in the same residue disc for this result to make sense.

        INPUT:

        - P a point on self
        - Q a point on self (in the same residue disc as P)

        OUTPUT:

        The integrals `\{\int_P^Q x^i dx/2y \}_{i=0}^{2g-1}`

        EXAMPLES::

            sage: K = pAdicField(17, 5)
            sage: E = EllipticCurve(K, [-31/3, -2501/108]) # 11a
            sage: P = E(K(14/3), K(11/2))
            sage: TP = E.teichmuller(P);
            sage: E.tiny_integrals_on_basis(P, TP)
            (17 + 14*17^2 + 17^3 + 8*17^4 + O(17^5), 16*17 + 5*17^2 + 8*17^3 + 14*17^4 + O(17^5))

        ::

            sage: K = pAdicField(11, 5)
            sage: x = polygen(K)
            sage: C = HyperellipticCurve(x^5 + 33/16*x^4 + 3/4*x^3 + 3/8*x^2 - 1/4*x + 1/16)
            sage: P = C.lift_x(11^(-2))
            sage: Q = C.lift_x(3*11^(-2))
            sage: C.tiny_integrals_on_basis(P,Q)
            (3*11^3 + 7*11^4 + 4*11^5 + 7*11^6 + 5*11^7 + O(11^8), 3*11 + 10*11^2 + 8*11^3 + 9*11^4 + 7*11^5 + O(11^6), 4*11^-1 + 2 + 6*11 + 6*11^2 + 7*11^3 + O(11^4), 11^-3 + 6*11^-2 + 2*11^-1 + 2 + O(11^2))


        Note that this fails if the points are not in the same residue disc::

            sage: S = C(0,1/4)
            sage: C.tiny_integrals_on_basis(P,S)
            Traceback (most recent call last):
            ...
            ValueError: (11^-2 + O(11^3) : 11^-5 + 8*11^-2 + O(11^0) : 1 + O(11^5)) and (0 : 3 + 8*11 + 2*11^2 + 8*11^3 + 2*11^4 + O(11^5) : 1 + O(11^5)) are not in the same residue disc

        """
        d = self.hyperelliptic_polynomials()[0].degree()
        g = self.genus()
        if d%2 == 1:
            dim = 2*g
        else:
            dim = 2*g+1
        if P == Q:
            V = VectorSpace(self.base_ring(), dim)
            return V(0)
        R = PolynomialRing(self.base_ring(), ['x', 'y'])
        x, y = R.gens()
        return self.tiny_integrals([x**i for i in range(dim)], P, Q)

    def teichmuller(self, P):
        r"""
        Find a Teichm\:uller point in the same residue class of `P`.

        Because this lift of frobenius acts as `x \mapsto x^p`,
        take the Teichmuller lift of `x` and then find a matching `y`
        from that.

        EXAMPLES::

            sage: K = pAdicField(7, 5)
            sage: E = EllipticCurve(K, [-31/3, -2501/108]) # 11a
            sage: P = E(K(14/3), K(11/2))
            sage: E.frobenius(P) == P
            False
            sage: TP = E.teichmuller(P); TP
            (0 : 2 + 3*7 + 3*7^2 + 3*7^4 + O(7^5) : 1 + O(7^5))
            sage: E.frobenius(TP) == TP
            True
            sage: (TP[0] - P[0]).valuation() > 0, (TP[1] - P[1]).valuation() > 0
            (True, True)
        """
        K = P[0].parent()
        x = K.teichmuller(P[0])
        pts = self.lift_x(x, all=True)
        p = K.prime()
        if (pts[0][1] - P[1]).valuation() > 0:
            return pts[0]
        else:
            return pts[1]

    def coleman_integrals_on_basis(self, P, Q, algorithm=None):
        r"""
        Computes the Coleman integrals `\{\int_P^Q x^i dx/2y \}_{i=0}^{2g-1}`

        INPUT:

        - P point on self
        - Q point on self
        - algorithm (optional) = None (uses Frobenius) or teichmuller (uses Teichmuller points)

        OUTPUT:

        the Coleman integrals `\{\int_P^Q x^i dx/2y \}_{i=0}^{2g-1}`

        EXAMPLES::

            sage: K = pAdicField(11, 5)
            sage: x = polygen(K)
            sage: C = HyperellipticCurve(x^5 + 33/16*x^4 + 3/4*x^3 + 3/8*x^2 - 1/4*x + 1/16)
            sage: P = C.lift_x(2)
            sage: Q = C.lift_x(3)
            sage: C.coleman_integrals_on_basis(P, Q)
            (10*11 + 6*11^3 + 2*11^4 + O(11^5), 11 + 9*11^2 + 7*11^3 + 9*11^4 + O(11^5), 3 + 10*11 + 5*11^2 + 9*11^3 + 4*11^4 + O(11^5), 3 + 11 + 5*11^2 + 4*11^4 + O(11^5))
            sage: C.coleman_integrals_on_basis(P, Q, algorithm='teichmuller')
            (10*11 + 6*11^3 + 2*11^4 + O(11^5), 11 + 9*11^2 + 7*11^3 + 9*11^4 + O(11^5), 3 + 10*11 + 5*11^2 + 9*11^3 + 4*11^4 + O(11^5), 3 + 11 + 5*11^2 + 4*11^4 + O(11^5))

        ::

            sage: K = pAdicField(11,5)
            sage: x = polygen(K)
            sage: C = HyperellipticCurve(x^5 + 33/16*x^4 + 3/4*x^3 + 3/8*x^2 - 1/4*x + 1/16)
            sage: P = C.lift_x(11^(-2))
            sage: Q = C.lift_x(3*11^(-2))
            sage: C.coleman_integrals_on_basis(P, Q)
            (3*11^3 + 7*11^4 + 4*11^5 + 7*11^6 + 5*11^7 + O(11^8), 3*11 + 10*11^2 + 8*11^3 + 9*11^4 + 7*11^5 + O(11^6), 4*11^-1 + 2 + 6*11 + 6*11^2 + 7*11^3 + O(11^4), 11^-3 + 6*11^-2 + 2*11^-1 + 2 + O(11^2))

        ::

            sage: R = C(0,1/4)
            sage: a = C.coleman_integrals_on_basis(P,R)  # long time (7s on sage.math, 2011)
            sage: b = C.coleman_integrals_on_basis(R,Q)  # long time (9s on sage.math, 2011)
            sage: c = C.coleman_integrals_on_basis(P,Q)  # long time
            sage: a+b == c  # long time
            True

        ::

            sage: R.<x> = QQ['x']
            sage: H = HyperellipticCurve(x^3-10*x+9)
            sage: K = Qp(5,8)
            sage: HK = H.change_ring(K)
            sage: S = HK(1,0)
            sage: P = HK(0,3)
            sage: T = HK(0,1,0)
            sage: Q = HK.lift_x(5^-2)
            sage: R = HK.lift_x(4*5^-2)
            sage: HK.coleman_integrals_on_basis(S,P)
            (2*5^2 + 5^4 + 5^5 + 3*5^6 + 3*5^7 + 2*5^8 + O(5^9), 5 + 2*5^2 + 4*5^3 + 2*5^4 + 3*5^6 + 4*5^7 + 2*5^8 + O(5^9))
            sage: HK.coleman_integrals_on_basis(T,P)
            (2*5^2 + 5^4 + 5^5 + 3*5^6 + 3*5^7 + 2*5^8 + O(5^9), 5 + 2*5^2 + 4*5^3 + 2*5^4 + 3*5^6 + 4*5^7 + 2*5^8 + O(5^9))
            sage: HK.coleman_integrals_on_basis(P,S) == -HK.coleman_integrals_on_basis(S,P)
            True
            sage: HK.coleman_integrals_on_basis(S,Q)
            (4*5 + 4*5^2 + 4*5^3 + O(5^4), 5^-1 + O(5^3))
            sage: HK.coleman_integrals_on_basis(Q,R)
            (4*5 + 2*5^2 + 2*5^3 + 2*5^4 + 5^5 + 5^6 + 5^7 + 3*5^8 + O(5^9), 2*5^-1 + 4 + 4*5 + 4*5^2 + 4*5^3 + 2*5^4 + 3*5^5 + 2*5^6 + O(5^7))
            sage: HK.coleman_integrals_on_basis(S,R) == HK.coleman_integrals_on_basis(S,Q) + HK.coleman_integrals_on_basis(Q,R)
            True
            sage: HK.coleman_integrals_on_basis(T,T)
            (0, 0)
            sage: HK.coleman_integrals_on_basis(S,T)
            (0, 0)

        AUTHORS:
            - Robert Bradshaw (2007-03): non-Weierstrass points
            - Jennifer Balakrishnan and Robert Bradshaw (2010-02): Weierstrass points
        """
        import sage.schemes.hyperelliptic_curves.monsky_washnitzer as monsky_washnitzer
        from sage.misc.profiler import Profiler
        prof = Profiler()
        prof("setup")
        K = self.base_ring()
        p = K.prime()
        prec = K.precision_cap()
        g = self.genus()
        d = self.hyperelliptic_polynomials()[0].degree()
        if d%2 == 1:
            dim = 2*g
        else:
            dim = 2*g+1
        V = VectorSpace(K, dim)
##        print 'P is ', P
#        print 'Q is ', Q
        #if P or Q is Weierstrass, use the Frobenius algorithm
        if self.is_in_weierstrass_disc(Q):
            if self.is_weierstrass(P) == False and self.is_in_weierstrass_disc(P) == False:
                W = self.find_char_zero_weier_point(Q)
                I1 = -self.coleman_integrals_on_basis(W,P)
                I2 = self.tiny_integrals_on_basis(W,Q)
                return I1 + I2
        if self.is_weierstrass(P):
            if self.is_weierstrass(Q):
                return V(0)
            elif self.is_in_weierstrass_disc(Q):
                W = self.find_char_zero_weier_point(Q)
                return self.tiny_integrals_on_basis(W,Q)
            elif self.is_same_disc(P,Q):
                return self.tiny_integrals_on_basis(P,Q)
            else:
                PP = None
                QQ = Q
                TP = None
                try:
                    TQ = self.frobenius(Q)
                except (TypeError,AttributeError):
                    xFQ = Q[0]**p
                    f = self.hyperelliptic_polynomials()[0]
                    y = f(xFQ)
                    yval = y.valuation()//ZZ(2)
                    yFQ = Q[0].parent().gen()**yval
                    for i in range(15):
                        yFQ = (yFQ + y/yFQ)
                    if yFQ.list()[0] != 1:
                        yFQ = -yFQ
                    TQ = (xFQ,yFQ)
        elif self.is_weierstrass(Q):
            PP = P
            QQ = None
            TQ = None
            TP = self.frobenius(P)
        elif self.is_same_disc(P,Q):
            return self.tiny_integrals_on_basis(P,Q)
        elif algorithm == 'teichmuller':
            prof("teichmuller")
            PP = TP = self.teichmuller(P)
            QQ = TQ = self.teichmuller(Q)
            evalP, evalQ = TP, TQ
        else:
            prof("frobPQ")
            TP = self.frobenius(P)
            TQ = self.frobenius(Q)
            PP, QQ = P, Q
#        print PP
##        print QQ
#        print TP
#        print TQ
        prof("tiny integrals")
        if TP == None:
            P_to_TP = V(0)
        else:
#            if TP!=None:
#                TPv = (TP[0]**g/TP[1]).valuation()
#                xTPv = TP[0].valuation()
#            else:
#                xTPv = TPv = +Infinity
#            if TQ!=None:
#                TQv = (TQ[0]**g/TQ[1]).valuation()
#                xTQv = TQ[0].valuation()
#            else:
#                xTQv = TQv = +Infinity
#            offset = (2*g-1)*max(TPv, TQv)
#            if offset == +Infinity:
#                offset = (2*g-1)*min(TPv,TQv)
#            if (offset > prec and (xTPv <0 or xTQv <0) and (self.residue_disc(P) == self.change_ring(GF(p))(0,1,0) or self.residue_disc(Q) == self.change_ring(GF(p))(0,1,0))):
#                newprec = offset + prec
#                K = pAdicField(p,newprec)
#                A = PolynomialRing(RationalField(),'x')
#                f = A(self.hyperelliptic_polynomials()[0])
#                from sage.schemes.hyperelliptic_curves.constructor import HyperellipticCurve
#                self = HyperellipticCurve(f).change_ring(K)
#                xP = P[0]
#                xPv = xP.valuation()
##                xPnew = K(sum(xP.list()[i]*p**(xPv + i) for i in range(len(xP.list()))))
#                PP = P = self.lift_x(xPnew)
#                TP = self.frobenius(P)
#                xQ = Q[0]
#                xQv = xQ.valuation()
#                xQnew = K(sum(xQ.list()[i]*p**(xQv + i) for i in range(len(xQ.list()))))
#                QQ = Q = self.lift_x(xQnew)
#                TQ = self.frobenius(Q)
#                V = VectorSpace(K,dim)
            P_to_TP = (self.tiny_integrals_on_basis(P, TP))
        V = VectorSpace(P[0].parent(),dim)
        P_to_TP = V(P_to_TP)
        if TQ == None:
            TQ_to_Q = V(0)
        else:
            TQ_to_Q = V(self.tiny_integrals_on_basis(TQ, Q))
        prof("mw calc")
        try:
            M_frob, forms = self._frob_calc
        except AttributeError:
            M_frob, forms = self._frob_calc = monsky_washnitzer.matrix_of_frobenius_hyperelliptic(self)
        prof("eval f")
#        R = forms[0].base_ring()
        R = (P[0]).parent()
        try:
            prof("eval f %s"%R)
            if PP is None:
                L = [-f(R(QQ[0]), R(QQ[1])) for f in forms]  ##changed
            elif QQ is None:
                L = [f(R(PP[0]), R(PP[1])) for f in forms]
            else:
                L = [f(R(PP[0]), R(PP[1])) - f(R(QQ[0]), R(QQ[1])) for f in forms]
        except ValueError:
            R = (Q[0]).parent()
            prof("changing rings")
            forms = [f.change_ring(self.base_ring()) for f in forms]
            prof("eval f %s"%self.base_ring())
            if PP is None:
                L = [-f(QQ[0], QQ[1]) for f in forms]  ##changed
            elif QQ is None:
                L = [f(PP[0], PP[1]) for f in forms]
            else:
                L = [f(PP[0], PP[1]) - f(QQ[0], QQ[1]) for f in forms]
        try:
            b = V(L)
        except ValueError:
            V = VectorSpace(Q[0].parent(),dim)
            b = V(L)
        if PP is None:
            b -= TQ_to_Q
        elif QQ is None:
            b -= P_to_TP
        elif algorithm != 'teichmuller':
            b -= P_to_TP + TQ_to_Q
        prof("lin alg")
        M_sys = matrix(K, M_frob).transpose() - 1
        TP_to_TQ = M_sys**(-1) * b
        prof("done")
#        print prof
        if algorithm == 'teichmuller':
            return P_to_TP + TP_to_TQ + TQ_to_Q
        else:
            return TP_to_TQ

    coleman_integrals_on_basis_hyperelliptic = coleman_integrals_on_basis


#    def invariant_differential(self):
#        """
#        Returns the invariant differential `dx/2y` on self
#
#        EXAMPLES::
#
#            sage: R.<x> = QQ['x']
#            sage: H = HyperellipticCurve(x^3+1)
#            sage: K = Qp(5,8)
#            sage: HK = H.change_ring(K)
#            sage: w = HK.invariant_differential(); w
#            (((1+O(5^8)))*1) dx/2y
#
#        ::
#
#            sage: K = pAdicField(11, 6)
#            sage: x = polygen(K)
#            sage: C = HyperellipticCurve(x^5 + 33/16*x^4 + 3/4*x^3 + 3/8*x^2 - 1/4*x + 1/16)
#            sage: C.invariant_differential()
#            (((1+O(11^6)))*1) dx/2y
#
#        """
#        import sage.schemes.hyperelliptic_curves.monsky_washnitzer as monsky_washnitzer
#        S = monsky_washnitzer.SpecialHyperellipticQuotientRing(self)
#        MW = monsky_washnitzer.MonskyWashnitzerDifferentialRing(S)
#        return MW.invariant_differential()

    def coleman_integral(self, w, P, Q, algorithm = 'None'):
        r"""
        Returns the Coleman integral `\int_P^Q w`

        INPUT:

        - w differential (if one of P,Q is Weierstrass, w must be odd)
        - P point on self
        - Q point on self
        - algorithm (optional) = None (uses Frobenius) or teichmuller (uses Teichmuller points)

        OUTPUT:

        the Coleman integral `\int_P^Q w`

        EXAMPLES:

        Example of Leprevost from Kiran Kedlaya
        The first two should be zero as `(P-Q) = 30(P-Q)` in the Jacobian
        and `dx/2y` and `x dx/2y` are holomorphic. ::

            sage: K = pAdicField(11, 6)
            sage: x = polygen(K)
            sage: C = HyperellipticCurve(x^5 + 33/16*x^4 + 3/4*x^3 + 3/8*x^2 - 1/4*x + 1/16)
            sage: P = C(-1, 1); P1 = C(-1, -1)
            sage: Q = C(0, 1/4); Q1 = C(0, -1/4)
            sage: x, y = C.monsky_washnitzer_gens()
            sage: w = C.invariant_differential()
            sage: w.coleman_integral(P, Q)
            O(11^6)
            sage: C.coleman_integral(x*w, P, Q)
            O(11^6)
            sage: C.coleman_integral(x^2*w, P, Q)
            7*11 + 6*11^2 + 3*11^3 + 11^4 + 5*11^5 + O(11^6)

        ::

            sage: p = 71; m = 4
            sage: K = pAdicField(p, m)
            sage: x = polygen(K)
            sage: C = HyperellipticCurve(x^5 + 33/16*x^4 + 3/4*x^3 + 3/8*x^2 - 1/4*x + 1/16)
            sage: P = C(-1, 1); P1 = C(-1, -1)
            sage: Q = C(0, 1/4); Q1 = C(0, -1/4)
            sage: x, y = C.monsky_washnitzer_gens()
            sage: w = C.invariant_differential()
            sage: w.integrate(P, Q), (x*w).integrate(P, Q)
            (O(71^4), O(71^4))
            sage: R, R1 = C.lift_x(4, all=True)
            sage: w.integrate(P, R)
            21*71 + 67*71^2 + 27*71^3 + O(71^4)
            sage: w.integrate(P, R) + w.integrate(P1, R1)
            O(71^4)

        A simple example, integrating dx::

            sage: R.<x> = QQ['x']
            sage: E= HyperellipticCurve(x^3-4*x+4)
            sage: K = Qp(5,10)
            sage: EK = E.change_ring(K)
            sage: P = EK(2, 2)
            sage: Q = EK.teichmuller(P)
            sage: x, y = EK.monsky_washnitzer_gens()
            sage: EK.coleman_integral(x.diff(), P, Q)
            5 + 2*5^2 + 5^3 + 3*5^4 + 4*5^5 + 2*5^6 + 3*5^7 + 3*5^9 + O(5^10)
            sage: Q[0] - P[0]
            5 + 2*5^2 + 5^3 + 3*5^4 + 4*5^5 + 2*5^6 + 3*5^7 + 3*5^9 + O(5^10)

        Yet another example::

            sage: R.<x> = QQ['x']
            sage: H = HyperellipticCurve(x*(x-1)*(x+9))
            sage: K = Qp(7,10)
            sage: HK = H.change_ring(K)
            sage: import sage.schemes.hyperelliptic_curves.monsky_washnitzer as mw
            sage: M_frob, forms = mw.matrix_of_frobenius_hyperelliptic(HK)
            sage: w = HK.invariant_differential()
            sage: x,y = HK.monsky_washnitzer_gens()
            sage: f = forms[0]
            sage: S = HK(9,36)
            sage: Q = HK.teichmuller(S)
            sage: P = HK(-1,4)
            sage: b = x*w*w._coeff.parent()(f)
            sage: HK.coleman_integral(b,P,Q)
            7 + 7^2 + 4*7^3 + 5*7^4 + 3*7^5 + 7^6 + 5*7^7 + 3*7^8 + 4*7^9 + 4*7^10 + O(7^11)

        ::

            sage: R.<x> = QQ['x']
            sage: H = HyperellipticCurve(x^3+1)
            sage: K = Qp(5,8)
            sage: HK = H.change_ring(K)
            sage: w = HK.invariant_differential()
            sage: P = HK(0,1)
            sage: Q = HK.lift_x(5)
            sage: x,y = HK.monsky_washnitzer_gens()
            sage: (2*y*w).coleman_integral(P,Q)
            5 + O(5^9)
            sage: xloc,yloc,zloc = HK.local_analytic_interpolation(P,Q)
            sage: I2 = (xloc.derivative()/(2*yloc)).integral()
            sage: I2.polynomial()(1) - I2(0)
            3*5 + 2*5^2 + 2*5^3 + 5^4 + 4*5^6 + 5^7 + O(5^9)
            sage: HK.coleman_integral(w,P,Q)
            3*5 + 2*5^2 + 2*5^3 + 5^4 + 4*5^6 + 5^7 + O(5^9)

        Integrals involving Weierstrass points::

            sage: R.<x> = QQ['x']
            sage: H = HyperellipticCurve(x^3-10*x+9)
            sage: K = Qp(5,8)
            sage: HK = H.change_ring(K)
            sage: S = HK(1,0)
            sage: P = HK(0,3)
            sage: negP = HK(0,-3)
            sage: T = HK(0,1,0)
            sage: w = HK.invariant_differential()
            sage: x,y = HK.monsky_washnitzer_gens()
            sage: HK.coleman_integral(w*x^3,S,T)
            0
            sage: HK.coleman_integral(w*x^3,T,S)
            0
            sage: HK.coleman_integral(w,S,P)
            2*5^2 + 5^4 + 5^5 + 3*5^6 + 3*5^7 + 2*5^8 + O(5^9)
            sage: HK.coleman_integral(w,T,P)
            2*5^2 + 5^4 + 5^5 + 3*5^6 + 3*5^7 + 2*5^8 + O(5^9)
            sage: HK.coleman_integral(w*x^3,T,P)
            5^2 + 2*5^3 + 3*5^6 + 3*5^7 + O(5^8)
            sage: HK.coleman_integral(w*x^3,S,P)
            5^2 + 2*5^3 + 3*5^6 + 3*5^7 + O(5^8)
            sage: HK.coleman_integral(w, P, negP, algorithm='teichmuller')
            5^2 + 4*5^3 + 2*5^4 + 2*5^5 + 3*5^6 + 2*5^7 + 4*5^8 + O(5^9)
            sage: HK.coleman_integral(w, P, negP)
            5^2 + 4*5^3 + 2*5^4 + 2*5^5 + 3*5^6 + 2*5^7 + 4*5^8 + O(5^9)

        AUTHORS:

        - Robert Bradshaw (2007-03)
        - Kiran Kedlaya (2008-05)
        - Jennifer Balakrishnan (2010-02)

        """
        # TODO: implement Jacobians and show the relationship directly
        import sage.schemes.hyperelliptic_curves.monsky_washnitzer as monsky_washnitzer
        K = self.base_ring()
        prec = K.precision_cap()
        #S = monsky_washnitzer.SpecialHyperellipticQuotientRing(self, K)
        #MW = monsky_washnitzer.MonskyWashnitzerDifferentialRing(S)
        #w = MW(w)
        f, vec = w.reduce_fast()
        #print("vec=", vec)
        basis_values = self.coleman_integrals_on_basis(P, Q, algorithm)
        #print("basis_values", basis_values)
        dim = len(basis_values)
        x,y = self.local_coordinates_at_infinity(2*prec)
        if self.is_weierstrass(P):
            if self.is_weierstrass(Q):
                return 0
            elif f == 0:
                return sum([vec[i] * basis_values[i] for i in range(dim)])
            elif w._coeff(x,-y)*x.derivative()/(-2*y)+w._coeff(x,y)*x.derivative()/(2*y) == 0:
                return self.coleman_integral(w,self(Q[0],-Q[1]), self(Q[0],Q[1]), algorithm)/2
            else:
                raise ValueError("The differential is not odd: use coleman_integral_from_weierstrass_via_boundary")

        elif self.is_weierstrass(Q):
            if f == 0:
                return sum([vec[i] * basis_values[i] for i in range(dim)])
            elif w._coeff(x,-y)*x.derivative()/(-2*y)+w._coeff(x,y)*x.derivative()/(2*y) == 0:
                return -self.coleman_integral(w,self(P[0],-P[1]), self(P[0],P[1]), algorithm)/2
            else:
                raise ValueError("The differential is not odd: use coleman_integral_from_weierstrass_via_boundary")
        else:
            return f(Q[0], Q[1]) - f(P[0], P[1]) + sum([vec[i] * basis_values[i] for i in range(dim)]) # this is just a dot product...

    def frobenius(self, P=None):
        """
        Returns the `p`-th power lift of Frobenius of `P`

        EXAMPLES::

            sage: K = Qp(11, 5)
            sage: R.<x> = K[]
            sage: E = HyperellipticCurve(x^5 - 21*x - 20)
            sage: P = E.lift_x(2)
            sage: E.frobenius(P)
            (2 + 10*11 + 5*11^2 + 11^3 + O(11^5) : 5 + 9*11 + 2*11^2 + 2*11^3 + O(11^5) : 1 + O(11^5))
            sage: Q = E.teichmuller(P); Q
            (2 + 10*11 + 4*11^2 + 9*11^3 + 11^4 + O(11^5) : 5 + 9*11 + 6*11^2 + 11^3 + 6*11^4 + O(11^5) : 1 + O(11^5))
            sage: E.frobenius(Q)
            (2 + 10*11 + 4*11^2 + 9*11^3 + 11^4 + O(11^5) : 5 + 9*11 + 6*11^2 + 11^3 + 6*11^4 + O(11^5) : 1 + O(11^5))

        ::

            sage: R.<x> = QQ[]
            sage: H = HyperellipticCurve(x^5-23*x^3+18*x^2+40*x)
            sage: Q = H(0,0)
            sage: u,v = H.local_coord(Q,prec=100)
            sage: K = Qp(11,5)
            sage: L.<a> = K.extension(x^20-11)
            sage: HL = H.change_ring(L)
            sage: S = HL(u(a),v(a))
            sage: HL.frobenius(S)
            (8*a^22 + 10*a^42 + 4*a^44 + 2*a^46 + 9*a^48 + 8*a^50 + a^52 + 7*a^54 +
            7*a^56 + 5*a^58 + 9*a^62 + 5*a^64 + a^66 + 6*a^68 + a^70 + 6*a^74 +
            2*a^76 + 2*a^78 + 4*a^82 + 5*a^84 + 2*a^86 + 7*a^88 + a^90 + 6*a^92 +
            a^96 + 5*a^98 + 2*a^102 + 2*a^106 + 6*a^108 + 8*a^110 + 3*a^112 +
            a^114 + 8*a^116 + 10*a^118 + 3*a^120 + O(a^122) :
            a^11 + 7*a^33 + 7*a^35 + 4*a^37 + 6*a^39 + 9*a^41 + 8*a^43 + 8*a^45 +
            a^47 + 7*a^51 + 4*a^53 + 5*a^55 + a^57 + 7*a^59 + 5*a^61 + 9*a^63 +
            4*a^65 + 10*a^69 + 3*a^71 + 2*a^73 + 9*a^75 + 10*a^77 + 6*a^79 +
            10*a^81 + 7*a^85 + a^87 + 4*a^89 + 8*a^91 + a^93 + 8*a^95 + 2*a^97 +
            7*a^99 + a^101 + 3*a^103 + 6*a^105 + 7*a^107 + 4*a^109 + O(a^111) :
            1 + O(a^100))

        AUTHORS:

        - Robert Bradshaw and Jennifer Balakrishnan (2010-02)
        """
        try:
            _frob = self._frob
        except AttributeError:
            K = self.base_ring()
            p = K.prime()
            x = K['x'].gen(0)

            f, f2 = self.hyperelliptic_polynomials()
            if f2 != 0:
                raise NotImplementedError("Curve must be in weierstrass normal form.")
            h = (f(x**p) - f**p)

            def _frob(P):
                if P == self(0,1,0):
                    return P
                x0 = P[0]
                y0 = P[1]
                try:
                    uN = (1 + h(x0)/y0**(2*p)).sqrt()
                    yres=y0**p * uN
                    xres=x0**p
                    if (yres-y0).valuation() == 0:
                        yres=-yres
                    return self.point([xres,yres, K(1)])
                except (TypeError, NotImplementedError):
                    uN2 = 1 + h(x0)/y0**(2*p)
                    #yfrob2 = f(x)
                    c = uN2.list()[0]
                    v = uN2.valuation()
                    a = uN2.parent().gen()
                    uN = self.newton_sqrt(uN2,c.sqrt()*a**(v//2),K.precision_cap())
                    yres = y0**p *uN
                    xres = x0**p
                    if (yres - y0).valuation() == 0:
                        yres = -yres
                    try:
                        return self(xres,yres)
                    except ValueError:
                        return self._curve_over_ram_extn(xres,yres)

            self._frob = _frob

        if P is None:
            return _frob
        else:
            return _frob(P)

    def newton_sqrt(self,f,x0, prec):
        r"""
        Takes the square root of the power series `f` by Newton's method

        NOTE:

        this function should eventually be moved to `p`-adic power series ring

        INPUT:

        - f power series wtih coefficients in `\QQ_p` or an extension
        - x0 seeds the Newton iteration
        - prec precision

        OUTPUT:

        the square root of `f`

        EXAMPLES::

            sage: R.<x> = QQ['x']
            sage: H = HyperellipticCurve(x^5-23*x^3+18*x^2+40*x)
            sage: Q = H(0,0)
            sage: u,v = H.local_coord(Q,prec=100)
            sage: K = Qp(11,5)
            sage: HK = H.change_ring(K)
            sage: L.<a> = K.extension(x^20-11)
            sage: HL = H.change_ring(L)
            sage: S = HL(u(a),v(a))
            sage: f = H.hyperelliptic_polynomials()[0]
            sage: y = HK.newton_sqrt( f(u(a)^11), a^11,5)
            sage: y^2 - f(u(a)^11)
            O(a^122)

        AUTHOR:

        - Jennifer Balakrishnan

        """
        z = x0
        try:
            x = f.parent().variable_name()
            if x!='a' :  #this is to distinguish between extensions of Qp that are finite vs. not
                S = f.base_ring()[[x]]
                x = S.gen()
        except ValueError:
            pass
        z = x0
        loop_prec = (log(RR(prec))/log(RR(2))).ceil()
        for i in range(loop_prec):
            z = (z+f/z)/2
        try:
            return z + O(x**prec)
        except (NameError,ArithmeticError,TypeError):
            return z

    def curve_over_ram_extn(self,deg):
        r"""
        Return ``self`` over `\QQ_p(p^(1/deg))`.

        INPUT:

        - deg: the degree of the ramified extension

        OUTPUT:

        ``self`` over `\QQ_p(p^(1/deg))`

        EXAMPLES::

            sage: R.<x> = QQ['x']
            sage: H = HyperellipticCurve(x^5-23*x^3+18*x^2+40*x)
            sage: K = Qp(11,5)
            sage: HK = H.change_ring(K)
            sage: HL = HK.curve_over_ram_extn(2)
            sage: HL
            Hyperelliptic Curve over Eisenstein Extension in a defined by x^2 - 11 with capped relative precision 10 over 11-adic Field defined by (1 + O(a^10))*y^2 = (1 + O(a^10))*x^5 + (10 + 8*a^2 + 10*a^4 + 10*a^6 + 10*a^8 + O(a^10))*x^3 + (7 + a^2 + O(a^10))*x^2 + (7 + 3*a^2 + O(a^10))*x

        AUTHOR:

        - Jennifer Balakrishnan

        """
        from sage.schemes.hyperelliptic_curves.constructor import HyperellipticCurve
        K = self.base_ring()
        p = K.prime()
        A = PolynomialRing(QQ,'x')
        x = A.gen()
        J = K.extension(x**deg-p,names='a')
        pol = self.hyperelliptic_polynomials()[0]
        H = HyperellipticCurve(A(pol))
        HJ = H.change_ring(J)
        self._curve_over_ram_extn = HJ
        self._curve_over_ram_extn._curve_over_Qp = self
        return HJ

    def get_boundary_point(self, curve_over_extn, P):
        """
        Given self over an extension field, find a point in the disc of `P` near the boundary

        INPUT:

        - curve_over_extn: self over a totally ramified extension
        - P: Weierstrass point

        OUTPUT:

        a point in the disc of `P` near the boundary

        EXAMPLES::

            sage: R.<x> = QQ['x']
            sage: H = HyperellipticCurve(x^3-10*x+9)
            sage: K = Qp(3,6)
            sage: HK = H.change_ring(K)
            sage: P = HK(1,0)
            sage: J.<a> = K.extension(x^30-3)
            sage: HJ  = H.change_ring(J)
            sage: S = HK.get_boundary_point(HJ,P)
            sage: S
            (1 + 2*a^2 + 2*a^6 + 2*a^18 + a^32 + a^34 + a^36 + 2*a^38 + 2*a^40 + a^42 + 2*a^44 + a^48 + 2*a^50 + 2*a^52 + a^54 + a^56 + 2*a^60 + 2*a^62 + a^70 + 2*a^72 + a^76 + 2*a^78 + a^82 + a^88 + a^96 + 2*a^98 + 2*a^102 + a^104 + 2*a^106 + a^108 + 2*a^110 + a^112 + 2*a^116 + a^126 + 2*a^130 + 2*a^132 + a^144 + 2*a^148 + 2*a^150 + a^152 + 2*a^154 + a^162 + a^164 + a^166 + a^168 + a^170 + a^176 + a^178 + O(a^180) : a + O(a^180) : 1 + O(a^180))

        AUTHOR:

        - Jennifer Balakrishnan

        """
        J = curve_over_extn.base_ring()
        a = J.gen()
        prec2 = J.precision_cap()
        x,y = self.local_coord(P,prec2)
        return curve_over_extn(x(a),y(a))

    def P_to_S(self, P, S):
        r"""
        Given a finite Weierstrass point `P` and a point `S`
        in the same disc, computes the Coleman integrals `\{\int_P^S x^i dx/2y \}_{i=0}^{2g-1}`

        INPUT:

        - P: finite Weierstrass point
        - S: point in disc of P

        OUTPUT:

        Coleman integrals `\{\int_P^S x^i dx/2y \}_{i=0}^{2g-1}`

        EXAMPLES::

            sage: R.<x> = QQ['x']
            sage: H = HyperellipticCurve(x^3-10*x+9)
            sage: K = Qp(5,4)
            sage: HK = H.change_ring(K)
            sage: P = HK(1,0)
            sage: HJ = HK.curve_over_ram_extn(10)
            sage: S = HK.get_boundary_point(HJ,P)
            sage: HK.P_to_S(P, S)
            (2*a + 4*a^3 + 2*a^11 + 4*a^13 + 2*a^17 + 2*a^19 + a^21 + 4*a^23 + a^25 + 2*a^27 + 2*a^29 + 3*a^31 + 4*a^33 + O(a^35), a^-5 + 2*a + 2*a^3 + a^7 + 3*a^11 + a^13 + 3*a^15 + 3*a^17 + 2*a^19 + 4*a^21 + 4*a^23 + 4*a^25 + 2*a^27 + a^29 + a^31 + O(a^33))

        AUTHOR:

        - Jennifer Balakrishnan

        """
        prec = self.base_ring().precision_cap()
        deg = (S[0]).parent().defining_polynomial().degree()
        prec2= prec*deg
        x,y = self.local_coord(P,prec2)
        g = self.genus()
        integrals = [((x**k*x.derivative()/(2*y)).integral()) for k in range(2*g)]
        val = [I(S[1]) for I in integrals]
        return vector(val)

    def coleman_integral_P_to_S(self,w,P,S):
        r"""
        Given a finite Weierstrass point `P` and a point `S`
        in the same disc, computes the Coleman integral `\int_P^S w`

        INPUT:

        - w: differential
        - P: Weierstrass point
        - S: point in the same disc of P (S is defined over an extension of `\QQ_p`; coordinates
          of S are given in terms of uniformizer `a`)

        OUTPUT:

        Coleman integral `\int_P^S w` in terms of `a`

        EXAMPLES::

            sage: R.<x> = QQ['x']
            sage: H = HyperellipticCurve(x^3-10*x+9)
            sage: K = Qp(5,4)
            sage: HK = H.change_ring(K)
            sage: P = HK(1,0)
            sage: J.<a> = K.extension(x^10-5)
            sage: HJ  = H.change_ring(J)
            sage: S = HK.get_boundary_point(HJ,P)
            sage: x,y = HK.monsky_washnitzer_gens()
            sage: S[0]-P[0] == HK.coleman_integral_P_to_S(x.diff(),P,S)
            True
            sage: HK.coleman_integral_P_to_S(HK.invariant_differential(),P,S) == HK.P_to_S(P,S)[0]
            True

        AUTHOR:

        - Jennifer Balakrishnan

        """
        prec = self.base_ring().precision_cap()
        deg = S[0].parent().defining_polynomial().degree()
        prec2= prec*deg
        x,y = self.local_coord(P,prec2)
        g = self.genus()
        int_sing = (w.coeff()(x,y)*x.derivative()/(2*y)).integral()
        int_sing_a = int_sing(S[1])
        return int_sing_a

    def S_to_Q(self,S,Q):
        r"""
        Given `S` a point on self over an extension field, computes the
        Coleman integrals `\{\int_S^Q x^i dx/2y \}_{i=0}^{2g-1}`

        **one should be able to feed `S,Q` into coleman_integral,
        but currently that segfaults**

        INPUT:

        - S: a point with coordinates in an extension of `\QQ_p` (with unif. a)
        - Q: a non-Weierstrass point defined over `\QQ_p`

        OUTPUT:

        the Coleman integrals `\{\int_S^Q x^i dx/2y \}_{i=0}^{2g-1}` in terms of `a`

        EXAMPLES::

            sage: R.<x> = QQ['x']
            sage: H = HyperellipticCurve(x^3-10*x+9)
            sage: K = Qp(5,6)
            sage: HK = H.change_ring(K)
            sage: J.<a> = K.extension(x^20-5)
            sage: HJ  = H.change_ring(J)
            sage: w = HK.invariant_differential()
            sage: x,y = HK.monsky_washnitzer_gens()
            sage: P = HK(1,0)
            sage: Q = HK(0,3)
            sage: S = HK.get_boundary_point(HJ,P)
            sage: P_to_S = HK.P_to_S(P,S)
            sage: S_to_Q = HJ.S_to_Q(S,Q)
            sage: P_to_S + S_to_Q
            (2*a^40 + a^80 + a^100 + O(a^105), a^20 + 2*a^40 + 4*a^60 + 2*a^80 + O(a^103))
            sage: HK.coleman_integrals_on_basis(P,Q)
            (2*5^2 + 5^4 + 5^5 + 3*5^6 + O(5^7), 5 + 2*5^2 + 4*5^3 + 2*5^4 + 5^6 + O(5^7))

        AUTHOR:

        - Jennifer Balakrishnan

        """
        FS = self.frobenius(S)
        FS = (FS[0],FS[1])
        FQ = self.frobenius(Q)
        import sage.schemes.hyperelliptic_curves.monsky_washnitzer as monsky_washnitzer
        try:
            M_frob, forms = self._frob_calc
        except AttributeError:
            M_frob, forms = self._frob_calc = monsky_washnitzer.matrix_of_frobenius_hyperelliptic(self)
        try:
            HJ = self._curve_over_ram_extn
            K = HJ.base_ring()
        except AttributeError:
            HJ = S.scheme()
            K = self.base_ring()
        g = self.genus()
        prec2 = K.precision_cap()
        p = K.prime()
        dim = 2*g
        V = VectorSpace(K,dim)
        if S == FS:
            S_to_FS = V(dim*[0])
        else:
            P = self(ZZ(FS[0][0]),ZZ(FS[1][0]))
            x,y = self.local_coord(P,prec2)
            integrals = [(x**i*x.derivative()/(2*y)).integral() for i in range(dim)]
            S_to_FS = vector([I.polynomial()(FS[1]) - I.polynomial()(S[1]) for I in integrals])
        if HJ(Q[0],Q[1]) == HJ(FQ):
            FQ_to_Q = V(dim*[0])
        else:
            FQ_to_Q = V(self.tiny_integrals_on_basis(FQ, Q))
        try:
            L = [f(K(S[0]), K(S[1])) - f(K(Q[0]), K(Q[1])) for f in forms]
        except ValueError:
            forms = [f.change_ring(K) for f in forms]
            L = [f(S[0], S[1]) - f(Q[0], Q[1]) for f in forms]
        b = V(L)
        M_sys = matrix(K, M_frob).transpose() - 1
        B = (~M_sys)
        v = [B.list()[i].valuation() for i in range(len(B.list()))]
        vv= min(v)
        B = (p**(-vv)*B).change_ring(K)
        B = p**(vv)*B
        return B*(b-S_to_FS-FQ_to_Q)

    def coleman_integral_S_to_Q(self,w,S,Q):
        r"""
        Computes the Coleman integral `\int_S^Q w`

        **one should be able to feed `S,Q` into coleman_integral,
        but currently that segfaults**

        INPUT:

        - w: a differential
        - S: a point with coordinates in an extension of `\QQ_p`
        - Q: a non-Weierstrass point defined over `\QQ_p`

        OUTPUT:

        the Coleman integral `\int_S^Q w`

        EXAMPLES::

            sage: R.<x> = QQ['x']
            sage: H = HyperellipticCurve(x^3-10*x+9)
            sage: K = Qp(5,6)
            sage: HK = H.change_ring(K)
            sage: J.<a> = K.extension(x^20-5)
            sage: HJ  = H.change_ring(J)
            sage: x,y = HK.monsky_washnitzer_gens()
            sage: P = HK(1,0)
            sage: Q = HK(0,3)
            sage: S = HK.get_boundary_point(HJ,P)
            sage: P_to_S = HK.coleman_integral_P_to_S(y.diff(),P,S)
            sage: S_to_Q = HJ.coleman_integral_S_to_Q(y.diff(),S,Q)
            sage: P_to_S  + S_to_Q
            3 + O(a^119)
            sage: HK.coleman_integral(y.diff(),P,Q)
            3 + O(5^6)

        AUTHOR:

        - Jennifer Balakrishnan

        """
        import sage.schemes.hyperelliptic_curves.monsky_washnitzer as monsky_washnitzer
        K = self.base_ring()
        #R = monsky_washnitzer.SpecialHyperellipticQuotientRing(self, K)
        #MW = monsky_washnitzer.MonskyWashnitzerDifferentialRing(R)
        #w = MW(w)
        f, vec = w.reduce_fast()
        g = self.genus()
        const = f(Q[0],Q[1])-f(S[0],S[1])
        if vec == vector(2*g*[0]):
            return const
        else:
            basis_values = self.S_to_Q(S, Q)
            dim = len(basis_values)
            dot = sum([vec[i] * basis_values[i] for i in range(dim)])
            return const + dot

    def coleman_integral_from_weierstrass_via_boundary(self, w, P, Q, d):
        r"""
        Computes the Coleman integral `\int_P^Q w` via a boundary point
        in the disc of `P`, defined over a degree `d` extension

        INPUT:

        - w: a differential
        - P: a Weierstrass point
        - Q: a non-Weierstrass point
        - d: degree of extension where coordinates of boundary point lie

        OUTPUT:

        the Coleman integral `\int_P^Q w`, written in terms of the uniformizer
        `a` of the degree `d` extension

        EXAMPLES::

            sage: R.<x> = QQ['x']
            sage: H = HyperellipticCurve(x^3-10*x+9)
            sage: K = Qp(5,6)
            sage: HK = H.change_ring(K)
            sage: P = HK(1,0)
            sage: Q = HK(0,3)
            sage: x,y = HK.monsky_washnitzer_gens()
            sage: HK.coleman_integral_from_weierstrass_via_boundary(y.diff(),P,Q,20)
            3 + O(a^119)
            sage: HK.coleman_integral(y.diff(),P,Q)
            3 + O(5^6)
            sage: w = HK.invariant_differential()
            sage: HK.coleman_integral_from_weierstrass_via_boundary(w,P,Q,20)
            2*a^40 + a^80 + a^100 + O(a^105)
            sage: HK.coleman_integral(w,P,Q)
            2*5^2 + 5^4 + 5^5 + 3*5^6 + O(5^7)

        AUTHOR:

        - Jennifer Balakrishnan

        """
        HJ = self.curve_over_ram_extn(d)
        S = self.get_boundary_point(HJ,P)
        P_to_S = self.coleman_integral_P_to_S(w,P,S)
        S_to_Q = HJ.coleman_integral_S_to_Q(w,S,Q)
        return P_to_S + S_to_Q


    def init_height(self,divisor1,divisor2,prec=20,cggen=False):
        """
        Initializes and caches certain quantities for p-adic local height computation

        AUTHOR:

        - Jennifer Balakrishnan
        """
        import sage.schemes.hyperelliptic_curves.monsky_washnitzer  as monsky_washnitzer
        g = self.genus()
        K = self.base_ring()
        p = K.prime()
        try:
            M_frob, forms = self._frob_calc
        except AttributeError:
            M_frob, forms = self._frob_calc = monsky_washnitzer.matrix_of_frobenius_hyperelliptic(self)
        A = matrix(K, M_frob).transpose() - 1
        m = max(a.valuation() for a in A.list())
        self._prec = max(m,prec)
        self._fwstrass = self.finite_weierstrass_points()
        self._div1 = divisor1
        self._div2 = divisor2
        self._cpm = self.cup_product_matrix()
        self._pth_roots = [self.find_pth_root_point(divisor1[i][1]) for i in range(2)]
        self._diff_log_div1 = self.differential_log(divisor1,prec)
        self._diff_log_div2 = self.differential_log(divisor2,prec)

        self._diff_log_hol_div1 =  vector([self._diff_log_div1[i] for i in range(g)]+[0]*g)

    def eta_integral(self,divisor1,divisor2,prec=5):
        """
        Coleman integral of eta, in the notation of Balakrishnan-Besser,
        ``Coleman-Gross height pairings and the p-adic sigma function,'' IMRN 2012

        AUTHOR:
            -- Jennifer Balakrishnan (2007-12)
        """
        coeffs = self._diff_log_hol_div1
        g = self.genus()
        int = self.coleman_integrals_on_basis(divisor2[1][1],divisor2[0][1])
        return coeffs*int

    def sum_of_local_symbols(self, divisor, prec=20):
        """
        For $w$ a differential with given residue divisor and $w_0,...,
        w_{2g-1}$ the basis of de Rham cohomology, computes
        $\{\sum_P <w,w_i>_P\}_{i=0,...,2g}$, where the sum is taken over all
        points $P$ in the divisor as well as all weierstrass points.

        NOTE: Assumes that divisor is of the form (P)-(Q)

        AUTHOR:
            -- Jennifer Balakrishnan (2007-12)
        """
        x,y = self.monsky_washnitzer_gens()
        w = self.invariant_differential()
        g = self.genus()
        P = divisor[0][1]
        Q = divisor[1][1]
        local = vector([divisor[1][0]*self.coleman_integral(w*x**j,P,Q) for j in range(2*g)])
        return local

    def differential_log(self, divisor, prec=40):
        """
        Given the hyperelliptic curve $C$, computes the
        log of a differential with given residue divisor
        lies in H^1_dR(C)

        This is Psi(w)

        if g = 1, W is spanned by x^(g+1) dx/y, ... x^(2g-1) dx/y
        else W is unit root subspace, given by Frob^n (x^(g+1) dx/y), ..., Frob^n (x^(2g-1) dx/y)
        EXAMPLES:
            sage: K = pAdicField(11,5)
            sage: R.<x> = PolynomialRing(K)
            sage: C = HyperellipticCurve(x^5-23*x^3+18*x^2+40*x)
            sage: P = C(1,6)
            sage: Q = C(-2,12)
            sage: C.differential_log([(1,P),(-1,Q)])

        AUTHOR:
            - Jennifer Balakrishnan (2007-12)
        """
        A = self._cpm
        v = self.sum_of_local_symbols(divisor,prec)
        g = self.genus()
        if v == vector([0]*2*g):
            return v
        import sage.schemes.hyperelliptic_curves.monsky_washnitzer as monsky_washnitzer
        try:
            M_frob, forms = self._frob_calc
        except AttributeError:
            M_frob, forms = self._frob_calc = monsky_washnitzer.matrix_of_frobenius_hyperelliptic(self)
        default_prec = self.base_ring().precision_cap()
        if g == 1:
            X = (M_frob**(default_prec)).matrix_from_columns([1]).transpose().list()
        else:
            X = (M_frob**(default_prec)).matrix_from_columns(range(g,2*g)).transpose().list()
        if g == 1:
            I = identity_matrix(2*g).matrix_from_columns([0]).transpose().list()
        else:
            I = identity_matrix(2*g).matrix_from_columns(range(g)).transpose().list()
        V = matrix(2*g,2*g, I + X).transpose()
        self._subspace = V
        return V**(-1)*(A**-1*v)

    def omega_integral(self,divisor1,divisor2,prec=20,cggen=False):
        """
        Coleman integral of omega, in the notation of Balakrishnan-Besser,
        ``Coleman-Gross height pairings and the p-adic sigma function,'' IMRN 2012
        Updated to handle cases considered in Balakrishnan-Besser-Mueller,
        ``Computing integral points on hyperelliptic curves using quadratic Chabauty,'' Math Comp 2017

        AUTHOR:
            - Jennifer Balakrishnan
        """
        p = self.base_ring().prime()
        P = divisor1[0][1]
        Q = divisor1[1][1]
        R = divisor2[0][1]
        S = divisor2[1][1]
        f = self.hyperelliptic_polynomials()[0]
        if self.is_same_disc(R,S):
            x,y,z= self.local_analytic_interpolation(S,R,5*prec)
            diff = self.diff(divisor1,x,y,True,False)
            int_diff = diff.integral()
            I = sum(int_diff.list())
            return I
        FR = self.frobenius(R)
        if R != FR:
            x,y,z = self.local_analytic_interpolation(R,FR,2*prec)
            if self.is_same_disc(R,P) == False and  self.is_same_disc(R,Q) == False:
                R_to_FR = (self.diff(divisor1,x,y,tiny=True)).integral()
                R_to_FR = R_to_FR.truncate(R_to_FR.degree()+1)
                R_to_FR = R_to_FR(1)
            #this is the case of beta having residue divisor "Q - wQ" in the notation of our paper
            elif P[0] == Q[0] and P[1] == -Q[1]:
            #changing P to R, P' to FR, Q to P (in our paper)
                f = self.hyperelliptic_polynomials()[0]
                diffpart1 = (f(P[0]) - f(x))*x.derivative()/(y*(x - P[0])*(P[1] + y))
                intpart = (diffpart1.integral())
                intpart = intpart.truncate(intpart.degree()+1)
                intpart1 = intpart(1)
                R_to_FR = intpart1 +log(FR[0]-P[0],0) - log(R[0] - P[0],0)
            elif self.is_same_disc(R,P):
                f = self.hyperelliptic_polynomials()[0]
                diffpart1 = (f(P[0]) - f(x))*x.derivative()/(2*y*(x-P[0])*(P[1] + y))
                intpart = (diffpart1.integral())
                intpart = intpart.truncate(intpart.degree()+1)
                intpart1 = intpart(1)
                diffpart2 = x.derivative()/(2*y)*(y + Q[1])/(x - Q[0])
                intpart2 = diffpart2.integral().truncate(2*prec)(1)
                R_to_FR = intpart1 +log(FR[0]-P[0],0) - log(R[0] - P[0],0) - intpart2
            elif self.is_same_disc(R,Q):
                f = self.hyperelliptic_polynomials()[0]
                diffpart1 = (f(Q[0]) - f(x))*x.derivative()/(2*y*(x-Q[0])*(Q[1] + y))
                intpart = (diffpart1.integral())
                intpart = intpart.truncate(intpart.degree()+1)
                intpart1 = intpart(1)
                diffpart2 = x.derivative()/(2*y)*(y + P[1])/(x - P[0])
                intpart2 = diffpart2.integral().truncate(2*prec)(1)
                R_to_FR = intpart2  - (intpart1 +log(FR[0]-Q[0],0) - log(R[0] - Q[0],0))
        else:
            R_to_FR = 0
        FS = self.frobenius(S)
        if S !=FS:
            if self.is_same_disc(S,P) == False and self.is_same_disc(S,Q) == False:
                x,y,z = self.local_analytic_interpolation(FS,S,2*prec)
                FS_to_S = (self.diff(divisor1,x,y,tiny=True)).integral()
                FS_to_S = FS_to_S.truncate(FS_to_S.degree()+1)
                FS_to_S = FS_to_S(1)
            elif P[0] == Q[0] and P[1] == -Q[1] and S[0] == R[0] and S[1] == -R[1]:
                FS_to_S = R_to_FR
            else:
                print S, FS, P, Q
        else:
            FS_to_S = 0
        res = self.res(divisor1,divisor2,prec)
        ab = self.res_alpha_int_beta(divisor1, divisor2, prec,cggen)
        cups = self.psiA_cup_psiB(divisor1,divisor2,prec)
        return 1/(1-p)*(cups+res+ab-FS_to_S-R_to_FR)

    def res(self,divisor1,divisor2,prec=30, cggen=False):
        """
        Returns sum(res(alpha*integral(beta))), where alpha and beta are
        in the notation of Balakrishnan-Besser,
        ``Coleman-Gross height pairings and the p-adic sigma function,'' IMRN 2012
        (need to sum over all of the right residue discs)
        alpha[0] is at P
        alpha[1] is at Q
        alpha[2] is at zeta_p x(P)^(1/p)
        alpha[3] is at zeta_p x(Q)^(1/p)
        alpha[4] is at finite weierstrass_1
        ...
        alpha[2g+4] is at finite weierstrass_{2g+1}
        alpha[2g+5] is at infinity

        AUTHOR:
            - Jennifer Balakrishnan
        """
        from sage.schemes.hyperelliptic_curves.constructor import HyperellipticCurve
        K = self.base_ring()
        p = K.prime()
        A = self.alpha(divisor1,prec)
        div3 = self._pth_roots
        B = []
        r = self._fwstrass
        prec = self.base_ring().precision_cap()
        g = self.genus()
        for R in r:
            if R[0] !=0:
                x,y = self.local_coord(R,2*p*prec-p+2*g-1)
                B = B + [self.diff(divisor2,x,y)]
        dd= [f.degree() for f in B]
        Anew = []
        for i in range(len(A)):
            v = B[i].valuation()
            try:
                Anew = Anew + [A[i].truncate_neg(v-max(dd))]
            except AttributeError:
                Anew = [A[i]]
        ddd = [f.degree() for f in Anew]
        res = [Anew[i]*((B[i]).integral()) for i in range(len(Anew))]
        dddd = [f.degree() for f in res]
        res = [res[i].residue() for i in range(len(res))]
        S = K['x']
        f = S(self.hyperelliptic_polynomials()[0])
        degrees = [x[0].degree() for x in f.factor()]
        if len(r) == 2*g + 1:
            return sum(res)
        else: #here len(r) != 2*g+1 so we have to construct splitting fields
            if g >  6:
                raise NotImplementedError
            oldres = sum(res)
            f = self.hyperelliptic_polynomials()[0]
            if g == 1:
                if len(r) == 1:
                    S = K[[f.parent().variable_name()]]
                    S.set_default_prec(p+1)
                    x = S.gen()
                    oldprod = x - r[0][0]
                    newg = (S(f)/S(oldprod)).truncate(p)
                    J = K.extension(newg, names = 'b')
                elif len(r) == 0:
                    J = K.extension(f,names= 'b')
                b = J.gen()
                EJ = self.change_ring(J)
                newr = self._newr = [EJ(b,0)]
            if g == 2:
                degrees = [x[0].degree() for x in f.factor()]
                if degrees == [5]:
                    J = K.extension(f,names='b')
                    b = J.gen()
                    HJ = self.change_ring(J)
                    newr = self._newr = [HJ(b,0)]
                elif (degrees == [1,4] or degrees == [1,1,1,3] or degrees == [1,1,1,2]):
                    S = K[[f.parent().variable_name()]]
                    x = S.gen()
                    oldprod=1
                    for i in range(len(r)):
                        oldprod = oldprod*(x-r[i][0])
                    J = K.extension((S(f)/S(oldprod)).polynomial(), names = 'b')
                    b = J.gen()
                    HJ = self.change_ring(J)
                    newr = self._newr = [HJ(b,0)]
                elif degrees == [1,2,2]:
                    pols = f.factor()
                    #print
                    J = K.extension(pols[1][0],names='b')
                    b = J.gen()
                    L = K.extension(pols[2][0],names='c')
                    c = L.gen()
                    newr = self._newr = [(b,0),(c,0)]
                elif degrees == [2,3]:
                    pols = f.factor()
                    J = K.extension(pols[0][0],names='b')
                    b = J.gen()
                    L = K.extension(pols[1][0],names='c')
                    c = L.gen()
                    newr = self._newr = [(b,0),(c,0)]
            if g == 3:
                rcount = len(r)
                pols = f.factor()
                if degrees == [7]:
                    J = K.extension(f,names='b')
                    b = J.gen()
                    HJ = self.change_ring(J)
                    newr = self._newr = [HJ(b,0)]
                elif (degrees == [1,6] or degrees == [1,1,5] or degrees == [1,1,1,4] or \
                      degrees == [1,1,1,1,3] or degrees == [1,1,1,1,1,2]):
                    J = K.extension(pols[rcount][0],names='b')
                    b = J.gen()
                    HJ = self.change_ring(J)
                    newr = self._newr = [HJ(b,0)]
                elif (degrees == [2,5] or degrees == [3,4] or degrees == [1,2,4] or \
                      degrees == [1,3,3] or degrees == [1,1,2,3] or degrees == [1,1,1,2,2]):
                    J = K.extension(pols[rcount][0],names='b')
                    b = J.gen()
                    L = K.extension(pols[rcount+1][0],names='c')
                    c = L.gen()
                    newr = self._newr = [(b,0),(c,0)]
                elif (degrees == [2,2,3] or degrees == [1,2,2,2]):
                    pols = f.factor()
                    J = K.extension(pols[rcount][0],names='b')
                    b = J.gen()
                    L = K.extension(pols[rcount+1][0],names='c')
                    c = L.gen()
                    M = K.extension(pols[rcount+2][0],names='d')
                    d = M.gen()
                    newr = self._newr = [(b,0),(c,0),(d,0)]
            if g == 4:
                rcount = len(r)
                pols = f.factor()
                if degrees == [9]:
                    J = K.extension(f,names='b')
                    b = J.gen()
                    HJ = self.change_ring(J)
                    newr = self._newr = [HJ(b,0)]
                elif degrees in [[1,8], [1,1,7], [1,1,1,6], [1,1,1,1,5], [1,1,1,1,1,4],\
                                 [1,1,1,1,1,1,3], [1,1,1,1,1,1,1,2]]:
                    J = K.extension(pols[rcount][0],names='b')
                    b = J.gen()
                    HJ = self.change_ring(J)
                    newr = self._newr = [HJ(b,0)]
                elif degrees in [[1,3,5], [3,6], [1,2,6], [1,1,2,5], [4,5], [2,7],\
                                 [1,4,4], [1,1,3,4], [1,1,1,2,4], [1,1,1,1,2,3], [1,1,1,3,3],\
                                 [1,1,1,1,1,2,2]]:
                    J = K.extension(pols[rcount][0],names='b')
                    b = J.gen()
                    L = K.extension(pols[rcount+1][0],names='c')
                    c = L.gen()
                    newr = self._newr = [(b,0),(c,0)]
                elif degrees in [[2,3,4],[2,2,5],[3,3,3],[1,2,2,4],[1,2,3,3],[1,1,2,2,3],[1,1,1,2,2,2]]:
                    pols = f.factor()
                    J = K.extension(pols[rcount][0],names='b')
                    b = J.gen()
                    L = K.extension(pols[rcount+1][0],names='c')
                    c = L.gen()
                    M = K.extension(pols[rcount+2][0],names='d')
                    d = M.gen()
                    newr = self._newr = [(b,0),(c,0),(d,0)]
                elif degrees in [[1,2,2,2,2],[2,2,2,3]]:
                    pols = f.factor()
                    J = K.extension(pols[rcount][0],names='b')
                    b = J.gen()
                    L = K.extension(pols[rcount+1][0],names='c')
                    c = L.gen()
                    M = K.extension(pols[rcount+2][0],names='d')
                    d = M.gen()
                    N = K.extension(pols[rcount+3][0],names='e')
                    e = N.gen()
                    newr = self._newr = [(b,0),(c,0),(d,0),(e,0)]
            if g == 5:
                raise NotImplementedError
            if g == 6:
                rcount = len(r)
                pols = f.factor()
                if degrees == 8*[1] + [2,3]:
                    J = K.extension(pols[rcount][0],names='b')
                    b = J.gen()
                    L = K.extension(pols[rcount+1][0],names='c')
                    c = L.gen()
                    newr = self._newr = [(b,0),(c,0)]
                else:
                    raise NotImplementedError
            newres = []
            for R in newr:
                x,y = self.local_coord(R, 2*p*prec - p - 3 + 2*g - 1 + 5)
                newfrob = self.frob_diff_wstrass(divisor1, x, y, prec)
                newdiff = self.diff(divisor1, x, y)
                newbeta = self.diff(divisor2, x, y)
                newalpha = newfrob - p*newdiff
            try:
                newres = newres + [(newalpha*newbeta.integral()).residue().trace()]
            except AttributeError:
                newres = newres + [(newalpha*newbeta.integral()).residue()]
            newres = sum(newres)
            return oldres + newres

    def alpha(self, divisor, prec=20,all=False):
        """
        Returns alpha = phi^*w - p*w in the various local coordinates, where
        w has residue divisor (P)-(Q) and

        if all = True: P, Q, pth roots, then weierstrass
        else: just finite weierstrass

        #alpha[0] is at P
        #alpha[1] is at Q
        #alpha[2] is at zeta_p x(P)^(1/p)
        #alpha[3] is at zeta_p x(Q)^(1/p)
        have to re-index the following:

        alpha[4] is at finite weierstrass_1
        ...
        alpha[2g+4] is at finite weierstrass_{2g+1}
        alpha[2g+5] is at infnity

        So we have the following consistency checks (since res in each disc is supposed to be 0):
        (this also works when supp(divisor) is just in 1 disc)

        alpha[0].residue() + alpha[2].residue().trace() = 0
        alpha[1].residue() + alpha[3].residue().trace() = 0
        alpha[4].residue() = ... = alpha[2g+5].residue() = 0

        sage: R.<x> = QQ['x']
        sage: K = Qp(7,6)
        sage: H = HyperellipticCurve(x*(x-1)*(x+9))
        sage: HK = H.change_ring(K)
        sage: P = HK(-1,4)
        sage: Q = HK(9,-36)
        sage: a = HK.alpha([(1,P),(-1,Q)])
        sage: (a[2]).residue().trace()+(a[0]).residue()
        O(7^5)
        sage: (a[3]).residue().trace()+(a[1]).residue()
        O(7^4)
        sage: [(a[i]).residue() for i in range(4,8)]
        [0, 0, 0, 0]

        AUTHOR:
            - Jennifer Balakrishnan
        """
        g = self.genus()
        p = self.base_ring().prime()
        if all:
            D1 = [divisor[0][1],divisor[1][1]]
        D2 = self._pth_roots
        frob = []
        diff = []
        if all:
            for i in range(2):
                x,y = self.local_coord(D1[i],2*prec)
                frob = frob+ [self.frob_diff_nw(divisor,x,y,prec)]
                diff = diff + [self.diff(divisor,x,y)]
            for i in range(2):
                x,y = self.local_coord(D2[i],2*prec)
                frob = frob + [self.frob_diff_nw(divisor,x,y,prec)]
                diff = diff + [self.diff(divisor,x,y)]
        r = self._fwstrass
        for R in r:
            if R[0] != 0:
                x,y = self.local_coord(R,2*p*prec-p+2*g-1) #this seems to be the min for prec=5
                frob = frob + [self.frob_diff_wstrass(divisor,x,y,prec)]
                diff = diff + [self.diff(divisor,x,y)]
        alpha = [frob[i]-p*diff[i] for i in range(len(frob))]
        return alpha

    def find_pth_root_point(self,P,all=False):
        """
        Given P=(a,b), finds a point P'=(a',b') over Qp(a^(1/p) such that
        a'^p = a

        if all=True, find all pth roots

        AUTHOR:
            - Jennifer Balakrishnan
        """
        K = self.base_ring()
        p = K.prime()
        xP = P[0]

        g = self.hyperelliptic_polynomials()[0]
        ###working over the appropriate field
        R = QQ['x']
        x = R.gen()
        self._sanity = sanity = None
        if xP**p==xP:
            f = cyclotomic_polynomial(p,var='y')
            J = K.extension(f(x+1),names='a')
        else:
            try:

                J = K.extension((x+QQ(xP))**p-QQ(xP),names='a')
            except (NameError, ValueError, NotImplementedError):
                try:
                    J = K.extension((x+xP)**p - (xP), names='a')
                except (NameError, NotImplementedError):
                    try:
                        rootshere = (x**p - xP).roots()
                    except :
                        #do hensel lifting
                        gg = x**p - xP
                        rootsmodp = GF(p)['x'](gg).roots()
                        xi = ZZ(rootsmodp[0][0])
                        for j in range(1,K.precision_cap()):
                            for i in range(p):
                                if gg(xi + i*p**j).valuation() == j+2:
                                    xi = xi + i*p**j
                                    break
                        r = xi
                        rootshere = [(r,1)]
                    if len(rootshere) > 0:
                        S = K[['x']]
                        S.set_default_prec(p+1)
                        newg = (S(x**p-xP)/(S(x-rootshere[0][0]))).truncate(p)
                        for i in range(p):
                            try:
                                J = K.extension(newg(x+i), names='a')
                                sanity = i
                                self._sanity = sanity
                                self._extrart = rootshere[0][0]
                            except (NameError,ValueError,NotImplementedError):
                                pass
                    else:
                        print "Sorry! Extension failed!"
        a = J.gen()
        HJ = self.change_ring(J)

        #find the pth roots of x(P)
        if xP**p == xP:
            xPfracpow = (1+a)*xP
        elif sanity == None:
            xPfracpow = a+xP
        else:
            xPfracpow = a + sanity
        if g(xPfracpow)==0:
            return HJ(xPfracpow,0)
        yPfracpow = HJ.square_root_extension(g(xPfracpow))
        Pfracpow = HJ(xPfracpow,yPfracpow)
        P = HJ(P[0],P[1])
        if P[0]==Pfracpow[0] :
            xnew = (a+xP)*Pfracpow[0]
            ynew = HJ.square_root_extension(g(xnew))
            Pfracpow = HJ(xnew,ynew)
        if ((Pfracpow[1]).list()[0] == (P[1]).list()[0]):
            point =  Pfracpow
        else:
            point = HJ(Pfracpow[0],-Pfracpow[1])
        if all == False:
            return point
        else:
            if xP**p != xP:
                print "Sorry, we can only print all of the roots when the extension is cyclotomic."
                return point
            else:
                pts = [point]
                xs = [(a+1)**i*(pts[0][0]) for i in range(1,p-1)]
                ys = [HJ.square_root_extension(g(x)) for x in xs]
                ynew = []
                for y in ys:
                    if y.list()[0] != (P[1]).list()[0] :
                        ynew = ynew + [-y]
                    else:
                        ynew = ynew + [y]
                pts = pts + [HJ(xs[i],ynew[i]) for i in range(len(xs))]
                return pts
    def square_root_extension(self,num):
        """
        Takes a square root in a p-adic extension
        """
        p = self.base_ring().prime()
        if num.valuation() == 0:
            c = num.list()[0]
            i = 1
            while i <p//2:
                if (i**2)%p == c:
                    break
                i=i+1
        ###Newton's method for square root
        j = 0
        while j <200:       #change prec if needed
            root = (i+num/i)/2
            if i == root:
                break
            i = root
            j = j+1
        if i**2 == num:
            return i

    def frob_diff_wstrass(self, divisor,x,y,prec=20):
        """
        Returns the action of Frobenius on the differential w associated
        to the divisor (P)-(Q) wrt local coordinates of a Weierstrass point

        Will not work for prime p = 2.

        This is phi^*w

        AUTHOR:
            - Jennifer Balakrishnan (2008-02)
        """
        p = self.base_ring().prime()
        P = divisor[0][1]
        Q = divisor[1][1]
        a,b,z = P
        c,d,zz =Q
        diff = p*x**(p-1)/(2*(x**p-a)*(x**p-c))*(a-c+((b-d)*x**p+a*d-b*c)*self.recip_froby(x,y,prec))*x.derivative()
        return diff

    def recip_froby(self,x,y,prec=10):
        """
        Given local expansions x(t) and y(t), computes the reciprocal of the Frobenius of y

        AUTHOR:
            - Jennifer Balakrishnan
        """
        f = self.hyperelliptic_polynomials()[0]
        p = self.base_ring().prime()
        s = 1+sum(self.Bm(i)*( (f(x**p)-f(x)**p)/(f(x)**p))**i for i in range(1,prec))
        return y**(-p)*s

    def Bp(self, i):
        """
        Binomial coeff (1/2,i)
        """
        return binomial(QQ(1)/QQ(2),i)

    def Bm(self, i):
        """
        Binomial coeff (-1/2,i)
        """
        return binomial(QQ(-1)/QQ(2),i)

    def diff(self,divisor,x,y,tiny=False,alpha=False):
        """
        Writing differential with residue divisor "divisor" in terms of x,y (an interpolation usually)

        alpha=True: truncates diffP to get rid of meaningless terms

        AUTHOR:
            - Jennifer Balakrishnan
        """
        P = divisor[0][1]
        Q = divisor[1][1]
        a,b,nn = P
        c,d,nn = Q
        g = self.genus()
        p = P[0].parent().prime()
        f = self.hyperelliptic_polynomials()[0]
        xt = x.truncate(x.degree()+1)
        yt = y.truncate(y.degree()+1)
        Z = (xt(0),yt(0))
        if (a==c and b==-d and self.is_good(P,Z) and self.is_good(Q, Z) ):
            return b*x.derivative()/(y*(x-a))
        elif P == self(0,1,0):
            return -x.derivative()/(2*y)*(y+d)/(x-c)
        elif Q == self(0,1,0):
            return x.derivative()/(2*y)*(y+b)/(x-a)
        elif (tiny==False or self.is_good(P, Z)):
            forP = (y+b)/(x-a)
        else:
            hP = ((f(x)-f(a))/(x-a))
            t = x.parent().gen()
            if hP.list()[-1]==0:
                if g== 1:
                    hP = x**2+x*a+a**2 + f.list()[2]*(x+a)+f.list()[1]
            forP = hP/(y-b)
        if (tiny==False or self.is_good(Q, Z)):
            forQ = (y+d)/(x-c)
        else:
            hQ = ((f(x)-f(c))/(x-c)).truncate(2*g+1)
            if hQ.list()[-1]==0:
                if g == 1:
                    hQ = x**2+x*c+c**2 + f.list()[2]*(x+c)+f.list()[1]
            forQ =hQ/(y-d)
        alpha = False
        if alpha:
            i = 0
            while i < len(forP.list())-3:
                if (forP.list()[i]==0 and forP.list()[i+1]==0 and forP.list()[i+2]==0):
                    forP = forP.truncate(i)
                    break
                else:
                    i=i+1
            i = 0
            while i < len(forQ.list())-3:
                if (forQ.list()[i]==0 and forQ.list()[i+1]==0 and forQ.list()[i+2]==0):
                    forQ = forQ.truncate(i)
                    break
                else:
                    i = i+1
        return x.derivative()/(2*y)*(forP-forQ)

    def is_good(self,P,R):
        """
        Checks if point P is good wrt R
        """
        if (P[0] == R[0] and P[1] == -R[1]):
            return True
        elif (self.is_neg_disc(P,R)==False):
            return True
        else:
            return False

    def is_neg_disc(self,P,Q):
        """
        Checks if P is in disc(hyperelliptic_involution(Q))
        """
        K = self.base_ring()
        if (P[0][0] == Q[0][0] and K(P[1][0])==K((-Q[1])[0])):
            return True
        else:
            return False

    def res_alpha_int_beta(self, divisor1, divisor2, prec=20, cggen=False):
        """
        Returns sum(res(alpha*(int(beta) + c))) where c is the right constant of integration
        and the sum is over non-Weierstrass poles of alpha

        AUTHOR:
            - Jennifer Balakrishnan
        """
        prec = prec
        p = self.base_ring().prime()
        g = self.genus()
        pth_roots = self._pth_roots
        P = divisor1[0][1]
        Q = divisor1[1][1]
        ####integrate beta from P to P_i, take the trace
        if P[0] != 0:
            x,y = self.local_analytic_interpolation_cyclotomic(P, pth_roots[0][0],3*p*prec+prec*g+1)
            xD21 = divisor2[0][1][0]
            xD22 = divisor2[1][1][0]
            yD21 = divisor2[0][1][1]
            if self.is_same_disc(P,divisor2[0][1]) and xD21 == xD22:
                xcoord = divisor2[0][1][0]
                ycoord = divisor2[0][1][1]
                f = self.hyperelliptic_polynomials()[0]
                betaP = x.derivative() * (f(xcoord) - f(x)) /(x - xcoord) * 1/(y.parent()(ycoord) + y)/y
                int_betaP_part = betaP.integral()
                int_betaP_part = int_betaP_part.truncate(int_betaP_part.degree()+1)
                log1 = log(pth_roots[0][0] - xcoord , 0)
                log2 = log(P[0] - xcoord,0)
                if self._sanity == None:
                    I1 = int_betaP_part(1) + (log1 - log2)
                else:
                #the sanity business is this problem that we encountered for x^7 - 48, where one root was over Qp...
                    rt = self.lift_x(self._extrart)
                    if self.is_same_disc(rt,P) == False:
                        rt = self(rt[0],-rt[1])
                    x,y,z = self.local_analytic_interpolation(P,rt)
                    betaP_P_rt = x.derivative() * (f(xcoord) - f(x)) /(x - xcoord) * 1/(y.parent()(ycoord) + y)/y
                    log3 = log(rt[0] - xcoord,0)
                    log4 = log(P[0] - xcoord,0)
                    I1 = int_betaP_part(1) + (log1 - log2)
            else:
                betaP = self.diff(divisor2, x,y,True,True)
                int_betaP = (betaP).integral()
                int_betaP = int_betaP.truncate(int_betaP.degree()+1)
                I1 = int_betaP(1)-int_betaP(0)
            if I1 != 0:
                if self._sanity == None:
                    I1 = I1.trace()
                else:
                    try:
                        I1 = I1.trace() + (betaP_P_rt.integral())(1) + log3 - log4
                    except UnboundLocalError:
                        rt = self.lift_x(self._extrart)
                        if self.is_same_disc(rt,P) == False:
                            rt = self(rt[0],-rt[1])
                        if self.is_same_disc(rt,P) == False:
                            I1 = I1.trace()
                        else:
                            x,y,z = self.local_analytic_interpolation(P,rt)
                            betaPbonus = self.diff(divisor2,x,y,True,True)
                            intbetaPbonus = betaPbonus.integral()
                            intbetaPbonus = intbetaPbonus.truncate(intbetaPbonus.degree()+1)
                            I1 = I1.trace() + intbetaPbonus(1)
            else:
                I1 = 0
        else:
            I1 = 0
        if self.is_same_disc(P,Q):
            ##if in same disc, then trace(\int(beta, P,Q_i))
            xx,yy = self.local_analytic_interpolation_cyclotomic(P,pth_roots[1][0], 3*p*prec+prec*g+1)
            betaQ = self.diff(divisor2,xx,yy,True,True)
            int_betaQ = (betaQ).integral()
            int_betaQ = int_betaQ.truncate(int_betaQ.degree()+1)
            I2 = int_betaQ(1)-int_betaQ(0)
            ##also have to integrate beta from P to Q
            xx2,yy2,z = self.local_analytic_interpolation(P,Q,2*p*prec)  ##prev: lai2
            fix = self.diff(divisor2,xx2,yy2,True,True)
            fix = (fix).integral()
            fix = sum(fix.list())
            xA,yA = self.local_coord(Q,prec)
            alphaQ = self.frob_diff_nw(divisor1,xA,yA,prec)-p*self.diff(divisor1,xA,yA)
            const = alphaQ.list()[0]
            return I1 - I2.trace() +  const*fix
        if Q[0] == P[0] and Q[1] == -P[1]:
            return 2*I1
        else:
            if Q[0] != 0:
                xx,yy = self.local_analytic_interpolation_cyclotomic(Q, pth_roots[1][0], 3*p*prec+2*g+1)
                if self.is_same_disc(Q,divisor2[1][1]):
                    ycoord = divisor2[1][1][1]
                    betaQ = ycoord*xx.derivative()/(xx-xcoord)*(1/yy + 1/yy.parent()(ycoord))
                    int_betaQ_part = betaQ.integral()
                    int_betaQ_part = int_betaQ_part.truncate(int_betaQ_part.degree()+1)

                    log1 = log(pth_roots[1][0] - xcoord,0)
                    log2 = log(Q[0] - xcoord, 0)
                    I2 = int_betaQ_part(1) - (log1 - log2)
                elif self.is_same_disc(Q,divisor2[0][1]):
                    print 'We need to do this case'
                else:
                    betaQ = self.diff(divisor2, xx,yy,True, True)
                    int_betaQ = (betaQ).integral()
                    int_betaQ = int_betaQ.truncate(int_betaQ.degree()+1)
                    I2 = int_betaQ(1)-int_betaQ(0)
            else:
                I2 = 0
            if I2 != 0:
                I2 = I2.trace()
                return I1 - I2
            else:
                return I1

    def psiA_cup_psiB(self,divisor1,divisor2,prec=5):
        """
        Returns the cup product of psiA and psiB

        AUTHOR:
            - Jennifer Balakrishnan (2008-05)
        """
        psiB = self._diff_log_div2
        if psiB == vector([0]*2*self.genus()):
            return 0
        psiA = self.psi_alpha(divisor1,prec)
        V = self._subspace
        psiB = V*psiB
        return self.cup(psiA,psiB)

    def psi_alpha(self,divisor,prec=20):
        """
        Computes Psi(alpha)= Psi(phi^*w-p*w) as phi^*(Psi(w))-p*Psi(w)

        AUTHOR:
            - Jennifer Balakrishnan
        """
        frob_psiw = self.frob_psi_diff(divisor,prec)
        p = self.base_ring().prime()
        if divisor == self._div1:
            psiw = self._diff_log_div1
        elif divisor == self._div2:
            psiw = self._diff_log_div2
        else:
            psiw = self.differential_log(divisor,prec)
        V = self._subspace
        return frob_psiw - p*V*psiw

    def frob_psi_diff(self,divisor,prec=20):
        """
        Computes Frobenius of Psi(diff), where diff has residue divisor
        "divisor"

        AUTHOR:
            - Jennifer Balakrishnan
        """
        import sage.schemes.hyperelliptic_curves.monsky_washnitzer as monsky_washnitzer
        M_frob, forms = self._frob_calc = monsky_washnitzer.matrix_of_frobenius_hyperelliptic(self)
        if divisor == self._div1:
            psiw = self._diff_log_div1
        elif divisor == self._div2:
            psiw = self._diff_log_div2
        else:
            psiw = self.differential_log(divisor,prec)
        V = self._subspace
        frob_psiw = M_frob*V*psiw
        return frob_psiw

    def cup(self,v,w):
        """
        Computes the cup product of the vectors v and w with respect to
        MW cohomology

        AUTHOR:
            - Jennifer Balakrishnan
        """
        M = self.cup_product_matrix()
        sum = 0
        for i in range(len(v.list())):
            for j in range(len(w.list())):
                sum = sum+ v[i]*w[j]*M[i,j]
        return sum

    def local_analytic_interpolation_cyclotomic(self,P,Q,prec=100):
        """
        Given P and x(Q), with P,Q
        in the same residue disc and P defined over Qp,
        this computes the local analytic interpolation
        between P,Q

        USE: for non-weierstrass points
        """
        #print "local_analytic_interpolation_cyclotomic", prec
        R = Q.parent()[['t']]
        t = R.gen()
        R.set_default_prec(prec)
        x,y = self.local_coord(P,prec)      #figure out precision here
        X = (x(R((Q-P[0])*t)))
        Y = (y(R((Q-P[0])*t)))
        return X,Y

    def sum_of_local_symbols_extension(self,divisor,P,Q,extension=False, prec=200):
        """
        Computes the vector of local symbols (<w,w_i>_A)_{i=0...2g-1}, where w is a differential form with residue divisor "divisor"

        if extension== True, creates the appropriate field extension and curve over that extension

        P is fixed point for all computations to link constants of integration
        Q is the residue disc where all the stuff should be happening

        TODO: merge with sum_of_local_symbols, make more modular
        """
        p = self.base_ring().prime()
        print 'sum of local symbols extn = ', prec
        if Q[1] == 0:
            wstrass = True
        else:
            wstrass = False
        if extension==True:
            A = self.find_pth_root_point(Q)
        else:
            A = Q
        g = self.hyperelliptic_polynomials()[0]
        gen = self.genus()

        ###working over the appropriate field
        cyc = False
        if extension==True:
            R = QQ['x']
            x = R.gen()
            if cyc==True:
                f = cyclotomic_polynomial(p)
                J = self.base_ring().extension(f(x+1),names='a')
            else:
                if Q[0]**p==Q[0]:
                    f =((x+Q[0])**p-Q[0])
                    d = f.degree()
                    ff = sum(f.list()[i]*x**(i-1) for i in range(1,d+1))
                    J = self.base_ring().extension(ff,names='a')
                else:
                    J = self.base_ring().extension((x+Q[0])**p-Q[0],names='a')
            a = J.gen()
            H = self.change_ring(J)
        else:
            H = self

        x,y = H.local_coord(A,prec)     #worry about prec later
        ###formal antiderivative of w_i
        try:
            I2 = vector(J,[0]*2*gen)
        except UnboundLocalError:
            R = QQ['x']
            x = R.gen()
            if cyc == True:
                f = cyclotomic_polynomial(p)
                J = self.base_ring().extension(f(x+1),names='a')
            else:
                if Q[0]**p==Q[0]:
                    f =((x+Q[0])**p-Q[0])
                    d = f.degree()
                    ff = sum(f.list()[i]*x**(i-1) for i in range(1,d+1))
                    J = self.base_ring().extension(ff,names='a')
                else:
                    J = self.base_ring().extension((x+Q[0])**p-Q[0],names='a')
            I2 = vector(J,[0]*2*gen)
        ##shouldnt this always be true?
        extension = True
        ###if working over an extension, need tiny integral + coleman integral over Qp
        if extension == True:
            xx,yy = H.local_analytic_interpolation_cyclotomic(Q,A[0],prec) #this will change when it's weiestrass
            Q_to_A = [(xx.derivative()*xx**i/(2*yy)).integral() for i in range(2*gen)] #changed 1210   ##changed 03/04
            I = vector([f(1)-f(0) for f in Q_to_A])  #changed 1210

            P = H(P[0],P[1])
        ###plus a Coleman integral to offset the constant if P,A aren't in the same residue disc #this will change when it's weierstrass
            xm,ym = self.monsky_washnitzer_gens()
            omega = self.invariant_differential()

            if ((P[0]).list()[0] != (A[0]).list()[0] or (P[1]).list()[0] != (A[1]).list()[0]):
                I2= vector([self.coleman_integral(omega*xm**i,divisor[0][1],divisor[1][1]) for i in range(2*gen)])
        else:
            I = vector([self.coleman_integral(omega*xm**i,divisor[0][1],A) for i in range(2*gen)]) #weierstrass case
        w  = self.frob_diff_nw(divisor,x,y,prec)
        v = [(w*(I[n]+I2[n])) for n in range(2*gen)]
        v = [f.residue_at_zero() for f in v]
        try:
            return vector([f.trace() for f in v])
        except AttributeError:
            return vector(self.base_ring(),v)


    def height(self,divisor1,divisor2,prec=None, cggen=False):
        """
        The p-part of the Coleman-Gross height pairing of divisor1 and
        divisor2/Users/jen

        If self has ordinary reduction at self.base_ring().prime(), the height pairing
        is symmetric.

        GENUS 1 EXAMPLES

        sage: R.<x> = QQ[]
        sage: H = HyperellipticCurve(x*(x-1)*(x+9))
        sage: K = Qp(7,10)
        sage: HK = H.change_ring(K)
        sage: P = HK(9,36)
        sage: Q = HK.teichmuller(P)
        sage: Pprime = HK(-4,10)
        sage: Qprime = HK.teichmuller(Pprime)
        sage: HK.height([(1,P),(-1,Q)],[(1,Pprime),(-1,Qprime)],10)
        2*7^2 + 5*7^3 + 7^4 + 7^5 + 2*7^6 + 3*7^7 + 7^8 + 3*7^9 + O(7^10)
        sage: HK.height([(1,Pprime),(-1,Qprime)],[(1,P),(-1,Q)],10)
        2*7^2 + 5*7^3 + 7^4 + 7^5 + 2*7^6 + 3*7^7 + 7^8 + 3*7^9 + O(7^10)


        sage: R.<x> = QQ[]
        sage: H = HyperellipticCurve(x*(x-1)*(x+9))
        sage: K = Qp(7,10)
        sage: HK = H.change_ring(K)
        sage: P = HK(-1,4)
        sage: Q = HK(-1,-4)
        sage: R = HK(-4,-10)
        sage: S = HK(-4,10)
        sage: Pprime = HK(25/16,195/64)
        sage: Qprime = HK(25/16,-195/64)

        Test that h_7(P-Q, R-S) + h_7(P-Q, S-Pprime) = h_7(P-Q,R-Pprime)

        sage: HK.height([(1,P),(-1,Q)],[(1,R),(-1,S)],9)
        6*7 + 5*7^2 + 2*7^3 + 4*7^4 + 7^5 + 3*7^6 + 7^7 + 4*7^9 + O(7^10)
        sage: HK.height([(1,P),(-1,Q)],[(1,S),(-1,Pprime)],9)
        4*7 + 2*7^2 + 3*7^3 + 6*7^4 + 5*7^5 + 4*7^6 + 6*7^7 + 2*7^8 + 5*7^9 + O(7^10)
        sage: HK.height([(1,P),(-1,Q)],[(1,R),(-1,Pprime)],9)
        3*7 + 7^2 + 6*7^3 + 3*7^4 + 7^6 + 7^7 + 3*7^8 + 2*7^9 + O(7^10)

        sage: 6*7 + 5*7^2 + 2*7^3 + 4*7^4 + 7^5 + 3*7^6 + O(7^7)+4*7 + 2*7^2 + 3*7^3 + 6*7^4 + 5*7^5 + 4*7^6 + 6*7^7 + 2*7^8 + 5*7^9 + O(7^10)
        3*7 + 7^2 + 6*7^3 + 3*7^4 + 7^6 + 7^7 + 3*7^8 + 2*7^9 + O(7^10)

        Test that h_7(Pprime-P, R-S) = h_7(Q-Qprime, R-S), where (Pprime)-(P) ~ (Q)-(Qprime)

        sage: HK.height([(1,Pprime),(-1,P)],[(1,R),(-1,S)],9)
        3*7 + 7^3 + 7^4 + 7^5 + 2*7^6 + 2*7^7 + 7^8 + O(7^10)

        sage: HK.height([(1,Q),(-1,Qprime)],[(1,R),(-1,S)],9)
        3*7 + 7^3 + 7^4 + 7^5 + 2*7^6 + 2*7^7 + 7^8 + O(7^10)

        GENUS 2 EXAMPLES
        (with respect to W the unit root subspace)

        sage: R.<x> = PolynomialRing(pAdicField(11,10))
        sage: H = HyperellipticCurve(x^5-23*x^3+18*x^2+40*x)
        sage: P = H(-4,24)
        sage: Pprime = H.teichmuller(P)
        sage: Q = H(5,30)
        sage: Qprime = H.teichmuller(Q)
        sage: H.height([(1,Q),(-1,Qprime)],[(1,P),(-1,Pprime)],10)
        6*11^2 + 9*11^3 + 4*11^4 + 2*11^5 + 6*11^6 + 4*11^7 + 6*11^8 + 11^9 + O(11^10)
        sage: H.height([(1,P),(-1,Pprime)],[(1,Q),(-1,Qprime)],10)
        6*11^2 + 9*11^3 + 4*11^4 + 2*11^5 + 6*11^6 + 4*11^7 + 6*11^8 + 11^9 + O(11^10)

        sage: R.<x> = PolynomialRing(pAdicField(11,10))
        sage: H = HyperellipticCurve(x^5-23*x^3+18*x^2+40*x)
        sage: P = H(-4,24)
        sage: Pprime = H(-4,-24)
        sage: Q = H(5,30)
        sage: Qprime = H(5,-30)
        sage: H.height([(1,P),(-1,Pprime)],[(1,Q),(-1,Qprime)],10)
        6*11^-1 + 10 + 7*11 + 6*11^2 + 3*11^3 + 7*11^4 + 7*11^5 + 11^6 + O(11^8)
        sage: H.height([(1,Q),(-1,Qprime)],[(1,P),(-1,Pprime)],10)
        6*11^-1 + 10 + 7*11 + 6*11^2 + 3*11^3 + 7*11^4 + 7*11^5 + 11^6 + O(11^8)

        sage: R.<x> = Qp(11,10)['x']
        sage: H = HyperellipticCurve(x^5-23*x^3+18*x^2+40*x)
        sage: P = H(-4,24)
        sage: Q = H(5,30)
        sage: R = H(1,6)
        sage: S = H(-2,12)
        sage: H.height([(1,P),(-1,Q)],[(1,R),(-1,S)],10)
        7*11^-1 + 3 + 8*11 + 6*11^2 + 5*11^3 + 7*11^4 + 3*11^5 + 9*11^6 + 6*11^7 + O(11^8)
        sage: H.height([(1,R),(-1,S)],[(1,P),(-1,Q)],10)
        7*11^-1 + 3 + 8*11 + 6*11^2 + 5*11^3 + 7*11^4 + 3*11^5 + 9*11^6 + 6*11^7 + O(11^8)

        """
        # print "height"
        if prec == None:
            prec = self.base_ring().precision_cap()
        P = divisor1[0][1]
        Q = divisor1[1][1]
        R = divisor2[0][1]
        S = divisor2[1][1]
        if P == R and Q == S == self(0,1,0):
            negP = self(P[0],-P[1])
            div1 = [(1,P),(-1,negP)]
            int_eta = self.init_height(div1,div1,prec)
            int_eta = self.eta_integral(div1,div1)
            Q = self.find_Q(P)
            print 'Q = ', Q
            negQ = self(Q[0],-Q[1])
            int_omega_at_P = self.special_int_omega(P)
            int_omega_P_to_Q = int_omega_at_P(Q[0]-P[0]) + log(Q[0]-P[0],0)
            self.init_height([(1,P),(-1,negP)],[(1,Q),(-1,negQ)])
            int_omega_wQ_to_Q = self.omega_integral([(1,P),(-1,negP)],[(1,Q),(-1,negQ)])
            height_minus = -2*int_omega_P_to_Q + int_omega_wQ_to_Q - int_eta
            b = P[1]
            return 1/QQ(4)*log(4*b**2) + 1/QQ(4)*height_minus

        else:
            self.init_height(divisor1,divisor2,prec)
            if (self.is_weierstrass(R) and self.is_weierstrass(S)):
                eta = 0
            else:
                eta = self.eta_integral(divisor1,divisor2)
            #print 'eta = ', eta
            omega = self.omega_integral(divisor1,divisor2,prec,cggen)
            #print 'omega = ', omega
            return omega - eta

    def tiny_integrals_on_basis_to_z(self,b):
        """
        Returns all tiny integrals on basis to a parameter z

        AUTHOR:
            - Jennifer Balakrishnan
        """
        prec = self.base_ring().precision_cap()
        x,y = self.local_coord(b,prec)
        S = self.base_ring()[['z']]
        z = S.gen()
        S.set_default_prec(prec+10)
        d = self.hyperelliptic_polynomials()[0].degree()
        return [((x**i)*x.derivative()/(2*y)).integral()(z) for i in range(d-1)]

    def tiny_double_integrals_on_basis_to_z(self,b):
        """
        Returns all tiny double integrals on basis unless b is infinity:
        then just returns \int w0 w0, \int w0 \int w_{2g-1}... \int w_{g-1} w_{2g-1}

        AUTHOR:
            - Jennifer Balakrishnan
        """
        prec = self.base_ring().precision_cap()
        x,y = self.local_coord(b,prec)
        S = self.base_ring()[['z']]
        d = self.hyperelliptic_polynomials()[0].degree()
        z = S.gen()
        S.set_default_prec(prec+10)
        inner = self.tiny_integrals_on_basis_to_z(b)
        doubles = []
        for i in range(d-1):
            doubles = doubles + [( ((x**i*x.derivative()/(2*y))(z))*J).integral() for J in inner]
        return doubles

    def coleman_integrals_on_basis_to_z(self, P, Q):
        """
        INPUT:
        - P: a non-Weierstrass point
        - Q: a point whose residue disc is where computations are taking place
        **i.e., we're doing things wrt z + Q[0]

        OUTPUT:
        Returns the vector (\int_P^Q x^i dx/(2y))

	    EXAMPLES:
	    sage: R.<x> = QQ['x']
	    sage: E = EllipticCurve('37a1')
	    sage: H = E.short_weierstrass_model()
	    sage: K = Qp(5,10)
	    sage: HK = H.change_ring(K)
	    sage: P = HK(0,4)
	    sage: Q = HK(4,4)
	    sage: f = HK.coleman_integrals_on_basis_to_z(P,Q)
	    sage: f(0)
	    (4*5 + 4*5^2 + 4*5^3 + 3*5^5 + 2*5^6 + 2*5^7 + 2*5^8 + 5^9 + O(5^10), 2 + 2*5 + 3*5^2 + 3*5^3 + 3*5^4 + 3*5^5 + 2*5^6 + 3*5^7 + 4*5^8 + 3*5^9 + O(5^10))
	    sage: HK.coleman_integrals_on_basis(P,Q)
	    (4*5 + 4*5^2 + 4*5^3 + 3*5^5 + 2*5^6 + 2*5^7 + 2*5^8 + 5^9 + O(5^10), 2 + 2*5 + 3*5^2 + 3*5^3 + 3*5^4 + 3*5^5 + 2*5^6 + 3*5^7 + 4*5^8 + 3*5^9 + O(5^10))
	    sage: HK.lift_x(4+5,all=True)[1]
	    (4 + 5 + O(5^10) : 4 + 4*5 + 2*5^2 + 2*5^3 + 5^4 + 4*5^5 + 3*5^6 + 2*5^7 + O(5^10) : 1 + O(5^10))
	    sage: R = HK.lift_x(4+5,all=True)[1]
	    sage: f(5)
	    (5 + 3*5^2 + 5^3 + 3*5^4 + 5^5 + 5^6 + 2*5^7 + 2*5^8 + 5^9 + O(5^10), 2 + 3*5^2 + 3*5^3 + 2*5^5 + 4*5^6 + 5^7 + 4*5^8 + 2*5^9 + O(5^10))
	    sage: HK.coleman_integrals_on_basis(P,R)
	    (5 + 3*5^2 + 5^3 + 3*5^4 + 5^5 + 5^6 + 2*5^7 + 2*5^8 + 5^9 + O(5^10), 2 + 3*5^2 + 3*5^3 + 2*5^5 + 4*5^6 + 5^7 + 4*5^8 + 2*5^9 + O(5^10))

        AUTHOR:
            - Jennifer Balakrishnan (2010-05)
            - Jennifer Balakrishnan (2015-04): added functionality for even degree models
        """
        import sage.schemes.hyperelliptic_curves.monsky_washnitzer as monsky_washnitzer
        K = self.base_ring()
        S = PowerSeriesRing(K,names='z')
        prec = K.precision_cap()
        p = K.prime()
        prec = prec +10
        S.set_default_prec(prec)
        z = S.gen()
        d = self.hyperelliptic_polynomials()[0].degree()
        dim = d-1
        disc = self.residue_disc(Q)
        Qold = Q
        Q = self.lift_x(z + Q[0])
        if self.residue_disc(Q) != disc:
            Q = (Q[0],-Q[1])
        x,y = self.local_coord_with_z(Q,prec)
        integrals = [(x**i*x.derivative()/(2*y)).integral() for i in range(dim)]
        if self.is_same_disc(P,Qold):
            return vector([-I(P[0]-Q[0]) for I in integrals])
        else:
            return self.coleman_integrals_on_basis(P,Qold) + vector([-I(-z) for I in integrals])

    def local_coord_with_z(self, P, prec = 20, name='t'):
        """
        For a non-Weierstrass point $P = (z,\sqrt(f(z)))$ on the hyperelliptic curve
        $y^2 = f(x)$, returns $(x(t),y(t))$ such that $y(t)^2 = f(x(t))$, where $t = x-z$
        is the local parameter.

        INPUT:
            - $P = (z, \sqrt(f(z)))$ is a non-Weierstrass point on self
            - prec: desired precision of the local coordinates
            - name: gen of the power series ring (default: 't')

        OUTPUT:
            $(x(t),y(t))$ such that $(y(t))^2 = f(x(t))$ and $t = x -a$ is the
            local parameter at $P$

        AUTHOR:
            - Jennifer Balakrishnan (2007-12)
        """
        d = P[1]
        if d == 0:
            raise TypeError, "P  = %s is a Weierstrass point "%P
        pol = self.hyperelliptic_polynomials()[0]
        L = PowerSeriesRing((P[0]).parent(),name)
        t = L.gen()
        L.set_default_prec(prec)
        K = PowerSeriesRing(L, 'x')
        pol = K(pol)
        x = K.gen()
        b = P[0]
        f = pol(t+b)
        for i in range((RR(log(prec)/log(2))).ceil()):
            d = (d + f/d)/2
        return t+b+O(t**(prec)), d + O(t**(prec))

    def b_to_P_doub_AB(self,P):
        '''
        the integral from infty to P of \alpha\beta in the case of an
        elliptic curve
        '''
        K = self.base_ring()
        if self.genus() != 1:
            raise ValueError
        f = self.hyperelliptic_polynomials()[0]
        fi = f.list()
        from sage.schemes.elliptic_curves.constructor import EllipticCurve
        E = EllipticCurve([0,fi[-2],0,fi[-3],fi[-4]]).change_ring(QQ)
        Emin = E.minimal_model()
        Dnew = ZZ(E.discriminant()/Emin.discriminant())**(ZZ(1)/ZZ(12))
        if self.is_in_weierstrass_disc(P):
            W = self.find_char_zero_weier_point(P)
            f = self.hyperelliptic_polynomials()[0]
            fprime = f.derivative()
            ainvs = self.a_invariants()
            inner = fprime(W[0]) -ainvs[0]*W[1]
            b_to_W_AB = ZZ(1)/ZZ(4)*log(inner,0) - log(K(Dnew))
            x,y = self.local_coord(W,prec=30)
            I2 = (x*x.derivative()/(2*y)).integral()
            I1 = (x.derivative()*I2/(2*y)).integral()
            W_to_P_AB = I1(P[1])
            return b_to_W_AB + W_to_P_AB
        else:
            f = E.change_ring(K).division_polynomial(3)
            try:
                S = self.lift_x(f.roots()[0][0])
            except ValueError:
                S = self.lift_x(f.roots()[1][0])
            b_to_P_A,b_to_P_B = self.coleman_integrals_on_basis(self(0,1,0),P)
            S_to_P_A = self.coleman_integrals_on_basis(S,P)[0]
            b_to_S_B = self.coleman_integrals_on_basis(self(0,1,0),S)[1]
            b_to_S_AB = ZZ(1)/ZZ(3)*log(2*S[1]) - log(K(Dnew))

            #print 'S = ', S
            #print 'P = ', P
            S_to_P_AB = self.double_integrals_on_basis(S,P)[1]

            b_to_P_AB = b_to_S_AB + S_to_P_AB + b_to_S_B*S_to_P_A
            return b_to_P_AB


    def double_integrals_on_basis(self,P,Q):
        """
        The double integrals on basis differentials:
        $\int_P^Q w_0 w_0, \int_P^Q w_0 w_1, ..., \int_P^Q w_{2g-1} w_{2g-1}$
        (via Frobenius)

        INPUT:
            - P: non-Weierstrass point on self
            - Q: non-Weierstrass point on self

        OUTPUT:
            The double integrals
            $\int_P^Q w_0 w_0, \int_P^Q w_0 w_1, ..., \int_P^Q w_{2g-1} w_{2g-1}$, where
            $w_i = x^i dx/(2y)$

        EXAMPLES:
        We check against the implementation that uses Teichmuller points:

            sage: R.<x> = QQ['x']
            sage: E = HyperellipticCurve(x^3-4*x+4)
            sage: K = Qp(5,8)
            sage: EK = E.change_ring(K)
            sage: P = EK(2,2)
            sage: Q = EK(1,1)
            sage: EK.double_integrals_on_basis_via_teich(P,Q).transpose()
            [                2*5^4 + 3*5^5 + 2*5^6 + O(5^8)]
            [2*5^2 + 3*5^3 + 3*5^5 + 3*5^6 + 3*5^7 + O(5^8)]
            [    2*5^2 + 3*5^4 + 3*5^5 + 5^6 + 5^7 + O(5^8)]
            [            2 + 4*5^2 + 2*5^4 + 3*5^5 + O(5^7)]
            sage: EK.double_integrals_on_basis(P,Q).transpose()
            [                2*5^4 + 3*5^5 + 2*5^6 + O(5^8)]
            [2*5^2 + 3*5^3 + 3*5^5 + 3*5^6 + 3*5^7 + O(5^8)]
            [    2*5^2 + 3*5^4 + 3*5^5 + 5^6 + 5^7 + O(5^8)]
            [            2 + 4*5^2 + 2*5^4 + 3*5^5 + O(5^7)]

        A Fubini-style check that $\int_P^Q w_i w_j = \int_Q^P w_j w_i$:

            sage: EK.double_integrals_on_basis_via_teich(Q,P).transpose()
            [                2*5^4 + 3*5^5 + 2*5^6 + O(5^8)]
            [    2*5^2 + 3*5^4 + 3*5^5 + 5^6 + 5^7 + O(5^8)]
            [2*5^2 + 3*5^3 + 3*5^5 + 3*5^6 + 3*5^7 + O(5^8)]
            [            2 + 4*5^2 + 2*5^4 + 3*5^5 + O(5^7)]
            sage: EK.double_integrals_on_basis(Q,P).transpose()
            [                2*5^4 + 3*5^5 + 2*5^6 + O(5^8)]
            [    2*5^2 + 3*5^4 + 3*5^5 + 5^6 + 5^7 + O(5^8)]
            [2*5^2 + 3*5^3 + 3*5^5 + 3*5^6 + 3*5^7 + O(5^8)]
            [            2 + 4*5^2 + 2*5^4 + 3*5^5 + O(5^7)]


        Checking that things are consistent for even degree models:

        sage: R.<x> = QQ['x']
        sage: H = HyperellipticCurve(x^6 + 31*x^4 + 31*x^2 + 1)
        sage: K = Qp(13,10)
        sage: HK = H.change_ring(K)
        sage: P = HK(0,1)
        sage: I = HK.coleman_integrals_on_basis(P,HK(1,8))
        sage: J = HK.double_integrals_on_basis(P,HK(1,8))
        sage: I[0]^2/2-J[0]
        O(13^10)
        sage: J[1] + J[5]-I[0]*I[1]
        O(13^10)
        sage: J[2] + J[10] - I[0]*I[2]
        O(13^10)
        sage: J[3] + J[15] - I[0]*I[3]
        O(13^9)
        sage: J[4] + J[20] - I[0]*I[4]
        O(13^9)
        sage: J[6] - I[1]^2/2
        O(13^11)
        sage: J[7] + J[11] - I[1]*I[2]
        O(13^10)
        sage: J[8] + J[16] - I[1]*I[3]
        O(13^9)
        sage: J[9] + J[21] - I[1]*I[4]
        O(13^9)
        sage: J[12] - I[2]^2/2
        O(13^10)
        sage: J[13] + J[17] - I[2]*I[3]
        O(13^9)
        sage: J[14] + J[22] - I[2]*I[4]
        O(13^9)
        sage: J[18] - I[3]^2/2
        O(13^9)
        sage: J[19] + J[23] - I[3]*I[4]
        O(13^8)
        sage: J[24] - I[4]^2/2
        O(13^8)


        AUTHOR:
            Jennifer Balakrishnan (2010-04)
            Jennifer Balakrishnan (2015-04): added functionality for even degree models


        """
        import sage.schemes.hyperelliptic_curves.monsky_washnitzer as monsky_washnitzer
        #g = self.genus()
        d = self.hyperelliptic_polynomials()[0].degree()
        dim = d - 1
        if P == Q:
            return vector([0]*(2*dim)**2)
        try:
            M_frob, forms = self._frob_calc
        except AttributeError:
            M_frob, forms = self._frob_calc = monsky_washnitzer.matrix_of_frobenius_hyperelliptic(self)


        #if self.is_in_weier_disc(P) and self.is_in_weier_disc(Q):
        #    ##have to break up the path twice
        #    print 'currently passing'
        #    return 'pass'
        #elif self.is_in_weier_disc(P) and self.is_in_weier_disc(Q) == False:
        #    ##this is symmetric to case below
        #    print 'currently passing'
        #    return 'pass'
        #elif self.is_in_weier_disc(P) == False and self.is_in_weier_disc(Q):
        #    ##this is the case needed for paper with netan
        #    #want to compute \int_P^W wiwj+ \int_W^Q wiwj +\int_P^W wj \int_W^Q wi = \int_P^Q
        #    #want to compute \int_P^W wiwj using point near point near boundary, \int_W^Q wiwj using tiny
        #else:
        ##have to indent everything below
        p = self.base_ring().prime()
        FP = self.frobenius(P)
        FQ = self.frobenius(Q)
        A = M_frob.transpose()
        A_rows = A.rows()
        g = self.genus()
        const = []
        fix = []
        xm,ym = self.monsky_washnitzer_gens()
        w = self.invariant_differential()

        P_to_Q_sing = self.coleman_integrals_on_basis(P,Q)
        #print P_to_Q_sing - self.tiny_integrals_on_basis(P,Q)

        Q_to_FQ_sing = self.tiny_integrals_on_basis(Q,FQ)

        ###this needs to be changed
        FP_to_P_sing = self.tiny_integrals_on_basis(FP,P)

        if P[0].parent() == self.base_ring() and FP[0].parent() == self.base_ring():
            FP_to_P_iter = self.tiny_double_integrals_on_basis(FP,P)
            #print 'FP_to_P_iter = ', FP_to_P_iter
        elif self.residue_disc(P) == self.change_ring(GF(p))(0,1,0):
            print "using double integrals in infinite disc"
            FP_to_P_iter = self.tiny_double_integrals_on_basis_in_infinite_disc(FP,P)
            #print FP_to_P_iter[1] + FP_to_P_iter[2] - FP_to_P_sing[0]*FP_to_P_sing[1]
        else:
            return "haven't done this yet"

        FP_to_FQ_sing = FP_to_P_sing + P_to_Q_sing + Q_to_FQ_sing
        #print FP_to_FQ_sing - self.coleman_integrals_on_basis(FP,FQ)

        if Q[0].parent() == self.base_ring() and FQ[0].parent() == self.base_ring():
            FQ_to_Q_iter = self.tiny_double_integrals_on_basis(FQ,Q)
            #print 'FQ_to_Q_iter = ', FQ_to_Q_iter
        else:
            print "using double integrals in infinite disc"
            FQ_to_Q_iter = self.tiny_double_integrals_on_basis_in_infinite_disc(FQ,Q)
            #print FQ_to_Q_iter[1] + FQ_to_Q_iter[2] - Q_to_FQ_sing[0]*Q_to_FQ_sing[1]

        int_xpowldxfk = [[self.coleman_integral(xm**l*w*w._coeff.parent()(form),P,Q) for l in range(dim)] for form in forms]

        if g == 1:
            formsq = [(f**2)/ZZ(2) for f in forms]
            f0f1 = forms[0]*forms[1]
            int_df0f1 = self.coleman_integral(forms[0].diff()*forms[1],P,Q)
            int_dfifk = [formsq[0](Q[0],Q[1]) -formsq[0](P[0],P[1]), int_df0f1 , f0f1(Q[0],Q[1]) - f0f1(P[0],P[1]) - int_df0f1 ,formsq[1](Q[0],Q[1]) -formsq[1](P[0],P[1])]
        fP = [f(P[0],P[1]) for f in forms]
        fQ = [f(Q[0],Q[1]) for f in forms]

        for i in range(dim):
            Ai = A_rows[i]
            fi = forms[i]
            for k in range(dim):
                Ak = A_rows[k]
                fk = forms[k]
                fkP = fP[k]
                fiP = fP[i]
                fiQ = fQ[i]
                p1 = -fkP*(fiQ-fiP)
                #print("p1 = ", p1)
                if g!= 1:
                    p2 = self.coleman_integral(fi.diff()*fk,P,Q)
                    #print("p2 = ",p2)
                else:
                    p2 = int_dfifk[dim*i + k]
#                p1 = -fk(P[0],P[1])*(fi(Q[0],Q[1])-fi(P[0],P[1]))
#                p2 = self.coleman_integral(fi.diff()*fk,P,Q)
#                p3 = -Ai*fk(P[0],P[1])*P_to_Q_sing
                p3 = -Ai*fkP*P_to_Q_sing
                #print("p3 = ", p3)
                if i == k:
                    p4 =0
                else:
                    #p4 = (Ai*vector([self.coleman_integral(xm**l*w*w._coeff.parent()(fk),P,Q) for l in range(dim)]) - Ak*vector([self.coleman_integral(xm**l*w*w._coeff.parent()(fi),P,Q) for l in range(dim)]))
                    p4 = (Ai*vector(int_xpowldxfk[k]) - Ak*vector(int_xpowldxfk[i]))
 #               print 'p4 = ', p4
                p5 =  fiQ*Ak*P_to_Q_sing
 #               print 'p5 = ', p5
                const = const + [p1+p2 + p3 + p4 + p5]
                fix = fix + [-FP_to_P_iter[dim*i+k] - P_to_Q_sing[i]*FP_to_P_sing[k] - Q_to_FQ_sing[i]*FP_to_FQ_sing[k] + FQ_to_Q_iter[dim*i+k]]
                #print "fix = ", fix  ##check this?
              #  print "1 loop done"
        const = vector(const)
#        print 'const =', const
        fix = vector(fix)
        AA = A.tensor_product(A)
        v = fix + const
        I = identity_matrix(dim**2)
        return  ((I-AA).inverse())*(v)

    def tiny_double_integrals_on_basis(self,P,Q):
        """

        The tiny double integrals on basis differentials:
        $\int_P^Q w_0 w_0, \int_P^Q w_0 w_1, ..., \int_P^Q w_{2g-1} w_{2g-1}$

        INPUT:
            - P: non-Weierstrass point on self
            - Q: point on self in same disc as P

        OUTPUT:
            the tiny double integrals on basis differentials:
            $\{\int_P^Q w_i w_j\}_{i,j= 0,..., 2g-1}$, where $w_i = x^i dx/(2y)$


        EXAMPLES:
        We check consistency with single Coleman integrals:

            sage: R.<x> = QQ['x']
            sage: H = HyperellipticCurve(x^3-4*x+4)
            sage: K = Qp(5,8)
            sage: HK = H.change_ring(K)
            sage: P = HK.lift_x(2)
            sage: FP = HK.frobenius(P)
            sage: I = HK.tiny_double_integrals_on_basis(P,FP)
            sage: C = HK.tiny_integrals_on_basis(P,FP)
            sage: I.transpose()
            [                3*5^2 + 5^3 + 3*5^5 + 5^6 + 4*5^7 + O(5^9)]
            [              5^2 + 4*5^3 + 4*5^6 + 3*5^7 + 2*5^8 + O(5^9)]
            [              5^2 + 2*5^4 + 4*5^6 + 3*5^7 + 4*5^8 + O(5^9)]
            [2*5^2 + 2*5^3 + 5^4 + 4*5^5 + 3*5^6 + 5^7 + 3*5^8 + O(5^9)]
            sage: I[1]+I[2] == C[0]*C[1]
            True
            sage: I[0] == C[0]^2/2
            True
            sage: I[3] == C[1]^2/2
            True


        An error if points are not in the same disc:
            sage: Q = HK.lift_x(1)
            sage: HK.tiny_double_integrals_on_basis(P,Q)
            Traceback (most recent call last):
            ...
            ValueError: (2 + O(5^8) : 2 + O(5^8) : 1 + O(5^8)) and (1 + O(5^8) : 1 + O(5^8) : 1 + O(5^8)) are not in the same residue disc

        AUTHOR:
            Jennifer Balakrishnan: odd (2010)
            JSB: even (2012)
        """
        g = self.genus()
        d = self.hyperelliptic_polynomials()[0].degree()
        if d%2 == 1:
            dim = 2*g
        else:
            dim = 2*g+1

        if P == Q:
            return vector((dim**2)*[0])
        try:
            if self.is_same_disc(P,Q) == False:
                raise ValueError, "%s and %s are not in the same residue disc "%(P,Q)
        except TypeError:
            pass
        p = self.base_ring().prime()
        integrals = []
        xP,yP = self.local_coord(P)
        single_ints = self.tiny_integrals_on_basis(P,Q)
        I2 = [(xP**j*xP.derivative()/(2*yP)).integral() for j in range(dim)]
        S = PowerSeriesRing(P[0].parent(),names='a')
        a = S.gen()
        I2_vals = [pol(a) for pol in I2]
        x = xP(a)
        y = yP(a)
        #f = self.hyperelliptic_polynomials()[0]
        #x = S(a+P[0])
        #y = S((f(x)).sqrt())
        #try:
	#    if GF(p)(y.list()[0]) == GF(p)(-P[1]):
        #        y = -y
        #except ValueError:
        #    if y.list()[0] == -P[1].list()[0]:
        #        y = -y
   	for i in range(dim):
            for j in range(dim):
                if j == i:
                    integrals = integrals + [((single_ints[j])**2)/2]
                elif j > i:
                    I1 = (x**i*(x.derivative())*I2_vals[j]/(2*y)).integral()
                    if P[1] != 0:
                        integrals = integrals + [I1(Q[0]-P[0])]
                    else:
                        #weierstrass case: parameter is y-coord
                        integrals = integrals + [I1(Q[1])]


                else:
                    integrals = integrals + [single_ints[j]*single_ints[i]-integrals[(dim)*j+i]]
        return vector(integrals)
    def double_integrals_on_basis_to_z(self,P,Q):
        """
        new implementation, from P to the disk of Q (a parameter z in disk of Q)
        (using tiny integrals from Q to z in the disk of Q)
        (why apply Frobenius unnecessarily?!)

        EXAMPLES:

        Old consistency checks from the old function (still good, and SO MUCH FASTER)

            sage: E = EllipticCurve('37a1')
            sage: H = E.short_weierstrass_model()
            sage: HK = H.change_ring(Qp(5,8))
            sage: P = HK(0,4)
            sage: Q = HK(4,4)
            sage: time f = HK.double_integrals_on_basis_to_z(P,Q)
            CPU times: user 2.79 s, sys: 0.07 s, total: 2.87 s
            Wall time: 2.91 s
            sage: g = HK.double_integrals_on_basis(P,Q)
            sage: f(0)-g
            (O(5^9), O(5^8), O(5^8), O(5^8))
            sage: R = HK.lift_x(9,all=True)[1]
            sage: h = HK.double_integrals_on_basis(P,R)
            sage: f(5)-h
            (O(5^9), O(5^8), O(5^8), O(5^8))
            sage: R = HK.lift_x(29,all=True)[1]
            sage: i = HK.double_integrals_on_basis(P,R)
            sage: f(5^2)-i
            (O(5^9), O(5^8), O(5^8), O(5^8))

        Consistency checks for the even degree model stuff

            sage: R.<x> = QQ['x']
            sage: H = HyperellipticCurve(x^6 + 31*x^4 + 31*x^2 + 1)
            sage: K = Qp(5,8)
            sage: HK = H.change_ring(K)
            sage: J = HK.double_integrals_on_basis_to_z(HK(0,1),HK(1,8))
            sage: L = HK.double_integrals_on_basis(HK(0,1),HK(1,8))
            sage: J(0)-L
            (O(5^8), O(5^8), O(5^8), O(5^7), O(5^7), O(5^8), O(5^8), O(5^8), O(5^7), O(5^7), O(5^8), O(5^8), O(5^8), O(5^7), O(5^7), O(5^7), O(5^7), O(5^7), O(5^7), O(5^6), O(5^7), O(5^7), O(5^7), O(5^6), O(5^6))
            sage: Q = HK.lift_x(6,all=True)[1]
            sage: Q
            (1 + 5 + O(5^8) : 3 + 3*5 + 5^3 + 3*5^4 + 4*5^7 + O(5^8) : 1 + O(5^8))
            sage: M = HK.double_integrals_on_basis(HK(0,1),Q)
            sage: J(5)-M
            (O(5^8), O(5^8), O(5^8), O(5^7), O(5^7), O(5^8), O(5^8), O(5^8), O(5^7), O(5^7), O(5^8), O(5^8), O(5^8), O(5^7), O(5^7), O(5^7), O(5^7), O(5^7), O(5^7), O(5^6), O(5^7), O(5^7), O(5^7), O(5^6), O(5^6))

        AUTHOR:
            Jennifer Balakrishnan, 2015-04-04
        """
        K = self.base_ring()
        p = K.prime()
        d = self.hyperelliptic_polynomials()[0].degree()
        dim = d - 1
        Q_to_Qz_sing = self.tiny_integrals_on_basis_to_z(Q)
        Q_to_Qz_doub = self.tiny_double_integrals_on_basis_to_z(Q)
        P_to_Q_doub = self.double_integrals_on_basis(P,Q)
        P_to_Q_sing = self.coleman_integrals_on_basis(P,Q)
        integrals = []
        for i in range(dim):
            for k in range(dim):
                integrals.append(P_to_Q_doub[dim*i + k] + Q_to_Qz_doub[dim*i + k] + P_to_Q_sing[k]*Q_to_Qz_sing[i])
        return vector(integrals)