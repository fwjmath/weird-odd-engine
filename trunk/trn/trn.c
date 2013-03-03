/* trn.c                 Thomas R. Nicely          2012.01.26.1000
 *
 * Freeware copyright (c) 2012 Thomas R. Nicely <http://www.trnicely.net>.
 * Released into the public domain by the author, who disclaims any legal
 * liability arising from its use. The routine iEvalExprMPZ is included
 * under the terms of the GNU GPL; see the header of that routine (at
 * the end of the code) for details.
 *
 * Trimmed by fwjmath, 2013.02.26
 */

#include "trn.h"

unsigned long ulDmax=0;

/**********************************************************************/
/**********************************************************************/
/*              Prime number generation and testing                   */
/**********************************************************************/
/**********************************************************************/
int iMiller(mpz_t mpzN, long iB)
{
/* Test N for primality using the Miller's strong probable prime
   test with base B. See Gary Miller's famous paper ("Riemann's
   hypothesis and tests for primality," Journal of Computation and
   System Science, 1976, Volume 13, pp 300-317).

   Returns 1 if N is a prime or a base-B strong probable prime.
   Returns 0 if N is definitely not a prime (composite or < 2).

   NOTE 1: Some will not regard this as a "pure" Miller's test with
   base B, since certain adjustments are made, prior to applying the
   algorithm, in order to work around invalid input values and
   improve performance:

   1) N < 3 and even N are screened out first.
   2) Multiples of the small primes (to qMax=# of binary digits in N)
      are returned as composite.
   3) Values of B < 2 are replaced by B=2.
   4) If N divides B exactly, B is replaced by B+1.

   If such adjustments are not made, a third return value (e.g., -1)
   must be allowed, indicating invalid input and an indeterminate result,
   and complicating the calling source code.

   NOTE 2: Not all authorities agree exactly on the conditions for
   Miller's test. Some allow B < 2 (Rosen, "Elementary number theory and
   its applications," 3rd ed., 1993, pp. 195-200), although there are good
   reasons to exclude such values. On the other hand, some require
   1 < B < N (Ribenboim, "The new book of prime number records,"
   3rd ed., 1996, pp. 113-116, 143-146). As far as I know, no one
   allows N to divide B, as this produces "false negatives"; e.g.,
   N=3 and B=6 fails Miller's test, thus indicating N=3 as composite.
   In practice, there appears to be no good reason to use any B < 2,
   and in fact its value is almost always chosen to be a small
   (positive) prime number. Furthermore, in my opinion, refusing to
   first screen out even values of N and N < 3 gratuitously adds
   unnecessary complication to the test.
*/

static long iFirst=1;
static mpz_t mpzB, mpzNm1, mpzd, mpzRem, mpzSqrt;
long iComp2, iBits, s, j, q, digits;
unsigned long qMax;

/* Allocate the static variables used in Miller's test. */

if(iFirst)
  {
  mpz_init(mpzB);  /* Never needs more than one limb */
  iBits=mp_bits_per_limb*(1 + mpz_size(mpzN));
  if(iBits < 512)iBits=512;
  mpz_init2(mpzNm1, iBits);
  mpz_init2(mpzd, iBits);
  mpz_init2(mpzRem, 2*iBits);  /* must contain products */
  //if(!iPrime16Initialized)vGenPrimes16();
  iFirst=0;
  }

/* First take care of all N < 3 and all even N. */

//iComp2=mpz_cmp_si(mpzN, 2);
//if(iComp2 < 0)return(0);        /* N < 2 is by convention not prime */
//if(iComp2==0)return(1);         /* N=2 is prime */
//if(mpz_even_p(mpzN))return(0);  /* Even N > 2 is composite */

/* Try small prime divisors from 3 to an UB qMax determined by the size
   of N (qMax >= 31). */

//mpz_sqrt(mpzSqrt, mpzN);
//qMax=mpz_sizeinbase(mpzN, 2);  /* Number of binary digits in N */
//if(qMax < 36)qMax=36;
//j=2;  /* First trial divisor is 3, the second prime */
/*
while(1)
  {
  q=ulPrime16[j++];
  if(q > qMax)break;
  if(mpz_cmp_si(mpzN, q)==0)return(1);
  if(mpz_cmp_si(mpzSqrt, q) < 0)return(1);
  if(mpz_divisible_ui_p(mpzN, q))return(0);
  }
*/
/* Check for valid input. Miller's test requires B > 1, and N must not
   divide B exactly. Choose B=2 and B<--B+1 if these problems arise.
   This is technically a deviation from the pure Miller's test, but
   avoids the necessity of handling an error return of -1. */

if(iB < 2)iB=2;
mpz_set_si(mpzB, iB);
if(mpz_divisible_p(mpzB, mpzN))mpz_add_ui(mpzB, mpzB, 1);

/* Now compute d and s, where d is odd and N - 1 = (2^s)*d. */

mpz_sub_ui(mpzNm1, mpzN, 1);
s=mpz_scan1(mpzNm1, 0);
mpz_tdiv_q_2exp(mpzd, mpzNm1, s);

/* Now proceed with the Miller's algorithm. First, if B^d is
   congruent to 1 mod N, N is a strong probable prime to base B. */

mpz_powm(mpzRem, mpzB, mpzd, mpzN);
if(mpz_cmp_si(mpzRem, 1)==0)return(1);
if(s==0)return(0);

/* Now calculate B^((2^j)*d), for j=0,1,...,s-1 by successive
   squaring. If any of these is congruent to -1 mod N, N is a
   sprp base B. Start with j=0 and B^d, already computed.
   Miller's test uses repeated modular squaring in place of repeated
   modular exponentiation for speed (squaring is an order of
   magnitude faster). */

if(mpz_cmp(mpzRem, mpzNm1)==0)return(1);  /* j=0 case */
for(j=1; j < s; j++)
  {
  mpz_mul(mpzRem, mpzRem, mpzRem);
  mpz_mod(mpzRem, mpzRem, mpzN);
  if(mpz_cmp(mpzRem, mpzNm1)==0)return(1);
  }

return(0);
}
/**********************************************************************/
int iBPSW(mpz_t mpzN)
{
/* Returns 1 if N is a probable prime, that is, passes the primality
 * tests in this algorithm; in that case, N is prime, or a strong
 * Baillie-Pomerance-Selfridge-Wagstaff (Baillie-PSW or BPSW) pseudoprime
 * Returns 0 if N is definitely composite, or if N < 2.
 *
 * The strong Lucas-Selfridge test returns roughly 30 % as many
 * pseudoprimes as the standard test, at the price of an additiona
 * running time of roughly 10 %. Thus the strong Lucas-Selfridge test
 * appears to be more effective, and is the one employed here.
 *
 * Determines if N is a probable prime, using a version of the
 * algorithm outlined by Baillie, Pomerance, Selfridge, and Wagstaff
 * (ca. 1980). Values of N are tested successively as follows.
 *
 * (1) N < 2 is not prime. N=2 is prime. Even N > 2 are composite.
 * (2) Try small primes as trial divisors, up to qMax=the # of binary
 *     digits in N. This step is implicit here here as part of Miller's
 *     test.
 * (3) If there is small prime divisor, apply Miller's strong
 *     probable prime test with base 2. If N fails, it is definitely
 *     composite. If N passes, it is a prime or a strong pseudoprime
 *     to base 2.
 * (4) Apply the strong Lucas sequence test with Selfridge's parameters.
 *     If N fails the Lucas-Selfridge test, it is definitely composite
 *     (and a strong pseudoprime to base 2). If N passes the strong
 *     Lucas-Selfridge test, it is a strong Lucas probable prime (lprp),
 *     i.e., a prime or a strong Lucas-Selfridge pseudoprime.
 * (5) If N has passed all these tests, it is a strong BPSW probable
 *     prime---either prime, or a strong BPSW pseudoprime. In this event
 *     the relative frequency of primality is believed to be very close
 *     to 1, and possibly even equal to 1. With the aid of Pinch's tables
 *     of pseudoprimes, the author verified (May, 2005) that there exists
 *     no Baillie-PSW pseudoprime (either strong or standard) in N < 10^13.
 *     In January, 2007, with the aid of the present implementation and
 *     William Galway's table of pseudoprimes, Martin Fuller determined
 *     that no Baillie-PSW pseudoprime (standard or strong) exists for
 *     N < 10^15. More recently, using the author's code and a database of
 *     pseudoprimes prepared by Jan Feitsma, Jeff Gilchrist has determined
 *     (13 June 2009) that no Baillie-PSW pseudoprime (standard or strong)
 *     exists below 10^17. Furthermore, preliminary analysis by Gilchrist
 *     of Feitsma's database, further extended, indicates (24 October 2009)
 *     that no Baillie-PSW pseudoprime (standard or strong) exists below
 *     2^64 ~ 1.8446744e19 (double checking of this result is in progress).
 * (6) Note, however, that Carl Pomerance (1984) presented a heuristic
 *     argument that an infinite number of counterexamples exist to the
 *     standard BPSW test (and presumably to the strong BPSW test as well,
 *     based on similar reasoning), and even that (for sufficiently large x,
 *     dependent on t) the number of Baillie-PSW pseudoprimes < x exceeds
 *     x^(1-t), where t is an arbitrarily small pre-assigned positive number.
 *     Nevertheless, not a single Baillie-PSW pseudoprime has yet been found;
 *     consequently, the Baillie-PSW test carries an aura of dependability
 *     (justified or not) exceeding that of competing algorithms, such as
 *     multiple Miller's tests (the Miller-Rabin algorithm).
 *
 * In the unexpected event that no counterexample exists, this algorithm
 * (the strong BPSW test) would constitute a definitive fast certification
 * of primality with polynomial running time, O((log N)^3).
 *
 * References:
 *
 * o Arnault, Francois. The Rabin-Monier theorem for Lucas pseudoprimes.
 *   Math. Comp. 66 (1997) 869-881. See
 *   <http://www.unilim.fr/pages_perso/francois.arnault/publications.html>
 * o Baillie, Robert, and Samuel S. Wagstaff, Jr. Lucas pseudoprimes.
 *   Math. Comp. 35:152 (1980) 1391-1417. MR0583518 (81j:10005). See
 *   <http://mpqs.free.fr/LucasPseudoprimes.pdf>.
 * o Feitsma, Jan. The pseudoprimes below 10^16. June 2009. Available at
 *   <http://www.janfeitsma.nl/math/psp2/database>.
 * o Galway, William. The pseudoprimes below 10^15. 4 November 2002.
 *   Available at <http://oldweb.cecm.sfu.ca/pseudoprime/>.
 * o Gilchrist, Jeff. Pseudoprime enumeration with probabilistic
 *   primality tests. 13 June 2009. Available at
 *   <http://gilchrist.ca/jeff/factoring/pseudoprimes.htm>..
 * o Grantham, Jon. Frobenius pseudoprimes. Preprint (16 July 1998)
 *   available at <http://www.pseudoprime.com/pseudo1.ps>.
 * o Martin, Marcel. Re: Baillie-PSW - Which variant is correct?
 *   9 January 2004. See
 *   <http://groups.google.com/groups?hl=en&lr=&ie=UTF-8&oe=UTF-8&safe=off&selm=3FFF275C.2C6B5185%40ellipsa.no.sp.am.net>.
 * o Mo, Zhaiyu, and James P. Jones. A new primality test using Lucas
 *   sequences. Preprint (circa 1997).
 * o Pinch, Richard G. E. Pseudoprimes up to 10^13. 4th International
 *   Algorithmic Number Theory Symposium, ANTS-IV, Leiden, The
 *   Netherlands, 2--7 July 2000. Springer Lecture Notes in Computer
 *   Science 1838 (2000) 459-474. See
 *   <http://www.chalcedon.demon.co.uk/rgep/carpsp.html>.
 * o Pomerance, Carl. Are there counterexamples to the Baillie-PSW
 *   primality test? (1984) See <http://www.pseudoprime.com/dopo.pdf>.
 * o Pomerance, Carl, John L. Selfridge, and Samuel S. Wagstaff, Jr.
 *   The pseudoprimes to 25*10^9. Math. Comp. 35 (1980) 1003-1026. See
 *   <http://mpqs.free.fr/ThePseudoprimesTo25e9.pdf>.
 * o Ribenboim, Paulo. The new book of prime number records. 3rd ed.,
 *   Springer-Verlag, 1995/6, pp. 53-83, 126-132, 141-142 (note that on
 *   line 2, p. 142, "0 < r < s" should read "0 <= r < s").
 * o Weisstein, Eric W. Baillie-PSW primality test. See
 *   <http://mathworld.wolfram.com/Baillie-PSWPrimalityTest.html>.
 * o Weisstein, Eric W. Strong Lucas pseudoprime. See
 *   <http://mathworld.wolfram.com/StrongLucasPseudoprime.html>.
 *
 */

//int iComp2;

/* First eliminate all N < 3 and all even N. */
/*
iComp2=mpz_cmp_si(mpzN, 2);
if(iComp2 < 0)return(0);
if(iComp2==0)return(1);
if(mpz_even_p(mpzN))return(0);
*/
/* Carry out Miller's test with base 2. This will also carry
   out a check for small prime divisors. */

if(iMiller(mpzN, 2)==0)return(0);

/* The rumored strategy of Mathematica could be imitated here by
 * performing additional Miller's tests. One could also carry out
 * one or more extra strong Lucas tests. See the routine iPrP for
 * an implementation.
 *
 * Now N is a prime, or a base-2 strong pseudoprime with no prime
 * divisor < 37. Apply the strong Lucas-Selfridge primality test.
 */

return(iStrongLucasSelfridge(mpzN));
}
/**********************************************************************/
int iStrongLucasSelfridge(mpz_t mpzN)
{
/* Test N for primality using the strong Lucas test with Selfridge's
   parameters. Returns 1 if N is prime or a strong Lucas-Selfridge
   pseudoprime (in which case N is also a pseudoprime to the standard
   Lucas-Selfridge test). Returns 0 if N is definitely composite.

   The running time of the strong Lucas-Selfridge test is, on average,
   roughly 10 % greater than the running time for the standard
   Lucas-Selfridge test (3 to 7 times that of a single Miller's test).
   However, the frequency of strong Lucas pseudoprimes appears to be
   only (roughly) 30 % that of (standard) Lucas pseudoprimes, and only
   slightly greater than the frequency of base-2 strong pseudoprimes,
   indicating that the strong Lucas-Selfridge test is more computationally
   effective than the standard version. */

int iComp2, iP, iJ, iSign;
long lDabs, lD, lQ;
unsigned long ulMaxBits, uldbits, ul, ulGCD, r, s;
mpz_t mpzU, mpzV, mpzNplus1, mpzU2m, mpzV2m, mpzQm, mpz2Qm,
      mpzT1, mpzT2, mpzT3, mpzT4, mpzD, mpzd, mpzQkd, mpz2Qkd;

#undef RETURN
#define RETURN(n)           \
  {                         \
  mpz_clear(mpzU);          \
  mpz_clear(mpzV);          \
  mpz_clear(mpzNplus1);     \
  mpz_clear(mpzU2m);        \
  mpz_clear(mpzV2m);        \
  mpz_clear(mpzQm);         \
  mpz_clear(mpz2Qm);        \
  mpz_clear(mpzT1);         \
  mpz_clear(mpzT2);         \
  mpz_clear(mpzT3);         \
  mpz_clear(mpzT4);         \
  mpz_clear(mpzD);          \
  mpz_clear(mpzd);          \
  mpz_clear(mpzQkd);        \
  mpz_clear(mpz2Qkd);       \
  return(n);                \
  }

/* This implementation of the algorithm assumes N is an odd integer > 2,
   so we first eliminate all N < 3 and all even N. As a practical matter,
   we also need to filter out all perfect square values of N, such as
   1093^2 (a base-2 strong pseudoprime); this is because we will later
   require an integer D for which Jacobi(D,N) = -1, and no such integer
   exists if N is a perfect square. The algorithm as written would
   still eventually return zero in this case, but would require
   nearly sqrt(N)/2 iterations. */

iComp2=mpz_cmp_si(mpzN, 2);
if(iComp2 < 0)return(0);
if(iComp2==0)return(1);
if(mpz_even_p(mpzN))return(0);
if(mpz_perfect_square_p(mpzN))return(0);

/* Allocate storage for the mpz_t variables. Most require twice
   the storage of mpzN, since multiplications of order O(mpzN)*O(mpzN)
   will be performed. */

ulMaxBits=2*mpz_sizeinbase(mpzN, 2) + mp_bits_per_limb;
mpz_init2(mpzU, ulMaxBits);
mpz_init2(mpzV, ulMaxBits);
mpz_init2(mpzNplus1, ulMaxBits);
mpz_init2(mpzU2m, ulMaxBits);
mpz_init2(mpzV2m, ulMaxBits);
mpz_init2(mpzQm, ulMaxBits);
mpz_init2(mpz2Qm, ulMaxBits);
mpz_init2(mpzT1, ulMaxBits);
mpz_init2(mpzT2, ulMaxBits);
mpz_init2(mpzT3, ulMaxBits);
mpz_init2(mpzT4, ulMaxBits);
mpz_init(mpzD);
mpz_init2(mpzd, ulMaxBits);
mpz_init2(mpzQkd, ulMaxBits);
mpz_init2(mpz2Qkd, ulMaxBits);

/* Find the first element D in the sequence {5, -7, 9, -11, 13, ...}
   such that Jacobi(D,N) = -1 (Selfridge's algorithm). Theory
   indicates that, if N is not a perfect square, D will "nearly
   always" be "small." Just in case, an overflow trap for D is
   included. */

lDabs=5;
iSign=1;
while(1)
  {
  lD=iSign*lDabs;
  iSign = -iSign;
  ulGCD=mpz_gcd_ui(NULL, mpzN, lDabs);
  /* if 1 < GCD < N then N is composite with factor lDabs, and
     Jacobi(D,N) is technically undefined (but often returned
     as zero). */
  if((ulGCD > 1) && mpz_cmp_ui(mpzN, ulGCD) > 0)RETURN(0);
  mpz_set_si(mpzD, lD);
  iJ=mpz_jacobi(mpzD, mpzN);
  if(iJ==-1)break;
  lDabs += 2;
  if(lDabs > ulDmax)ulDmax=lDabs;  /* tracks global max of |D| */
  if(lDabs > INT32_MAX-2)
    {
    fprintf(stderr,
      "\n ERROR: D overflows signed long in Lucas-Selfridge test.");
    fprintf(stderr, "\n N=");
    mpz_out_str(stderr, 10, mpzN);
    fprintf(stderr, "\n |D|=%ld\n\n", lDabs);
    exit(EXIT_FAILURE);
    }
  }

iP=1;         /* Selfridge's choice */
lQ=(1-lD)/4;  /* Required so D = P*P - 4*Q */

/* NOTE: The conditions (a) N does not divide Q, and
   (b) D is square-free or not a perfect square, are included by
   some authors; e.g., "Prime numbers and computer methods for
   factorization," Hans Riesel (2nd ed., 1994, Birkhauser, Boston),
   p. 130. For this particular application of Lucas sequences,
   these conditions were found to be immaterial. */

/* Now calculate N - Jacobi(D,N) = N + 1 (even), and calculate the
   odd positive integer d and positive integer s for which
   N + 1 = 2^s*d (similar to the step for N - 1 in Miller's test).
   The strong Lucas-Selfridge test then returns N as a strong
   Lucas probable prime (slprp) if any of the following
   conditions is met: U_d=0, V_d=0, V_2d=0, V_4d=0, V_8d=0,
   V_16d=0, ..., etc., ending with V_{2^(s-1)*d}=V_{(N+1)/2}=0
   (all equalities mod N). Thus d is the highest index of U that
   must be computed (since V_2m is independent of U), compared
   to U_{N+1} for the standard Lucas-Selfridge test; and no
   index of V beyond (N+1)/2 is required, just as in the
   standard Lucas-Selfridge test. However, the quantity Q^d must
   be computed for use (if necessary) in the latter stages of
   the test. The result is that the strong Lucas-Selfridge test
   has a running time only slightly greater (order of 10 %) than
   that of the standard Lucas-Selfridge test, while producing
   only (roughly) 30 % as many pseudoprimes (and every strong
   Lucas pseudoprime is also a standard Lucas pseudoprime). Thus
   the evidence indicates that the strong Lucas-Selfridge test is
   more effective than the standard Lucas-Selfridge test, and a
   Baillie-PSW test based on the strong Lucas-Selfridge test
   should be more reliable. */


mpz_add_ui(mpzNplus1, mpzN, 1);
s=mpz_scan1(mpzNplus1, 0);
mpz_tdiv_q_2exp(mpzd, mpzNplus1, s);

/* We must now compute U_d and V_d. Since d is odd, the accumulated
   values U and V are initialized to U_1 and V_1 (if the target
   index were even, U and V would be initialized instead to U_0=0
   and V_0=2). The values of U_2m and V_2m are also initialized to
   U_1 and V_1; the FOR loop calculates in succession U_2 and V_2,
   U_4 and V_4, U_8 and V_8, etc. If the corresponding bits
   (1, 2, 3, ...) of t are on (the zero bit having been accounted
   for in the initialization of U and V), these values are then
   combined with the previous totals for U and V, using the
   composition formulas for addition of indices. */

mpz_set_ui(mpzU, 1);                      /* U=U_1 */
mpz_set_ui(mpzV, iP);                     /* V=V_1 */
mpz_set_ui(mpzU2m, 1);                    /* U_1 */
mpz_set_si(mpzV2m, iP);                   /* V_1 */
mpz_set_si(mpzQm, lQ);
mpz_set_si(mpz2Qm, 2*lQ);
mpz_set_si(mpzQkd, lQ);  /* Initializes calculation of Q^d */

uldbits=mpz_sizeinbase(mpzd, 2);
for(ul=1; ul < uldbits; ul++)  /* zero bit on, already accounted for */
  {
/* Formulas for doubling of indices (carried out mod N). Note that
 * the indices denoted as "2m" are actually powers of 2, specifically
 * 2^(ul-1) beginning each loop and 2^ul ending each loop.
 *
 * U_2m = U_m*V_m
 * V_2m = V_m*V_m - 2*Q^m
 */
  mpz_mul(mpzU2m, mpzU2m, mpzV2m);
  mpz_mod(mpzU2m, mpzU2m, mpzN);
  mpz_mul(mpzV2m, mpzV2m, mpzV2m);
  mpz_sub(mpzV2m, mpzV2m, mpz2Qm);
  mpz_mod(mpzV2m, mpzV2m, mpzN);
  /* Must calculate powers of Q for use in V_2m, also for Q^d later */
  mpz_mul(mpzQm, mpzQm, mpzQm);
  mpz_mod(mpzQm, mpzQm, mpzN);  /* prevents overflow */
  mpz_mul_2exp(mpz2Qm, mpzQm, 1);
  if(mpz_tstbit(mpzd, ul))
    {
/* Formulas for addition of indices (carried out mod N);
 *
 * U_(m+n) = (U_m*V_n + U_n*V_m)/2
 * V_(m+n) = (V_m*V_n + D*U_m*U_n)/2
 *
 * Be careful with division by 2 (mod N)!
 */
    mpz_mul(mpzT1, mpzU2m, mpzV);
    mpz_mul(mpzT2, mpzU, mpzV2m);
    mpz_mul(mpzT3, mpzV2m, mpzV);
    mpz_mul(mpzT4, mpzU2m, mpzU);
    mpz_mul_si(mpzT4, mpzT4, lD);
    mpz_add(mpzU, mpzT1, mpzT2);
    if(mpz_odd_p(mpzU))mpz_add(mpzU, mpzU, mpzN);
    mpz_fdiv_q_2exp(mpzU, mpzU, 1);
    mpz_add(mpzV, mpzT3, mpzT4);
    if(mpz_odd_p(mpzV))mpz_add(mpzV, mpzV, mpzN);
    mpz_fdiv_q_2exp(mpzV, mpzV, 1);
    mpz_mod(mpzU, mpzU, mpzN);
    mpz_mod(mpzV, mpzV, mpzN);
    mpz_mul(mpzQkd, mpzQkd, mpzQm);  /* Calculating Q^d for later use */
    mpz_mod(mpzQkd, mpzQkd, mpzN);
    }
  }

/* If U_d or V_d is congruent to 0 mod N, then N is a prime or a
   strong Lucas pseudoprime. */

if(mpz_sgn(mpzU)==0)RETURN(1);
if(mpz_sgn(mpzV)==0)RETURN(1);

/* NOTE: Ribenboim ("The new book of prime number records," 3rd ed.,
   1995/6) omits the condition Vð0 on p.142, but includes it on
   p. 130. The condition is NECESSARY; otherwise the test will
   return false negatives---e.g., the primes 29 and 2000029 will be
   returned as composite. */

/* Otherwise, we must compute V_2d, V_4d, V_8d, ..., V_{2^(s-1)*d}
   by repeated use of the formula V_2m = V_m*V_m - 2*Q^m. If any of
   these are congruent to 0 mod N, then N is a prime or a strong
   Lucas pseudoprime. */

mpz_mul_2exp(mpz2Qkd, mpzQkd, 1);  /* Initialize 2*Q^(d*2^r) for V_2m */
for(r=1; r < s; r++)
  {
  mpz_mul(mpzV, mpzV, mpzV);
  mpz_sub(mpzV, mpzV, mpz2Qkd);
  mpz_mod(mpzV, mpzV, mpzN);
  if(mpz_sgn(mpzV)==0)RETURN(1);
/* Calculate Q^{d*2^r} for next r (final iteration irrelevant). */
  if(r < s-1)
    {
    mpz_mul(mpzQkd, mpzQkd, mpzQkd);
    mpz_mod(mpzQkd, mpzQkd, mpzN);
    mpz_mul_2exp(mpz2Qkd, mpzQkd, 1);
    }
  }

/* Otherwise N is definitely composite. */

RETURN(0);
}