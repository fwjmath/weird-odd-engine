/* trn.h                 Thomas R. Nicely          2012.01.26.1000
 *
 * Freeware copyright (c) 2012 Thomas R. Nicely <http://www.trnicely.net>.
 * Released into the public domain by the author, who disclaims any legal
 * liability arising from its use.
 *
 * Trimmed by fwjmath, 2013.02.26
 *
 */

#include <stdlib.h>
#include <stdio.h>

#include "../gmp.h"

#define INT32_MAX 2147483647L

/* Prime number generation and testing using GMP */

int     iMiller(mpz_t mpzN, long iB);
int     iBPSW(mpz_t mpzN);
int     iStrongLucasSelfridge(mpz_t mpzN);