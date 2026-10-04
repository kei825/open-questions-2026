/*
 * Enumerate every possible image of a (243,121,60) difference set of
 * G = Z3 x Z9 x Z9 in the quotient G/3G = Z3^3 (each coset has 9 elements).
 *
 * The image is a function E : Z3^3 -> {0..9} with
 *     sum E = 121,   sum_x E(x) E(x+s) = 60*9 = 540  for s != 0,
 *     sum_x E(x)^2 = 61 + 540 = 601.
 *
 * Method (complete, see README "Proof", step 4):
 *  - For each of the 13 directions d (nonzero vectors of Z3^3 up to sign),
 *    the plane sums P_d(j) = sum_{d.x = j} E(x), j = 0,1,2, form the image
 *    in the cyclic quotient Z3, so they satisfy  sum = 121, sum of squares
 *    = 61 + 60*81 = 4921.  The only integer solutions are the 6
 *    permutations of (36,40,45) (checked below by brute force).
 *  - E is recovered from the plane sums:
 *        sum_d P_d(d.x) = 13 E(x) + 4 (121 - E(x)) = 9 E(x) + 484.
 *  - So we run over all 6^13 choices of plane-sum vectors (with interval
 *    pruning), keep those for which (sum - 484)/9 is an integer in [0,9],
 *    and then check the definition (sum, autocorrelation) directly on E.
 *
 *  - With the argument "inv" (the default) we also impose what the
 *    multiplier 61 forces: every 61-orbit {g, 7g, 4g} of size 3 lies inside
 *    one coset of 3G (7g - g = 6g is in 3G), and the 27 fixed points of 61
 *    are exactly G[3] = Z3 x 3Z9 x 3Z9, which fills the 3 cosets
 *    (x1,0,0).  Hence E(x) = 0 (mod 3) for x2 or x3 != 0.
 *    With the argument "all" this is not imposed and only a count is printed.
 *
 * Output: one line per image, 27 numbers, x = (x1,x2,x3) in lexicographic
 * order (index 9*x1 + 3*x2 + x3).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int dirs[13][3];
static int dot[13][27];           /* d.x mod 3 */
static int perms[6][3];
static long long acc[27];
static long long nodes = 0, found = 0, rejected = 0;
static int nsol = 0;
static int sols[4096][27];
static int inv_mode = 1;

static int check_E(const int *E) {
    int s = 0, sq = 0;
    for (int x = 0; x < 27; x++) { if (E[x] < 0 || E[x] > 9) return 0; s += E[x]; sq += E[x]*E[x]; }
    if (s != 121 || sq != 601) return 0;
    for (int sh = 1; sh < 27; sh++) {
        int a1 = sh / 9, a2 = (sh / 3) % 3, a3 = sh % 3, c = 0;
        for (int x = 0; x < 27; x++) {
            int x1 = x / 9, x2 = (x / 3) % 3, x3 = x % 3;
            int y = 9*((x1+a1)%3) + 3*((x2+a2)%3) + (x3+a3)%3;
            c += E[x]*E[y];
        }
        if (c != 540) return 0;
    }
    return 1;
}

static void rec(int m) {
    nodes++;
    int r = 13 - m;
    for (int x = 0; x < 27; x++) {
        if (acc[x] + 36LL*r > 565 || acc[x] + 45LL*r < 484) return;
    }
    if (m == 13) {
        int E[27];
        for (int x = 0; x < 27; x++) {
            long long t = acc[x] - 484;
            if (t % 9) return;
            E[x] = (int)(t / 9);
        }
        found++;
        if (!check_E(E)) { rejected++; return; }
        if (!inv_mode) { nsol++; return; }
        for (int x = 0; x < 27; x++) if ((x % 9) != 0 && E[x] % 3) return;
        for (int i = 0; i < nsol; i++) if (!memcmp(sols[i], E, sizeof E)) return;
        if (nsol >= 4096) { fprintf(stderr, "too many\n"); exit(2); }
        memcpy(sols[nsol++], E, sizeof E);
        return;
    }
    for (int p = 0; p < 6; p++) {
        for (int x = 0; x < 27; x++) acc[x] += perms[p][dot[m][x]];
        rec(m + 1);
        for (int x = 0; x < 27; x++) acc[x] -= perms[p][dot[m][x]];
    }
}

int main(int argc, char **argv) {
    if (argc > 1 && !strcmp(argv[1], "all")) inv_mode = 0;
    /* step 0: integer solutions of c0+c1+c2=121, c0^2+c1^2+c2^2=4921 */
    int np = 0;
    for (int a = 0; a <= 81; a++) for (int b = 0; b <= 81; b++) {
        int c = 121 - a - b;
        if (c < 0 || c > 81) continue;
        if (a*a + b*b + c*c == 4921) {
            if (np >= 6) { fprintf(stderr, "unexpected extra Z3-image\n"); return 1; }
            perms[np][0] = a; perms[np][1] = b; perms[np][2] = c; np++;
        }
    }
    fprintf(stderr, "Z3-quotient images: %d:", np);
    for (int i = 0; i < np; i++) fprintf(stderr, " (%d,%d,%d)", perms[i][0], perms[i][1], perms[i][2]);
    fprintf(stderr, "\n");
    if (np != 6) return 1;
    /* directions: first nonzero coordinate equal to 1 */
    int nd = 0;
    for (int v = 1; v < 27; v++) {
        int d[3] = { v / 9, (v / 3) % 3, v % 3 };
        int f = d[0] ? d[0] : (d[1] ? d[1] : d[2]);
        if (f != 1) continue;
        memcpy(dirs[nd++], d, sizeof d);
    }
    if (nd != 13) return 1;
    for (int i = 0; i < 13; i++) for (int x = 0; x < 27; x++)
        dot[i][x] = (dirs[i][0]*(x/9) + dirs[i][1]*((x/3)%3) + dirs[i][2]*(x%3)) % 3;
    /* sanity check of the inversion formula on random functions */
    srand(12345);
    for (int trial = 0; trial < 1000; trial++) {
        int f[27], s = 0;
        for (int x = 0; x < 27; x++) { f[x] = rand() % 10; s += f[x]; }
        for (int x = 0; x < 27; x++) {
            int tot = 0;
            for (int i = 0; i < 13; i++) for (int y = 0; y < 27; y++)
                if (dot[i][y] == dot[i][x]) tot += f[y];
            if (tot != 9*f[x] + 4*s) { fprintf(stderr, "inversion formula fails\n"); return 1; }
        }
    }
    fprintf(stderr, "inversion formula sum_d P_d(d.x) = 9 f(x) + 4 sum f: ok on 1000 random f\n");
    rec(0);
    fprintf(stderr, "search nodes %lld, integral candidates %lld, rejected by direct check %lld, distinct images %d\n",
            nodes, found, rejected, nsol);
    if (!inv_mode) return 0;
    for (int i = 0; i < nsol; i++) {
        for (int x = 0; x < 27; x++) printf("%d%c", sols[i][x], x == 26 ? '\n' : ' ');
    }
    return 0;
}
