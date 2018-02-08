/* Voting application based on the Damgard-Jurik cryptosystem
 * Copyright (C) 2008-2010  Andreas Steffen
 * HSR Hochschule fuer Technik Rapperswil, Switzerland
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by the
 * Free Software Foundation; either version 2 of the License, or (at your
 * option) any later version.  See <http://www.fsf.org/copyleft/gpl.txt>.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * for more details.
 *
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <gmp.h>

#define NCHOICEMAX        4
#define NVOTEMAX        8
#define NMAX          100    
#define NPRINTMAX      225
#define NSTOREMAX    20000
#define SMAX            6

static const int N = 5;
static const int T = 3;

static void extract_parameter(char *query, char* name, unsigned int *value)
{
    char *pos = strstr(query, name);

    if (pos)
    {
        *value = atoi(pos + strlen(name) + 1);
    }
}

static void printf_prime_selection_list(char *label, unsigned int prime)
{
    unsigned int primes[] = { 3, 5, 7, 11, 23, 47, 59, 83, 107, 167, 179 };
    const int NPRIMES = 11;
    int n;

    printf("    %s = \n", label);
    printf("    <select name=\"%s\">\n", label);
    for (n = 0; n < NPRIMES; n++)
    {
        printf("      <option value=\"%u\"%s>%u</option>\n",
               primes[n],
              (primes[n] == prime)? " selected=\"selected\"":"",
               primes[n]);
    }
    printf("    </select>\n");
}

static void printf_vote(unsigned int v, unsigned int *votes, unsigned int *cheat)
{
    unsigned int k;

    printf("        <tr>\n");
    printf("          <td>V%u</td>\n", v);

    for (k = 0; k < NCHOICEMAX; k++)
    {
        printf("          <td><input type=\"radio\" name=\"v%u\" value=\"%u\"", v, k);
        if (k == votes[v-1])
        {
            printf(" checked=\"checked\"");
        }
        if (k == 0)
        {
            printf(">None</td>\n");
        }
        else
        {
            printf(">C%u</td>\n", k);
        }
    }
    printf("          <td class=\"%s\">", (cheat[v-1] == 1)? "numg":"numb");
    printf("<input name=\"m%u\" type=\"text\" size=\"3\" value=\"%u\"></td>\n",
            v, cheat[v-1]);
    printf("        </tr>\n");
}

static void iterative_decrypt(mpz_t i, mpz_t c, mpz_t nj[], unsigned int s)
{
    unsigned int j, k, kfac;
    mpz_t a, t1, t2, t3;

    mpz_init(t1);
    mpz_init(t2);
    mpz_init(t3);
    mpz_init_set(a, c);
    mpz_set_ui(i, 0);

    for (j = 1; j <=s; j++)
    {
        mpz_set(t1, a);
        mpz_mod(t1, t1, nj[j]);
        mpz_sub_ui(t1, t1, 1);
        mpz_div(t1, t1, nj[0]);
        mpz_set(t2, i);
        kfac = 1;

        for (k = 2; k <= j; k++)
        {
            kfac *= k;
            mpz_sub_ui(i, i, 1);
            mpz_mul(t2, t2, i);
            mpz_mod(t2, t2, nj[j-1]);
            mpz_set_ui(t3, kfac);
            if (mpz_invert(t3, t3, nj[j-1]) == 0)
            {
                printf("\nFAILURE: could not invert %u! = %u\n", k, kfac);
            }
            mpz_mul(t3, t3, t2);
            mpz_mod(t3, t3, nj[j-1]);
            mpz_mul(t3, t3, nj[k-2]);
            mpz_mod(t3, t3, nj[j-1]);
            mpz_sub(t1, t1, t3);
            mpz_mod(t1, t1, nj[j-1]);
        }
        mpz_set(i, t1);
    }
    mpz_clear(a);
    mpz_clear(t1);
    mpz_clear(t2);
    mpz_clear(t3);
}

static void damgard_jurik_encrypt(mpz_t c, mpz_t m, mpz_t r, mpz_t g, mpz_t ns, mpz_t ns1)
{
    mpz_t gm, rns;

    mpz_init(gm);
    mpz_init(rns);
    mpz_powm(gm, g, m, ns1);
    mpz_powm(rns, r, ns, ns1);
    mpz_mul(c, gm, rns);
    mpz_mod(c, c, ns1);
    mpz_clear(gm);
    mpz_clear(rns);
}

static void damgard_jurik_decrypt(mpz_t m, mpz_t c, mpz_t d, mpz_t mu, mpz_t nj[], unsigned int s)
{
    mpz_powm(m, c, d, nj[s]);
    iterative_decrypt(m, m, nj, s);
    mpz_mul(m, m, mu);
    mpz_mod(m, m, nj[s-1]);
}

/**
 * Evaluate a polynomial
 */
static void polynomial(mpz_t y, unsigned int x, unsigned int a[], int n, mpz_t q)
{
    int k;

    mpz_init_set_ui(y, a[n-1]);
    for (k = n-2; k >= 0; k--)
    {
        mpz_mul_ui(y, y, x);
        mpz_add_ui(y, y, a[k]);
        mpz_mod(y, y, q);
    }
}

/**
 * Compute coefficients for Lagrange interpolation
*/
static void lagrange(int l[], int N, long set, unsigned int delta_ui)
{
    int i, j;

    for (i = 0; i < N; i++)
    {
        if (set & 1<<i)
        {
            l[i] = delta_ui;

            for (j = 0; j < N; j++)
            {
                if (i != j && (set & 1<<j))
                {
                    l[i] /= j - i;
                    l[i] *= j + 1;
                }
            }
        }
        else
        {
            l[i] = 0;
        }
        if (l[i])
        {
            printf("      <td class=\"numc\">%d</td>\n", l[i]);
        }
        else
        {
            printf("      <td class=\"numc\">&nbsp;</td>\n");
        }
    }
}

static void mpz_export_ui(unsigned int *x_ui, mpz_t x)
{
    if (mpz_cmp_ui(x, 0) == 0)
    {
        *x_ui = 0;
    }
    else
    {
        mpz_export(x_ui, NULL, 1, sizeof(unsigned int), 0, 0, x);
    }
}

/**
 * Special exponential product
 */
static void exponential(mpz_t y, mpz_t *c, int N, int *l, mpz_t ns1)
{
    unsigned int y_ui;
    mpz_t v;
    int i;

    mpz_init(v);
    mpz_set_ui(y, 1);

    for (i = 0; i < N; i++)
    {
        if (l[i])
        {
            mpz_powm_ui(v, c[i], 2*abs(l[i]), ns1);
            if (l[i] < 0)
            {
                mpz_invert(v, v, ns1);
            }
            mpz_mul(y, y, v);
            mpz_mod(y, y, ns1);
        }
    }
    mpz_export_ui(&y_ui, y);
    printf("    <td>%u</td>\n", y_ui);
    mpz_clear(v);
}

static void normalize(mpz_t y, mpz_t delta2_inv, mpz_t nj[], unsigned int s)
{
    unsigned int y_ui;

    iterative_decrypt(y, y, nj, s);
    mpz_mul(y, y, delta2_inv);
    mpz_mod(y, y, nj[s-1]);
    mpz_export_ui(&y_ui, y);
    printf("    <td class=\"numi\">%u</td>\n", y_ui);
}

static unsigned int mpz_random_ui(gmp_randstate_t randstate, unsigned int max_ui)
{
    unsigned int r_ui;
    mpz_t max, r;

    mpz_init(r);
    mpz_init_set_ui(max, max_ui);
    mpz_urandomm(r, randstate, max);
    mpz_export_ui(&r_ui, r);
    mpz_clear(r);
    mpz_clear(max);

    return r_ui;
}

int main(int argc, char **argv)
{
    unsigned int hide_enc   =  0;
    unsigned int hide_proof =  0;
    unsigned int alpha_fixed = 0;
    unsigned int beta_fixed  = 0;
    unsigned int base    =  6;
    unsigned int seed_ui =  6;
    unsigned int p_ui    =  7;
    unsigned int q_ui    = 11;
    unsigned int s_ui    =  2;
    unsigned int alpha_ui, beta_ui, lambda_ui, phi_ui;
    unsigned int n_ui, ns_ui, ns1_ui, p1_ui, q1_ui, n1_ui;
    unsigned int g_ui, d_ui, mu_ui;
    unsigned int r_ui[NSTOREMAX];
    unsigned int r_votes[NVOTEMAX];
    unsigned int t_choices[NCHOICEMAX];
    unsigned int votes[] = { 1, 2, 2, 3, 2, 3, 1, 0 };
    unsigned int cheat[] = { 1, 1, 1, 2, 1, 1, 2, 1 };
    unsigned int cheaters = 0;
    unsigned int bits;
    int i, j, k;

    mpz_t nj[SMAX];
    mpz_t p, q, n, n1, ns, ns1, d, g, g_inv, mu, t, phi, lambda;
    gmp_randstate_t randstate;

    char *query = getenv("QUERY_STRING");

    memset(t_choices, 0x00, sizeof(t_choices));
 
    extract_parameter(query, "p", &p_ui);
    extract_parameter(query, "q", &q_ui);
    extract_parameter(query, "s", &s_ui);
    extract_parameter(query, "base", &base);
    extract_parameter(query, "seed", &seed_ui);
    extract_parameter(query, "hide_enc", &hide_enc);
    extract_parameter(query, "hide_proof", &hide_proof);
    extract_parameter(query, "alpha_fixed", &alpha_fixed);
    extract_parameter(query, "beta_fixed", &beta_fixed);

    for (j = 0; j < NVOTEMAX; j++)
    {
        char buffer[10];

        snprintf(buffer, sizeof(buffer), "v%u", j+1);
        extract_parameter(query, buffer, &votes[j]);
        snprintf(buffer, sizeof(buffer), "m%u", j+1);
        extract_parameter(query, buffer, &cheat[j]);
        if (cheat[j] == 1)
        {
            t_choices[votes[j]]++;
        }
        else
        {
            cheaters++;
        }
    }

    printf("Content-Type: text/html\n");
    printf("\n");
    printf("<html>\n");
    printf("<head>\n");
    printf("  <title>Damg&aring;rd-Jurik Cryptosystem</title>\n");
    printf("  <style>\n");
    printf("    body     { font-family: sans-serif }\n");
    printf("    td       { text-align: left;   padding: 0px 3px 0px 3px; background: #FFFF66 }\n");
    printf("    td.tr    { text-align: left;   background: #00FF66 }\n");
    printf("    td.outer { text-align: left;   background: #FFFFFF }\n");
    printf("    td.tcg   { text-align: center; background: #00FF66 }\n");
    printf("    td.tcb   { text-align: center; background: #FF3333 }\n");
    printf("    td.num   { text-align: right;  background: #FFFF66 }\n");
    printf("    td.numa  { text-align: right;  background: #FFCC66 }\n");
    printf("    td.numb  { text-align: right;  background: #FF3333 }\n");
    printf("    td.numc  { text-align: right;  background: #FFCC66 }\n");
    printf("    td.nume  { text-align: right;  background: #FFCCCC }\n");
    printf("    td.numg  { text-align: right;  background: #00FF66 }\n");
    printf("    td.numi  { text-align: right;  background: #99FFFF }\n");
    printf("    td.numt  { text-align: right;  background: #00FF66 }\n");
    printf("    td.numu  { text-align: right;  background: #FFCCCC }\n");
    printf("    td.numz  { text-align: right;  background: #FFCC66 }\n");
    printf("    td.headl { text-align: left;   padding: 1px 3px 1px 3px; background: #FFA522 }\n");
    printf("    td.headr { text-align: right;  padding: 1px 3px 1px 3px; background: #FFA522 }\n");
    printf("    hr { background-color: #000000; border: 0; height: 1px; }\n");
    printf("    a:visited { color: #000000 }\n");
    printf("    a:link    { color: #000000 }\n");
    printf("    a:hover   { color: #0000FF }\n");
    printf("  </style>\n");
    printf("</head>\n");
    printf("<body>\n");
    printf("  <h1><a href=\"/msevote/glossary.html#damgardjurik\">Damg&aring;rd-Jurik Cryptosystem</a></h1>\n");
    printf("  <form action=\"/msevote/damgardjurik\">\n");
    printf("    <a href=\"/msevote/glossary.html#rsa\">RSA Factors</a>: \n");
    printf_prime_selection_list("p", p_ui);
    printf_prime_selection_list("q", q_ui);
    printf("    <input type=\"submit\" value=\"Start\">\n");
    printf("    <p>\n");
    printf("    <table><tr>\n");
    printf("    <td class=\"outer\">\n");
    printf("      <table>\n");
    printf("        <tr>\n");
    printf("          <td class=\"headl\">Voter</td>\n");
    printf("          <td class=\"headl\" colspan=\"4\">Candidates</td>\n");
    printf("          <td class=\"headl\">Cheat</td>\n");
    printf("        </tr>\n");
    for (j = 1; j <= NVOTEMAX; j++)
    {
        printf_vote(j, votes, cheat);
    }
    printf("        <tr>\n");
    printf("          <td class=\"tr\">Tally</td>\n");
    for (k = 0; k < NCHOICEMAX; k++)
    {
        printf("          <td class=\"tcg\">%u</td>\n", t_choices[k]);
    }
    printf("          <td class=\"tcb\">%u</td>\n", cheaters);
    printf("        </tr>\n");
    printf("      </table>\n");
    printf("    </td>\n");
    printf("    <td class=\"outer\">\n");
    printf("      <table>\n");
    printf("        <tr><td class=\"outer\" colspan=\"2\">\n");
    printf("          Hide details of:\n");
    printf("        </td></tr>\n");
    printf("        <tr><td class=\"outer\" colspan=\"2\">\n");
    printf("          <input name=\"hide_enc\" type=\"checkbox\" value=\"1\" %s>", hide_enc? "checked=\"checked\"":"");
    printf("          Damg&aring;rd-Jurik <a href=\"/msevote/glossary.html#paillierEncryption\">Encryption</a>\n");
    printf("          / <a href=\"/msevote/glossary.html#paillierDecryption\">Decryption</a>\n");
    printf("        </td></tr>\n");
    printf("        <tr><td class=\"outer\" colspan=\"2\">\n");
    printf("          <input name=\"hide_proof\" type=\"checkbox\" value=\"1\" %s>", hide_proof? "checked=\"checked\"":"");
    printf("          <a href=\"/msevote/glossary.html#zeroKnowledgeProof\">Zero-Knowledge Proof</a>\n");
    printf("        </td></tr>\n");
    printf("        <tr><td class=\"outer\">\n");
    printf("          &nbsp;\n");
    printf("        </td></tr>\n");
    printf("        <tr><td class=\"outer\" colspan=\"2\">\n");
    printf("          Generator g:\n");
    printf("        </td></tr>\n");
    printf("        <tr><td class=\"outer\" colspan=\"2\">\n");
    printf("          <input name=\"alpha_fixed\" type=\"checkbox\" value=\"1\" %s>", alpha_fixed? "checked=\"checked\"":"");
    printf("          &alpha; fixed to 1\n");
    printf("        </td></tr>\n");
    printf("        <tr><td class=\"outer\" colspan=\"2\">\n");
    printf("          <input name=\"beta_fixed\" type=\"checkbox\" value=\"1\" %s>", beta_fixed? "checked=\"checked\"":"");
    printf("          &beta; fixed to 1\n");
    printf("        </td></tr>\n");
    printf("        <tr><td class=\"outer\">\n");
    printf("          &nbsp;\n");
    printf("        </td></tr>\n");
    printf("        <tr>\n");
    printf("          <td class=\"outer\">\n");
    printf("            <a href=\"/msevote/glossary.html#paillierExponent\">Exponent s</a>\n");
    printf("          </td>\n");
    printf("          <td class=\"outer\">\n");
    printf("            <input name=\"s\" type=\"text\" size=\"3\" value=\"%d\"> \n", s_ui);
    printf("          </td>\n");
    printf("        </tr>\n");
    printf("        <tr>\n");
    printf("          <td class=\"outer\">\n");
    printf("            <a href=\"/msevote/glossary.html#paillierMessage\">Message</a> \n");
    printf("            <a href=\"/msevote/glossary.html#paillierMessageBase\">Base</a>\n");
    printf("          </td>\n");
    printf("          <td class=\"outer\">\n");
    printf("            <input name=\"base\" type=\"text\" size=\"3\" value=\"%d\"> \n", base);
    printf("          </td>\n");
    printf("        </tr>\n");
    printf("        <tr>\n");
    printf("          <td class=\"outer\">\n");
    printf("            <a href=\"/msevote/glossary.html#randomSeed\">Random Seed</a>\n");
    printf("          </td>\n");
    printf("          <td class=\"outer\">\n");
    printf("            <input name=\"seed\" type=\"text\" size=\"3\" value=\"%d\"> \n", seed_ui);
    printf("          </td>\n");
    printf("        </tr>\n");
    printf("      </table>\n");
    printf("    </td></tr></table>\n");    
    printf("    </p>\n");
    printf("  </form>\n");
    printf("  <pre>\n");

     if (p_ui == q_ui)
    {
        printf("FAILURE: <em>p</em> = <em>q</em> = %u  cannot be equal.\n\n", p_ui);
        printf("  </pre>\n");
        goto end;
    }

    if (s_ui > SMAX)
    {
        printf("WARNING: the exponent s is too large and has been limited to s = %u.\n", SMAX);
        s_ui = SMAX;
    }

    if (q_ui <= s_ui)
    {
        printf("FAILURE: since q &le; s the Damg&aring;rd-Jurik Cryptosystem will not work!\n");
        printf("  </pre>\n");
        goto end;
    }

    if (p_ui <= s_ui)
    {
        printf("FAILURE: since p &le; s the Damg&aring;rd-Jurik Cryptosystem will not work!\n");
        printf("  </pre>\n");
        goto end;
    }
 
 
    /* compute n = p*q and n^2, phi(n) and lambda(n) */
    n_ui  = p_ui * q_ui;
    p1_ui = (p_ui - 1)/2;
    q1_ui = (q_ui - 1)/2;
    n1_ui = p1_ui * q1_ui;
    phi_ui = 4 * n1_ui;
    lambda_ui = 2 * n1_ui;

    /* convert p, q, n, n1, phi(n), and lambda(n) to mpz_t values */
    mpz_init_set_ui(p, p_ui);
    mpz_init_set_ui(q, q_ui);
    mpz_init_set_ui(n, n_ui);
    mpz_init_set_ui(n1, n1_ui);
    mpz_init_set_ui(phi, phi_ui);
    mpz_init_set_ui(lambda, lambda_ui);

    /* compute all s+1 powers of n */
    mpz_init_set(nj[0], n);
    for (j = 1; j <= s_ui; j++)
    {
        mpz_init_set(nj[j], nj[j-1]);
        mpz_mul(nj[j], nj[j], n);
    }
    mpz_init_set(ns, nj[s_ui-1]);
    mpz_export_ui(&ns_ui, ns);
    mpz_init_set(ns1, nj[s_ui]);
    mpz_export_ui(&ns1_ui, ns1);

    if (phi_ui > NSTOREMAX)
    {
        printf("FAILURE: <em>&phi;(n) = (p-1)(q-1)</em> = %u exceeds the maximum simulation size NSTOREMAX = %u.\n\n",
                phi_ui, NSTOREMAX);
        printf("  </pre>\n");
        goto end;
    }
 
    /* Test if a tally overflow will occur */
    {
        unsigned int tm_ui = 0;

        for (k = 1; k < NCHOICEMAX; k++)
        {
            if (k < NCHOICEMAX - 1 && t_choices[k] >= base)
            {
                printf("WARNING:  A tally overflow for candidate C%u will occur. Set the message base &gt; %u.\n",
                        k, t_choices[k]);
            }
            tm_ui = tm_ui * base + t_choices[NCHOICEMAX - k];
        }
        if (tm_ui >= ns_ui)
        {
            printf("WARNING:  A tally overflow will occur with the given message base. Choose n^s = &gt; %u.\n",
                    tm_ui);
        }
    }

    /* initialize random generator */
    gmp_randinit_default(randstate);
    gmp_randseed_ui(randstate, seed_ui);

    /* Determine all coprimes using the sieve of Erathostenes */
    {
        char sieve[n_ui];

        /* set all integers */
        for (i = 0; i < n_ui; i++)
        {
            sieve[i] = 1;
        }

        /* delete all multiples of p */
        for (i = 1; i < q_ui; i++)
        {
            sieve[i * p_ui] = 0;
        }

        /* delete all multiples of q */
        for (i = 1; i < p_ui; i++)
        {
            sieve[i * q_ui] = 0;
        }

        /* store the remaining integers that are coprime */
        k = 0;
        for (i = 1; i < n_ui; i++)
        {
            if (sieve[i])
            {
                r_ui[k++] = i;
            }
        }
    }

    /* Set the generator g */
    {
        mpz_t rn;

        alpha_ui = alpha_fixed ? 1 : r_ui[mpz_random_ui(randstate, phi_ui)];
        beta_ui  = beta_fixed  ? 1 : r_ui[mpz_random_ui(randstate, phi_ui)];
        g_ui =  n_ui + 1;
        mpz_init_set_ui(g, g_ui);
        mpz_powm_ui(g, g, alpha_ui, ns1);
        mpz_init_set_ui(rn, beta_ui);
        mpz_powm(rn, rn, ns, ns1);
        mpz_mul(g, g, rn);
        mpz_mod(g, g, ns1);
        mpz_export_ui(&g_ui, g);
        mpz_clear(rn);
    }

    /* Compute the inverse of g */
    mpz_init(g_inv);
    mpz_invert(g_inv, g, ns1);

    /* Print the crypto system parameters */
    printf("\np = %u, q = %u, n = pq = %u, &phi;(n) = 4n' = %u, &lambda;(n) = lcm(p-1,q-1) = 2n' = %u\n\n",
            p_ui, q_ui, n_ui, phi_ui, lambda_ui);
    printf("p'= (p-1)/2 = %u, q'= (q-1)/2 = %u, n'= p'q'= %u\n\n",
             p1_ui, q1_ui, n1_ui);
    printf("s = %u, ns = n^s = %u, n^(s+1) = %u\n\n",
            s_ui, ns_ui, ns1_ui);

    /* Test if phi(n) and n are coprime */
    {
        mpz_t gcd;

        mpz_init(gcd);
        mpz_gcd(gcd, phi, n);
        if (mpz_cmp_ui(gcd, 1) != 0)
        {
            printf("WARNING:  n and &phi;(n) are not coprime. Therefore the Damg&aring;rd-Jurik Encryption will not work!\n\n");
        }
        mpz_clear(gcd);
    }
    printf("<a href=\"/msevote/glossary.html#paillierMessage\">Valid Voting Messages</a>:        m = mi, None: m0 = 0, C1: m1 = 1, C2: m2 = b = %d, C3: m3 = b^2 = %d\n\n", base, base * base);

    /* Determine private exponent d */
    {
        mpz_t gcd, x, y;
        u_int gcd_ui, x_ui, y_ui;

        mpz_init(gcd);
        mpz_init(x);
        mpz_init(y);
        mpz_gcdext(gcd, x, y, lambda, ns);
        while (mpz_sgn(y) > 0)
        {
            mpz_sub(y, y, lambda);
            mpz_add(x, x, ns);
        }
        mpz_export_ui(&x_ui, x);
        mpz_export_ui(&y_ui, y);
        mpz_init(d);
        mpz_mul(d, x, lambda);
        mpz_export_ui(&d_ui, d);
        mpz_clear(gcd);
        mpz_clear(x);
        mpz_clear(y);
        printf("Damg&aring;rd-Jurik Private Key:    d = x*&lambda;(n) = %u*%u = y*n^s + 1 = %u*%u + 1 = %u\n\n",
               x_ui, lambda_ui, y_ui, ns_ui, d_ui);
    }

    /* Compute secret decryption factor mu */
    mpz_init(mu);
    mpz_powm(mu, g, d, ns1);
    iterative_decrypt(mu, mu, nj, s_ui);
    mpz_invert(mu, mu, ns);
    mpz_export_ui(&mu_ui, mu);

    printf("Damg&aring;rd-Jurik Encryption:     c[m,r] = g^m * r^(n^s) mod n^(s+1), with generator "
           "g = (n+1)^&alpha; * &beta^(n^s) mod n^(s+1) = %u  (&alpha; = %u, &beta; = %u)\n\n",
            g_ui, alpha_ui, beta_ui);

    if (n_ui <= NMAX && ns1_ui < 10000000 && !hide_enc)
    {
        int i_max = (ns_ui > NPRINTMAX) ? NPRINTMAX : ns_ui;
        mpz_t rns[NMAX], gm[NPRINTMAX];

        /* Print all possible messages m */
        printf("              ");
        for (i = 0; i < i_max; i++)
        {
            printf(" %7u", i);
        }
        printf("  m\n");

        /* Compute and print all powers m of the generator g */
        {
            unsigned int gm_ui;

            printf("               %7u", 1);
            mpz_init_set_ui(gm[0], 1);
            for (i = 1; i < i_max; i++)
            {
                mpz_init(gm[i]);
                mpz_mul(gm[i], gm[i-1], g);
                mpz_mod(gm[i], gm[i], ns1);
                mpz_export_ui(&gm_ui, gm[i]);
                printf(" %7u", gm_ui);
            }
            printf("  g^m\n\n");
        }
    
        /* Compute and print all possible Damgard-Jurik encryptions */
        {
            unsigned int rns_ui, c_ui;
            mpz_t r, c;

            mpz_init(r);
            mpz_init(c);

            for (k = 0; k < phi_ui; k++)
            {
                mpz_set_ui(r, r_ui[k]);
                mpz_init(rns[k]);
                mpz_powm(rns[k], r, ns, ns1); 
                mpz_export_ui(&rns_ui, rns[k]);
                printf("%4u %7u  ", r_ui[k], rns_ui); 

                for (i = 0; i < i_max; i++)
                {
                    mpz_mul(c, rns[k], gm[i]);
                    mpz_mod(c, c, ns1);
                    mpz_export_ui(&c_ui, c);
                    printf(" %7u", c_ui);
                }
                printf("\n");            
            }
            printf("   r  r^(n^s)\n\n");

            mpz_clear(r);
            mpz_clear(c);
        }

        /* Damgard-Jurik  Decryption */
        {
            unsigned int dx_ui;
            mpz_t dx;

            mpz_init(dx);

            printf("Damg&aring;rd-Jurik Decryption I:   c[m,r]^d mod n^(s+1)\n\n");

            for (k = 0; k < phi_ui; k++)
            {
                printf("%4u          ", r_ui[k]); 

                for (i = 0; i < i_max; i++)
                {
                    mpz_mul(dx, rns[k], gm[i]);
                    mpz_mod(dx, dx, ns1);
                    mpz_powm(dx, dx, d, ns1);
                    mpz_export_ui(&dx_ui, dx);
                    printf(" %7u", dx_ui);
                }
                printf("\n");            
            }
            printf("   r\n\n");

            printf("Damg&aring;rd-Jurik Decryption II:  I(c[m,r]^d mod n^(s+1)) mod n^s\n\n");
            printf("  any r              0");
            for (i = 1; i < i_max; i++)
            {
                mpz_powm(dx, gm[i], d, ns1);
                iterative_decrypt(dx, dx, nj, s_ui);  
                mpz_export_ui(&dx_ui, dx);
                printf(" %7u", dx_ui);
            }
            printf("\n\n");    

            printf("Damg&aring;rd-Jurik Decryption III: I(c[m,r]^d mod n^(s+1)) * &mu; mod n^s, with &mu; = 1/I(g^d mod n^(s+1)) mod n^s = %u\n\n",
                    mu_ui);

            printf("  any r              0");
            for (i = 1; i < i_max; i++)
            {
                mpz_powm(dx, gm[i], d, ns1);
                iterative_decrypt(dx, dx, nj, s_ui);  
                mpz_mul(dx, dx, mu);
                mpz_mod(dx, dx, ns);
                mpz_export_ui(&dx_ui, dx);
                printf(" %7u", dx_ui);
            }
            printf("\n\n");    
        
            mpz_clear(dx);
        }

        /* Cleaning up */
        for (i = 0; i < n_ui; i++)
        {
            mpz_clear(gm[i]);
        }

        for (k = 0; k < phi_ui; k++)
        {
            mpz_clear(rns[k]);
        }
    }
    else
    {
        printf("Damg&aring;rd-Jurik Decryption:     I(c[m,r]^d mod n^(s+1)) * &mu; mod n^s, "
               "with &mu; = 1/I(g^d mod n^(s+1)) mod n^s = %u\n\n", mu_ui);
    }

    /* Voting and Tallying */
    {
        unsigned int m_ui, rj_ui, c_ui, e_max_ui, es_ui, t_ui, tm_ui;
        unsigned int mk_ui[NCHOICEMAX];
        mpz_t m, c, r, e_max, es;
        mpz_t gmk_inv[NCHOICEMAX], uk[NCHOICEMAX];
        mpz_t ak[NCHOICEMAX], ek[NCHOICEMAX], zk[NCHOICEMAX];
        mpz_t znk[NCHOICEMAX], znsk[NCHOICEMAX];

        mpz_init(m);
        mpz_init(c);
        mpz_init(r);
        bits = mpz_sizeinbase((p_ui < q_ui)? p : q, 2) - 1;
        mpz_init_set_ui(e_max, 2);
        mpz_pow_ui(e_max, e_max, bits);
        mpz_export_ui(&e_max_ui, e_max);
        mpz_init(es);
        mpz_init_set_ui(t, 1);

        printf("<a href=\"/msevote/glossary.html#zeroKnowledgeProof\">Validity Proof of Ballot</a>:     "
               "uk = c[m,r]/g^mk mod n^(s+1) must be an (n^s)-th power for k == i\n\n", e_max_ui, bits);
        if (!hide_proof)
        {
            printf("P:          (k == i)          &omega;\n");
            printf("P --> V:                      ai = &omega;^(n^s) mod n^(s+1)\n");
            printf("P:          (k != i)          zk, ek < 2^%u\n", bits);
            printf("P --> V:                      ak = zk^(n^s) / uk^ek mod n^(s+1)\n");
            printf("V --> P:                      es < 2^%u\n", bits);
            printf("P --> V:    (k == i)          ei = es - &Sigma;(ek) mod %u, for all k != i\n", e_max_ui);
            printf("P --> V:                      zi = &omega; * r^ei mod n\n");
            printf("P --> V:    (k != i)          ek\n");
            printf("P --> V:                      zk\n");
            printf("V:                            &Sigma;(ek) == es mod %u\n", e_max_ui);
            printf("V:                            zk^(n^s) == ak * uk^ek mod n^(s+1)\n\n");
        }
        printf("Voting and Tallying:          t = &Pi;(c[m,r]) mod n^(s+1)\n");
        printf("  </pre>\n");
        printf("  <table>\n");
        printf("    <tr>\n");
        printf("      <td class=\"headl\">Voter</td>\n");
        printf("      <td class=\"headr\">m</td>\n");
        printf("      <td class=\"headr\">r</td>\n");
        printf("      <td class=\"headr\">c</td>\n");
        if (!hide_proof)
        {
            for (k = 0; k < NCHOICEMAX; k++)
            {
                printf("      <td class=\"headr\">u%u</td>\n", k);
            }
            for (k = 0; k < NCHOICEMAX; k++)
            {
                printf("      <td class=\"headr\">a%u</td>\n", k);
            }
            printf("      <td class=\"headr\">es</td>\n");
            for (k = 0; k < NCHOICEMAX; k++)
            {
                printf("      <td class=\"headr\">e%u</td>\n", k);
            }
            printf("      <td class=\"headr\">&omega;</td>\n");
            for (k = 0; k < NCHOICEMAX; k++)
            {
                printf("      <td class=\"headr\">z%u</td>\n", k);
            }
        }
        for (k = 0; k < NCHOICEMAX; k++)
        {
            mpz_init(uk[k]);
            mpz_init(ak[k]);
            mpz_init(ek[k]);
            mpz_init(zk[k]);
            mpz_init(znk[k]);
            mpz_init(znsk[k]);
            printf("      <td class=\"headr\">z%u^ns</td>\n", k);
        }
        printf("      <td class=\"headr\">t</td>\n");
        printf("      <td class=\"headr\">tm</td>\n");
        printf("      <td class=\"headr\">C1</td>\n");
        printf("      <td class=\"headr\">C2</td>\n");
        printf("      <td class=\"headr\">C3</td>\n");
        printf("    </tr>\n");

        /* precompute g^-m mod n^(s+1) for all valid messages m */
        mk_ui[0] = 0;
        mpz_init_set_ui(gmk_inv[0], 1);
        m_ui = 1;

        for (k = 1; k < NCHOICEMAX; k++)
        {
            mk_ui[k] = m_ui;
            mpz_init(gmk_inv[k]);
            mpz_set_ui(m, m_ui);
            mpz_powm(gmk_inv[k], g_inv, m, ns1); 
            m_ui *= base;
        }

        for (j = 0; j < NVOTEMAX; j++)
        {
            unsigned int w_ui, x_ui;
            int cheated_k[NCHOICEMAX];
            int cheated = 0;

            /* encryption of vote */
            m_ui = mk_ui[votes[j]] * cheat[j];
            mpz_set_ui(m, m_ui);
            rj_ui = r_ui[1 + mpz_random_ui(randstate, phi_ui-1)];
            mpz_set_ui(r, rj_ui);
            damgard_jurik_encrypt(c, m, r, g, ns, ns1); 
            mpz_export_ui(&c_ui, c);

            /* generate zero knowledge proof challenge */
            mpz_urandomm(es, randstate, e_max);
            mpz_export_ui(&es_ui, es);

            for (k = 0; k < NCHOICEMAX; k++)
            {
                /* compute uk */
                mpz_mul(uk[k], c, gmk_inv[k]);
                mpz_mod(uk[k], uk[k], ns1);

                /* generate ek and uk^ek mod n^(s+1) */
                if (k != votes[j])
                {
                    mpz_urandomm(ek[k], randstate, e_max);
                    mpz_sub(es, es, ek[k]);
                    mpz_powm(znsk[k], uk[k], ek[k], ns1);
                }

                /* generate zk and zk^(n^s) */
                mpz_set_ui(zk[k], r_ui[mpz_random_ui(randstate, phi_ui)]);
                mpz_powm(znk[k], zk[k], ns, ns1);

                /* compute ak */
                if (k == votes[j])
                {
                    mpz_set(ak[k], znk[k]);
                }
                else
                {
                    mpz_invert(ak[k], znsk[k], ns1);
                    mpz_mul(ak[k], ak[k], znk[k]);
                    mpz_mod(ak[k], ak[k], ns1);
                }
            }

            /* complete zero-knowledge proof response for vote */
            k = votes[j];
            mpz_export_ui(&w_ui, zk[k]); /* save omega for later printing */
            mpz_mod(ek[k], es, e_max);
            mpz_powm(znsk[k], uk[k], ek[k], ns1);
            mpz_set_ui(r, rj_ui);
            mpz_powm(r, r, ek[k], n);
            mpz_mul(zk[k], zk[k], r);
            mpz_mod(zk[k], zk[k], n);
            mpz_powm(znk[k], zk[k], ns, ns1);
            
            /* verify zero-knowledge proof response */
            for (k = 0; k < NCHOICEMAX; k++)
            {
                mpz_mul(znsk[k], znsk[k], ak[k]);
                mpz_mod(znsk[k], znsk[k], ns1);
                cheated_k[k] = mpz_cmp(znk[k], znsk[k]);
                if (cheated_k[k])
                {
                    cheated = 1;
                }
            }            

            /* tallying of correct votes */
            if (!cheated)
            {
                mpz_mul(t, t, c);
                mpz_mod(t, t, ns1);
            }
            damgard_jurik_decrypt(m, t, d, mu, nj, s_ui);
            mpz_export_ui(&t_ui, t);
            mpz_export_ui(&tm_ui, m);

            printf("    <tr>\n");
            printf("      <td>V%u</td>\n", j+1);
            printf("      <td class=\"num\">%u</td>\n", m_ui);
            printf("      <td class=\"num\">%u</td>\n", rj_ui);
            printf("      <td class=\"numc\">%u</td>\n", c_ui);
            if (!hide_proof)
            {
                for (k = 0; k < NCHOICEMAX; k++)
                {
                    mpz_export_ui(&x_ui, uk[k]);
                    printf("      <td class=\"numu\">%u</td>\n", x_ui);
                }
                for (k = 0; k < NCHOICEMAX; k++)
                {
                    mpz_export_ui(&x_ui, ak[k]);
                    printf("      <td class=\"numa\">%u</td>\n", x_ui);
                }
                printf("      <td class=\"numg\">%u</td>\n", es_ui);
                for (k = 0; k < NCHOICEMAX; k++)
                {
                    mpz_export_ui(&x_ui, ek[k]);
                    printf("      <td class=\"nume\">%u</td>\n", x_ui);
                }
                printf("      <td class=\"num\">%u</td>\n", w_ui);
                for (k = 0; k < NCHOICEMAX; k++)
                {
                    mpz_export_ui(&x_ui, zk[k]);
                    printf("      <td class=\"numz\">%u</td>\n", x_ui);
                }
            }
            for (k = 0; k < NCHOICEMAX; k++)
            {
                mpz_export_ui(&x_ui, znk[k]);
                printf("      <td class=\"%s\">%u</td>\n",
                    (mpz_cmp_ui(ek[k], 0) == 0) ? "num" :
                    (cheated_k[k] ? "numb":"numg"), x_ui);
            }
            printf("      <td class=\"numc\">%u</td>\n", t_ui);
            printf("      <td class=\"numi\">%u</td>\n", tm_ui);
            for (k = 1; k < NCHOICEMAX; k++)
            {
                char *numclass;
                unsigned int tc = tm_ui;

                tm_ui /= base;
                tc -= tm_ui * base;
                numclass = (j == NVOTEMAX-1)? ((tc == t_choices[k])? "numg":"numb") : "numi";
                printf("      <td class=\"%s\">%u</td>\n", numclass, tc);
            }
            printf("    </tr>\n");
        }
        printf("  </table>\n");
        printf("  <pre>\n");

        mpz_clear(m);
        mpz_clear(r);
        mpz_clear(c);
        for (k = 0; k < NCHOICEMAX; k++)
        {
            mpz_clear(gmk_inv[k]);
            mpz_clear(uk[k]);
            mpz_clear(ak[k]);
            mpz_clear(ek[k]);
            mpz_clear(zk[k]);
            mpz_clear(znk[k]);
        }
    }

    /* Secret Sharing */
    {
        mpz_t delta, delta2_inv, n1ns, ct, e, y;
        mpz_t s[N], c[N];
        int l[N];
        unsigned int a_ui[T];
        unsigned int delta_ui, delta2_inv_ui, n1ns_ui, m_ui, r_ui, ct_ui;
        
        /* compute delta = N! */
        mpz_init_set_ui(delta, 1);
        for (i = 2; i <= N; i++)
        {
            mpz_mul_ui(delta, delta, i);
        }
        mpz_export_ui(&delta_ui, delta);
        printf("Secret Sharing:               N = %u, T = %u, &Delta; = N! = %u",
                N, T, delta_ui);

        if (N >= q_ui)
        {
            printf(", 1/&Delta mod n^s does not exist because q &le; N\n");
            printf("  </pre>\n");
            goto end;
        }
        if (N >= p_ui)
        {
            printf(", 1/&Delta mod n^s does not exist because p &le; N\n");
            printf("  </pre>\n");
            goto end;
        }

        /* compute the inverse of 4*delta^2 */
        mpz_init_set(delta2_inv, delta);
        mpz_mod(delta2_inv, delta2_inv, ns);
        mpz_mul(delta2_inv, delta2_inv, delta);
        mpz_mul_ui(delta2_inv, delta2_inv, 4*alpha_ui);
        mpz_mod(delta2_inv, delta2_inv, ns);
        if (mpz_invert(delta2_inv, delta2_inv, ns) == 0)
        {
            printf("inverse not defined\n");
            mpz_set_ui(delta2_inv, 1);
        }
        mpz_export_ui(&delta2_inv_ui, delta2_inv);
        printf(", 1/(4&alpha;&Delta;^2) mod n^s = %u\n\n", delta2_inv_ui);

        /* generate the random coefficients of the secret sharing polynomial */
        n1ns_ui = n1_ui * ns_ui;
        mpz_init_set_ui(n1ns, n1ns_ui);
        a_ui[0] = d_ui;
        for (j = 1; j < T; j++)
        {
            a_ui[j] = 1 + mpz_random_ui(randstate, n1ns_ui - 1);
        }
        printf("Secret Sharing Polynomial:    d(x) = a0 + a1*x + a2*x^2 mod n'*n^s"
                                                 " = %u + %u*x + %u*x^2 mod %u\n\n",
                a_ui[0], a_ui[1], a_ui[2], n1ns_ui);

        printf("Partial Decryption:           ci = t^[2&Delta;*d(i)] mod n^(s+1)\n");
        printf("  </pre>\n");

        printf("  <table>\n");
        printf("    <tr>\n");
        printf("      <td class=\"headl\">i</td>\n");
        printf("      <td class=\"headr\">&nbsp;d(i)</td>\n");
        printf("      <td class=\"headr\">&nbsp;ci</td>\n");
        printf("    </tr>\n");
        mpz_init(e);

        for (i = 0; i < N; i++)
        {
            unsigned int si_ui, ci_ui;

            mpz_init(s[i]);
            polynomial(s[i], i+1, a_ui, T, n1ns);    
            mpz_export_ui(&si_ui, s[i]);    
            mpz_set(e, delta);
            mpz_add(e, e, delta);
            mpz_mul(e, e, s[i]);
            mpz_init(c[i]);
            mpz_powm(c[i], t, e, ns1);
            mpz_export_ui(&ci_ui, c[i]); 
            printf("    <tr>\n");
            printf("      <td>A%d&nbsp;</td>\n", i+1);
            printf("      <td class=\"num\">%u</td>\n", si_ui);
            printf("      <td class=\"num\">%u</td>\n", ci_ui);
            printf("    </tr>\n");
        }
        printf("  </table>\n");
        printf("  <p/>\n");

        printf("  <pre>\n");
        printf("Lagrange Interpolation:       c' = &Pi;(ci^[2*&lambda;i])/(4&alpha;&Delta;^2) mod n^(s+1)\n\n");
        printf("Iterative Mapping:            tm = I(c') * &mu; mod n^s\n");
        printf("  </pre>\n");

        mpz_init(y);
        printf("  <table>\n");
        printf("    <tr>\n");
        printf("      <td class=\"headl\">Authorities</td>\n");
        for (i = 0; i < N; i++)
        {        
            printf("      <td class=\"headr\">&lambda;%u</td>\n", i+1);
        }
        printf("      <td class=\"headr\">c'</td>\n");
        printf("      <td class=\"headr\">tm</td>\n");
        printf("    </tr>\n");
        printf("    <tr>\n");
        printf("      <td>A1 & A2 & A3</td>\n");
        lagrange(l, N, 0x07, delta_ui);
        exponential(y, c, N, l, ns1);
        normalize(y, delta2_inv, nj, s_ui);
        printf("    </tr>\n");
        printf("    <tr>\n");
        printf("      <td>A3 & A4 & A5</td>\n");
        lagrange(l, N, 0x1c, delta_ui);
        exponential(y, c, N, l, ns1);
        normalize(y, delta2_inv, nj, s_ui);
        printf("    </tr>\n");
        printf("    <tr>\n");
        printf("      <td>A1 & A2 & A4 & A5</td>\n");
        lagrange(l, N, 0x1b, delta_ui);
        exponential(y, c, N, l, ns1);
        normalize(y, delta2_inv, nj, s_ui);
        printf("    </tr>\n");
        printf("    <tr>\n");
        printf("      <td>A1 & A2 & A3 & A4 & A5</td>\n");
        lagrange(l, N, 0x1f, delta_ui);
        exponential(y, c, N, l, ns1);
        normalize(y, delta2_inv, nj, s_ui);
        printf("    </tr>\n");
        printf("  </table>\n");
        printf("\n");

        mpz_clear(e);
        mpz_clear(n1ns);
        mpz_clear(delta);
        mpz_clear(delta2_inv);
        for (i = 0; i < N; i++)
        {
            mpz_clear(s[i]);
            mpz_clear(c[i]);
        }
    }

    /* Cleaning up */
    mpz_clear(t);
    mpz_clear(p);
    mpz_clear(q);
    mpz_clear(n);
    mpz_clear(n1);
    mpz_clear(phi);
    mpz_clear(lambda);
    mpz_clear(g);
    mpz_clear(g_inv);
    mpz_clear(mu);
    mpz_clear(ns);
    mpz_clear(ns1);
    for (j = 0; j <= s_ui; j++)
    {
        mpz_clear(nj[j]);
    }
    gmp_randclear(randstate);

end:
    printf("  </p>\n");
    printf("  The <a href=\"/msevote/vote-cgi/damgardjurik.c\">source code</a> of the simulator is available under a\n");
    printf("  <a href=\"http://www.fsf.org/licensing/licenses/gpl.txt\" target=\"popup\">GPLv2 license</a>.\n");
    printf("  </p>\n");
    printf("  <hr/>\n");
    printf("  &copy; 2008-2010 by Andreas Steffen, \n");
    printf("  <a href=\"http://www.hsr.ch/MRU-Software-and-Systems.1236.0.html\" target=\"popup\">HSR Hochschule f&uuml;r Technik Rapperswil</a>\n");
    printf("</body>\n");
    printf("</html>\n");
    exit(0);
}
