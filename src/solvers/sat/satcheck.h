/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_SAT_SATCHECK_H
#define CPROVER_SOLVERS_SAT_SATCHECK_H

// This sets a define for the SAT solver
// based on set flags that come via the compiler
// command line.

// #define SATCHECK_ZCHAFF
// #define SATCHECK_MINISAT1
// #define SATCHECK_MINISAT2
// #define SATCHECK_GLUCOSE
// #define SATCHECK_BOOLEFORCE
// #define SATCHECK_PICOSAT
// #define SATCHECK_LINGELING
// #define SATCHECK_CADICAL

#if defined(HAVE_IPASIR) && !defined(SATCHECK_IPASIR)
#define SATCHECK_IPASIR
#endif

#if defined(HAVE_ZCHAFF) && !defined(SATCHECK_ZCHAFF)
#define SATCHECK_ZCHAFF
#endif

#if defined(HAVE_MINISAT1) && !defined(SATCHECK_MINISAT1)
#define SATCHECK_MINISAT1
#endif

#if defined(HAVE_MINISAT2) && !defined(SATCHECK_MINISAT2)
#define SATCHECK_MINISAT2
#endif

#if defined(HAVE_GLUCOSE) && !defined(SATCHECK_GLUCOSE)
#define SATCHECK_GLUCOSE
#endif

#if defined(HAVE_BOOLEFORCE) && !defined(SATCHECK_BOOLEFORCE)
#define SATCHECK_BOOLEFORCE
#endif

#if defined(HAVE_PICOSAT) && !defined(SATCHECK_PICOSAT)
#define SATCHECK_PICOSAT
#endif

#if defined(HAVE_LINGELING) && !defined(SATCHECK_LINGELING)
#define SATCHECK_LINGELING
#endif

#if defined(HAVE_CADICAL) && !defined(SATCHECK_CADICAL)
#define SATCHECK_CADICAL
#endif

#if defined SATCHECK_ZCHAFF
#  include "satcheck_zchaff.h"
#endif

#if defined SATCHECK_BOOLEFORCE
#  include "satcheck_booleforce.h"
#endif

#if defined SATCHECK_MINISAT1
#  include "satcheck_minisat.h"
#endif

#if defined SATCHECK_MINISAT2
#  include "satcheck_minisat2.h"
#endif

#if defined SATCHECK_IPASIR
#  include "satcheck_ipasir.h"
#endif

#if defined SATCHECK_PICOSAT
#  include "satcheck_picosat.h"
#endif

#if defined SATCHECK_LINGELING
#  include "satcheck_lingeling.h"
#endif

#if defined SATCHECK_GLUCOSE
#  include "satcheck_glucose.h"
#endif

#if defined SATCHECK_CADICAL
#  include "satcheck_cadical.h"
#endif

#if defined SATCHECK_ZCHAFF

typedef satcheck_zchafft satcheckt;
typedef satcheck_zchafft satcheck_no_simplifiert;

#elif defined SATCHECK_BOOLEFORCE

typedef satcheck_booleforcet satcheckt;
typedef satcheck_booleforcet satcheck_no_simplifiert;

#elif defined SATCHECK_MINISAT1

typedef satcheck_minisat1t satcheckt;
typedef satcheck_minisat1t satcheck_no_simplifiert;

#elif defined SATCHECK_MINISAT2

typedef satcheck_minisat_simplifiert satcheckt;
typedef satcheck_minisat_no_simplifiert satcheck_no_simplifiert;

#elif defined SATCHECK_IPASIR

typedef satcheck_ipasirt satcheckt;
typedef satcheck_ipasirt satcheck_no_simplifiert;

#elif defined SATCHECK_PICOSAT

typedef satcheck_picosatt satcheckt;
typedef satcheck_picosatt satcheck_no_simplifiert;

#elif defined SATCHECK_LINGELING

typedef satcheck_lingelingt satcheckt;
typedef satcheck_lingelingt satcheck_no_simplifiert;

#elif defined SATCHECK_GLUCOSE

typedef satcheck_glucose_simplifiert satcheckt;
typedef satcheck_glucose_no_simplifiert satcheck_no_simplifiert;

#elif defined SATCHECK_CADICAL

typedef satcheck_cadical_no_preprocessingt satcheckt;
typedef satcheck_cadical_no_preprocessingt satcheck_no_simplifiert;

#endif

#endif // CPROVER_SOLVERS_SAT_SATCHECK_H
