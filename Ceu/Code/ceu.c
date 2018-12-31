int _CEU_INPUT;

#include <string.h>     /* memset */

typedef u8 tceu_nevt;   /* TODO */
typedef u8 tceu_nstk;   /* TODO */
typedef <<< CEU_TCEU_NTRL >>> tceu_ntrl;

#define CEU_TRAILS_N <<< CEU_TRAILS_N >>>

#define CEU_API static
CEU_API void ceu_start (int argc, char* argv[]);
CEU_API void ceu_stop  (void);
CEU_API void ceu_input (tceu_nevt evt);
CEU_API int  ceu_loop  (int argc, char* argv[]);

typedef struct tceu_bcast {
    tceu_nevt evt;
    tceu_ntrl trail_0;
    tceu_ntrl trail_n;
} tceu_bcast;

typedef struct tceu_stk {
    tceu_nstk  level;
    bool       is_alive;
    tceu_ntrl  trail;
    struct tceu_stk* prv;
} tceu_stk;

static void CEU_LABEL_ROOT (tceu_stk* _ceu_stk);

typedef struct tceu_trl {
    tceu_nevt evt;
    tceu_nstk level;
    typeof(CEU_LABEL_ROOT)* lbl;
} tceu_trl;

/* CEU_NATIVE_PRE */
//<|< CEU_NATIVE_PRE >|>

/* EVENTS_ENUM */

enum {
    /* non-emitable */
    CEU_INPUT__NONE = 0,
    CEU_INPUT__STACKED,
    //CEU_INPUT__FINALIZE,

    /* emitable */
    //CEU_INPUT__CLEAR,
CEU_INPUT__PRIM,
    //CEU_INPUT__ASYNC,
    //CEU_INPUT__WCLOCK,

//CEU_INPUT__MIN,
    /* CEU_INPS */
<<< CEU_INPS >>>
//CEU_INPUT__MAX,

CEU_EVENT__MIN,
<<< CEU_EVTS >>>
};

enum {
    CEU_OUTPUT__NONE = 0,
    //<|< CEU_EXTS_ENUM_OUTPUT >|>
};

/* CEU_MAIN */
//<|< CEU_MAIN_C >|>

//#pragma GCC diagnostic ignored "-Wmaybe-uninitialized"

/* EVENTS_DEFINES */
//<|< CEU_EXTS_DEFINES_INPUT_OUTPUT >|>

/*****************************************************************************/

/* CEU_TYPES */
typedef struct {} tceu_unit;
static tceu_unit CEU_UNIT;
<<< CEU_TYPES >>>

/*****************************************************************************/

typedef struct tceu_mem_ROOT {
    tceu_trl trails[CEU_TRAILS_N];
    /* CEU_VARS */
<<< CEU_VARS >>>
} tceu_mem_ROOT;

typedef struct tceu_app {
    tceu_mem_ROOT root;
} tceu_app;

CEU_API tceu_app CEU_APP;

/*****************************************************************************/

static void ceu_stack_clear (tceu_stk* stk, tceu_ntrl t0, tceu_ntrl n) {
    if (stk == NULL) {
        return;
    }
    if (stk->trail>=t0 && stk->trail<t0+n) {
        stk->is_alive = 0;
    }
    ceu_stack_clear(stk->prv, t0, n);
}

/*****************************************************************************/

static void ceu_bcast_mark (tceu_bcast* cst, tceu_stk* cur)
{
    tceu_ntrl i = cst->trail_0;
    tceu_ntrl n = i + cst->trail_n;
    for (; i<n; i++) {
        tceu_trl* trl = &CEU_APP.root.trails[i];
        if (trl->evt == cst->evt) {
            trl->evt   = CEU_INPUT__STACKED;
            trl->level = cur->level;
        }
    }
}

static void ceu_bcast_exec (tceu_bcast* cst, tceu_stk* cur)
{
    tceu_ntrl i = cst->trail_0;
    tceu_ntrl n = i + cst->trail_n;
    for (; i<n; i++) {
        tceu_trl* trl = &CEU_APP.root.trails[i];
        if (trl->evt==CEU_INPUT__STACKED && trl->level==cur->level) {
            trl->evt = CEU_INPUT__NONE;
            trl->lbl(cur);
        }
    }
}

static void ceu_bcast (tceu_bcast* cst, tceu_stk* cur)
{
    ceu_bcast_mark(cst, cur);
    ceu_bcast_exec(cst, cur);
}

CEU_API void ceu_input (tceu_nevt evt)
{
    tceu_bcast cst = {evt, 0, CEU_TRAILS_N};
    tceu_stk cur = { 0, 1, 0, NULL };
    ceu_bcast(&cst, &cur);
}

CEU_API void ceu_start (int argc, char* argv[])
{
    memset(&CEU_APP.root.trails, 0, CEU_TRAILS_N*sizeof(tceu_trl));

    ceu_callback_start();

    tceu_stk stk = { 0, 1, 0, NULL };
    CEU_LABEL_ROOT(&stk);

#ifdef CEU_HISTORY
<<< CEU_HISTORY >>>
#endif
}

CEU_API void ceu_stop (void)
{
    ceu_callback_stop();
}

/*****************************************************************************/

CEU_API int ceu_loop (int argc, char* argv[])
{
    ceu_start(argc, argv);

    while (1)
    {
        ceu_callback_step();
#ifdef CEU_FEATURES_ASYNC
        ceu_input(CEU_INPUT__ASYNC);
#endif
    }

    return 0;
}

/*****************************************************************************/

// PRELUDE

static int negate (int v) {
    return -v;
}

static int Add__tceu__int__int (tceu__int__int* v) {
    return v->_1 + v->_2;
}

static int Mul__tceu__int__int (tceu__int__int* v) {
    return v->_1 * v->_2;
}

static int equal (tceu__int__int* v) {
    return v->_1 == v->_2;
}

static int Eq__tceu__int__int (tceu__int__int* v) {
    return v->_1 == v->_2;
}

static int Eq__tceu__tceu_unit__tceu_unit (tceu__tceu_unit__tceu_unit* v) {
    return 1;
}

/*****************************************************************************/

//<|< CEU_NATIVE_POS >|>

//<|< CEU_CALLBACKS_OUTPUTS >|>

/* CEU_LABELS */

<<< CEU_LABELS >>>
