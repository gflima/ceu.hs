#define ceu_callback_output_LED(v) digitalWrite(13, v)
#define ceu_callback_output_PRINT(v) printf("%d\n", v)
int _CEU_INPUT;

#include <stddef.h>     /* offsetof */
#include <stdlib.h>     /* NULL */
#include <string.h>     /* memset, strlen */
#ifdef CEU_TESTS
#include <stdio.h>
#endif

#ifdef CEU_FEATURES_LUA
#include <lua5.3/lua.h>
#include <lua5.3/lauxlib.h>
#include <lua5.3/lualib.h>
#endif

#define S8_MIN   -127
#define S8_MAX    127
#define U8_MAX    255

#define S16_MIN  -32767
#define S16_MAX   32767
#define U16_MAX   65535

#define S32_MIN  -2147483647
#define S32_MAX   2147483647
#define U32_MAX   4294967295

#define S64_MIN  -9223372036854775807
#define S64_MAX   9223372036854775807
#define U64_MAX   18446744073709551615

typedef u16 tceu_nevt;   /* TODO */
typedef u8  tceu_nstk;   /* TODO */
//typedef <|< CEU_TCEU_NTRL >|> tceu_ntrl;
typedef u8 tceu_ntrl;

#define CEU_TRAILS_N <<< CEU_TRAILS_N >>>
#ifndef CEU_STACK_N
#define CEU_STACK_N 500
#endif

#define CEU_API
CEU_API void ceu_start (int argc, char* argv[]);
CEU_API void ceu_stop  (void);
CEU_API void ceu_input (tceu_nevt id, void* params);
CEU_API int  ceu_loop  (int argc, char* argv[]);

struct tceu_trl;
int CEU_LABEL_ROOT (struct tceu_trl* _ceu_trl);

typedef struct tceu_evt {
    tceu_nevt id;
    tceu_ntrl trl0;
    tceu_ntrl trlF;
} tceu_evt;

typedef struct tceu_stk {
    tceu_evt   evt;
    void*      params;
    usize      params_n;
    bool       is_alive;
    struct tceu_stk* prv;
} tceu_stk;

typedef struct tceu_trl {
    struct {
        tceu_evt evt;
        union {
            struct {
                typeof(CEU_LABEL_ROOT)* lbl;
                tceu_nstk level;       /* CEU_INPUT__STACKED */
            };
#ifdef CEU_FEATURES_PAUSE
            struct {
                tceu_evt  pse_evt;
                tceu_ntrl pse_skip;
                u8        pse_paused;
            };
#endif
        };
    };
} tceu_trl;

/* CEU_NATIVE_PRE */
//<|< CEU_NATIVE_PRE >|>

/* EVENTS_ENUM */

enum {
    /* non-emitable */
    CEU_INPUT__NONE = 0,
    CEU_INPUT__STACKED,
    CEU_INPUT__FINALIZE,

    /* emitable */
    CEU_INPUT__CLEAR,
CEU_INPUT__PRIM,
    CEU_INPUT__ASYNC,
    CEU_INPUT__WCLOCK,

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

//<|< CEU_EXTS_TYPES >|>
//<|< CEU_EVTS_TYPES >|>
//<|< CEU_CODES_MEMS >|>

/*****************************************************************************/

typedef struct tceu_mem_ROOT {
    tceu_trl trails[CEU_TRAILS_N];
    /* CEU_VARS */
<<< CEU_VARS >>>
} tceu_mem_ROOT;

typedef struct tceu_app {
    /* ASYNC */
#ifdef CEU_FEATURES_ASYNC
    bool async_pending;
#endif

    /* WCLOCK */
    s32 wclk_late;
    s32 wclk_min_set;
    s32 wclk_min_cmp;

    byte  stack[CEU_STACK_N];
    usize stack_i;

    tceu_mem_ROOT root;
} tceu_app;

CEU_API static tceu_app CEU_APP;

/*****************************************************************************/

#define CEU_WCLOCK_INACTIVE INT32_MAX
#define ceu_wclock(a,b,c,d) ceu_wclock_(a,b,c)

static int ceu_wclock_ (s32 dt, s32* set, s32* sub)
{
    s32 t;          /* expiring time of track to calculate */
    int ret = 0;    /* if track expired (only for "sub") */

    /* SET */
    if (set != NULL) {
        t = dt - CEU_APP.wclk_late;
        *set = t;

    /* SUB */
    } else {
        t = *sub;
        if ((t > CEU_APP.wclk_min_cmp) || (t > dt)) {
            *sub -= dt;    /* don't expire yet */
            t = *sub;
        } else {
            ret = 1;    /* single "true" return */
        }
    }

    /* didn't awake, but can be the smallest wclk */
    if ( (!ret) && (CEU_APP.wclk_min_set > t) ) {
        CEU_APP.wclk_min_set = t;
        ceu_callback_wclock_min(t, CEU_TRACE_null);
    }

    return ret;
}

static void ceu_params_cpy (tceu_stk* stk, void* params, usize params_n) {
    ceu_assert_sys(CEU_APP.stack_i+params_n < CEU_STACK_N, "stack overflow");
    memcpy(&CEU_APP.stack[CEU_APP.stack_i], params, params_n);
    stk->params   = &CEU_APP.stack[CEU_APP.stack_i];
    stk->params_n = params_n;
    CEU_APP.stack_i += stk->params_n;
}

/*****************************************************************************/

#if 0
void ceu_stack_clear (tceu_stk* cur, tceu_mem* mem) {
    if (cur == NULL) {
        return;
    }
    if (cur->evt.mem == mem) {
        cur->is_alive = 0;
    }
    ceu_stack_clear(cur->prv, mem);
}
#endif

/*****************************************************************************/

//<|< CEU_NATIVE_POS >|>

//<|< CEU_CALLBACKS_OUTPUTS >|>

#define CEU_LABEL__CALL(lbl,trl)    \
    {                               \
        int ret = (lbl)(trl);       \
        if (ret != 0) {             \
            return ret;             \
        }                           \
    }

/* CEU_LABELS */

<<< CEU_LABELS >>>

/*****************************************************************************/

static void ceu_bcast_mark (tceu_nstk level, tceu_stk* cur)
{
    tceu_ntrl trlK = cur->evt.trl0;

    for (; trlK<=cur->evt.trlF; trlK++)
    {
        tceu_trl* trl = &CEU_APP.root.trails[trlK];

        //printf(">|> mark [%d/%p] evt=%d\n", trlK, trl, trl->evt.id);
        if (cur->evt.id == CEU_INPUT__CLEAR) {
            if (trl->evt.id == CEU_INPUT__FINALIZE) {
                goto _CEU_AWAKE_YES_;
            }
        } else if (trl->evt.id == cur->evt.id) {
            if (trl->evt.id>CEU_EVENT__MIN) {
                //if (trl->evt.mem == cur->evt.mem) {
                    goto _CEU_AWAKE_YES_;   /* internal event matches "mem" */
                //}
            } else {
                if (cur->evt.id != CEU_INPUT__NONE) {
                    goto _CEU_AWAKE_YES_;       /* external event matches */
                }
            }
        }
        continue;

_CEU_AWAKE_YES_:
        trl->evt.id = CEU_INPUT__STACKED;
        trl->level  = level;
    }
}

static int ceu_bcast_exec (tceu_nstk level, tceu_stk* cur, tceu_stk* nxt)
{
    /* CLEAR: inverse execution order */
    tceu_ntrl trl0 = cur->evt.trl0;
    tceu_ntrl trlF = cur->evt.trlF;
    if (trl0 > trlF) {
        return 0;
    }
    if (cur->evt.id == CEU_INPUT__CLEAR) {
        tceu_ntrl tmp = trl0;
        trl0 = trlF;
        trlF = tmp;
    }

    tceu_ntrl trlK = trl0;

    //printf(">|> exec %d -> %d\n", trl0, trlF);
    while (1)
    {
        tceu_trl* trl = &CEU_APP.root.trails[trlK];

        //printf(">|> exec [%d/%p] evt=%d\n", trlK, trl, trl->evt.id);
        switch (trl->evt.id)
        {
            case CEU_INPUT__STACKED: {
                if (trl->evt.id==CEU_INPUT__STACKED && trl->level==level) {
                    trl->evt.id = CEU_INPUT__NONE;
//printf("STK = %d\n", trlK);
                    CEU_LABEL__CALL(trl->lbl, trl)
                    //if (ceu_lbl(level, cur, nxt, cur->evt.mem, trl->lbl, &trlK)) {
                        //return 1;
                    //}
//printf("<< trlK = %d\n", trlK);
                }
                break;
            }
        }

        if (cur->evt.id == CEU_INPUT__CLEAR) {
            trl->evt.id = CEU_INPUT__NONE;
        }

        if (trlK == trlF) {
            break;
        } else if (cur->evt.id == CEU_INPUT__CLEAR) {
            trlK--; trl--;
        } else {
            trlK++; trl++;
        }
    }
    return 0;
}

void ceu_bcast (tceu_nstk level, tceu_stk* cur)
{
    if (cur->evt.id>CEU_INPUT__PRIM && cur->evt.id<CEU_EVENT__MIN) {
        switch (cur->evt.id) {
            case CEU_INPUT__WCLOCK:
                CEU_APP.wclk_min_cmp = CEU_APP.wclk_min_set;    /* swap "cmp" to last "set" */
                CEU_APP.wclk_min_set = CEU_WCLOCK_INACTIVE;     /* new "set" resets to inactive */
                ceu_callback_wclock_min(CEU_WCLOCK_INACTIVE, CEU_TRACE_null);
                if (CEU_APP.wclk_min_cmp <= *((s32*)cur->params)) {
                    CEU_APP.wclk_late = *((s32*)cur->params) - CEU_APP.wclk_min_cmp;
                }
                break;
#ifdef CEU_FEATURES_ASYNC
            case CEU_INPUT__ASYNC:
                CEU_APP.async_pending = 0;
                break;
#endif
        }
        if (cur->evt.id != CEU_INPUT__WCLOCK) {
            CEU_APP.wclk_late = 0;
        }
    }

    //printf(">|> BCAST[%d]: %d\n", cur->evt.id, level);
    ceu_bcast_mark(level, cur);
    while (1) {
        tceu_stk nxt;
        nxt.is_alive = 1;
        nxt.prv = cur;
        int ret = ceu_bcast_exec(level, cur, &nxt);
        if (ret) {
            ceu_assert_sys(level < 255, "too many stack levels");
            ceu_bcast(level+1, &nxt);
            if (!cur->is_alive) {
                break;
            }
        } else {
            break;
        }
    }

    CEU_APP.stack_i -= cur->params_n;
    //printf("<< BCAST: %d\n", level);
}

CEU_API void ceu_input (tceu_nevt id, void* params)
{
    s32 dt = ceu_callback_wclock_dt(CEU_TRACE_null);
    if (dt != CEU_WCLOCK_INACTIVE) {
        tceu_evt evt = {CEU_INPUT__WCLOCK, 0, CEU_TRAILS_N-1};
        tceu_stk cur = { evt, &dt, 0, 1, NULL };
        ceu_bcast(1, &cur);
    }
    if (id != CEU_INPUT__NONE) {
        tceu_evt evt = {id, 0, CEU_TRAILS_N-1};
        tceu_stk cur = { evt, params, 0, 1, NULL };
        ceu_bcast(1, &cur);
    }
}

CEU_API void ceu_start (int argc, char* argv[]) {
#ifdef CEU_FEATURES_ASYNC
    CEU_APP.async_pending = 0;
#endif

    CEU_APP.wclk_late = 0;
    CEU_APP.wclk_min_set = CEU_WCLOCK_INACTIVE;
    CEU_APP.wclk_min_cmp = CEU_WCLOCK_INACTIVE;

    CEU_APP.stack_i = 0;

    //CEU_APP.root.trails_n = CEU_TRAILS_N;
    memset(&CEU_APP.root.trails, 0, CEU_TRAILS_N*sizeof(tceu_trl));
    CEU_APP.root.trails[0].evt.id = CEU_INPUT__STACKED;
    CEU_APP.root.trails[0].level  = 1;
    CEU_APP.root.trails[0].lbl    = CEU_LABEL_ROOT;

    ceu_callback_start(CEU_TRACE_null);

    tceu_evt evt = {CEU_INPUT__NONE, 0, CEU_TRAILS_N-1};
    tceu_stk cur = { evt, NULL, 0, 1, NULL };
    ceu_bcast(1, &cur);
}
CEU_API void ceu_stop (void) {
    ceu_callback_stop(CEU_TRACE_null);
}

/*****************************************************************************/

CEU_API int ceu_loop (int argc, char* argv[])
{
    ceu_start(argc, argv);

    while (1)
    {
        ceu_callback_step(CEU_TRACE_null);
#ifdef CEU_FEATURES_ASYNC
        ceu_input(CEU_INPUT__ASYNC, NULL);
#endif
    }

    return 0;
}
