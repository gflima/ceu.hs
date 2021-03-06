#define ceu_callback_output_LED(v) digitalWrite(13, v)
#define ceu_callback_output_PRINT(v) printf("%d\n", v)

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
//typedef <|< CEU_TCEU_NLBL >|> tceu_nlbl;
typedef u8 tceu_ntrl;
typedef u8 tceu_nlbl;

#define CEU_TRAILS_N 10
//#define CEU_TRAILS_N <|< CEU_TRAILS_N >|>
#ifndef CEU_STACK_N
#define CEU_STACK_N 500
#endif

#define CEU_API
CEU_API void ceu_start (int argc, char* argv[]);
CEU_API void ceu_stop  (void);
CEU_API void ceu_input (tceu_nevt id, void* params);
CEU_API int  ceu_loop  (int argc, char* argv[]);

struct tceu_code_mem;

typedef struct tceu_evt {
    tceu_nevt id;
    union {
        void* mem;                   /* CEU_INPUT__PROPAGATE_CODE, CEU_EVENT__MIN */
#ifdef CEU_FEATURES_POOL
        struct tceu_pool_pak* pak;   /* CEU_INPUT__PROPAGATE_POOL */
#endif
    };
} tceu_evt;

typedef struct tceu_range {
    struct tceu_code_mem* mem;
    tceu_ntrl             trl0;
    tceu_ntrl             trlF;
} tceu_range;

typedef struct tceu_stk {
    tceu_evt   evt;
    tceu_range range;
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
                tceu_nlbl lbl;
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

typedef struct tceu_code_mem {
    struct tceu_code_mem* up_mem;
    u8          depth;
    bool has_term;
    tceu_ntrl   trails_n;
    tceu_trl    _trails[0];
} tceu_code_mem;

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
    //<|< CEU_EXTS_ENUM_INPUT >|>
//CEU_INPUT__MAX,

CEU_EVENT__MIN,
    //<|< CEU_EVTS_ENUM >|>
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

enum {
    CEU_LABEL_NONE = 0,
    CEU_LABEL_ROOT = 1,
    CEU_LABEL_4_Trap
};

/*****************************************************************************/

//<|< REMOVE >|>
typedef struct tceu_code_mem_ROOT {
    tceu_code_mem _mem;                                                         
    tceu_trl      _trails[7];                                                   
    byte          _params[0];                                                   
    int           _ret;
} tceu_code_mem_ROOT;

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

    tceu_code_mem_ROOT root;
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

void ceu_stack_clear (tceu_stk* cur, tceu_code_mem* mem) {
    if (cur == NULL) {
        return;
    }
    if (cur->range.mem == mem) {
        cur->is_alive = 0;
    }
    ceu_stack_clear(cur->prv, mem);
}

/*****************************************************************************/

static int ceu_lbl (tceu_nstk _ceu_level, tceu_stk* _ceu_cur, tceu_stk* _ceu_nxt, tceu_code_mem* _ceu_mem, tceu_nlbl _ceu_lbl, tceu_ntrl* _ceu_trlK);

//<|< CEU_NATIVE_POS >|>

//<|< CEU_CALLBACKS_OUTPUTS >|>

/*****************************************************************************/

#define CEU_GOTO(lbl) {_ceu_lbl=lbl; goto _CEU_LBL_;}

static int ceu_lbl (tceu_nstk _ceu_level, tceu_stk* _ceu_cur, tceu_stk* _ceu_nxt, tceu_code_mem* _ceu_mem, tceu_nlbl _ceu_lbl, tceu_ntrl* _ceu_trlK)
{
#ifdef CEU_STACK_MAX
    {
        static void* base = NULL;
        if (base == NULL) {
            base = &_ceu_level;
        } else {
            ceu_assert((usize)(((byte*)base)-CEU_STACK_MAX) <= (usize)(&_ceu_level), "stack overflow");
        }
    }
#endif

_CEU_LBL_:
    //printf("-=-=- %d -=-=-\n", _ceu_lbl);
    switch (_ceu_lbl) {
        case CEU_LABEL_NONE:
            break;
        case CEU_LABEL_ROOT:;
        #line 1"" // trap
  {
#line 3"" // emit
    ceu_callback_output_PRINT(10);
#line 5"" // await
    return 0;
  }
case CEU_LABEL_4_Trap:;
#line 1"" // await
  return 0;

    }
    //ceu_assert(0, "unreachable code");
    return 0;
}

static void ceu_bcast_mark (tceu_nstk level, tceu_stk* cur)
{
    tceu_ntrl trlK = cur->range.trl0;

    for (; trlK<=cur->range.trlF; trlK++)
    {
        tceu_trl* trl = &cur->range.mem->_trails[trlK];

        //printf(">|> mark [%d/%p] evt=%d\n", trlK, trl, trl->evt.id);
        switch (trl->evt.id)
        {
#ifdef CEU_FEATURES_PAUSE
            case CEU_INPUT__PAUSE_BLOCK: {
                u8 was_paused = trl->pse_paused;
                if ( (cur->evt.id == trl->pse_evt.id)                               &&
                     (cur->evt.id<CEU_EVENT__MIN || cur->evt.mem==trl->pse_evt.mem) &&
                     (*((u8*)cur->params) != trl->pse_paused) )
                {
                    trl->pse_paused = *((u8*)cur->params);

                    tceu_evt evt_;
                    tceu_range range_ = { cur->range.mem,
                                          (tceu_ntrl)(trlK+1), (tceu_ntrl)(trlK+trl->pse_skip) };
                    if (trl->pse_paused) {
                        evt_.id = CEU_INPUT__PAUSE;
                    } else {
                        CEU_APP.wclk_min_set = 0;   /* maybe resuming a timer, let it be the minimum set */
                        evt_.id = CEU_INPUT__RESUME;
                    }
                    tceu_stk cur_ = { evt_, range_, NULL, 0 };
                    ceu_bcast_mark(level, &cur_);
                }
                /* don't skip if pausing now */
                if (was_paused && cur->evt.id!=CEU_INPUT__CLEAR) {
                                  /* also don't skip on CLEAR (going reverse) */
                    trlK += trl->pse_skip;
                }
                break;
            }
#endif

            default: {
                if (cur->evt.id == CEU_INPUT__CLEAR) {
                    if (trl->evt.id == CEU_INPUT__FINALIZE) {
                        goto _CEU_AWAKE_YES_;
                    }
                } else if (trl->evt.id == cur->evt.id) {
#ifdef CEU_FEATURES_PAUSE
                    if (cur->evt.id==CEU_INPUT__PAUSE || cur->evt.id==CEU_INPUT__RESUME) {
                        goto _CEU_AWAKE_YES_;
                    }
#endif
                    if (trl->evt.id>CEU_EVENT__MIN) {
                        if (trl->evt.mem == cur->evt.mem) {
                            goto _CEU_AWAKE_YES_;   /* internal event matches "mem" */
                        }
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
    }
}

static int ceu_bcast_exec (tceu_nstk level, tceu_stk* cur, tceu_stk* nxt)
{
    /* CLEAR: inverse execution order */
    tceu_ntrl trl0 = cur->range.trl0;
    tceu_ntrl trlF = cur->range.trlF;
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
        tceu_trl* trl = &cur->range.mem->_trails[trlK];

        //printf(">|> exec [%d/%p] evt=%d\n", trlK, trl, trl->evt.id);
        switch (trl->evt.id)
        {
            case CEU_INPUT__STACKED: {
                if (trl->evt.id==CEU_INPUT__STACKED && trl->level==level) {
                    trl->evt.id = CEU_INPUT__NONE;
//printf("STK = %d\n", trlK);
                    if (ceu_lbl(level, cur, nxt, cur->range.mem, trl->lbl, &trlK)) {
                        return 1;
                    }
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
        tceu_evt   evt   = {CEU_INPUT__WCLOCK, {NULL}};
        tceu_range range = {(tceu_code_mem*)&CEU_APP.root, 0, CEU_TRAILS_N-1};
        tceu_stk   cur   = { evt, range, &dt, 0, 1, NULL };
        ceu_bcast(1, &cur);
    }
    if (id != CEU_INPUT__NONE) {
        tceu_evt   evt   = {id, {NULL}};
        tceu_range range = {(tceu_code_mem*)&CEU_APP.root, 0, CEU_TRAILS_N-1};
        tceu_stk   cur   = { evt, range, params, 0, 1, NULL };
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

    CEU_APP.root._mem.up_mem   = NULL;
    CEU_APP.root._mem.depth    = 0;

    CEU_APP.stack_i = 0;

    CEU_APP.root._mem.trails_n = CEU_TRAILS_N;
    memset(&CEU_APP.root._trails, 0, CEU_TRAILS_N*sizeof(tceu_trl));
    CEU_APP.root._trails[0].evt.id = CEU_INPUT__STACKED;
    CEU_APP.root._trails[0].level  = 1;
    CEU_APP.root._trails[0].lbl    = CEU_LABEL_ROOT;

    ceu_callback_start(CEU_TRACE_null);

    tceu_evt   evt   = {CEU_INPUT__NONE, {NULL}};
    tceu_range range = {(tceu_code_mem*)&CEU_APP.root, 0, CEU_TRAILS_N-1};
    tceu_stk   cur   = { evt, range, NULL, 0, 1, NULL };
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
