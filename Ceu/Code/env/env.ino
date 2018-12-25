#if 0
    #define ceu_assert_ex(a,b,c) if (!(a)) { ceu_callback_abort((10+__COUNTER__),c); }
    #define ceu_assert_sys(a,b)  if (!(a)) { ceu_callback_abort((10+__COUNTER__),CEU_TRACE_null); }
    #define ceu_arduino_assert(cnd,err) if (!(cnd)) { ceu_arduino_callback_abort(err); }
#else
    #define ceu_assert_ex(a,b,c)        // no assert
    #define ceu_assert_sys(a,b)         // no assert
    #define ceu_arduino_assert(cnd,err) // no assert
#endif

///////////////////////////////////////////////////////////////////////////////
// DO NOT EDIT
///////////////////////////////////////////////////////////////////////////////

#include "types.h"

#define ceu_callback_stop(trace)
#define ceu_callback_step(trace)
#define ceu_callback_async_pending(trace)
#define ceu_callback_wclock_dt(trace) //ceu_arduino_callback_wclock_dt()
s32 ceu_arduino_callback_wclock_dt (void);
#define ceu_callback_wclock_min(dt,trace) //ceu_arduino_callback_wclock_min(dt)
void ceu_arduino_callback_wclock_min (s32);
#define ceu_callback_abort(err,trace) ceu_arduino_callback_abort(err)
void ceu_arduino_callback_abort (int err);
#define ceu_callback_start(trace)
#define ceu_callback_isr_enable(on,trace) //ceu_arduino_callback_isr_enable(on)
void ceu_arduino_callback_isr_enable (int on);
#define ceu_callback_isr_emit(n,evt,trace) //ceu_arduino_callback_isr_emit(n,evt)
void ceu_arduino_callback_isr_emit (int n, void* evt);

#define ceu_callback_output_LED(v) digitalWrite(13, v)

#include "_ceu.c.h"

///////////////////////////////////////////////////////////////////////////////

#if 0
u32 ceu_arduino_micros_old;
void ceu_arduino_callback_wclock_min (s32) {}
s32 ceu_arduino_callback_wclock_dt (void) {
    u32 now = micros();
    u32 dt  = (now - ceu_arduino_micros_old);  // no problems with overflow
    ceu_arduino_micros_old = now;
    return dt;
}
#endif

void setup ()
{
    //ceu_arduino_micros_old = micros();
    pinMode(2, INPUT_PULLUP);
    pinMode(13, OUTPUT);
    ceu_start(0, NULL);
}

void loop()
{
    static int v = 0;
    int v_ = digitalRead(2);
    if (v != v_) {
        _CEU_INPUT = v = v_;
        ceu_input(CEU_INPUT_BUT);
    }
}
