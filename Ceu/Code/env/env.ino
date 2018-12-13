#if 1
    #define ceu_assert_ex(a,b,c) if (!(a)) { ceu_callback_abort((10+__COUNTER__),c); }
    #define ceu_assert_sys(a,b)  if (!(a)) { ceu_callback_abort((10+__COUNTER__),CEU_TRACE_null); }
    #define ceu_arduino_assert(cnd,err) if (!(cnd)) { ceu_arduino_callback_abort(err); }
#else
    #define ceu_assert_ex(a,b,c)        // no assert
    #define ceu_assert_sys(a,b)         // no assert
    #define ceu_arduino_assert(cnd,err) // no assert
#endif

#define CEU_STACK_N 100
#if ARDUINO_ARCH_AVR
    #define CEU_STACK_MAX 1000
#elif ARDUINO_ARCH_SAMD
    #define CEU_STACK_MAX 1000
#else
    #error "Unsupported Platform!"
#endif
#undef CEU_STACK_MAX

///////////////////////////////////////////////////////////////////////////////
// DO NOT EDIT
///////////////////////////////////////////////////////////////////////////////

#include "types.h"

#define _DELAY(ms)                      \
    {                                   \
        int i;                          \
        for (i=0; i<ms; i++) {          \
            delayMicroseconds(1000);    \
        }                               \
    }

void ceu_arduino_callback_abort (int err) {
    noInterrupts();
#ifdef ARDUINO_ARCH_AVR
    SPCR &= ~_BV(SPE);  // releases PIN13
#endif
    pinMode(13, OUTPUT);
    //digitalWrite(13, 1);
    for (;;) {
        for (int j=0; j<err; j++) {
            _DELAY(200);
            digitalWrite(13, 0);
            _DELAY(200);
            digitalWrite(13, 1);
        }
        _DELAY(1000);
    }
    interrupts();
}

void ceu_arduino_warn (int cnd, int err) {
    if (cnd) return;

    noInterrupts();
#ifdef ARDUINO_ARCH_AVR
    //SPCR &= ~_BV(SPE);  // releases PIN13
#endif
    pinMode(13, OUTPUT);
    //digitalWrite(13, 1);
    //for (;;) {
        for (int j=0; j<err; j++) {
            _DELAY(200);
            digitalWrite(13, 0);
            _DELAY(200);
            digitalWrite(13, 1);
        }
        _DELAY(500);
    //}
    digitalWrite(13, 0);
    interrupts();
}

#define ceu_callback_stop(trace)
#define ceu_callback_step(trace)
#define ceu_callback_async_pending(trace)
#define ceu_callback_wclock_dt(trace) ceu_arduino_callback_wclock_dt()
s32 ceu_arduino_callback_wclock_dt (void);
#define ceu_callback_wclock_min(dt,trace) ceu_arduino_callback_wclock_min(dt)
void ceu_arduino_callback_wclock_min (s32);
#define ceu_callback_abort(err,trace) ceu_arduino_callback_abort(err)
void ceu_arduino_callback_abort (int err);
#define ceu_callback_start(trace)
#define ceu_callback_isr_enable(on,trace) ceu_arduino_callback_isr_enable(on)
void ceu_arduino_callback_isr_enable (int on);
#define ceu_callback_isr_emit(n,evt,trace) ceu_arduino_callback_isr_emit(n,evt)
void ceu_arduino_callback_isr_emit (int n, void* evt);

#include "_ceu_app.c.h"

///////////////////////////////////////////////////////////////////////////////

#if defined(CEU_IN_PIN00) || \
    defined(CEU_IN_PIN01) || \
    defined(CEU_IN_PIN02) || \
    defined(CEU_IN_PIN03) || \
    defined(CEU_IN_PIN04) || \
    defined(CEU_IN_PIN05) || \
    defined(CEU_IN_PIN06) || \
    defined(CEU_IN_PIN07) || \
    defined(CEU_IN_PIN08) || \
    defined(CEU_IN_PIN09) || \
    defined(CEU_IN_PIN00) || \
    defined(CEU_IN_PIN01) || \
    defined(CEU_IN_PIN12) || \
    defined(CEU_IN_PIN13)
int _ceu_arduino_V;
#endif

u32 ceu_arduino_micros_old;
void ceu_arduino_callback_wclock_min (s32) {}
s32 ceu_arduino_callback_wclock_dt (void) {
    u32 now = micros();
    u32 dt  = (now - ceu_arduino_micros_old);  // no problems with overflow
    ceu_arduino_micros_old = now;
    return dt;
}

void setup ()
{
#ifdef CEU_IN_PIN00
    pinMode( 0, INPUT);
#endif
#ifdef CEU_OUT_PIN00
    pinMode( 0, OUTPUT);
#endif
#ifdef CEU_IN_PIN01
    pinMode( 1, INPUT);
#endif
#ifdef CEU_OUT_PIN01
    pinMode( 1, OUTPUT);
#endif
#ifdef CEU_IN_PIN02
    pinMode( 2, INPUT);
#endif
#ifdef CEU_OUT_PIN02
    pinMode( 2, OUTPUT);
#endif
#ifdef CEU_IN_PIN03
    pinMode( 3, INPUT);
#endif
#ifdef CEU_OUT_PIN03
    pinMode( 3, OUTPUT);
#endif
#ifdef CEU_IN_PIN04
    pinMode( 4, INPUT);
#endif
#ifdef CEU_OUT_PIN04
    pinMode( 4, OUTPUT);
#endif
#ifdef CEU_IN_PIN05
    pinMode( 5, INPUT);
#endif
#ifdef CEU_OUT_PIN05
    pinMode( 5, OUTPUT);
#endif
#ifdef CEU_IN_PIN06
    pinMode( 6, INPUT);
#endif
#ifdef CEU_OUT_PIN06
    pinMode( 6, OUTPUT);
#endif
#ifdef CEU_IN_PIN07
    pinMode( 7, INPUT);
#endif
#ifdef CEU_OUT_PIN07
    pinMode( 7, OUTPUT);
#endif
#ifdef CEU_IN_PIN08
    pinMode( 8, INPUT);
#endif
#ifdef CEU_OUT_PIN08
    pinMode( 8, OUTPUT);
#endif
#ifdef CEU_IN_PIN09
    pinMode( 9, INPUT);
#endif
#ifdef CEU_OUT_PIN09
    pinMode( 9, OUTPUT);
#endif
#ifdef CEU_IN_PIN10
    pinMode(10, INPUT);
#endif
#ifdef CEU_OUT_PIN10
    pinMode(10, OUTPUT);
#endif
#ifdef CEU_IN_PIN11
    pinMode(11, INPUT);
#endif
#ifdef CEU_OUT_PIN11
    pinMode(11, OUTPUT);
#endif
#ifdef CEU_IN_PIN12
    pinMode(12, INPUT);
#endif
#ifdef CEU_OUT_PIN12
    pinMode(12, OUTPUT);
#endif
#ifdef CEU_IN_PIN13
    pinMode(13, INPUT);
#endif
#ifdef CEU_OUT_PIN13
    pinMode(13, OUTPUT);
#endif

    ceu_arduino_micros_old = micros();
    ceu_start(0, NULL);
}

void loop()
{
#ifdef CEU_ASYNCS
    if (CEU_APP.async_pending) {
        ceu_input(CEU_INPUT__ASYNC, NULL);
    }
#endif

#if defined(CEU_IN_PIN00) || \
    defined(CEU_IN_PIN01) || \
    defined(CEU_IN_PIN02) || \
    defined(CEU_IN_PIN03) || \
    defined(CEU_IN_PIN04) || \
    defined(CEU_IN_PIN05) || \
    defined(CEU_IN_PIN06) || \
    defined(CEU_IN_PIN07) || \
    defined(CEU_IN_PIN08) || \
    defined(CEU_IN_PIN09) || \
    defined(CEU_IN_PIN10) || \
    defined(CEU_IN_PIN11) || \
    defined(CEU_IN_PIN12) || \
    defined(CEU_IN_PIN13)
    int tmp;
#endif

#ifdef CEU_IN_PIN00
    tmp = digitalRead(0);
    if (bitRead(_ceu_arduino_V,0) != tmp) {
        bitWrite(_ceu_arduino_V,0,tmp);
        ceu_sys_go(&CEU_APP, CEU_IN_PIN00, &tmp);
    }
#endif

#ifdef CEU_IN_PIN01
    tmp = digitalRead(1);
    if (bitRead(_ceu_arduino_V,1) != tmp) {
        bitWrite(_ceu_arduino_V,1,tmp);
        ceu_sys_go(&CEU_APP, CEU_IN_PIN01, &tmp);
    }
#endif

#ifdef CEU_IN_PIN02
    tmp = digitalRead(2);
    if (bitRead(_ceu_arduino_V,2) != tmp) {
        bitWrite(_ceu_arduino_V,2,tmp);
#ifdef CEU_TIMEMACHINE
#ifdef CEU_IN_PIN02_
        ceu_sys_go(&CEU_APP, CEU_IN_PIN02_, &tmp);
#endif
#endif
if (!CEU_TIMEMACHINE_ON) {
        ceu_sys_go(&CEU_APP, CEU_IN_PIN02, &tmp);
}
    }
#endif

#ifdef CEU_IN_PIN03
    tmp = digitalRead(3);
    if (bitRead(_ceu_arduino_V,3) != tmp) {
        bitWrite(_ceu_arduino_V,3,tmp);
#ifdef CEU_TIMEMACHINE
#ifdef CEU_IN_PIN03_
        ceu_sys_go(&CEU_APP, CEU_IN_PIN03_, &tmp);
#endif
#endif
if (!CEU_TIMEMACHINE_ON) {
        ceu_sys_go(&CEU_APP, CEU_IN_PIN03, &tmp);
}
    }
#endif

#ifdef CEU_IN_PIN04
    tmp = digitalRead(4);
    if (bitRead(_ceu_arduino_V,4) != tmp) {
        bitWrite(_ceu_arduino_V,4,tmp);
        ceu_sys_go(&CEU_APP, CEU_IN_PIN04, &tmp);
    }
#endif

#ifdef CEU_IN_PIN05
    tmp = digitalRead(5);
    if (bitRead(_ceu_arduino_V,5) != tmp) {
        bitWrite(_ceu_arduino_V,5,tmp);
        ceu_sys_go(&CEU_APP, CEU_IN_PIN05, &tmp);
    }
#endif

#ifdef CEU_IN_PIN06
    tmp = digitalRead(6);
    if (bitRead(_ceu_arduino_V,6) != tmp) {
        bitWrite(_ceu_arduino_V,6,tmp);
        ceu_sys_go(&CEU_APP, CEU_IN_PIN06, &tmp);
    }
#endif

#ifdef CEU_IN_PIN07
    tmp = digitalRead(7);
    if (bitRead(_ceu_arduino_V,7) != tmp) {
        bitWrite(_ceu_arduino_V,7,tmp);
        ceu_sys_go(&CEU_APP, CEU_IN_PIN07, &tmp);
    }
#endif

#ifdef CEU_IN_PIN08
    tmp = digitalRead(8);
    if (bitRead(_ceu_arduino_V,8) != tmp) {
        bitWrite(_ceu_arduino_V,8,tmp);
        ceu_sys_go(&CEU_APP, CEU_IN_PIN08, &tmp);
    }
#endif

#ifdef CEU_IN_PIN09
    tmp = digitalRead(9);
    if (bitRead(_ceu_arduino_V,9) != tmp) {
        bitWrite(_ceu_arduino_V,9,tmp);
        ceu_sys_go(&CEU_APP, CEU_IN_PIN09, &tmp);
    }
#endif

#ifdef CEU_IN_PIN10
    tmp = digitalRead(10);
    if (bitRead(_ceu_arduino_V,10) != tmp) {
        bitWrite(_ceu_arduino_V,10,tmp);
        ceu_sys_go(&CEU_APP, CEU_IN_PIN10, &tmp);
    }
#endif

#ifdef CEU_IN_PIN11
    tmp = digitalRead(11);
    if (bitRead(_ceu_arduino_V,11) != tmp) {
        bitWrite(_ceu_arduino_V,11,tmp);
        ceu_sys_go(&CEU_APP, CEU_IN_PIN11, &tmp);
    }
#endif

#ifdef CEU_IN_PIN12
    tmp = digitalRead(12);
    if (bitRead(_ceu_arduino_V,12) != tmp) {
        bitWrite(_ceu_arduino_V,12,tmp);
        ceu_sys_go(&CEU_APP, CEU_IN_PIN12, &tmp);
    }
#endif

#ifdef CEU_IN_PIN13
    tmp = digitalRead(13);
    if (bitRead(_ceu_arduino_V,13) != tmp) {
        bitWrite(_ceu_arduino_V,13,tmp);
        ceu_sys_go(&CEU_APP, CEU_IN_PIN13, &tmp);
    }
#endif

#ifdef CEU_IN_SERIAL
    if (Serial.available() > 0) {
        char c = Serial.read();
        ceu_sys_go(&CEU_APP, CEU_IN_SERIAL, &c);
    }
#endif

#ifdef CEU_ASYNCS
    ceu_sys_go(&CEU_APP, CEU_IN__ASYNC, NULL);
#endif
}
