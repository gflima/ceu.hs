#include <stdlib.h>
#include <stdio.h>
#include "types.h"

#define ceu_callback_start()
#define ceu_callback_step()
#define ceu_callback_stop()
#define ceu_callback_terminating()
#define ceu_callback_thread_terminating()
#define ceu_callback_async_pending()
#define ceu_callback_isr_enable(on)
#define ceu_callback_isr_attach(on,f,args)
#define ceu_callback_isr_emit(a,b,c)
#define ceu_callback_abort(err) abort()
#define ceu_callback_wclock_dt() CEU_WCLOCK_INACTIVE
#define ceu_callback_wclock_min(dt)
#define ceu_callback_log_str(str) printf("%s", str)
#define ceu_callback_log_ptr(ptr) printf("%p", ptr)
#define ceu_callback_log_num(num) printf("%d", num)
#define ceu_callback_log_flush() fflush(stdout)
#define ceu_callback_realloc(ptr,size) realloc(ptr,size)

#define ceu_assert_sys(a,b)

#define CEU_HISTORY

#include "_ceu.c"

int main (int argc, char* argv[]) {
    ceu_start(0, NULL);
    return CEU_APP.root._ret__1;
}
