#include <stdint.h>

// string, int
__thread struct { void* a; void* b; int32_t c; int32_t filler; } __qbuffer = {0UL, 0UL, 0, 0};
void* get_qbuffer_ptr() { return &__qbuffer; }
