#include <stdlib.h>  /*a more portable size_t definition than stddef.h itself*/
#ifdef __cplusplus
extern "C" {
#endif
void*  ltmalloc(size_t);
void   ltfree(void*);
void*  ltrealloc( void *, size_t );
void*  ltcalloc( size_t, size_t );
void*  ltmemalign( size_t, size_t );
void   ltsqueeze(size_t pad); /*return memory to system (see README.md)*/
size_t ltmsize(void*);
#ifdef __cplusplus
}
#endif
