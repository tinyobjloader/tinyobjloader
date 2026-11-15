/* SPDX-License-Identifier: MIT */
#include "obj_number.h"

#include <math.h>
#include <stdlib.h>
/* These hosted executables start in the standard C locale and use one loader
   thread. Keep status thread-local as well. The core library does not use this
   parser or mutate the process locale. */
static _Thread_local int number_error;
void tess_obj_numbers_reset(void) { number_error = 0; }
int tess_obj_numbers_error(void) { return number_error; }
static int space(char c) {
  return c == ' ' || c == '\t' || c == '\r' || c == '\n' || c == '\v' ||
         c == '\f';
}
bool tess_obj_scan_double(const char** position, const char* end, double* out) {
  const char* start = *position;
  const char* stop;
  char token[4097], *tail;
  size_t n, i;
  double value;
  while (start < end && space(*start)) start++;
  if (start == end || *start == '#') return false;
  stop = start;
  while (stop < end && !space(*stop) && *stop != '#') stop++;
  n = (size_t)(stop - start);
  if (n > 4096) {
    number_error = 2;
    return false;
  }
  for (i = 0; i < n; i++) token[i] = start[i];
  token[n] = 0;
  value = strtod(token, &tail);
  if (tail != token + n || tail == token || !isfinite(value)) {
    if (number_error != 2) number_error = 1;
    return false;
  }
  *position = stop;
  *out = value;
  return true;
}
