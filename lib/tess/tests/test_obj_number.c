#include <float.h>
#include <math.h>
#include <stdio.h>
#include <string.h>

#include "obj_number.h"
static int accepted(const char* text, double expected) {
  const char* p = text;
  double value = 123;
  tess_obj_numbers_reset();
  return tess_obj_scan_double(&p, text + strlen(text), &value) &&
         !tess_obj_numbers_error() && value == expected &&
         (expected != 0 || signbit(value) == signbit(expected));
}
int main(void) {
  const char* bad[] = {"nan", "-infinity", "inf", "1e9999", "1junk", "--0"};
  size_t i;
  if (!accepted("9.3326361850321888e-302", 0x1p-1000) ||
      !accepted("4.9406564584124654e-324", 0x1p-1074) ||
      !accepted("1.7976931348623157e+308", DBL_MAX) || !accepted("-0", -0.) ||
      !accepted("0.33333333333333331", 0x1.5555555555555p-2) ||
      !accepted(" \t1.25#comment", 1.25))
    return 1;
  for (i = 0; i < sizeof(bad) / sizeof(bad[0]); i++) {
    const char* p = bad[i];
    double value = 123;
    tess_obj_numbers_reset();
    if (tess_obj_scan_double(&p, p + strlen(p), &value) ||
        tess_obj_numbers_error() != 1 || value != 123)
      return 2;
  }
  {
    char token[4098];
    const char* p = token;
    double value = 123;
    memset(token, '1', 4097);
    token[4097] = 0;
    tess_obj_numbers_reset();
    if (tess_obj_scan_double(&p, token + 4097, &value) ||
        tess_obj_numbers_error() != 2)
      return 3;
  }
  return 0;
}
