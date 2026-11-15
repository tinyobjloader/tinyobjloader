/* SPDX-License-Identifier: MIT. Private numeric policy for the CLI tools. */
#ifndef TESS_OBJ_NUMBER_H
#define TESS_OBJ_NUMBER_H
#include <stdbool.h>
bool tess_obj_scan_double(const char** position, const char* end, double* out);
void tess_obj_numbers_reset(void);
int tess_obj_numbers_error(
    void); /* 1 invalid/nonfinite; 2 token resource cap */
#endif
