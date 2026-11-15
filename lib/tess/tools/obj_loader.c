/* SPDX-License-Identifier: MIT */
/* Reuse tinyobjloader's C11 OBJ implementation with a private strict hosted
   numeric policy. The normal loader build keeps its original number scanner. */
#include "obj_number.h"
#define TOBJ_SCAN_DOUBLE_OVERRIDE tess_obj_scan_double
#include "../../../tiny_obj_c.c"
