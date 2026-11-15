/* Differential-testing harness: runs the real compiled verified-core C
 * functions on the inputs read from stdin (same format as formal/CDiff.lean). */
#include "../../tiny_gltf_v3.c"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int hexval(int c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    return c - 'A' + 10;
}

int main(void) {
    static char line[1 << 20];
    while (fgets(line, sizeof(line), stdin)) {
        size_t n = strlen(line);
        while (n && (line[n - 1] == '\n' || line[n - 1] == '\r')) line[--n] = 0;
        if (strncmp(line, "frame", 5) == 0) {
            const char *hex = line[5] == ' ' ? line + 6 : line + 5;
            size_t len = strlen(hex) / 2, i;
            uint8_t *d = (uint8_t *)malloc(len ? len : 1);
            tg3__glb_frame f;
            tg3_error_code e;
            for (i = 0; i < len; ++i) d[i] = (uint8_t)(hexval(hex[2 * i]) * 16 + hexval(hex[2 * i + 1]));
            e = tg3__glb_frame_parse(d, (uint64_t)len, &f);
            if (e == TG3_OK) {
                printf("%d %llu %llu %llu %llu %d %d %d\n", (int)e,
                       (unsigned long long)f.json_off, (unsigned long long)f.json_len,
                       (unsigned long long)f.bin_off, (unsigned long long)f.bin_len,
                       f.has_json, f.has_bin, f.is64);
            } else {
                printf("%d\n", (int)e);
            }
            free(d);
        } else if (strncmp(line, "layout ", 7) == 0) {
            unsigned long long jl, bl;
            int is64;
            tg3__glb_frame f;
            uint64_t total = 0;
            int r;
            if (sscanf(line + 7, "%llu %llu %d", &jl, &bl, &is64) != 3) { puts("BADLINE"); continue; }
            r = tg3__glb_layout(jl, bl, is64, &f, &total);
            if (r) {
                printf("1 %llu %llu %llu %llu %llu %d %d %d\n", (unsigned long long)total,
                       (unsigned long long)f.json_off, (unsigned long long)f.json_len,
                       (unsigned long long)f.bin_off, (unsigned long long)f.bin_len,
                       f.has_json, f.has_bin, f.is64);
            } else {
                printf("0\n");
            }
        } else {
            puts("BADLINE");
        }
    }
    return 0;
}
