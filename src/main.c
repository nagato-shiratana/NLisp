#include "nlisp.h"

#include <stdio.h>
#include <string.h>

static void usage(FILE *stream) {
    fputs("usage: nlisp <check|run|expand> <file.nlisp>\n", stream);
}

int main(int argc, char **argv) {
    if (argc != 3) {
        usage(stderr);
        return NLISP_USAGE_ERROR;
    }

    if (strcmp(argv[1], "check") == 0) {
        return nlisp_check_file(argv[2], stdout, stderr);
    }
    if (strcmp(argv[1], "run") == 0) {
        return nlisp_run_file(argv[2], stdout, stderr);
    }
    if (strcmp(argv[1], "expand") == 0) {
        return nlisp_expand_file(argv[2], stdout, stderr);
    }

    usage(stderr);
    return NLISP_USAGE_ERROR;
}
