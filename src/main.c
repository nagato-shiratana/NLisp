#include "nlisp.h"

#include <stdint.h>
#include <stdio.h>
#include <string.h>

static void usage(FILE *stream) {
    fputs("usage: nlisp <check|run|expand|export-core|export-syntax> <file.nlisp> [limits]\n"
          "limits: --max-expansions N --max-generated-nodes N\n"
          "        --max-expansion-depth N --max-check-steps N\n", stream);
}

static int parse_limit(const char *text, size_t *result) {
    size_t value = 0U;
    if (*text == '\0') return 0;
    for (; *text != '\0'; text++) {
        size_t digit;
        if (*text < '0' || *text > '9') return 0;
        digit = (size_t)(*text - '0');
        if (value > (SIZE_MAX - digit) / 10U) return 0;
        value = value * 10U + digit;
    }
    *result = value; return 1;
}

int main(int argc, char **argv) {
    NLispCommand command;
    NLispLimits limits = nlisp_default_limits();
    const char *path = NULL;
    int i;
    if (argc < 3) { usage(stderr); return NLISP_USAGE_ERROR; }
    if (strcmp(argv[1], "check") == 0) command = NLISP_CHECK;
    else if (strcmp(argv[1], "run") == 0) command = NLISP_RUN;
    else if (strcmp(argv[1], "expand") == 0) command = NLISP_EXPAND;
    else if (strcmp(argv[1], "export-core") == 0) command = NLISP_EXPORT;
    else if (strcmp(argv[1], "export-syntax") == 0) command = NLISP_SYNTAX;
    else { usage(stderr); return NLISP_USAGE_ERROR; }
    for (i = 2; i < argc; i++) {
        size_t *limit = NULL;
        if (strcmp(argv[i], "--max-expansions") == 0) limit = &limits.max_expansions;
        else if (strcmp(argv[i], "--max-generated-nodes") == 0) limit = &limits.max_generated_nodes;
        else if (strcmp(argv[i], "--max-expansion-depth") == 0) limit = &limits.max_expansion_depth;
        else if (strcmp(argv[i], "--max-check-steps") == 0) limit = &limits.max_check_steps;
        else if (argv[i][0] == '-' || path != NULL) { usage(stderr); return NLISP_USAGE_ERROR; }
        else { path = argv[i]; continue; }
        if (++i >= argc || !parse_limit(argv[i], limit)) { usage(stderr); return NLISP_USAGE_ERROR; }
    }
    if (path == NULL) { usage(stderr); return NLISP_USAGE_ERROR; }
    return nlisp_process_file(path, command, &limits, stdout, stderr);
}
