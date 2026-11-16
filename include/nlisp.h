#ifndef NLISP_H
#define NLISP_H

#include <stdio.h>

typedef enum NLispStatus {
    NLISP_OK = 0,
    NLISP_USAGE_ERROR = 2,
    NLISP_IO_ERROR = 3,
    NLISP_PARSE_ERROR = 4,
    NLISP_TYPE_ERROR = 5,
    NLISP_RUNTIME_ERROR = 6
} NLispStatus;

NLispStatus nlisp_check_file(const char *path, FILE *out, FILE *err);
NLispStatus nlisp_run_file(const char *path, FILE *out, FILE *err);
NLispStatus nlisp_expand_file(const char *path, FILE *out, FILE *err);

#endif
