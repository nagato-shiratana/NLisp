#ifndef NLISP_H
#define NLISP_H

#include <stdio.h>
#include <stddef.h>

typedef enum NLispStatus {
    NLISP_OK = 0,
    NLISP_USAGE_ERROR = 2,
    NLISP_IO_ERROR = 3,
    NLISP_PARSE_ERROR = 4,
    NLISP_TYPE_ERROR = 5,
    NLISP_RUNTIME_ERROR = 6,
    NLISP_UNKNOWN = 7
} NLispStatus;

typedef struct {
    size_t max_expansions;
    size_t max_generated_nodes;
    size_t max_expansion_depth;
    size_t max_check_steps;
} NLispLimits;

typedef enum { NLISP_CHECK, NLISP_RUN, NLISP_EXPAND, NLISP_EXPORT, NLISP_SYNTAX } NLispCommand;

NLispLimits nlisp_default_limits(void);
NLispStatus nlisp_process_file(const char *path, NLispCommand command,
                             const NLispLimits *limits, FILE *out, FILE *err);

NLispStatus nlisp_check_file(const char *path, FILE *out, FILE *err);
NLispStatus nlisp_run_file(const char *path, FILE *out, FILE *err);
NLispStatus nlisp_expand_file(const char *path, FILE *out, FILE *err);
NLispStatus nlisp_export_file(const char *path, FILE *out, FILE *err);

#endif
