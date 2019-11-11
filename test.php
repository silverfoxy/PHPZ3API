<?php
// create gettimeofday() binding
$ffi = FFI::cdef("
typedef struct _Z3_config *Z3_config;
typedef const char * Z3_string;
typedef Z3_string * Z3_string_ptr;
typedef struct _Z3_context *Z3_context;
typedef struct _Z3_solver *Z3_solver;
typedef struct _Z3_symbol *Z3_symbol;

Z3_config Z3_mk_config();
void Z3_set_param_value(Z3_config c, Z3_string param_id, Z3_string param_value);
Z3_context Z3_mk_context(Z3_config c);
Z3_solver Z3_mk_solver(Z3_context c);
Z3_symbol Z3_mk_int_symbol(Z3_context c, int i);
", "/z3-4.8.6-x64-ubuntu-16.04/bin/libz3.so");
// create C data structures
$cfg = $ffi->Z3_mk_config();
$ffi->Z3_set_param_value($cfg, "model", "true");
$ctx = $ffi->Z3_mk_context($cfg);
$solver = $ffi->Z3_mk_solver($ctx);

$a = $ffi->Z3_mk_int_symbol($ctx, 'a');
var_dump($solver);
?>