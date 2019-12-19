<?php

$z3_definitions = file_get_contents('defs.c');
$ffi = FFI::cdef($z3_definitions, "/z3-4.8.6-x64-ubuntu-16.04/bin/libz3.so");

class Z3_const {
    // Z3_lbool
    public const Z3_L_FALSE = -1;
    public const Z3_L_UNDEF = 0;
    public const Z3_L_TRUE = 1;

    // Z3_symbol_kind
    public const Z3_INT_SYMBOL = 0;
    public const Z3_STRING_SYMBOL = 1;

    // Z3_parameter_kind
    public const Z3_PARAMETER_INT = 0;
    public const Z3_PARAMETER_DOUBLE = 1;
    public const Z3_PARAMETER_RATIONAL = 2;
    public const Z3_PARAMETER_SYMBOL = 3;
    public const Z3_PARAMETER_SORT = 4;
    public const Z3_PARAMETER_AST = 5;
    public const Z3_PARAMETER_FUNC_DECL = 6;

    // Z3_sort_kind
    public const Z3_UNINTERPRETED_SORT = 0;
    public const Z3_BOOL_SORT = 1;
    public const Z3_INT_SORT = 2;
    public const Z3_REAL_SORT = 3;
    public const Z3_BV_SORT = 4;
    public const Z3_ARRAY_SORT = 5;
    public const Z3_DATATYPE_SORT = 6;
    public const Z3_RELATION_SORT = 7;
    public const Z3_FINITE_DOMAIN_SORT = 8;
    public const Z3_FLOATING_POINT_SORT = 9;
    public const Z3_ROUNDING_MODE_SORT = 10;
    public const Z3_SEQ_SORT = 11;
    public const Z3_RE_SORT = 12;
    public const Z3_UNKNOWN_SORT = 1000;

    // Z3_ast_kind
    public const Z3_NUMERAL_AST = 0;
    public const Z3_APP_AST = 1;
    public const Z3_VAR_AST = 2;
    public const Z3_QUANTIFIER_AST = 3;
    public const Z3_SORT_AST = 4;
    public const Z3_FUNC_DECL_AST = 5;
    public const Z3_UNKNOWN_AST = 1000;

    // Z3_decl_kind

    // Basic
    public const Z3_OP_TRUE = 0x100;
    public const Z3_OP_FALSE = 0x101;
    public const Z3_OP_EQ = 0x102;
    public const Z3_OP_DISTINCT = 0x103;
    public const Z3_OP_ITE = 0x104;
    public const Z3_OP_AND = 0x105;
    public const Z3_OP_OR = 0x106;
    public const Z3_OP_IFF = 0x107;
    public const Z3_OP_XOR = 0x108;
    public const Z3_OP_NOT = 0x109;
    public const Z3_OP_IMPLIES = 0x10A;
    public const Z3_OP_OEQ = 0x10B;

    // Arithmetic
    public const Z3_OP_ANUM = 0x200;
    public const Z3_OP_AGNUM = 0x201;
    public const Z3_OP_LE = 0x202;
    public const Z3_OP_GE = 0x203;
    public const Z3_OP_LT = 0x204;
    public const Z3_OP_GT = 0x205;
    public const Z3_OP_ADD = 0x206;
    public const Z3_OP_SUB = 0x207;
    public const Z3_OP_UMINUS = 0x208;
    public const Z3_OP_MUL = 0x209;
    public const Z3_OP_DIV = 0x20A;
    public const Z3_OP_IDIV = 0x20B;
    public const Z3_OP_REM = 0x20C;
    public const Z3_OP_MOD = 0x20D;
    public const Z3_OP_TO_REAL = 0x20E;
    public const Z3_OP_TO_INT = 0x20F;
    public const Z3_OP_IS_INT = 0x210;
    public const Z3_OP_POWER = 0x211;

    // Arrays & Sets
    public const Z3_OP_STORE = 0x300;
    public const Z3_OP_SELECT = 0x301;
    public const Z3_OP_CONST_ARRAY = 0x302;
    public const Z3_OP_ARRAY_MAP = 0x303;
    public const Z3_OP_ARRAY_DEFAULT = 0x304;
    public const Z3_OP_SET_UNION = 0x305;
    public const Z3_OP_SET_INTERSECT = 0x306;
    public const Z3_OP_SET_DIFFERENCE = 0x307;
    public const Z3_OP_SET_COMPLEMENT = 0x308;
    public const Z3_OP_SET_SUBSET = 0x309;
    public const Z3_OP_AS_ARRAY = 0x30A;
    public const Z3_OP_ARRAY_EXT = 0x30B;

    // Bit-vectors
    public const Z3_OP_BNUM = 0x400;
    public const Z3_OP_BIT1 = 0x401;
    public const Z3_OP_BIT0 = 0x402;
    public const Z3_OP_BNEG = 0x403;
    public const Z3_OP_BADD = 0x404;
    public const Z3_OP_BSUB = 0x405;
    public const Z3_OP_BMUL = 0x406;
    
    public const Z3_OP_BSDIV = 0x407;
    public const Z3_OP_BUDIV = 0x408;
    public const Z3_OP_BSREM = 0x409;
    public const Z3_OP_BUREM = 0x40A;
    public const Z3_OP_BSMOD = 0x40B;

    // special functions to record the division by 0 cases
    // these are internal functions
    public const Z3_OP_BSDIV0 = 0x40C;
    public const Z3_OP_BUDIV0 = 0x40D;
    public const Z3_OP_BSREM0 = 0x40E;
    public const Z3_OP_BUREM0 = 0x40F;
    public const Z3_OP_BSMOD0 = 0x410;

    public const Z3_OP_ULEQ = 0x411;
    public const Z3_OP_SLEQ = 0x412;
    public const Z3_OP_UGE = 0x413;
    public const Z3_OP_SGEQ = 0x414;
    public const Z3_OP_ULT = 0x415;
    public const Z3_OP_SLT = 0x416;
    public const Z3_OP_UGT = 0x417;
    public const Z3_OP_SGT = 0x418;

    public const Z3_OP_BAND = 0x419;
    public const Z3_OP_BOR = 0x41A;
    public const Z3_OP_BNOT = 0x41B;
    public const Z3_OP_BXOR = 0x41C;
    public const Z3_OP_BNAND = 0x41D;
    public const Z3_OP_BNOR = 0x41E;
    public const Z3_OP_BXNOR = 0x41F;

    public const Z3_OP_CONCAT = 0x420;
    public const Z3_OP_SIGN_EXT = 0x421;
    public const Z3_OP_ZERO_EXT = 0x422;
    public const Z3_OP_EXTRACT = 0x423;
    public const Z3_OP_REPEAT = 0x424;

    public const Z3_OP_BREDOR = 0x425;
    public const Z3_OP_BREDAND = 0x426;
    public const Z3_OP_BCOMP = 0x426;

    public const Z3_OP_BSHL = 0x427;
    public const Z3_OP_BLSHR = 0x428;
    public const Z3_OP_BASHR = 0x429;
    public const Z3_OP_ROTATE_LEFT = 0x42A;
    public const Z3_OP_ROTATE_RIGHT = 0x42B;
    public const Z3_OP_EXT_ROTATE_LEFT = 0x42C;
    public const Z3_OP_EXT_ROTATE_RIGHT = 0x42D;

    public const Z3_OP_BIT2BOOL = 0x42E;
    public const Z3_OP_INT2BV = 0x42F;
    public const Z3_OP_BV2INT = 0x430;
    public const Z3_OP_CARRY = 0x431;
    public const Z3_OP_XOR3 = 0x432;

    public const Z3_OP_BSMUL_NO_OVFL = 0x433;
    public const Z3_OP_BUMUL_NO_OVFL = 0x434;
    public const Z3_OP_BSMUL_NO_UDFL = 0x435;
    public const Z3_OP_BSDIV_I = 0x436;
    public const Z3_OP_BUDIV_I = 0x437;
    public const Z3_OP_BSREM_I = 0x438;
    public const Z3_OP_BUREM_I = 0x439;
    public const Z3_OP_BSMOD_I = 0x43A;

    // Proofs
    public const Z3_OP_PR_UNDEF = 0x500;
    public const Z3_OP_PR_TRUE = 0x501;
    public const Z3_OP_PR_ASSERTED = 0x502;
    public const Z3_OP_PR_GOAL = 0x503;
    public const Z3_OP_PR_MODUS_PONENS = 0x504;
    public const Z3_OP_PR_REFLEXIVITY = 0x505;
    public const Z3_OP_PR_SYMMETRY = 0x506;
    public const Z3_OP_PR_TRANSITIVITY = 0x507;
    public const Z3_OP_PR_TRANSITIVITY_STAR = 0x508;
    public const Z3_OP_PR_MONOTONICITY = 0x509;
    public const Z3_OP_PR_QUANT_INTRO = 0x50A;
    public const Z3_OP_PR_BIND = 0x50B;
    public const Z3_OP_PR_DISTRIBUTIVITY = 0x50C;
    public const Z3_OP_PR_AND_ELIM = 0x50D;
    public const Z3_OP_PR_NOT_OR_ELIM = 0x50E;
    public const Z3_OP_PR_REWRITE = 0x50F;
    public const Z3_OP_PR_REWRITE_STAR = 0x510;
    public const Z3_OP_PR_PULL_QUANT = 0x511;
    public const Z3_OP_PR_PUSH_QUANT = 0x512;
    public const Z3_OP_PR_ELIM_UNUSED_VARS = 0x513;
    public const Z3_OP_PR_DER = 0x514;
    public const Z3_OP_PR_QUANT_INST = 0x515;
    public const Z3_OP_PR_HYPOTHESIS = 0x516;
    public const Z3_OP_PR_LEMMA = 0x517;
    public const Z3_OP_PR_UNIT_RESOLUTION = 0x518;
    public const Z3_OP_PR_IFF_TRUE = 0x519;
    public const Z3_OP_PR_IFF_FALSE = 0x51A;
    public const Z3_OP_PR_COMMUTATIVITY = 0x51B;
    public const Z3_OP_PR_DEF_AXIOM = 0x51C;
    public const Z3_OP_PR_ASSUMPTION_ADD = 0x51D;
    public const Z3_OP_PR_LEMMA_ADD = 0x51E;
    public const Z3_OP_PR_REDUNDANT_DEL = 0x51F;
    public const Z3_OP_PR_CLAUSE_TRAIL = 0x520;
    public const Z3_OP_PR_DEF_INTRO = 0x521;
    public const Z3_OP_PR_APPLY_DEF = 0x522;
    public const Z3_OP_PR_IFF_OEQ = 0x523;
    public const Z3_OP_PR_NNF_POS = 0x524;
    public const Z3_OP_PR_NNF_NEG = 0x525;
    public const Z3_OP_PR_SKOLEMIZE = 0x526;
    public const Z3_OP_PR_MODUS_PONENS_OEQ = 0x527;
    public const Z3_OP_PR_TH_LEMMA = 0x528;
    public const Z3_OP_PR_HYPER_RESOLVE = 0x529;

    // Relational algebra
    public const Z3_OP_RA_STORE = 0x600;
    public const Z3_OP_RA_EMPTY = 0x601;
    public const Z3_OP_RA_IS_EMPTY = 0x602;
    public const Z3_OP_RA_JOIN = 0x603;
    public const Z3_OP_RA_UNION = 0x604;
    public const Z3_OP_RA_WIDEN = 0x605;
    public const Z3_OP_RA_PROJECT = 0x606;
    public const Z3_OP_RA_FILTER = 0x607;
    public const Z3_OP_RA_NEGATION_FILTER = 0x608;
    public const Z3_OP_RA_RENAME = 0x609;
    public const Z3_OP_RA_COMPLEMENT = 0x60A;
    public const Z3_OP_RA_SELECT = 0x60B;
    public const Z3_OP_RA_CLONE = 0x60C;
    public const Z3_OP_FD_CONSTANT = 0x60D;
    public const Z3_OP_FD_LT = 0x60E;

    // Sequences
    public const Z3_OP_SEQ_UNIT = 0x60F;
    public const Z3_OP_SEQ_EMPTY = 0x610;
    public const Z3_OP_SEQ_CONCAT = 0x611;
    public const Z3_OP_SEQ_PREFIX = 0x612;
    public const Z3_OP_SEQ_SUFFIX = 0x613;
    public const Z3_OP_SEQ_CONTAINS = 0x614;
    public const Z3_OP_SEQ_EXTRACT = 0x615;
    public const Z3_OP_SEQ_REPLACE = 0x616;
    public const Z3_OP_SEQ_AT = 0x617;
    public const Z3_OP_SEQ_NTH = 0x618;
    public const Z3_OP_SEQ_LENGTH = 0x619;
    public const Z3_OP_SEQ_INDEX = 0x61A;
    public const Z3_OP_SEQ_LAST_INDEX = 0x61B;
    public const Z3_OP_SEQ_TO_RE = 0x61C;
    public const Z3_OP_SEQ_IN_RE = 0x61D;

    // strings
    public const Z3_OP_STR_TO_INT = 0x61E;
    public const Z3_OP_INT_TO_STR = 0x61F;

    // regular expressions
    public const Z3_OP_RE_PLUS = 0x620;
    public const Z3_OP_RE_STAR = 0x621;
    public const Z3_OP_RE_OPTION = 0x622;
    public const Z3_OP_RE_CONCAT = 0x623;
    public const Z3_OP_RE_UNION = 0x624;
    public const Z3_OP_RE_RANGE = 0x625;
    public const Z3_OP_RE_LOOP = 0x626;
    public const Z3_OP_RE_INTERSECT = 0x627;
    public const Z3_OP_RE_EMPTY_SET = 0x628;
    public const Z3_OP_RE_FULL_SET = 0x629;
    public const Z3_OP_RE_COMPLEMENT = 0x62A;

    // Auxiliary
    public const Z3_OP_LABEL = 0x700;
    public const Z3_OP_LABEL_LIT = 0x701;

    // Datatypes
    public const Z3_OP_DT_CONSTRUCTOR = 0x800;
    public const Z3_OP_DT_RECOGNISER = 0x801;
    public const Z3_OP_DT_IS = 0x802;
    public const Z3_OP_DT_ACCESSOR = 0x803;
    public const Z3_OP_DT_UPDATE_FIELD = 0x804;

    // Pseudo Booleans
    public const Z3_OP_PB_AT_MOST = 0x900;
    public const Z3_OP_PB_AT_LEAST = 0x901;
    public const Z3_OP_PB_LE = 0x902;
    public const Z3_OP_PB_GE = 0x903;
    public const Z3_OP_PB_EQ = 0x904;

    // Special relations
    public const Z3_OP_SPECIAL_RELATION_LO = 0xa000;
    public const Z3_OP_SPECIAL_RELATION_PO = 0xa001;
    public const Z3_OP_SPECIAL_RELATION_PLO = 0xa002;
    public const Z3_OP_SPECIAL_RELATION_TO = 0xa003;
    public const Z3_OP_SPECIAL_RELATION_TC = 0xa004;
    public const Z3_OP_SPECIAL_RELATION_TRC = 0xa005;


    // Floating-Point Arithmetic
    public const Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN = 0xb000;
    public const Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY = 0xb001;
    public const Z3_OP_FPA_RM_TOWARD_POSITIVE = 0xb002;
    public const Z3_OP_FPA_RM_TOWARD_NEGATIVE = 0xb003;
    public const Z3_OP_FPA_RM_TOWARD_ZERO = 0xb004;

    public const Z3_OP_FPA_NUM = 0xb005;
    public const Z3_OP_FPA_PLUS_INF = 0xb006;
    public const Z3_OP_FPA_MINUS_INF = 0xb007;
    public const Z3_OP_FPA_NAN = 0xb008;
    public const Z3_OP_FPA_PLUS_ZERO = 0xb009;
    public const Z3_OP_FPA_MINUS_ZERO = 0xb00A;

    public const Z3_OP_FPA_ADD = 0xb00B;
    public const Z3_OP_FPA_SUB = 0xb00C;
    public const Z3_OP_FPA_NEG = 0xb00D;
    public const Z3_OP_FPA_MUL = 0xb00E;
    public const Z3_OP_FPA_DIV = 0xb00F;
    public const Z3_OP_FPA_REM = 0xb010;
    public const Z3_OP_FPA_ABS = 0xb011;
    public const Z3_OP_FPA_MIN = 0xb012;
    public const Z3_OP_FPA_MAX = 0xb013;
    public const Z3_OP_FPA_FMA = 0xb014;
    public const Z3_OP_FPA_SQRT = 0xb015;
    public const Z3_OP_FPA_ROUND_TO_INTEGRAL = 0xb016;

    public const Z3_OP_FPA_EQ = 0xb017;
    public const Z3_OP_FPA_LT = 0xb018;
    public const Z3_OP_FPA_GT = 0xb019;
    public const Z3_OP_FPA_LE = 0xb01A;
    public const Z3_OP_FPA_GE = 0xb01B;
    public const Z3_OP_FPA_IS_NAN = 0xb01C;
    public const Z3_OP_FPA_IS_INF = 0xb01D;
    public const Z3_OP_FPA_IS_ZERO = 0xb01E;
    public const Z3_OP_FPA_IS_NORMAL = 0xb01F;
    public const Z3_OP_FPA_IS_SUBNORMAL = 0xb020;
    public const Z3_OP_FPA_IS_NEGATIVE = 0xb021;
    public const Z3_OP_FPA_IS_POSITIVE = 0xb022;

    public const Z3_OP_FPA_FP = 0xb023;
    public const Z3_OP_FPA_TO_FP = 0xb024;
    public const Z3_OP_FPA_TO_FP_UNSIGNED = 0xb025;
    public const Z3_OP_FPA_TO_UBV = 0xb026;
    public const Z3_OP_FPA_TO_SBV = 0xb027;
    public const Z3_OP_FPA_TO_REAL = 0xb028;

    public const Z3_OP_FPA_TO_IEEE_BV = 0xb029;

    public const Z3_OP_FPA_BVWRAP = 0xb02A;
    public const Z3_OP_FPA_BV2RM = 0xb02B;

    public const Z3_OP_INTERNAL = 0xb02C;

    public const Z3_OP_UNINTERPRETED = 0xb02D;

    // Z3_param_kind
    public const Z3_PK_BOOL = 0;
    public const Z3_PK_DOUBLE = 1;
    public const Z3_PK_UINT = 2;
    public const Z3_PK_SYMBOL = 3;
    public const Z3_PK_STRING = 4;
    public const Z3_PK_OTHER = 5;
    public const Z3_PK_INVALID = 6;

    // Z3_ast_print_mode
    public const Z3_PRINT_SMTLIB_FULL = 0;
    public const Z3_PRINT_LOW_LEVEL = 1;
    public const Z3_PRINT_SMTLIB2_COMPLIANT = 2;

    // Z3_error_code
    public const Z3_OK = 0;
    public const Z3_SORT_ERROR = 1;
    public const Z3_IOB = 2;
    public const Z3_INVALID_ARG = 3;
    public const Z3_PARSER_ERROR = 4;
    public const Z3_NO_PARSER = 5;
    public const Z3_INVALID_PATTERN = 6;
    public const Z3_MEMOUT_FAIL = 7;
    public const Z3_FILE_ACCESS_ERROR = 8;
    public const Z3_INTERNAL_FATAL = 9;
    public const Z3_INVALID_USAGE = 10;
    public const Z3_DEC_REF_ERROR = 11;
    public const Z3_EXCEPTION = 12;

    // Z3_goal_prec
    public const Z3_GOAL_PRECISE = 0;
    public const Z3_GOAL_UNDER = 1;
    public const Z3_GOAL_OVER = 2;
    public const Z3_GOAL_UNDER_OVER = 3;
}

/**public const 
 * exit gracefully in case of error.
 *
 * @param [string] $message
 * @return void
 */
function exitf($message) {
    echo 'BUG: ' . $message . PHP_EOL;
}
/**
 * exit if unreachable code was reached.
 *
 * @return void
 */
function unreachable() {
    exitf('unreachable code was reached');
}
/**
 * Simpler error handler.
 *
 * @param [Z3_context] $context
 * @param [Z3_error_code] $error_code
 * @return void
 */
$error_handler = function($context, $error_code) {
    echo 'Error code: ' . $error_code . PHP_EOL;
    exitf('incorrect use of Z3');
};
/**
 * Create a logical context.
 * Enable model construction. Other configuration parameters can be passed in the cfg variable.
 * Also enable tracing to stderr and register custom error handler.
 *
 * @param [Z3_config] $config
 * @param [Z3_error_handler] $error
 * @return Z3_context
 */
function mk_context_custom($config, $error) {
    global $ffi;

    $ffi->Z3_set_param_value($config, 'model', 'true');
    $context = $ffi->Z3_mk_context($config);
    $ffi->Z3_set_error_handler($context, $error);

    return $context;
}
/**
 * Create a z3 solver instance
 *
 * @param [Z3_context] $context
 * @return Z3_solver
 */
function mk_solver($context) {
    global $ffi;
    $solver = $ffi->Z3_mk_solver($context);
    $ffi->Z3_solver_inc_ref($context, $solver);
    return $solver;
}

/**
 * Delete a z3 solver instance
 *
 * @param [Z3_context] $context
 * @param [Z3_solver] $solver
 * @return void
 */
function del_solver($context, $solver) {
    global $ffi;
    $ffi->Z3_solver_dec_ref($context, $solver);
}
/**
 *  Create a logical context.
 * Enable model construction only.
 * Also enable tracing to stderr and register standard error handler.
 *
 * @return Z3_context
 */
function mk_context() {
    global $ffi;
    global $error_handler;
    $config = $ffi->Z3_mk_config();
    $context = mk_context_custom($config, $error_handler);
    $ffi->Z3_del_config($config);
    return $context;
}
/**
 * Create a logical context.
 * Enable fine-grained proof construction.
 * Enable model construction.
 * Also enable tracing to stderr and register standard error handler.
 *
 * @return Z3_context
 */
function mk_proof_context() {
    global $ffi;
    global $error_handler;
    $config = $ffi->Z3_mk_config();
    $ffi->Z3_set_param_value($config, 'proof', 'true');
    $context = mk_context_custom($config, $error_handler);
    $ffi->Z3_del_config($config);
    return $context;
}
/**
 * Create a variable using the given name and type.
 *
 * @param [Z3_context] $context
 * @param [string] $name
 * @param [Z3_sort] $type
 * @return Z3_ast
 */
function mk_var($context, $name, $type) {
    global $ffi;
    $symbol = $ffi->Z3_mk_string_symbol($context, $name);
    return $ffi->Z3_mk_const($context, $symbol, $type);
}
/**
 * Create a boolean variable using the given name.
 *
 * @param [Z3_context] $context
 * @param [string] $name
 * @return Z3_ast
 */
function mk_bool_var($context, $name) {
    global $ffi;
    $type = $ffi->Z3_mk_bool_sort($context);
    return mk_var($context, $name, $type);
}
/**
 * Create an integer variable using the given name.
 *
 * @param [Z3_context] $context
 * @param [string] $name
 * @return Z3_ast
 */
function mk_int_var($context, $name) {
    global $ffi;
    $type = $ffi->Z3_mk_int_sort($context);
    return mk_var($context, $name, $type);
}
/**
 * Create a Z3 integer node using a PHP int
 *
 * @param [Z3_context] $context
 * @param [int] $value
 * @return Z3_ast
 */
function mk_int($context, $value) {
    global $ffi;
    $type = $ffi->Z3_mk_int_sort($context);
    return $ffi->Z3_mk_int($context, $value, $type);
}
/**
 * Create a real variable using the given name.
 *
 * @param [Z3_context] $context
 * @param [string] $name
 * @return Z3_ast
 */
function mk_real_var($context, $name) {
    global $ffi;
    $type = $ffi->Z3_mk_real_sort($context);
    return mk_var($context, $name, $type);
}
/**
 * Make an array of specific type and populate items
 *
 * @param [string] $type
 * @param [int] $dim
 * @param [array] $items
 * @return FFI\CData
 */
function mk_1d_array($type, $dim, $items) {
    global $ffi;
    // Create $type[$dim] type
    $arg_type = FFI::arrayType($ffi->type($type), array($dim));
    // Create array of type $type[$dim]
    $args = FFI::new($arg_type);
    // Populate the array
    for ($i=0; $i < $dim; $i++) { 
        $args[$i] = $items[$i];
    }
    return $args;
}
/**
 * Create the unary function application: <tt>(f x)</tt>.
 *
 * @param [Z3_context] $context
 * @param [Z3_func_decl] $function
 * @param [Z3_ast] $param1
 * @return Z3_ast
 */
function mk_unary_app($context, $function, $param1) {
    global $ffi;
    $args = mk_1d_array('Z3_ast', 1, $param1);
    return $ffi->Z3_mk_app($context, $function, 1, $args);
}
/**
 * Create the binary function application: <tt>(f x y)</tt>.
 *
 * @param [Z3_context] $context
 * @param [Z3_func_decl] $function
 * @param [Z3_ast] $param1
 * @param [Z3_ast] $param2
 * @return Z3_ast
 */
function mk_binary_app($context, $function, $param1, $param2) {
    global $ffi;
    $args = array($param1, $param2);
    $args = mk_1d_array('Z3_ast', 2, $args);
    return $ffi->Z3_mk_app($context, $function, 2, $args);
}
/**
 * Check whether the logical context is satisfiable, and compare the result with the expected result.
 * If the context is satisfiable, then display the model.
 *
 * @param [Z3_context] $context
 * @param [Z3_solver] $solver
 * @param [Z3_lbool] $expected_result
 * @return void
 */
function check($context, $solver, $expected_result) {
    global $ffi;
    $result = $ffi->Z3_solver_check($context, $solver);
    switch ($result) {
        case Z3_const::Z3_L_FALSE:
            echo 'unsat' . PHP_EOL;
            break;
        case Z3_const::Z3_L_UNDEF:
            echo 'unknown' . PHP_EOL;
            $model = $ffi->Z3_solver_get_model($context, $solver);
            if (isset($model)) {
                echo 'potential mode:' . PHP_EOL . $ffi->Z3_model_to_string($context, $model) . PHP_EOL;
            }
            break;
        case Z3_const::Z3_L_TRUE:
            $model = $ffi->Z3_solver_get_model($context, $solver);
            if (isset($model)) {
                $ffi->Z3_model_inc_ref($context, $model);
            }
            echo 'sat' . PHP_EOL . $ffi->Z3_model_to_string($context, $model) . PHP_EOL;
            break;
        default:
            break;
    }
    if ($result !== $expected_result) {
        exitf('unexpected result');
    }
    if (isset($model)) {
        $ffi->Z3_model_dec_ref($context, $model);
    }
}
/**
 * Similar to #check, but uses #display_model instead of #Z3_model_to_string.
 *
 * @param [Z3_context] $context
 * @param [Z3_solver] $solver
 * @param [Z3_lbool] $expected_result
 * @return void
 */
function check2($context, $solver, $expected_result) {
    global $ffi;
    $result = $ffi->Z3_solver_check($context, $solver);
    switch ($result) {
        case Z3_const::Z3_L_FALSE:
            echo 'unsat' . PHP_EOL;
            break;
        case Z3_const::Z3_L_UNDEF:
            echo 'unknown' . PHP_EOL;
            echo 'potential model:' . PHP_EOL;
            $model = $ffi->Z3_solver_get_model($context, $solver);
            if ($model !== 0) {
                $ffi->Z3_model_inc_ref($context, $model);
            }
            break;
        case Z3_const::Z3_L_TRUE:
            echo 'sat' . PHP_EOL;
            $model = $ffi->Z3_solver_get_model($context, $solver);
            if ($model !== 0) {
                $ffi->Z3_model_inc_ref($context, $model);
            }
            display_model($context, $model);
            break;
        default:
            break;
    }
    if ($result !== $expected_result) {
        exitf('unexpected result');
    }
    if (isset($model)) {
        $ffi->Z3_model_dec_ref($context, $model);
    }
}
/**
 * Custom model pretty printer
 *
 * @param [Z3_context] $context
 * @param [Z3_model] $model
 * @return void
 */
function display_model($context, $model) {
    global $ffi;
    if ($model === 0) {
        return;
    }

    $num_constants = $ffi->Z3_model_get_num_constants($context, $model);
    for ($i=0; $i < $num_constants; $i++) { 
        $constant = $ffi->Z3_model_get_constant_decl($context, $model, $i);
        $name = $ffi->Z3_get_decl_name($context, $constant);
        display_symbol($context, $name);
        echo ' = ';
        $a = $ffi->Z3_mk_app($context, $constant, 0, 0);
        $v = $a;
        $ok = $ffi->Z3_model_eval($context, $model, $a, 1, FFI::addr($v));
        display_ast($context, $v);
        echo PHP_EOL;
    }
    display_function_interpretations($context, $model);
}
/**
 * Custom function interpretations pretty printer
 *
 * @param [Z3_context] $context
 * @param [Z3_model] $model
 * @return void
 */
function display_function_interpretations($context, $model) {
    global $ffi;
    echo 'function interpretations:' . PHP_EOL;

    $num_functions = $ffi->Z3_model_get_num_funcs($context, $model);
    for ($i=0; $i < $num_functions; $i++) { 
        $num_entries = 0;
        $fdecl = $ffi->Z3_model_get_func_decl($context, $model, $i);
        $finterp = $ffi->Z3_model_get_func_interp($context, $model, $fdecl);
        $ffi->Z3_func_interp_inc_ref($context, $finterp);
        $name = $ffi->Z3_get_decl_name($context, $fdecl);
        display_symbol($context, $name);
        echo ' = {';
        if ($finterp) {
            $num_entries = $ffi->Z3_func_interp_get_num_entries($context, $finterp);
        }
        for ($j=0; $j < $num_entries; $j++) { 
            $fentry = $ffi->Z3_func_interp_get_entry($context, $finterp, $j);
            $ffi->Z3_func_entry_inc_ref($context, $fentry);
            if ($j > 0) {
                echo ', ';
            }
            $num_args = $ffi->Z3_func_entry_get_num_args($context, $fentry);
            echo '(';
            for ($k=0; $k < $num_args; $k++) { 
                if ($k > 0) {
                    echo ', ';
                }
                display_ast($context, $ffi->Z3_func_entry_get_arg($context, $fentry, $k));
            }
            echo '|->';
            display_ast($context, $ffi->Z3_func_entry_get_value($context, $fentry));
            echo ')';
            $ffi->Z3_func_entry_dec_ref($context, $fentry);
        }
        if ($num_entries > 0) {
            echo ', ';
        }
        echo '(else|->';
        $func_else = $ffi->Z3_func_interp_get_else($context, $finterp);
        display_ast($context, $func_else);
        echo ')}' . PHP_EOL;
        $ffi->Z3_func_interp_dec_ref($context, $finterp);
    }
}
/**
 * Custom ast pretty printer.
 * This function demonstrates how to use the API to navigate terms.
 *
 * @return void
 */
function display_ast($context, $value) {
    global $ffi;
    switch ($ffi->Z3_get_ast_kind($context, $value)) {
        case Z3_const::Z3_NUMERAL_AST:
            echo $ffi->Z3_get_numeral_string($context, $value);
            $t = $ffi->Z3_get_sort($context, $value);
            echo ':';
            display_sort($context, $t);
            break;
        
        default:
            # code...
            break;
    }
}
/**
 * Display the given type
 *
 * @param [Z3_context] $context
 * @param [Z3_sort] $type
 * @return void
 */
function display_sort($context, $type) {
    global $ffi;
    switch ($ffi->Z3_get_sort_kind($context, $type)) {
        case Z3_const::Z3_UNINTERPRETED_SORT:
            display_symbol($context, $ffi->Z3_get_sort_name($context, $type));
            break;
        case Z3_const::Z3_BOOL_SORT:
            echo 'bool';
            break;
        case Z3_const::Z3_INT_SORT:
            echo 'int';
            break;
        case Z3_const::Z3_REAL_SORT:
            echo 'real';
            break;
        case Z3_const::Z3_BV_SORT:
            echo 'bv' . $ffi->Z3_get_bv_sort_size($context, $type);
            break;
        case Z3_const::Z3_ARRAY_SORT:
            echo '[';
            display_sort($context, $ffi->Z3_get_array_sort_domain($context, $type));
            echo '->';
            display_sort($context, $ffi->Z3_get_array_sort_range($context, $type));
            echo ']';
            break;
        case Z3_const::Z3_DATATYPE_SORT:
            if ($ffi->Z3_get_datatype_sort_num_contructors($context, $type) !== 1) {
                echo $ffi->Z3_sort_to_string($context, $type);
                break;
            }
            $num_fields = $ffi->Z3_get_type_sort_num_fields($context, $type);
            echo '(';
            for ($i=0; $i < $num_fields; $i++) { 
                $field = $ffi->Z3_get_tuple_sort_field_dec($context, $type, $i);
                if ($i > 0) {
                    echo ',';
                }
                display_sort($context, $ffi->Z3_get_range($context, $field));
            }
            echo ')';
            break;
        default:
            echo 'unknown[';
            display_symbol($context, $ffi->Z3_get_sort_name($context, $type));
            echo ']';
            break;
    }
}
/**
 * Prove that the constraints already asserted into the logical
 * context implies the given formula.  The result of the proof is
 * displayed.

 * Z3 is a satisfiability checker. So, one can prove \c f by showing
 * that <tt>(not f)</tt> is unsatisfiable.

 * The context \c ctx is not modified by this function.
 *
 * @param [Z3_context] $context
 * @param [Z3_solver] $solver
 * @param [Z3_ast] $f
 * @param [bool] $is_valid
 * @return void
 */
function prove($context, $solver, $f, $is_valid) {
    global $ffi;
    // Save the current state of the context
    $ffi->Z3_solver_push($context, $solver);

    $not_f = $ffi->Z3_mk_not($context, $f);
    $ffi->Z3_solver_assert($context, $solver, $not_f);

    switch ($ffi->Z3_solver_check($context, $solver)) {
        case Z3_const::Z3_L_FALSE:
            // proved
            echo 'valid' . PHP_EOL;
            if (!$is_valid) {
                exitf('unexpected result');
            }
            break;
        case Z3_const::Z3_L_UNDEF:
            // Z3 failed to prove/disprove f
            echo 'unknown' . PHP_EOL;
            $model = $ffi->Z3_solver_get_model($context, $solver);
            if ($model !== 0) {
                $ffi->Z3_model_inc_ref($context, $model);
                // m should be viewed as a potential counterexample
                echo 'potential counterexample:' . PHP_EOL . $ffi->Z3_model_to_string($context, $model) . PHP_EOL;
            }
            if ($is_valid) {
                exitf('unexpected result');
            }
            break;
        case Z3_const::Z3_L_TRUE:
            // disproved
            echo 'invalid' . PHP_EOL;
            $model = $ffi->Z3_solver_get_model($context, $solver);
            if ($model !== 0) {
                $ffi->Z3_model_inc_ref($context, $model);
                // the model returned by Z3 is a counterexample
                echo 'counterexample:' . PHP_EOL . $ffi->Z3_model_to_string($context, $model) . PHP_EOL;
            }
            if ($is_valid) {
                exitf('unexpected result');
            }
            break; 
        default:
            break;
    }
    if (isset($model)) {
        $ffi->Z3_model_dec_ref($context, $model);
    }
    // restore the scope
    $ffi->Z3_solver_pop($context, $solver, 1);
}
/**
 * Assert the axiom: function f is injective in the i-th argument.
 * The following axiom is asserted into the logical context:
 * \code
 * forall (x_0, ..., x_n) finv(f(x_0, ..., x_i, ..., x_{n-1})) = x_i
 * \endcode
 * Where, \c finv is a fresh function declaration.
 *
 * @param [Z3_context] $context
 * @param [Z3_solver] $solver
 * @param [Z3_func_decl] $function
 * @param [unsigned] $i
 * @return void
 */
function assert_inj_axiom($context, $solver, $function, $i) {
    global $ffi;
    $sz = $ffi->Z3_get_domain_size($context, $function);

    if ($i >= $sz) {
        exitf('failed to create inj axiom');
    }

    // declare the i-th inverse of f: finv
    $finv_domain = $ffi->Z3_get_range($context, $function);
    $finv_range = $ffi->Z3_get_domain($context, $function, $i);
    $finv = $ffi->Z3_mk_fresh_func_decl($context, 'inv', 1, FFI::addr($finv_domain), $finv_range);

    // allocate temporary arrays
    for ($j=0; $j < $sz; $j++) { 
        $types[$j] = $ffi->Z3_get_domain($context, $function, $j);
    }
    $types = mk_1d_array('Z3_sort', $sz, $types);
    for ($j=0; $j < $sz; $j++) { 
        $names[$j] = $ffi->Z3_mk_int_symbol($context, $j);
    }
    $names = mk_1d_array('Z3_symbol', $sz, $names);
    for ($j=0; $j < $sz; $j++) { 
        $xs[$j] = $ffi->Z3_mk_bound($context, $j, $types[$j]);
    }
    $xs = mk_1d_array('Z3_ast', $sz, $xs);
    $x_i = $xs[$i];

    // create f(x_0, ..., x_i, ..., x_{n-1})
    $fxs = $ffi->Z3_mk_app($context, $function, $sz, $xs);
    // create f_inv(f(x_0, ..., x_i, ..., x_{n-1}))
    $finv_fxs = mk_unary_app($context, $finv, $fxs);
    // create finv(f(x_0, ..., x_i, ..., x_{n-1})) = x_i
    $eq = $ffi->Z3_mk_eq($context, $finv_fxs, $x_i);
    // use f(x_0, ..., x_i, ..., x_{n-1}) as the pattern for the quantifier
    $p = $ffi->Z3_mk_pattern($context, 1, FFI::addr($fxs));
    echo 'pattern: ' . $ffi->Z3_pattern_to_string($context, $p) . PHP_EOL . PHP_EOL;

    // create & assert quantifier
    $q = $ffi->Z3_mk_forall($context, 
                            0, // using default weight
                            1, // number of patterns
                            FFI::addr($p), // address of the "array" of patterns
                            $sz, // number of quantified variables
                            $types,
                            $names,
                            $eq);
    echo 'assert axiom:' . PHP_EOL . $ffi->Z3_ast_to_string($context, $q) . PHP_EOL;
    $ffi->Z3_solver_assert($context, $solver, $q);
}
/**
 * Display a symbol
 *
 * @param [Z3_context] $context
 * @param [Z3_symbol] $symbol
 * @return void
 */
function display_symbol($context, $symbol) {
    global $ffi;
    switch ($ffi->Z3_get_symbol_kind($context, $symbol)) {
        case Z3_const::Z3_INT_SYMBOL:
            echo '#' . $ffi->Z3_get_symbol_int($context, $symbol);
            break;
        case Z3_const::Z3_STRING_SYMBOL:
            echo $ffi->Z3_get_symbol_string($context, $symbol);
            break;
        default:
            unreachable();
    }
}
/**
 * Display Z3 version
 *
 * @return void
 */
function display_version() {
    global $ffi;
    $major = FFI::new('unsigned');
    $minor = FFI::new('unsigned');
    $build = FFI::new('unsigned');
    $revision = FFI::new('unsigned');
    $ffi->Z3_get_version(FFI::addr($major), FFI::addr($minor), FFI::addr($build), FFI::addr($revision));
    echo 'Z3 ' . $major . '.' . $minor . '.' . $build . '.' . $revision . PHP_EOL;
}

/**
 * Examples
 */

function simple_example() {
    global $ffi;
    echo 'simple example' . PHP_EOL;
    $context = mk_context();
    // delete logical context
    $ffi->Z3_del_context($context);
}
/**
 * Demonstration of how Z3 can be used to prove validity of
 * De Morgan's Duality Law: {e not(x and y) <-> (not x) or ( not y) }
 *
 * @return void
 */
function demorgan() {
    global $ffi;
    echo 'DeMorgan' . PHP_EOL;
    $config = $ffi->Z3_mk_config();
    $context = $ffi->Z3_mk_context($config);
    $ffi->Z3_del_config($config);
    $bool_sort = $ffi->Z3_mk_bool_sort($context);
    $symbol_x = $ffi->Z3_mk_int_symbol($context, 0);
    $symbol_y = $ffi->Z3_mk_int_symbol($context, 1);
    $x = $ffi->Z3_mk_const($context, $symbol_x, $bool_sort);
    $y = $ffi->Z3_mk_const($context, $symbol_y, $bool_sort);

    // De Morgan - with a negation around
    // !(!(x && y) <-> (!x || !y))
    $not_x = $ffi->Z3_mk_not($context, $x);
    $not_y = $ffi->Z3_mk_not($context, $y);
    // // Create Z3_ast[2] type
    // $arg_type = FFI::arrayType($ffi->type('Z3_ast'), [2]);
    // // Create array of type Z3_ast[2]
    // $args = FFI::new($arg_type);
    // // Populate the array
    // $args[0] = $x;
    // $args[1] = $y;
    $args = mk_1d_array('Z3_ast', 2, [$x, $y]);
    $x_and_y = $ffi->Z3_mk_and($context, 2, $args);
    $ls = $ffi->Z3_mk_not($context, $x_and_y);
    $args[0] = $not_x;
    $args[1] = $not_y;
    $rs = $ffi->Z3_mk_or($context, 2, $args);
    $conjecture = $ffi->Z3_mk_iff($context, $ls, $rs);
    $negated_conejcture = $ffi->Z3_mk_not($context, $conjecture);

    $solver = mk_solver($context);
    $ffi->Z3_solver_assert($context, $solver, $negated_conejcture);
    switch ($ffi->Z3_solver_check($context, $solver)) {
        case Z3_const::Z3_L_FALSE:
            // The negated conjecture was unsatisfiable, hence the conjecture is valid
            echo 'DeMorgan is valid' . PHP_EOL;
            break;
        case Z3_const::Z3_L_UNDEF:
            // Check returned undef
            echo 'Undef' . PHP_EOL;
            break;
        case Z3_const::Z3_L_TRUE:
            // The negated conjecture was satisfiable, hence the conjecture is not valid
            echo 'DeMorgan is not valid' . PHP_EOL;
        default:
            break;
    }
    del_solver($context, $solver);
    $ffi->Z3_del_context($context);
}
/**
 * Find a model for <tt>x xor y</tt>.
 *
 * @return void
 */
function find_model_example1() {
    global $ffi;
    echo 'find_model_example1' . PHP_EOL;

    $context = mk_context();
    $solver = mk_solver($context);

    $x = mk_bool_var($context, 'x');
    $y = mk_bool_var($context, 'y');
    $x_xor_y = $ffi->Z3_mk_xor($context, $x, $y);
    $ffi->Z3_solver_assert($context, $solver, $x_xor_y);

    echo 'model for x xor y' . PHP_EOL;
    check($context, $solver, Z3_const::Z3_L_TRUE);

    del_solver($context, $solver);
    $ffi->Z3_del_context($context);
}
/**
 * Find a model for <tt>x < y + 1, x > 2</tt>.
 * Then, assert <tt>not(x = y)</tt>, and find another model.
 *
 * @return void
 */
function find_model_example2() {
    global $ffi;
    echo 'find_model_example2' . PHP_EOL;

    $context = mk_context();
    $solver = mk_solver($context);
    $x = mk_int_var($context, 'x');
    $y = mk_int_var($context, 'y');
    $one = mk_int($context, 1);
    $two = mk_int($context, 2);
    
    $args = mk_1d_array('Z3_ast', 2, [$y, $one]);
    $y_plus_one = $ffi->Z3_mk_add($context, 2, $args);

    $c1 = $ffi->Z3_mk_lt($context, $x, $y_plus_one);
    $c2 = $ffi->Z3_mk_gt($context, $x, $two);

    $ffi->Z3_solver_assert($context, $solver, $c1);
    $ffi->Z3_solver_assert($context, $solver, $c2);

    echo 'model for: x < y + 1, x > 2 ' . PHP_EOL;
    check($context, $solver, Z3_const::Z3_L_TRUE);

    // assert not(x = y)
    $x_eq_y = $ffi->Z3_mk_eq($context, $x, $y);
    $c3 = $ffi->Z3_mk_not($context, $x_eq_y);
    $ffi->Z3_solver_assert($context, $solver, $c3);

    echo 'model for: x < y + 1, x > 2, not(x = y)' . PHP_EOL;
    check($context, $solver, Z3_const::Z3_L_TRUE);

    del_solver($context, $solver);
    $ffi->Z3_del_context($context);

}

function prove_example1() {
    global $ffi;
    echo 'prove_example1' . PHP_EOL;

    $context = mk_context();
    $solver = mk_solver($context);

    // create uninterpreted type
    $U_name = $ffi->Z3_mk_string_symbol($context, 'U');
    $U = $ffi->Z3_mk_uninterpreted_sort($context, $U_name);

    // declare function g
    $g_name = $ffi->Z3_mk_string_symbol($context, 'g');
    $g_domain = mk_1d_array('Z3_sort', 1, $U);
    $g = $ffi->Z3_mk_func_decl($context, $g_name, 1, $g_domain, $U);

    // create x and y
    $x_name = $ffi->Z3_mk_string_symbol($context, 'x');
    $y_name = $ffi->Z3_mk_string_symbol($context, 'y');
    $x = $ffi->Z3_mk_const($context, $x_name, $U);
    $y = $ffi->Z3_mk_const($context, $y_name, $U);
    // create g(x), g(y)
    $gx = mk_unary_app($context, $g, $x);
    $gy = mk_unary_app($context, $g, $y);
    // assert x = y
    $eq = $ffi->Z3_mk_eq($context, $x, $y);
    $ffi->Z3_solver_assert($context, $solver, $eq);

    // prove g(x) = g(y)
    $f = $ffi->Z3_mk_eq($context, $gx, $gy);
    echo 'prove: x = y implies g(x) = g(y)' . PHP_EOL;
    prove($context, $solver, $f, true);

    // create g(g(x))
    $ggx = mk_unary_app($context, $g, $gx);

    // disprove g(g(x)) = g(y)
    $f = $ffi->Z3_mk_eq($context, $ggx, $gy);
    echo 'disprove: x = y implies g(g(x)) = g(y)' . PHP_EOL;
    prove($context, $solver, $f, false);

    del_solver($context, $solver);
    $ffi->Z3_del_context($context);
}

function prove_example2() {
    global $ffi;
    echo 'prove_example2' . PHP_EOL;

    $context = mk_context();
    $solver = mk_solver($context);

    // declare function g
    $int_sort = $ffi->Z3_mk_int_sort($context);
    $g_name = $ffi->Z3_mk_string_symbol($context, 'g');
    $g_domain = mk_1d_array('Z3_sort', 1, $int_sort);
    $g = $ffi->Z3_mk_func_decl($context, $g_name, 1, $g_domain, $int_sort);

    // create x, y, z
    $x = mk_int_var($context, 'x');
    $y = mk_int_var($context, 'y');
    $z = mk_int_var($context, 'z');

    // create gx, gy, gz
    $gx = mk_unary_app($context, $g, $x);
    $gy = mk_unary_app($context, $g, $y);
    $gz = mk_unary_app($context, $g, $z);

    // create zero
    $zero = mk_int($context, 0);

    // assert not(g(g(x) - g(y)) = g(z))
    $args = mk_1d_array('Z3_ast', 2, [$gx, $gy]);
    $gx_gy = $ffi->Z3_mk_sub($context, 2, $args);
    $ggx_gy = mk_unary_app($context, $g, $gx_gy);
    $eq = $ffi->Z3_mk_eq($context, $ggx_gy, $gz);
    $c1 = $ffi->Z3_mk_not($context, $eq);
    $ffi->Z3_solver_assert($context, $solver, $c1);

    // assert x + z <= y
    $args = mk_1d_array('Z3_ast', 2, [$x, $z]);
    $x_plus_z = $ffi->Z3_mk_add($context, 2, $args);
    $c2 = $ffi->Z3_mk_le($context, $x_plus_z, $y);
    $ffi->Z3_solver_assert($context, $solver, $c2);

    // assert y <= x
    $c3 = $ffi->Z3_mk_le($context, $y, $x);
    $ffi->Z3_solver_assert($context, $solver, $c3);

    // prove z < 0
    $f = $ffi->Z3_mk_lt($context, $z, $zero);
    echo 'prove not(g(gx) - g(y)) = g(z)), x + z <= y <= x implies z < 0' . PHP_EOL;
    prove($context, $solver, $f, true);

    // disprove z < -1
    $minus_one = mk_int($context, -1);
    $f = $ffi->Z3_mk_lt($context, $z, $minus_one);
    echo 'disprove: not(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < -1' . PHP_EOL;
    prove($context, $solver, $f, false);

    del_solver($context, $solver);
    $ffi->Z3_del_context($context);
}
/**
 * Show how push & pop can be used to create "backtracking" points.
 * This example also demonstrates how big numbers can be created in Z3.
 *
 * @return void
 */
function push_pop_example1() {
    global $ffi;
    echo 'push_pop_example1' . PHP_EOL;

    $context = mk_context();
    $solver = mk_solver($context);

    // create a big number
    $int_sort = $ffi->Z3_mk_int_sort($context);
    $big_number = $ffi->Z3_mk_numeral($context, '1000000000000000000000000000000000000000000000000000000', $int_sort);

    // create number 3
    $three = $ffi->Z3_mk_numeral($context, '3', $int_sort);

    // create x
    $x_sym = $ffi->Z3_mk_string_symbol($context, 'x');
    $x = $ffi->Z3_mk_const($context, $x_sym, $int_sort);

    // assert x >= "big number"
    $c1 = $ffi->Z3_mk_ge($context, $x, $big_number);
    $ffi->Z3_solver_assert($context, $solver, $c1);

    // create a backtracking point
    echo 'push' . PHP_EOL;
    $ffi->Z3_solver_push($context, $solver);

    echo 'number of scopes: ' . $ffi->Z3_solver_get_num_scopes($context, $solver) . PHP_EOL;

    // assert x <= 3
    $c2 = $ffi->Z3_mk_le($context, $x, $three);
    echo 'assert: x <= 3' . PHP_EOL;
    $ffi->Z3_solver_assert($context, $solver, $c2);

    // context is inconsistent at this point
    check2($context, $solver, Z3_const::Z3_L_FALSE);
}
/**
 * Prove that <tt>f(x, y) = f(w, v) implies y = v</tt> when
 * f is injective in the second argument.
 *
 * @return void
 */
function quantifier_example1() {
    global $ffi;
    global $error_handler;
    echo 'quantifier_example' . PHP_EOL;
    $config = $ffi->Z3_mk_config();
    /* If quantified formulas are asserted in a logical context, then
       Z3 may return L_UNDEF. In this case, the model produced by Z3 should be viewed as a potential/candidate model.
    */

    /*
       The current model finder for quantified formulas cannot handle injectivity.
       So, we are limiting the number of iterations to avoid a long "wait".
    */
    $ffi->Z3_global_param_set('smt.mbqi.max_iterations', '10');
    $context = mk_context_custom($config, $error_handler);
    $ffi->Z3_del_config($config);
    $solver = mk_solver($context);

    // declare function f
    $int_sort = $ffi->Z3_mk_int_sort($context);
    $f_name = $ffi->Z3_mk_string_symbol($context, 'f');
    $f_domain = mk_1d_array('Z3_sort', 2, [$int_sort, $int_sort]);
    $f = $ffi->Z3_mk_func_decl($context, $f_name, 2, $f_domain, $int_sort);

    // assert that f is injective in the second argument
    assert_inj_axiom($context, $solver, $f, 1);

    // create x, y, v, w, fxy, fwv
    $x = mk_int_var($context, 'x');
    $y = mk_int_var($context, 'y');
    $v = mk_int_var($context, 'v');
    $w = mk_int_var($context, 'w');
    $fxy = mk_binary_app($context, $f, $x, $y);
    $fwv = mk_binary_app($context, $f, $w, $v);

    // assert f(x, y) = f(w, v)
    $p1 = $ffi->Z3_mk_eq($context, $fxy, $fwv);
    $ffi->Z3_solver_assert($context, $solver, $p1);

    // prove f(x, y) = f(w, v) implies y = v
    $p2 = $ffi->Z3_mk_eq($context, $y, $v);
    echo 'prove: f(x, y) = f(w, v) implies y = v' . PHP_EOL;
    prove($context, $solver, $p2, true);

    // disprove f(x, y) = f(w, v) implies x = w
    // using check2 instead of prove
    $p3 = $ffi->Z3_mk_eq($context, $x, $w);
    $not_p3 = $ffi->Z3_mk_not($context, $p3);
    $ffi->Z3_solver_assert($context, $solver, $not_p3);
    echo 'disprove: f(x, y) = f(w, v) implies x = w' . PHP_EOL;
    echo 'that is: not(f(x, y) = f(w, v) implies x = w) is satisfiable' . PHP_EOL;
    check2($context, $solver, Z3_const::Z3_L_UNDEF);
    echo 'reason for last failure: ' . $ffi->Z3_solver_get_reason_unknown($context, $solver) . PHP_EOL;
    del_solver($context, $solver);
    $ffi->Z3_del_context($context);
    // reset global parameters set by this function
    $ffi->Z3_global_param_reset_all();
}

function main() {
    display_version();
    simple_example();
    demorgan();
    find_model_example1();
    find_model_example2();
    prove_example1();
    prove_example2();
    push_pop_example1();
    quantifier_example1();
}

main();