// Replace Z3_boolـopt with Z3_bool
// Replace Z3_sort_opt with Z3_sort
// Replace Z3_ast_opt with Z3_ast
// Replace Z3_func_interp_opt with Z3_func_interp

typedef struct _Z3_symbol *Z3_symbol;
typedef struct _Z3_literals *Z3_literals;
typedef struct _Z3_config *Z3_config;
typedef struct _Z3_context *Z3_context;
typedef struct _Z3_sort *Z3_sort;
typedef struct _Z3_func_decl *Z3_func_decl;
typedef struct _Z3_ast *Z3_ast;
typedef struct _Z3_app *Z3_app;
typedef struct _Z3_pattern *Z3_pattern;
typedef struct _Z3_model *Z3_model;
typedef struct _Z3_constructor *Z3_constructor;
typedef struct _Z3_constructor_list *Z3_constructor_list;
typedef struct _Z3_params *Z3_params;
typedef struct _Z3_param_descrs *Z3_param_descrs;
typedef struct _Z3_goal *Z3_goal;
typedef struct _Z3_tactic *Z3_tactic;
typedef struct _Z3_probe *Z3_probe;
typedef struct _Z3_stats *Z3_stats;
typedef struct _Z3_solver *Z3_solver;
typedef struct _Z3_ast_vector *Z3_ast_vector;
typedef struct _Z3_ast_map *Z3_ast_map;
typedef struct _Z3_apply_result *Z3_apply_result;
typedef struct _Z3_func_interp *Z3_func_interp;
typedef struct _Z3_func_entry *Z3_func_entry;
typedef struct _Z3_fixedpoint *Z3_fixedpoint;
typedef struct _Z3_optimize *Z3_optimize;
typedef struct _Z3_rcf_num *Z3_rcf_num;

/**
   \brief Z3 Boolean type. It is just an alias for \c bool.
*/
typedef bool Z3_bool;
/**
   \brief Z3 string type. It is just an alias for \ccode{const char *}.
*/
typedef const char * Z3_string;
typedef Z3_string * Z3_string_ptr;

/**
   \brief Lifted Boolean type: \c false, \c undefined, \c true.
*/
typedef enum
{
    Z3_L_FALSE = -1,
    Z3_L_UNDEF,
    Z3_L_TRUE
} Z3_lbool;

/**
   \brief The different kinds of symbol.
   In Z3, a symbol can be represented using integers and strings (See #Z3_get_symbol_kind).

   \sa Z3_mk_int_symbol
   \sa Z3_mk_string_symbol
*/
typedef enum
{
    Z3_INT_SYMBOL,
    Z3_STRING_SYMBOL
} Z3_symbol_kind;

/**
   \brief The different kinds of parameters that can be associated with function symbols.
   \sa Z3_get_decl_num_parameters
   \sa Z3_get_decl_parameter_kind

   - Z3_PARAMETER_INT is used for integer parameters.
   - Z3_PARAMETER_DOUBLE is used for double parameters.
   - Z3_PARAMETER_RATIONAL is used for parameters that are rational numbers.
   - Z3_PARAMETER_SYMBOL is used for parameters that are symbols.
   - Z3_PARAMETER_SORT is used for sort parameters.
   - Z3_PARAMETER_AST is used for expression parameters.
   - Z3_PARAMETER_FUNC_DECL is used for function declaration parameters.
*/
typedef enum
{
    Z3_PARAMETER_INT,
    Z3_PARAMETER_DOUBLE,
    Z3_PARAMETER_RATIONAL,
    Z3_PARAMETER_SYMBOL,
    Z3_PARAMETER_SORT,
    Z3_PARAMETER_AST,
    Z3_PARAMETER_FUNC_DECL
} Z3_parameter_kind;

/**
   \brief The different kinds of Z3 types (See #Z3_get_sort_kind).
*/
typedef enum
{
    Z3_UNINTERPRETED_SORT,
    Z3_BOOL_SORT,
    Z3_INT_SORT,
    Z3_REAL_SORT,
    Z3_BV_SORT,
    Z3_ARRAY_SORT,
    Z3_DATATYPE_SORT,
    Z3_RELATION_SORT,
    Z3_FINITE_DOMAIN_SORT,
    Z3_FLOATING_POINT_SORT,
    Z3_ROUNDING_MODE_SORT,
    Z3_SEQ_SORT,
    Z3_RE_SORT,
    Z3_UNKNOWN_SORT = 1000
} Z3_sort_kind;

/**
   \brief
   The different kinds of Z3 AST (abstract syntax trees). That is, terms, formulas and types.

   - Z3_APP_AST:            constant and applications
   - Z3_NUMERAL_AST:        numeral constants
   - Z3_VAR_AST:            bound variables
   - Z3_QUANTIFIER_AST:     quantifiers
   - Z3_SORT_AST:           sort
   - Z3_FUNC_DECL_AST:      function declaration
   - Z3_UNKNOWN_AST:        internal
*/
typedef enum
{
    Z3_NUMERAL_AST,
    Z3_APP_AST,
    Z3_VAR_AST,
    Z3_QUANTIFIER_AST,
    Z3_SORT_AST,
    Z3_FUNC_DECL_AST,
    Z3_UNKNOWN_AST = 1000
} Z3_ast_kind;

/**
   \brief The different kinds of interpreted function kinds.

   - Z3_OP_TRUE The constant true.

   - Z3_OP_FALSE The constant false.

   - Z3_OP_EQ The equality predicate.

   - Z3_OP_DISTINCT The n-ary distinct predicate (every argument is mutually distinct).

   - Z3_OP_ITE The ternary if-then-else term.

   - Z3_OP_AND n-ary conjunction.

   - Z3_OP_OR n-ary disjunction.

   - Z3_OP_IFF equivalence (binary).

   - Z3_OP_XOR Exclusive or.

   - Z3_OP_NOT Negation.

   - Z3_OP_IMPLIES Implication.

   - Z3_OP_OEQ Binary equivalence modulo namings. This binary predicate is used in proof terms.
        It captures equisatisfiability and equivalence modulo renamings.

   - Z3_OP_ANUM Arithmetic numeral.

   - Z3_OP_AGNUM Arithmetic algebraic numeral. Algebraic numbers are used to represent irrational numbers in Z3.

   - Z3_OP_LE <=.

   - Z3_OP_GE >=.

   - Z3_OP_LT <.

   - Z3_OP_GT >.

   - Z3_OP_ADD Addition - Binary.

   - Z3_OP_SUB Binary subtraction.

   - Z3_OP_UMINUS Unary minus.

   - Z3_OP_MUL Multiplication - Binary.

   - Z3_OP_DIV Division - Binary.

   - Z3_OP_IDIV Integer division - Binary.

   - Z3_OP_REM Remainder - Binary.

   - Z3_OP_MOD Modulus - Binary.

   - Z3_OP_TO_REAL Coercion of integer to real - Unary.

   - Z3_OP_TO_INT Coercion of real to integer - Unary.

   - Z3_OP_IS_INT Check if real is also an integer - Unary.

   - Z3_OP_POWER Power operator x^y.

   - Z3_OP_STORE Array store. It satisfies select(store(a,i,v),j) = if i = j then v else select(a,j).
        Array store takes at least 3 arguments.

   - Z3_OP_SELECT Array select.

   - Z3_OP_CONST_ARRAY The constant array. For example, select(const(v),i) = v holds for every v and i. The function is unary.

   - Z3_OP_ARRAY_DEFAULT Default value of arrays. For example default(const(v)) = v. The function is unary.

   - Z3_OP_ARRAY_MAP Array map operator.
         It satisfies map[f](a1,..,a_n)[i] = f(a1[i],...,a_n[i]) for every i.

   - Z3_OP_SET_UNION Set union between two Boolean arrays (two arrays whose range type is Boolean). The function is binary.

   - Z3_OP_SET_INTERSECT Set intersection between two Boolean arrays. The function is binary.

   - Z3_OP_SET_DIFFERENCE Set difference between two Boolean arrays. The function is binary.

   - Z3_OP_SET_COMPLEMENT Set complement of a Boolean array. The function is unary.

   - Z3_OP_SET_SUBSET Subset predicate between two Boolean arrays. The relation is binary.

   - Z3_OP_AS_ARRAY An array value that behaves as the function graph of the
                    function passed as parameter.

   - Z3_OP_ARRAY_EXT Array extensionality function. It takes two arrays as arguments and produces an index, such that the arrays
                    are different if they are different on the index.

   - Z3_OP_BNUM Bit-vector numeral.

   - Z3_OP_BIT1 One bit bit-vector.

   - Z3_OP_BIT0 Zero bit bit-vector.

   - Z3_OP_BNEG Unary minus.

   - Z3_OP_BADD Binary addition.

   - Z3_OP_BSUB Binary subtraction.

   - Z3_OP_BMUL Binary multiplication.

   - Z3_OP_BSDIV Binary signed division.

   - Z3_OP_BUDIV Binary unsigned division.

   - Z3_OP_BSREM Binary signed remainder.

   - Z3_OP_BUREM Binary unsigned remainder.

   - Z3_OP_BSMOD Binary signed modulus.

   - Z3_OP_BSDIV0 Unary function. bsdiv(x,0) is congruent to bsdiv0(x).

   - Z3_OP_BUDIV0 Unary function. budiv(x,0) is congruent to budiv0(x).

   - Z3_OP_BSREM0 Unary function. bsrem(x,0) is congruent to bsrem0(x).

   - Z3_OP_BUREM0 Unary function. burem(x,0) is congruent to burem0(x).

   - Z3_OP_BSMOD0 Unary function. bsmod(x,0) is congruent to bsmod0(x).

   - Z3_OP_ULEQ Unsigned bit-vector <= - Binary relation.

   - Z3_OP_SLEQ Signed bit-vector  <= - Binary relation.

   - Z3_OP_UGEQ Unsigned bit-vector  >= - Binary relation.

   - Z3_OP_SGEQ Signed bit-vector  >= - Binary relation.

   - Z3_OP_ULT Unsigned bit-vector  < - Binary relation.

   - Z3_OP_SLT Signed bit-vector < - Binary relation.

   - Z3_OP_UGT Unsigned bit-vector > - Binary relation.

   - Z3_OP_SGT Signed bit-vector > - Binary relation.

   - Z3_OP_BAND Bit-wise and - Binary.

   - Z3_OP_BOR Bit-wise or - Binary.

   - Z3_OP_BNOT Bit-wise not - Unary.

   - Z3_OP_BXOR Bit-wise xor - Binary.

   - Z3_OP_BNAND Bit-wise nand - Binary.

   - Z3_OP_BNOR Bit-wise nor - Binary.

   - Z3_OP_BXNOR Bit-wise xnor - Binary.

   - Z3_OP_CONCAT Bit-vector concatenation - Binary.

   - Z3_OP_SIGN_EXT Bit-vector sign extension.

   - Z3_OP_ZERO_EXT Bit-vector zero extension.

   - Z3_OP_EXTRACT Bit-vector extraction.

   - Z3_OP_REPEAT Repeat bit-vector n times.

   - Z3_OP_BREDOR Bit-vector reduce or - Unary.

   - Z3_OP_BREDAND Bit-vector reduce and - Unary.

   - Z3_OP_BCOMP .

   - Z3_OP_BSHL Shift left.

   - Z3_OP_BLSHR Logical shift right.

   - Z3_OP_BASHR Arithmetical shift right.

   - Z3_OP_ROTATE_LEFT Left rotation.

   - Z3_OP_ROTATE_RIGHT Right rotation.

   - Z3_OP_EXT_ROTATE_LEFT (extended) Left rotation. Similar to Z3_OP_ROTATE_LEFT, but it is a binary operator instead of a parametric one.

   - Z3_OP_EXT_ROTATE_RIGHT (extended) Right rotation. Similar to Z3_OP_ROTATE_RIGHT, but it is a binary operator instead of a parametric one.

   - Z3_OP_INT2BV Coerce integer to bit-vector. NB. This function
       is not supported by the decision procedures. Only the most
       rudimentary simplification rules are applied to this function.

   - Z3_OP_BV2INT Coerce bit-vector to integer. NB. This function
       is not supported by the decision procedures. Only the most
       rudimentary simplification rules are applied to this function.

   - Z3_OP_CARRY Compute the carry bit in a full-adder.
       The meaning is given by the equivalence
       (carry l1 l2 l3) <=> (or (and l1 l2) (and l1 l3) (and l2 l3)))

   - Z3_OP_XOR3 Compute ternary XOR.
       The meaning is given by the equivalence
       (xor3 l1 l2 l3) <=> (xor (xor l1 l2) l3)

   - Z3_OP_BSMUL_NO_OVFL: a predicate to check that bit-wise signed multiplication does not overflow.
     Signed multiplication overflows if the operands have the same sign and the result of multiplication
     does not fit within the available bits. \sa Z3_mk_bvmul_no_overflow.

   - Z3_OP_BUMUL_NO_OVFL: check that bit-wise unsigned multiplication does not overflow.
     Unsigned multiplication overflows if the result does not fit within the available bits.
     \sa Z3_mk_bvmul_no_overflow.

   - Z3_OP_BSMUL_NO_UDFL: check that bit-wise signed multiplication does not underflow.
     Signed multiplication underflows if the operands have opposite signs and the result of multiplication
     does not fit within the available bits. Z3_mk_bvmul_no_underflow.

   - Z3_OP_BSDIV_I: Binary signed division.
     It has the same semantics as Z3_OP_BSDIV, but created in a context where the second operand can be assumed to be non-zero.

   - Z3_OP_BUDIV_I: Binary unsigned division.
     It has the same semantics as Z3_OP_BUDIV, but created in a context where the second operand can be assumed to be non-zero.

   - Z3_OP_BSREM_I: Binary signed remainder.
     It has the same semantics as Z3_OP_BSREM, but created in a context where the second operand can be assumed to be non-zero.

   - Z3_OP_BUREM_I: Binary unsigned remainder.
     It has the same semantics as Z3_OP_BUREM, but created in a context where the second operand can be assumed to be non-zero.

   - Z3_OP_BSMOD_I: Binary signed modulus.
     It has the same semantics as Z3_OP_BSMOD, but created in a context where the second operand can be assumed to be non-zero.

   - Z3_OP_PR_UNDEF: Undef/Null proof object.

   - Z3_OP_PR_TRUE: Proof for the expression 'true'.

   - Z3_OP_PR_ASSERTED: Proof for a fact asserted by the user.

   - Z3_OP_PR_GOAL: Proof for a fact (tagged as goal) asserted by the user.

   - Z3_OP_PR_MODUS_PONENS: Given a proof for p and a proof for (implies p q), produces a proof for q.
       \nicebox{
          T1: p
          T2: (implies p q)
          [mp T1 T2]: q
          }
          The second antecedents may also be a proof for (iff p q).

   - Z3_OP_PR_REFLEXIVITY: A proof for (R t t), where R is a reflexive relation. This proof object has no antecedents.
        The only reflexive relations that are used are
        equivalence modulo namings, equality and equivalence.
        That is, R is either '~', '=' or 'iff'.

   - Z3_OP_PR_SYMMETRY: Given an symmetric relation R and a proof for (R t s), produces a proof for (R s t).
          \nicebox{
          T1: (R t s)
          [symmetry T1]: (R s t)
          }
          T1 is the antecedent of this proof object.

   - Z3_OP_PR_TRANSITIVITY: Given a transitive relation R, and proofs for (R t s) and (R s u), produces a proof
       for (R t u).
       \nicebox{
       T1: (R t s)
       T2: (R s u)
       [trans T1 T2]: (R t u)
       }

   - Z3_OP_PR_TRANSITIVITY_STAR: Condensed transitivity proof. 
     It combines several symmetry and transitivity proofs.

          Example:
          \nicebox{
          T1: (R a b)
          T2: (R c b)
          T3: (R c d)
          [trans* T1 T2 T3]: (R a d)
          }
          R must be a symmetric and transitive relation.

          Assuming that this proof object is a proof for (R s t), then
          a proof checker must check if it is possible to prove (R s t)
          using the antecedents, symmetry and transitivity.  That is,
          if there is a path from s to t, if we view every
          antecedent (R a b) as an edge between a and b.

   - Z3_OP_PR_MONOTONICITY: Monotonicity proof object.
          \nicebox{
          T1: (R t_1 s_1)
          ...
          Tn: (R t_n s_n)
          [monotonicity T1 ... Tn]: (R (f t_1 ... t_n) (f s_1 ... s_n))
          }
          Remark: if t_i == s_i, then the antecedent Ti is suppressed.
          That is, reflexivity proofs are suppressed to save space.

   - Z3_OP_PR_QUANT_INTRO: Given a proof for (~ p q), produces a proof for (~ (forall (x) p) (forall (x) q)).

       T1: (~ p q)
       [quant-intro T1]: (~ (forall (x) p) (forall (x) q))

   - Z3_OP_PR_BIND: Given a proof p, produces a proof of lambda x . p, where x are free variables in p.
       T1: f
       [proof-bind T1] forall (x) f

   - Z3_OP_PR_DISTRIBUTIVITY: Distributivity proof object.
          Given that f (= or) distributes over g (= and), produces a proof for

          (= (f a (g c d))
             (g (f a c) (f a d)))

          If f and g are associative, this proof also justifies the following equality:

          (= (f (g a b) (g c d))
             (g (f a c) (f a d) (f b c) (f b d)))

          where each f and g can have arbitrary number of arguments.

          This proof object has no antecedents.
          Remark. This rule is used by the CNF conversion pass and
          instantiated by f = or, and g = and.

   - Z3_OP_PR_AND_ELIM: Given a proof for (and l_1 ... l_n), produces a proof for l_i

       \nicebox{
       T1: (and l_1 ... l_n)
       [and-elim T1]: l_i
       }
   - Z3_OP_PR_NOT_OR_ELIM: Given a proof for (not (or l_1 ... l_n)), produces a proof for (not l_i).

       \nicebox{
       T1: (not (or l_1 ... l_n))
       [not-or-elim T1]: (not l_i)
       }

   - Z3_OP_PR_REWRITE: A proof for a local rewriting step (= t s).
          The head function symbol of t is interpreted.

          This proof object has no antecedents.
          The conclusion of a rewrite rule is either an equality (= t s),
          an equivalence (iff t s), or equi-satisfiability (~ t s).
          Remark: if f is bool, then = is iff.


          Examples:
          \nicebox{
          (= (+ x 0) x)
          (= (+ x 1 2) (+ 3 x))
          (iff (or x false) x)
          }

   - Z3_OP_PR_REWRITE_STAR: A proof for rewriting an expression t into an expression s.
       This proof object can have n antecedents.
       The antecedents are proofs for equalities used as substitution rules.
       The proof rule is used in a few cases. The cases are:
         - When applying contextual simplification (CONTEXT_SIMPLIFIER=true)
         - When converting bit-vectors to Booleans (BIT2BOOL=true)

   - Z3_OP_PR_PULL_QUANT: A proof for (iff (f (forall (x) q(x)) r) (forall (x) (f (q x) r))). This proof object has no antecedents.

   - Z3_OP_PR_PUSH_QUANT: A proof for:

       \nicebox{
          (iff (forall (x_1 ... x_m) (and p_1[x_1 ... x_m] ... p_n[x_1 ... x_m]))
               (and (forall (x_1 ... x_m) p_1[x_1 ... x_m])
                 ...
               (forall (x_1 ... x_m) p_n[x_1 ... x_m])))
               }
         This proof object has no antecedents.

   - Z3_OP_PR_ELIM_UNUSED_VARS:
          A proof for (iff (forall (x_1 ... x_n y_1 ... y_m) p[x_1 ... x_n])
                           (forall (x_1 ... x_n) p[x_1 ... x_n]))

          It is used to justify the elimination of unused variables.
          This proof object has no antecedents.

   - Z3_OP_PR_DER: A proof for destructive equality resolution:
          (iff (forall (x) (or (not (= x t)) P[x])) P[t])
          if x does not occur in t.

          This proof object has no antecedents.

          Several variables can be eliminated simultaneously.

   - Z3_OP_PR_QUANT_INST: A proof of (or (not (forall (x) (P x))) (P a))

   - Z3_OP_PR_HYPOTHESIS: Mark a hypothesis in a natural deduction style proof.

   - Z3_OP_PR_LEMMA:

       \nicebox{
          T1: false
          [lemma T1]: (or (not l_1) ... (not l_n))
          }
          This proof object has one antecedent: a hypothetical proof for false.
          It converts the proof in a proof for (or (not l_1) ... (not l_n)),
          when T1 contains the open hypotheses: l_1, ..., l_n.
          The hypotheses are closed after an application of a lemma.
          Furthermore, there are no other open hypotheses in the subtree covered by
          the lemma.

   - Z3_OP_PR_UNIT_RESOLUTION:
       \nicebox{
          T1:      (or l_1 ... l_n l_1' ... l_m')
          T2:      (not l_1)
          ...
          T(n+1):  (not l_n)
          [unit-resolution T1 ... T(n+1)]: (or l_1' ... l_m')
          }

   - Z3_OP_PR_IFF_TRUE:
      \nicebox{
       T1: p
       [iff-true T1]: (iff p true)
       }

   - Z3_OP_PR_IFF_FALSE:
      \nicebox{
       T1: (not p)
       [iff-false T1]: (iff p false)
       }

   - Z3_OP_PR_COMMUTATIVITY:

          [comm]: (= (f a b) (f b a))

          f is a commutative operator.

          This proof object has no antecedents.
          Remark: if f is bool, then = is iff.

   - Z3_OP_PR_DEF_AXIOM: Proof object used to justify Tseitin's like axioms:

          \nicebox{
          (or (not (and p q)) p)
          (or (not (and p q)) q)
          (or (not (and p q r)) p)
          (or (not (and p q r)) q)
          (or (not (and p q r)) r)
          ...
          (or (and p q) (not p) (not q))
          (or (not (or p q)) p q)
          (or (or p q) (not p))
          (or (or p q) (not q))
          (or (not (iff p q)) (not p) q)
          (or (not (iff p q)) p (not q))
          (or (iff p q) (not p) (not q))
          (or (iff p q) p q)
          (or (not (ite a b c)) (not a) b)
          (or (not (ite a b c)) a c)
          (or (ite a b c) (not a) (not b))
          (or (ite a b c) a (not c))
          (or (not (not a)) (not a))
          (or (not a) a)
          }
          This proof object has no antecedents.
          Note: all axioms are propositional tautologies.
          Note also that 'and' and 'or' can take multiple arguments.
          You can recover the propositional tautologies by
          unfolding the Boolean connectives in the axioms a small
          bounded number of steps (=3).

   - Z3_OP_PR_ASSUMPTION_ADD
     Clausal proof adding axiom

   - Z3_OP_PR_LEMMA_ADD
     Clausal proof lemma addition

   - Z3_OP_PR_REDUNDANT_DEL
     Clausal proof lemma deletion

   - Z3_OP_PR_CLAUSE_TRAIL,
     Clausal proof trail of additions and deletions

   - Z3_OP_PR_DEF_INTRO: Introduces a name for a formula/term.
       Suppose e is an expression with free variables x, and def-intro
       introduces the name n(x). The possible cases are:

       When e is of Boolean type:
       [def-intro]: (and (or n (not e)) (or (not n) e))

       or:
       [def-intro]: (or (not n) e)
       when e only occurs positively.

       When e is of the form (ite cond th el):
       [def-intro]: (and (or (not cond) (= n th)) (or cond (= n el)))

       Otherwise:
       [def-intro]: (= n e)

   - Z3_OP_PR_APPLY_DEF:
       [apply-def T1]: F ~ n
       F is 'equivalent' to n, given that T1 is a proof that
       n is a name for F.

   - Z3_OP_PR_IFF_OEQ:
       T1: (iff p q)
       [iff~ T1]: (~ p q)

   - Z3_OP_PR_NNF_POS: Proof for a (positive) NNF step. Example:
       \nicebox{
          T1: (not s_1) ~ r_1
          T2: (not s_2) ~ r_2
          T3: s_1 ~ r_1'
          T4: s_2 ~ r_2'
          [nnf-pos T1 T2 T3 T4]: (~ (iff s_1 s_2)
                                    (and (or r_1 r_2') (or r_1' r_2)))
          }
       The negation normal form steps NNF_POS and NNF_NEG are used in the following cases:
       (a) When creating the NNF of a positive force quantifier.
        The quantifier is retained (unless the bound variables are eliminated).
        Example
        \nicebox{
           T1: q ~ q_new
           [nnf-pos T1]: (~ (forall (x T) q) (forall (x T) q_new))
        }
       (b) When recursively creating NNF over Boolean formulas, where the top-level
       connective is changed during NNF conversion. The relevant Boolean connectives
       for NNF_POS are 'implies', 'iff', 'xor', 'ite'.
       NNF_NEG furthermore handles the case where negation is pushed
       over Boolean connectives 'and' and 'or'.


   - Z3_OP_PR_NNF_NEG: Proof for a (negative) NNF step. Examples:
          \nicebox{
          T1: (not s_1) ~ r_1
          ...
          Tn: (not s_n) ~ r_n
         [nnf-neg T1 ... Tn]: (not (and s_1 ... s_n)) ~ (or r_1 ... r_n)
      and
          T1: (not s_1) ~ r_1
          ...
          Tn: (not s_n) ~ r_n
         [nnf-neg T1 ... Tn]: (not (or s_1 ... s_n)) ~ (and r_1 ... r_n)
      and
          T1: (not s_1) ~ r_1
          T2: (not s_2) ~ r_2
          T3: s_1 ~ r_1'
          T4: s_2 ~ r_2'
         [nnf-neg T1 T2 T3 T4]: (~ (not (iff s_1 s_2))
                                   (and (or r_1 r_2) (or r_1' r_2')))
       }

   - Z3_OP_PR_SKOLEMIZE: Proof for:

          \nicebox{
          [sk]: (~ (not (forall x (p x y))) (not (p (sk y) y)))
          [sk]: (~ (exists x (p x y)) (p (sk y) y))
          }

          This proof object has no antecedents.

   - Z3_OP_PR_MODUS_PONENS_OEQ: Modus ponens style rule for equi-satisfiability.
       \nicebox{
          T1: p
          T2: (~ p q)
          [mp~ T1 T2]: q
          }

    - Z3_OP_PR_TH_LEMMA: Generic proof for theory lemmas.

         The theory lemma function comes with one or more parameters.
         The first parameter indicates the name of the theory.
         For the theory of arithmetic, additional parameters provide hints for
         checking the theory lemma.
         The hints for arithmetic are:

         - farkas - followed by rational coefficients. Multiply the coefficients to the
           inequalities in the lemma, add the (negated) inequalities and obtain a contradiction.

         - triangle-eq - Indicates a lemma related to the equivalence:
         \nicebox{
            (iff (= t1 t2) (and (<= t1 t2) (<= t2 t1)))
         }

         - gcd-test - Indicates an integer linear arithmetic lemma that uses a gcd test.


    - Z3_OP_PR_HYPER_RESOLVE: Hyper-resolution rule.

        The premises of the rules is a sequence of clauses.
        The first clause argument is the main clause of the rule.
        with a literal from the first (main) clause.

        Premises of the rules are of the form
        \nicebox{
                (or l0 l1 l2 .. ln)
        }
        or
        \nicebox{
             (=> (and l1 l2 .. ln) l0)
        }
        or in the most general (ground) form:
        \nicebox{
             (=> (and ln+1 ln+2 .. ln+m) (or l0 l1 .. ln))
        }
        In other words we use the following (Prolog style) convention for Horn
        implications:
        The head of a Horn implication is position 0,
        the first conjunct in the body of an implication is position 1
        the second conjunct in the body of an implication is position 2

        For general implications where the head is a disjunction, the
        first n positions correspond to the n disjuncts in the head.
        The next m positions correspond to the m conjuncts in the body.

        The premises can be universally quantified so that the most
        general non-ground form is:

        \nicebox{
             (forall (vars) (=> (and ln+1 ln+2 .. ln+m) (or l0 l1 .. ln)))
        }

        The hyper-resolution rule takes a sequence of parameters.
        The parameters are substitutions of bound variables separated by pairs
        of literal positions from the main clause and side clause.


      - Z3_OP_RA_STORE: Insert a record into a relation.
        The function takes \c n+1 arguments, where the first argument is the relation and the remaining \c n elements
        correspond to the \c n columns of the relation.

      - Z3_OP_RA_EMPTY: Creates the empty relation.

      - Z3_OP_RA_IS_EMPTY: Tests if the relation is empty.

      - Z3_OP_RA_JOIN: Create the relational join.

      - Z3_OP_RA_UNION: Create the union or convex hull of two relations.
        The function takes two arguments.

      - Z3_OP_RA_WIDEN: Widen two relations.
        The function takes two arguments.

      - Z3_OP_RA_PROJECT: Project the columns (provided as numbers in the parameters).
        The function takes one argument.

      - Z3_OP_RA_FILTER: Filter (restrict) a relation with respect to a predicate.
        The first argument is a relation.
        The second argument is a predicate with free de-Bruijn indices
        corresponding to the columns of the relation.
        So the first column in the relation has index 0.

      - Z3_OP_RA_NEGATION_FILTER: Intersect the first relation with respect to negation
        of the second relation (the function takes two arguments).
        Logically, the specification can be described by a function

           target = filter_by_negation(pos, neg, columns)

        where columns are pairs c1, d1, .., cN, dN of columns from pos and neg, such that
        target are elements in x in pos, such that there is no y in neg that agrees with
        x on the columns c1, d1, .., cN, dN.


      - Z3_OP_RA_RENAME: rename columns in the relation.
        The function takes one argument.
        The parameters contain the renaming as a cycle.

      - Z3_OP_RA_COMPLEMENT: Complement the relation.

      - Z3_OP_RA_SELECT: Check if a record is an element of the relation.
        The function takes \c n+1 arguments, where the first argument is a relation,
        and the remaining \c n arguments correspond to a record.

      - Z3_OP_RA_CLONE: Create a fresh copy (clone) of a relation.
        The function is logically the identity, but
        in the context of a register machine allows
        for #Z3_OP_RA_UNION to perform destructive updates to the first argument.


      - Z3_OP_FD_LT: A less than predicate over the finite domain Z3_FINITE_DOMAIN_SORT.

      - Z3_OP_LABEL: A label (used by the Boogie Verification condition generator).
                     The label has two parameters, a string and a Boolean polarity.
                     It takes one argument, a formula.

      - Z3_OP_LABEL_LIT: A label literal (used by the Boogie Verification condition generator).
                     A label literal has a set of string parameters. It takes no arguments.

      - Z3_OP_DT_CONSTRUCTOR: datatype constructor.

      - Z3_OP_DT_RECOGNISER: datatype recognizer.

      - Z3_OP_DT_IS: datatype recognizer.

      - Z3_OP_DT_ACCESSOR: datatype accessor.

      - Z3_OP_DT_UPDATE_FIELD: datatype field update.

      - Z3_OP_PB_AT_MOST: Cardinality constraint.
              E.g., x + y + z <= 2

      - Z3_OP_PB_AT_LEAST: Cardinality constraint.
              E.g., x + y + z >= 2

      - Z3_OP_PB_LE: Generalized Pseudo-Boolean cardinality constraint.
              Example  2*x + 3*y <= 4

      - Z3_OP_PB_GE: Generalized Pseudo-Boolean cardinality constraint.
              Example  2*x + 3*y + 2*z >= 4

      - Z3_OP_PB_EQ: Generalized Pseudo-Boolean equality constraint.
              Example  2*x + 1*y + 2*z + 1*u = 4

       - Z3_OP_SPECIAL_RELATION_LO: A relation that is a total linear order

       - Z3_OP_SPECIAL_RELATION_PO: A relation that is a partial order

       - Z3_OP_SPECIAL_RELATION_PLO: A relation that is a piecewise linear order

       - Z3_OP_SPECIAL_RELATION_TO: A relation that is a tree order

       - Z3_OP_SPECIAL_RELATION_TC: Transitive closure of a relation

       - Z3_OP_SPECIAL_RELATION_TRC: Transitive reflexive closure of a relation

      - Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN: Floating-point rounding mode RNE

      - Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY: Floating-point rounding mode RNA

      - Z3_OP_FPA_RM_TOWARD_POSITIVE: Floating-point rounding mode RTP

      - Z3_OP_FPA_RM_TOWARD_NEGATIVE: Floating-point rounding mode RTN

      - Z3_OP_FPA_RM_TOWARD_ZERO: Floating-point rounding mode RTZ

      - Z3_OP_FPA_NUM: Floating-point value

      - Z3_OP_FPA_PLUS_INF: Floating-point +oo

      - Z3_OP_FPA_MINUS_INF: Floating-point -oo

      - Z3_OP_FPA_NAN: Floating-point NaN

      - Z3_OP_FPA_PLUS_ZERO: Floating-point +zero

      - Z3_OP_FPA_MINUS_ZERO: Floating-point -zero

      - Z3_OP_FPA_ADD: Floating-point addition

      - Z3_OP_FPA_SUB: Floating-point subtraction

      - Z3_OP_FPA_NEG: Floating-point negation

      - Z3_OP_FPA_MUL: Floating-point multiplication

      - Z3_OP_FPA_DIV: Floating-point division

      - Z3_OP_FPA_REM: Floating-point remainder

      - Z3_OP_FPA_ABS: Floating-point absolute value

      - Z3_OP_FPA_MIN: Floating-point minimum

      - Z3_OP_FPA_MAX: Floating-point maximum

      - Z3_OP_FPA_FMA: Floating-point fused multiply-add

      - Z3_OP_FPA_SQRT: Floating-point square root

      - Z3_OP_FPA_ROUND_TO_INTEGRAL: Floating-point round to integral

      - Z3_OP_FPA_EQ: Floating-point equality

      - Z3_OP_FPA_LT: Floating-point less than

      - Z3_OP_FPA_GT: Floating-point greater than

      - Z3_OP_FPA_LE: Floating-point less than or equal

      - Z3_OP_FPA_GE: Floating-point greater than or equal

      - Z3_OP_FPA_IS_NAN: Floating-point isNaN

      - Z3_OP_FPA_IS_INF: Floating-point isInfinite

      - Z3_OP_FPA_IS_ZERO: Floating-point isZero

      - Z3_OP_FPA_IS_NORMAL: Floating-point isNormal

      - Z3_OP_FPA_IS_SUBNORMAL: Floating-point isSubnormal

      - Z3_OP_FPA_IS_NEGATIVE: Floating-point isNegative

      - Z3_OP_FPA_IS_POSITIVE: Floating-point isPositive

      - Z3_OP_FPA_FP: Floating-point constructor from 3 bit-vectors

      - Z3_OP_FPA_TO_FP: Floating-point conversion (various)

      - Z3_OP_FPA_TO_FP_UNSIGNED: Floating-point conversion from unsigned bit-vector

      - Z3_OP_FPA_TO_UBV: Floating-point conversion to unsigned bit-vector

      - Z3_OP_FPA_TO_SBV: Floating-point conversion to signed bit-vector

      - Z3_OP_FPA_TO_REAL: Floating-point conversion to real number

      - Z3_OP_FPA_TO_IEEE_BV: Floating-point conversion to IEEE-754 bit-vector

      - Z3_OP_FPA_BVWRAP: (Implicitly) represents the internal bitvector-
        representation of a floating-point term (used for the lazy encoding
        of non-relevant terms in theory_fpa)

      - Z3_OP_FPA_BV2RM: Conversion of a 3-bit bit-vector term to a
        floating-point rounding-mode term

        The conversion uses the following values:
            0 = 000 = Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN,
            1 = 001 = Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY,
            2 = 010 = Z3_OP_FPA_RM_TOWARD_POSITIVE,
            3 = 011 = Z3_OP_FPA_RM_TOWARD_NEGATIVE,
            4 = 100 = Z3_OP_FPA_RM_TOWARD_ZERO.

      - Z3_OP_INTERNAL: internal (often interpreted) symbol, but no additional
        information is exposed. Tools may use the string representation of the
        function declaration to obtain more information.

      - Z3_OP_UNINTERPRETED: kind used for uninterpreted symbols.
*/
typedef enum {
    // Basic
    Z3_OP_TRUE = 0x100,
    Z3_OP_FALSE,
    Z3_OP_EQ,
    Z3_OP_DISTINCT,
    Z3_OP_ITE,
    Z3_OP_AND,
    Z3_OP_OR,
    Z3_OP_IFF,
    Z3_OP_XOR,
    Z3_OP_NOT,
    Z3_OP_IMPLIES,
    Z3_OP_OEQ,

    // Arithmetic
    Z3_OP_ANUM = 0x200,
    Z3_OP_AGNUM,
    Z3_OP_LE,
    Z3_OP_GE,
    Z3_OP_LT,
    Z3_OP_GT,
    Z3_OP_ADD,
    Z3_OP_SUB,
    Z3_OP_UMINUS,
    Z3_OP_MUL,
    Z3_OP_DIV,
    Z3_OP_IDIV,
    Z3_OP_REM,
    Z3_OP_MOD,
    Z3_OP_TO_REAL,
    Z3_OP_TO_INT,
    Z3_OP_IS_INT,
    Z3_OP_POWER,

    // Arrays & Sets
    Z3_OP_STORE = 0x300,
    Z3_OP_SELECT,
    Z3_OP_CONST_ARRAY,
    Z3_OP_ARRAY_MAP,
    Z3_OP_ARRAY_DEFAULT,
    Z3_OP_SET_UNION,
    Z3_OP_SET_INTERSECT,
    Z3_OP_SET_DIFFERENCE,
    Z3_OP_SET_COMPLEMENT,
    Z3_OP_SET_SUBSET,
    Z3_OP_AS_ARRAY,
    Z3_OP_ARRAY_EXT,

    // Bit-vectors
    Z3_OP_BNUM = 0x400,
    Z3_OP_BIT1,
    Z3_OP_BIT0,
    Z3_OP_BNEG,
    Z3_OP_BADD,
    Z3_OP_BSUB,
    Z3_OP_BMUL,

    Z3_OP_BSDIV,
    Z3_OP_BUDIV,
    Z3_OP_BSREM,
    Z3_OP_BUREM,
    Z3_OP_BSMOD,

    // special functions to record the division by 0 cases
    // these are internal functions
    Z3_OP_BSDIV0,
    Z3_OP_BUDIV0,
    Z3_OP_BSREM0,
    Z3_OP_BUREM0,
    Z3_OP_BSMOD0,

    Z3_OP_ULEQ,
    Z3_OP_SLEQ,
    Z3_OP_UGEQ,
    Z3_OP_SGEQ,
    Z3_OP_ULT,
    Z3_OP_SLT,
    Z3_OP_UGT,
    Z3_OP_SGT,

    Z3_OP_BAND,
    Z3_OP_BOR,
    Z3_OP_BNOT,
    Z3_OP_BXOR,
    Z3_OP_BNAND,
    Z3_OP_BNOR,
    Z3_OP_BXNOR,

    Z3_OP_CONCAT,
    Z3_OP_SIGN_EXT,
    Z3_OP_ZERO_EXT,
    Z3_OP_EXTRACT,
    Z3_OP_REPEAT,

    Z3_OP_BREDOR,
    Z3_OP_BREDAND,
    Z3_OP_BCOMP,

    Z3_OP_BSHL,
    Z3_OP_BLSHR,
    Z3_OP_BASHR,
    Z3_OP_ROTATE_LEFT,
    Z3_OP_ROTATE_RIGHT,
    Z3_OP_EXT_ROTATE_LEFT,
    Z3_OP_EXT_ROTATE_RIGHT,

    Z3_OP_BIT2BOOL,
    Z3_OP_INT2BV,
    Z3_OP_BV2INT,
    Z3_OP_CARRY,
    Z3_OP_XOR3,

    Z3_OP_BSMUL_NO_OVFL,
    Z3_OP_BUMUL_NO_OVFL,
    Z3_OP_BSMUL_NO_UDFL,
    Z3_OP_BSDIV_I,
    Z3_OP_BUDIV_I,
    Z3_OP_BSREM_I,
    Z3_OP_BUREM_I,
    Z3_OP_BSMOD_I,

    // Proofs
    Z3_OP_PR_UNDEF = 0x500,
    Z3_OP_PR_TRUE,
    Z3_OP_PR_ASSERTED,
    Z3_OP_PR_GOAL,
    Z3_OP_PR_MODUS_PONENS,
    Z3_OP_PR_REFLEXIVITY,
    Z3_OP_PR_SYMMETRY,
    Z3_OP_PR_TRANSITIVITY,
    Z3_OP_PR_TRANSITIVITY_STAR,
    Z3_OP_PR_MONOTONICITY,
    Z3_OP_PR_QUANT_INTRO,
    Z3_OP_PR_BIND,
    Z3_OP_PR_DISTRIBUTIVITY,
    Z3_OP_PR_AND_ELIM,
    Z3_OP_PR_NOT_OR_ELIM,
    Z3_OP_PR_REWRITE,
    Z3_OP_PR_REWRITE_STAR,
    Z3_OP_PR_PULL_QUANT,
    Z3_OP_PR_PUSH_QUANT,
    Z3_OP_PR_ELIM_UNUSED_VARS,
    Z3_OP_PR_DER,
    Z3_OP_PR_QUANT_INST,
    Z3_OP_PR_HYPOTHESIS,
    Z3_OP_PR_LEMMA,
    Z3_OP_PR_UNIT_RESOLUTION,
    Z3_OP_PR_IFF_TRUE,
    Z3_OP_PR_IFF_FALSE,
    Z3_OP_PR_COMMUTATIVITY,
    Z3_OP_PR_DEF_AXIOM,
    Z3_OP_PR_ASSUMPTION_ADD, 
    Z3_OP_PR_LEMMA_ADD, 
    Z3_OP_PR_REDUNDANT_DEL, 
    Z3_OP_PR_CLAUSE_TRAIL,
    Z3_OP_PR_DEF_INTRO,
    Z3_OP_PR_APPLY_DEF,
    Z3_OP_PR_IFF_OEQ,
    Z3_OP_PR_NNF_POS,
    Z3_OP_PR_NNF_NEG,
    Z3_OP_PR_SKOLEMIZE,
    Z3_OP_PR_MODUS_PONENS_OEQ,
    Z3_OP_PR_TH_LEMMA,
    Z3_OP_PR_HYPER_RESOLVE,

    // Relational algebra
    Z3_OP_RA_STORE = 0x600,
    Z3_OP_RA_EMPTY,
    Z3_OP_RA_IS_EMPTY,
    Z3_OP_RA_JOIN,
    Z3_OP_RA_UNION,
    Z3_OP_RA_WIDEN,
    Z3_OP_RA_PROJECT,
    Z3_OP_RA_FILTER,
    Z3_OP_RA_NEGATION_FILTER,
    Z3_OP_RA_RENAME,
    Z3_OP_RA_COMPLEMENT,
    Z3_OP_RA_SELECT,
    Z3_OP_RA_CLONE,
    Z3_OP_FD_CONSTANT,
    Z3_OP_FD_LT,

    // Sequences
    Z3_OP_SEQ_UNIT,
    Z3_OP_SEQ_EMPTY,
    Z3_OP_SEQ_CONCAT,
    Z3_OP_SEQ_PREFIX,
    Z3_OP_SEQ_SUFFIX,
    Z3_OP_SEQ_CONTAINS,
    Z3_OP_SEQ_EXTRACT,
    Z3_OP_SEQ_REPLACE,
    Z3_OP_SEQ_AT,
    Z3_OP_SEQ_NTH,
    Z3_OP_SEQ_LENGTH,
    Z3_OP_SEQ_INDEX,
    Z3_OP_SEQ_LAST_INDEX,
    Z3_OP_SEQ_TO_RE,
    Z3_OP_SEQ_IN_RE,

    // strings
    Z3_OP_STR_TO_INT,
    Z3_OP_INT_TO_STR,

    // regular expressions
    Z3_OP_RE_PLUS,
    Z3_OP_RE_STAR,
    Z3_OP_RE_OPTION,
    Z3_OP_RE_CONCAT,
    Z3_OP_RE_UNION,
    Z3_OP_RE_RANGE,
    Z3_OP_RE_LOOP,
    Z3_OP_RE_INTERSECT,
    Z3_OP_RE_EMPTY_SET,
    Z3_OP_RE_FULL_SET,
    Z3_OP_RE_COMPLEMENT,

    // Auxiliary
    Z3_OP_LABEL = 0x700,
    Z3_OP_LABEL_LIT,

    // Datatypes
    Z3_OP_DT_CONSTRUCTOR=0x800,
    Z3_OP_DT_RECOGNISER,
    Z3_OP_DT_IS,
    Z3_OP_DT_ACCESSOR,
    Z3_OP_DT_UPDATE_FIELD,

    // Pseudo Booleans
    Z3_OP_PB_AT_MOST=0x900,
    Z3_OP_PB_AT_LEAST,
    Z3_OP_PB_LE,
    Z3_OP_PB_GE,
    Z3_OP_PB_EQ,

    // Special relations
    Z3_OP_SPECIAL_RELATION_LO = 0xa000,
    Z3_OP_SPECIAL_RELATION_PO,
    Z3_OP_SPECIAL_RELATION_PLO,
    Z3_OP_SPECIAL_RELATION_TO,
    Z3_OP_SPECIAL_RELATION_TC,
    Z3_OP_SPECIAL_RELATION_TRC,


    // Floating-Point Arithmetic
    Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN = 0xb000,
    Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY,
    Z3_OP_FPA_RM_TOWARD_POSITIVE,
    Z3_OP_FPA_RM_TOWARD_NEGATIVE,
    Z3_OP_FPA_RM_TOWARD_ZERO,

    Z3_OP_FPA_NUM,
    Z3_OP_FPA_PLUS_INF,
    Z3_OP_FPA_MINUS_INF,
    Z3_OP_FPA_NAN,
    Z3_OP_FPA_PLUS_ZERO,
    Z3_OP_FPA_MINUS_ZERO,

    Z3_OP_FPA_ADD,
    Z3_OP_FPA_SUB,
    Z3_OP_FPA_NEG,
    Z3_OP_FPA_MUL,
    Z3_OP_FPA_DIV,
    Z3_OP_FPA_REM,
    Z3_OP_FPA_ABS,
    Z3_OP_FPA_MIN,
    Z3_OP_FPA_MAX,
    Z3_OP_FPA_FMA,
    Z3_OP_FPA_SQRT,
    Z3_OP_FPA_ROUND_TO_INTEGRAL,

    Z3_OP_FPA_EQ,
    Z3_OP_FPA_LT,
    Z3_OP_FPA_GT,
    Z3_OP_FPA_LE,
    Z3_OP_FPA_GE,
    Z3_OP_FPA_IS_NAN,
    Z3_OP_FPA_IS_INF,
    Z3_OP_FPA_IS_ZERO,
    Z3_OP_FPA_IS_NORMAL,
    Z3_OP_FPA_IS_SUBNORMAL,
    Z3_OP_FPA_IS_NEGATIVE,
    Z3_OP_FPA_IS_POSITIVE,

    Z3_OP_FPA_FP,
    Z3_OP_FPA_TO_FP,
    Z3_OP_FPA_TO_FP_UNSIGNED,
    Z3_OP_FPA_TO_UBV,
    Z3_OP_FPA_TO_SBV,
    Z3_OP_FPA_TO_REAL,

    Z3_OP_FPA_TO_IEEE_BV,

    Z3_OP_FPA_BVWRAP,
    Z3_OP_FPA_BV2RM,

    Z3_OP_INTERNAL,

    Z3_OP_UNINTERPRETED
} Z3_decl_kind;

/**
   \brief The different kinds of parameters that can be associated with parameter sets.
   (see #Z3_mk_params).

    - Z3_PK_UINT integer parameters.
    - Z3_PK_BOOL boolean parameters.
    - Z3_PK_DOUBLE double parameters.
    - Z3_PK_SYMBOL symbol parameters.
    - Z3_PK_STRING string parameters.
    - Z3_PK_OTHER all internal parameter kinds which are not exposed in the API.
    - Z3_PK_INVALID invalid parameter.
*/
typedef enum {
    Z3_PK_UINT,
    Z3_PK_BOOL,
    Z3_PK_DOUBLE,
    Z3_PK_SYMBOL,
    Z3_PK_STRING,
    Z3_PK_OTHER,
    Z3_PK_INVALID
} Z3_param_kind;

/**
    \brief Z3 pretty printing modes (See #Z3_set_ast_print_mode).

   - Z3_PRINT_SMTLIB_FULL:   Print AST nodes in SMTLIB verbose format.
   - Z3_PRINT_LOW_LEVEL:     Print AST nodes using a low-level format.
   - Z3_PRINT_SMTLIB2_COMPLIANT: Print AST nodes in SMTLIB 2.x compliant format.
*/
typedef enum {
    Z3_PRINT_SMTLIB_FULL,
    Z3_PRINT_LOW_LEVEL,
    Z3_PRINT_SMTLIB2_COMPLIANT
} Z3_ast_print_mode;


/**
   \brief Z3 error codes (See #Z3_get_error_code).

   - Z3_OK:            No error.
   - Z3_SORT_ERROR:    User tried to build an invalid (type incorrect) AST.
   - Z3_IOB:           Index out of bounds.
   - Z3_INVALID_ARG:   Invalid argument was provided.
   - Z3_PARSER_ERROR:  An error occurred when parsing a string or file.
   - Z3_NO_PARSER:     Parser output is not available, that is, user didn't invoke #Z3_parse_smtlib2_string or #Z3_parse_smtlib2_file.
   - Z3_INVALID_PATTERN: Invalid pattern was used to build a quantifier.
   - Z3_MEMOUT_FAIL:   A memory allocation failure was encountered.
   - Z3_FILE_ACCESS_ERRROR: A file could not be accessed.
   - Z3_INVALID_USAGE:   API call is invalid in the current state.
   - Z3_INTERNAL_FATAL: An error internal to Z3 occurred.
   - Z3_DEC_REF_ERROR: Trying to decrement the reference counter of an AST that was deleted or the reference counter was not initialized with #Z3_inc_ref.
   - Z3_EXCEPTION:     Internal Z3 exception. Additional details can be retrieved using #Z3_get_error_msg.
*/
typedef enum
{
    Z3_OK,
    Z3_SORT_ERROR,
    Z3_IOB,
    Z3_INVALID_ARG,
    Z3_PARSER_ERROR,
    Z3_NO_PARSER,
    Z3_INVALID_PATTERN,
    Z3_MEMOUT_FAIL,
    Z3_FILE_ACCESS_ERROR,
    Z3_INTERNAL_FATAL,
    Z3_INVALID_USAGE,
    Z3_DEC_REF_ERROR,
    Z3_EXCEPTION
} Z3_error_code;

/**
  Definitions for update_api.py

  def_Type('CONFIG',           'Z3_config',           'Config')
  def_Type('CONTEXT',          'Z3_context',          'ContextObj')
  def_Type('AST',              'Z3_ast',              'Ast')
  def_Type('APP',              'Z3_app',              'Ast')
  def_Type('SORT',             'Z3_sort',             'Sort')
  def_Type('FUNC_DECL',        'Z3_func_decl',        'FuncDecl')
  def_Type('PATTERN',          'Z3_pattern',          'Pattern')
  def_Type('MODEL',            'Z3_model',            'Model')
  def_Type('LITERALS',         'Z3_literals',         'Literals')
  def_Type('CONSTRUCTOR',      'Z3_constructor',      'Constructor')
  def_Type('CONSTRUCTOR_LIST', 'Z3_constructor_list', 'ConstructorList')
  def_Type('SOLVER',           'Z3_solver',           'SolverObj')
  def_Type('GOAL',             'Z3_goal',             'GoalObj')
  def_Type('TACTIC',           'Z3_tactic',           'TacticObj')
  def_Type('PARAMS',           'Z3_params',           'Params')
  def_Type('PROBE',            'Z3_probe',            'ProbeObj')
  def_Type('STATS',            'Z3_stats',            'StatsObj')
  def_Type('AST_VECTOR',       'Z3_ast_vector',       'AstVectorObj')
  def_Type('AST_MAP',          'Z3_ast_map',          'AstMapObj')
  def_Type('APPLY_RESULT',     'Z3_apply_result',     'ApplyResultObj')
  def_Type('FUNC_INTERP',      'Z3_func_interp',      'FuncInterpObj')
  def_Type('FUNC_ENTRY',       'Z3_func_entry',       'FuncEntryObj')
  def_Type('FIXEDPOINT',       'Z3_fixedpoint',       'FixedpointObj')
  def_Type('OPTIMIZE',         'Z3_optimize',         'OptimizeObj')
  def_Type('PARAM_DESCRS',     'Z3_param_descrs',     'ParamDescrs')
  def_Type('RCF_NUM',          'Z3_rcf_num',          'RCFNumObj')
*/

/**
   \brief Z3 custom error handler (See #Z3_set_error_handler).
*/
typedef void Z3_error_handler(Z3_context c, Z3_error_code e);

/**
   \brief A Goal is essentially a set of formulas.
   Z3 provide APIs for building strategies/tactics for solving and transforming Goals.
   Some of these transformations apply under/over approximations.

   - Z3_GOAL_PRECISE:    Approximations/Relaxations were not applied on the goal (sat and unsat answers were preserved).
   - Z3_GOAL_UNDER:      Goal is the product of a under-approximation (sat answers are preserved).
   - Z3_GOAL_OVER:       Goal is the product of an over-approximation (unsat answers are preserved).
   - Z3_GOAL_UNDER_OVER: Goal is garbage (it is the product of over- and under-approximations, sat and unsat answers are not preserved).
*/
typedef enum
{
    Z3_GOAL_PRECISE,
    Z3_GOAL_UNDER,
    Z3_GOAL_OVER,
    Z3_GOAL_UNDER_OVER
} Z3_goal_prec;

void Z3_global_param_set(Z3_string param_id, Z3_string param_value);
void Z3_global_param_reset_all();
Z3_bool Z3_global_param_get(Z3_string param_id, Z3_string_ptr param_value);
Z3_config Z3_mk_config();
void Z3_del_config(Z3_config c);
void Z3_set_param_value(Z3_config c, Z3_string param_id, Z3_string param_value);
Z3_context Z3_mk_context(Z3_config c);
Z3_context Z3_mk_context_rc(Z3_config c);
void Z3_del_context(Z3_context c);
void Z3_inc_ref(Z3_context c, Z3_ast a);
void Z3_dec_ref(Z3_context c, Z3_ast a);
void Z3_update_param_value(Z3_context c, Z3_string param_id, Z3_string param_value);
void Z3_interrupt(Z3_context c);
Z3_params Z3_mk_params(Z3_context c);
void Z3_params_inc_ref(Z3_context c, Z3_params p);
void Z3_params_dec_ref(Z3_context c, Z3_params p);
void Z3_params_set_bool(Z3_context c, Z3_params p, Z3_symbol k, bool v);
void Z3_params_set_uint(Z3_context c, Z3_params p, Z3_symbol k, unsigned v);
void Z3_params_set_double(Z3_context c, Z3_params p, Z3_symbol k, double v);
void Z3_params_set_symbol(Z3_context c, Z3_params p, Z3_symbol k, Z3_symbol v);
Z3_string Z3_params_to_string(Z3_context c, Z3_params p);
void Z3_params_validate(Z3_context c, Z3_params p, Z3_param_descrs d);
void Z3_param_descrs_inc_ref(Z3_context c, Z3_param_descrs p);
void Z3_param_descrs_dec_ref(Z3_context c, Z3_param_descrs p);
Z3_param_kind Z3_param_descrs_get_kind(Z3_context c, Z3_param_descrs p, Z3_symbol n);
unsigned Z3_param_descrs_size(Z3_context c, Z3_param_descrs p);
Z3_symbol Z3_param_descrs_get_name(Z3_context c, Z3_param_descrs p, unsigned i);
Z3_string Z3_param_descrs_get_documentation(Z3_context c, Z3_param_descrs p, Z3_symbol s);
Z3_string Z3_param_descrs_to_string(Z3_context c, Z3_param_descrs p);
Z3_symbol Z3_mk_int_symbol(Z3_context c, int i);
Z3_symbol Z3_mk_string_symbol(Z3_context c, Z3_string s);
Z3_sort Z3_mk_uninterpreted_sort(Z3_context c, Z3_symbol s);
Z3_sort Z3_mk_bool_sort(Z3_context c);
Z3_sort Z3_mk_int_sort(Z3_context c);
Z3_sort Z3_mk_real_sort(Z3_context c);
Z3_sort Z3_mk_bv_sort(Z3_context c, unsigned sz);
Z3_sort Z3_mk_finite_domain_sort(Z3_context c, Z3_symbol name, uint64_t size);
Z3_sort Z3_mk_array_sort(Z3_context c, Z3_sort domain, Z3_sort range);
Z3_sort Z3_mk_array_sort_n(Z3_context c, unsigned n, Z3_sort const * domain, Z3_sort range);
Z3_sort Z3_mk_tuple_sort(Z3_context c,
                                    Z3_symbol mk_tuple_name,
                                    unsigned num_fields,
                                    Z3_symbol const field_names[],
                                    Z3_sort const field_sorts[],
                                    Z3_func_decl * mk_tuple_decl,
                                    Z3_func_decl proj_decl[]);
Z3_sort Z3_mk_enumeration_sort(Z3_context c,
                                        Z3_symbol name,
                                        unsigned n,
                                        Z3_symbol  const enum_names[],
                                        Z3_func_decl enum_consts[],
                                        Z3_func_decl enum_testers[]);
Z3_sort Z3_mk_list_sort(Z3_context c,
                                Z3_symbol name,
                                Z3_sort   elem_sort,
                                Z3_func_decl* nil_decl,
                                Z3_func_decl* is_nil_decl,
                                Z3_func_decl* cons_decl,
                                Z3_func_decl* is_cons_decl,
                                Z3_func_decl* head_decl,
                                Z3_func_decl* tail_decl
                                );
Z3_constructor Z3_mk_constructor(Z3_context c,
                                        Z3_symbol name,
                                        Z3_symbol recognizer,
                                        unsigned num_fields,
                                        Z3_symbol const field_names[],
                                        Z3_sort const sorts[],
                                        unsigned sort_refs[]
                                        );
void Z3_del_constructor(Z3_context c, Z3_constructor constr);
Z3_sort Z3_mk_datatype(Z3_context c,
                                Z3_symbol name,
                                unsigned num_constructors,
                                Z3_constructor constructors[]);
Z3_constructor_list Z3_mk_constructor_list(Z3_context c,
                                                    unsigned num_constructors,
                                                    Z3_constructor const constructors[]);
void Z3_del_constructor_list(Z3_context c, Z3_constructor_list clist);
void Z3_mk_datatypes(Z3_context c,
                            unsigned num_sorts,
                            Z3_symbol const sort_names[],
                            Z3_sort sorts[],
                            Z3_constructor_list constructor_lists[]);
void Z3_query_constructor(Z3_context c,
                                    Z3_constructor constr,
                                    unsigned num_fields,
                                    Z3_func_decl* constructor,
                                    Z3_func_decl* tester,
                                    Z3_func_decl accessors[]);
Z3_func_decl Z3_mk_func_decl(Z3_context c, Z3_symbol s,
                                    unsigned domain_size, Z3_sort const domain[],
                                    Z3_sort range);
Z3_ast Z3_mk_app(
    Z3_context c,
    Z3_func_decl d,
    unsigned num_args,
    Z3_ast const args[]);
Z3_ast Z3_mk_const(Z3_context c, Z3_symbol s, Z3_sort ty);
Z3_func_decl Z3_mk_fresh_func_decl(Z3_context c, Z3_string prefix,
                                                unsigned domain_size, Z3_sort const domain[],
                                                Z3_sort range);
Z3_ast Z3_mk_fresh_const(Z3_context c, Z3_string prefix, Z3_sort ty);
Z3_func_decl Z3_mk_rec_func_decl(Z3_context c, Z3_symbol s,
                                    unsigned domain_size, Z3_sort const domain[],
                                    Z3_sort range);
void Z3_add_rec_def(Z3_context c, Z3_func_decl f, unsigned n, Z3_ast args[], Z3_ast body);
Z3_ast Z3_mk_true(Z3_context c);
Z3_ast Z3_mk_false(Z3_context c);
Z3_ast Z3_mk_eq(Z3_context c, Z3_ast l, Z3_ast r);
Z3_ast Z3_mk_distinct(Z3_context c, unsigned num_args, Z3_ast const args[]);
Z3_ast Z3_mk_not(Z3_context c, Z3_ast a);
Z3_ast Z3_mk_ite(Z3_context c, Z3_ast t1, Z3_ast t2, Z3_ast t3);
Z3_ast Z3_mk_iff(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_implies(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_xor(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_and(Z3_context c, unsigned num_args, Z3_ast const args[]);
Z3_ast Z3_mk_or(Z3_context c, unsigned num_args, Z3_ast const args[]);
Z3_ast Z3_mk_add(Z3_context c, unsigned num_args, Z3_ast const args[]);
Z3_ast Z3_mk_mul(Z3_context c, unsigned num_args, Z3_ast const args[]);
Z3_ast Z3_mk_sub(Z3_context c, unsigned num_args, Z3_ast const args[]);
Z3_ast Z3_mk_unary_minus(Z3_context c, Z3_ast arg);
Z3_ast Z3_mk_div(Z3_context c, Z3_ast arg1, Z3_ast arg2);
Z3_ast Z3_mk_mod(Z3_context c, Z3_ast arg1, Z3_ast arg2);
Z3_ast Z3_mk_rem(Z3_context c, Z3_ast arg1, Z3_ast arg2);
Z3_ast Z3_mk_power(Z3_context c, Z3_ast arg1, Z3_ast arg2);
Z3_ast Z3_mk_lt(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_le(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_gt(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_ge(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_int2real(Z3_context c, Z3_ast t1);
Z3_ast Z3_mk_real2int(Z3_context c, Z3_ast t1);
Z3_ast Z3_mk_is_int(Z3_context c, Z3_ast t1);
Z3_ast Z3_mk_bvnot(Z3_context c, Z3_ast t1);
Z3_ast Z3_mk_bvredand(Z3_context c, Z3_ast t1);
Z3_ast Z3_mk_bvredor(Z3_context c, Z3_ast t1);
Z3_ast Z3_mk_bvand(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_bvor(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_bvxor(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_bvnand(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_bvnor(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_bvxnor(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_bvneg(Z3_context c, Z3_ast t1);
Z3_ast Z3_mk_bvadd(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_bvsub(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_bvmul(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_bvudiv(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_bvsdiv(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_bvurem(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_bvsrem(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_bvsmod(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_bvult(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_bvslt(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_bvule(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_bvsle(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_bvuge(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_bvsge(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_bvugt(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_bvsgt(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_concat(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_extract(Z3_context c, unsigned high, unsigned low, Z3_ast t1);
Z3_ast Z3_mk_sign_ext(Z3_context c, unsigned i, Z3_ast t1);
Z3_ast Z3_mk_zero_ext(Z3_context c, unsigned i, Z3_ast t1);
Z3_ast Z3_mk_repeat(Z3_context c, unsigned i, Z3_ast t1);
Z3_ast Z3_mk_bvshl(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_bvlshr(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_bvashr(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_rotate_left(Z3_context c, unsigned i, Z3_ast t1);
Z3_ast Z3_mk_rotate_right(Z3_context c, unsigned i, Z3_ast t1);
Z3_ast Z3_mk_ext_rotate_left(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_ext_rotate_right(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_int2bv(Z3_context c, unsigned n, Z3_ast t1);
Z3_ast Z3_mk_bv2int(Z3_context c,Z3_ast t1, bool is_signed);
Z3_ast Z3_mk_bvadd_no_overflow(Z3_context c, Z3_ast t1, Z3_ast t2, bool is_signed);
Z3_ast Z3_mk_bvadd_no_underflow(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_bvsub_no_overflow(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_bvsub_no_underflow(Z3_context c, Z3_ast t1, Z3_ast t2, bool is_signed);
Z3_ast Z3_mk_bvsdiv_no_overflow(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_bvneg_no_overflow(Z3_context c, Z3_ast t1);
Z3_ast Z3_mk_bvmul_no_overflow(Z3_context c, Z3_ast t1, Z3_ast t2, bool is_signed);
Z3_ast Z3_mk_bvmul_no_underflow(Z3_context c, Z3_ast t1, Z3_ast t2);
Z3_ast Z3_mk_select(Z3_context c, Z3_ast a, Z3_ast i);
Z3_ast Z3_mk_select_n(Z3_context c, Z3_ast a, unsigned n, Z3_ast const* idxs);
Z3_ast Z3_mk_store(Z3_context c, Z3_ast a, Z3_ast i, Z3_ast v);
Z3_ast Z3_mk_store_n(Z3_context c, Z3_ast a, unsigned n, Z3_ast const* idxs, Z3_ast v);
Z3_ast Z3_mk_const_array(Z3_context c, Z3_sort domain, Z3_ast v);
Z3_ast Z3_mk_map(Z3_context c, Z3_func_decl f, unsigned n, Z3_ast const* args);
Z3_ast Z3_mk_array_default(Z3_context c, Z3_ast array);
Z3_ast Z3_mk_as_array(Z3_context c, Z3_func_decl f);
Z3_ast Z3_mk_set_has_size(Z3_context c, Z3_ast set, Z3_ast k);
Z3_sort Z3_mk_set_sort(Z3_context c, Z3_sort ty);
Z3_ast Z3_mk_empty_set(Z3_context c, Z3_sort domain);
Z3_ast Z3_mk_full_set(Z3_context c, Z3_sort domain);
Z3_ast Z3_mk_set_add(Z3_context c, Z3_ast set, Z3_ast elem);
Z3_ast Z3_mk_set_del(Z3_context c, Z3_ast set, Z3_ast elem);
Z3_ast Z3_mk_set_union(Z3_context c, unsigned num_args, Z3_ast const args[]);
Z3_ast Z3_mk_set_intersect(Z3_context c, unsigned num_args, Z3_ast const args[]);
Z3_ast Z3_mk_set_difference(Z3_context c, Z3_ast arg1, Z3_ast arg2);
Z3_ast Z3_mk_set_complement(Z3_context c, Z3_ast arg);
Z3_ast Z3_mk_set_member(Z3_context c, Z3_ast elem, Z3_ast set);
Z3_ast Z3_mk_set_subset(Z3_context c, Z3_ast arg1, Z3_ast arg2);
Z3_ast Z3_mk_array_ext(Z3_context c, Z3_ast arg1, Z3_ast arg2);
Z3_ast Z3_mk_numeral(Z3_context c, Z3_string numeral, Z3_sort ty);
Z3_ast Z3_mk_real(Z3_context c, int num, int den);
Z3_ast Z3_mk_int(Z3_context c, int v, Z3_sort ty);
Z3_ast Z3_mk_unsigned_int(Z3_context c, unsigned v, Z3_sort ty);
Z3_ast Z3_mk_int64(Z3_context c, int64_t v, Z3_sort ty);
Z3_ast Z3_mk_unsigned_int64(Z3_context c, uint64_t v, Z3_sort ty);
Z3_ast Z3_mk_bv_numeral(Z3_context c, unsigned sz, bool const* bits);
Z3_sort Z3_mk_seq_sort(Z3_context c, Z3_sort s);
bool Z3_is_seq_sort(Z3_context c, Z3_sort s);
Z3_sort Z3_get_seq_sort_basis(Z3_context c, Z3_sort s);
Z3_sort Z3_mk_re_sort(Z3_context c, Z3_sort seq);
bool Z3_is_re_sort(Z3_context c, Z3_sort s);
Z3_sort Z3_get_re_sort_basis(Z3_context c, Z3_sort s);
Z3_sort Z3_mk_string_sort(Z3_context c);
bool Z3_is_string_sort(Z3_context c, Z3_sort s);
Z3_ast Z3_mk_string(Z3_context c, Z3_string s);
Z3_ast Z3_mk_lstring(Z3_context c, unsigned len, Z3_string s);
bool Z3_is_string(Z3_context c, Z3_ast s);
Z3_string Z3_get_string(Z3_context c, Z3_ast s);
Z3_string Z3_get_lstring(Z3_context c, Z3_ast s, unsigned* length);
Z3_ast Z3_mk_seq_empty(Z3_context c, Z3_sort seq);
Z3_ast Z3_mk_seq_unit(Z3_context c, Z3_ast a);
Z3_ast Z3_mk_seq_concat(Z3_context c, unsigned n, Z3_ast const args[]);
Z3_ast Z3_mk_seq_prefix(Z3_context c, Z3_ast prefix, Z3_ast s);
Z3_ast Z3_mk_seq_suffix(Z3_context c, Z3_ast suffix, Z3_ast s);
Z3_ast Z3_mk_seq_contains(Z3_context c, Z3_ast container, Z3_ast containee);
Z3_ast Z3_mk_str_lt(Z3_context c, Z3_ast prefix, Z3_ast s);
Z3_ast Z3_mk_str_le(Z3_context c, Z3_ast prefix, Z3_ast s);
Z3_ast Z3_mk_seq_extract(Z3_context c, Z3_ast s, Z3_ast offset, Z3_ast length);
Z3_ast Z3_mk_seq_replace(Z3_context c, Z3_ast s, Z3_ast src, Z3_ast dst);
Z3_ast Z3_mk_seq_at(Z3_context c, Z3_ast s, Z3_ast index);
Z3_ast Z3_mk_seq_nth(Z3_context c, Z3_ast s, Z3_ast index);
Z3_ast Z3_mk_seq_length(Z3_context c, Z3_ast s);
Z3_ast Z3_mk_seq_index(Z3_context c, Z3_ast s, Z3_ast substr, Z3_ast offset);
Z3_ast Z3_mk_seq_last_index(Z3_context c, Z3_ast, Z3_ast substr);
Z3_ast Z3_mk_str_to_int(Z3_context c, Z3_ast s);
Z3_ast Z3_mk_int_to_str(Z3_context c, Z3_ast s);
Z3_ast Z3_mk_seq_to_re(Z3_context c, Z3_ast seq);
Z3_ast Z3_mk_seq_in_re(Z3_context c, Z3_ast seq, Z3_ast re);
Z3_ast Z3_mk_re_plus(Z3_context c, Z3_ast re);
Z3_ast Z3_mk_re_star(Z3_context c, Z3_ast re);
Z3_ast Z3_mk_re_option(Z3_context c, Z3_ast re);
Z3_ast Z3_mk_re_union(Z3_context c, unsigned n, Z3_ast const args[]);
Z3_ast Z3_mk_re_concat(Z3_context c, unsigned n, Z3_ast const args[]);
Z3_ast Z3_mk_re_range(Z3_context c, Z3_ast lo, Z3_ast hi);
Z3_ast Z3_mk_re_loop(Z3_context c, Z3_ast r, unsigned lo, unsigned hi);
Z3_ast Z3_mk_re_intersect(Z3_context c, unsigned n, Z3_ast const args[]);
Z3_ast Z3_mk_re_complement(Z3_context c, Z3_ast re);
Z3_ast Z3_mk_re_empty(Z3_context c, Z3_sort re);
Z3_ast Z3_mk_re_full(Z3_context c, Z3_sort re);
Z3_func_decl Z3_mk_linear_order(Z3_context c, Z3_sort a, unsigned id);
Z3_func_decl Z3_mk_partial_order(Z3_context c, Z3_sort a, unsigned id);
Z3_func_decl Z3_mk_piecewise_linear_order(Z3_context c, Z3_sort a, unsigned id);
Z3_func_decl Z3_mk_tree_order(Z3_context c, Z3_sort a, unsigned id);
Z3_func_decl Z3_mk_transitive_closure(Z3_context c, Z3_func_decl f);
Z3_pattern Z3_mk_pattern(Z3_context c, unsigned num_patterns, Z3_ast const terms[]);
Z3_ast Z3_mk_bound(Z3_context c, unsigned index, Z3_sort ty);
Z3_ast Z3_mk_forall(Z3_context c, unsigned weight,
                            unsigned num_patterns, Z3_pattern const patterns[],
                            unsigned num_decls, Z3_sort const sorts[],
                            Z3_symbol const decl_names[],
                            Z3_ast body);
Z3_ast Z3_mk_exists(Z3_context c, unsigned weight,
                            unsigned num_patterns, Z3_pattern const patterns[],
                            unsigned num_decls, Z3_sort const sorts[],
                            Z3_symbol const decl_names[],
                            Z3_ast body);
Z3_ast Z3_mk_quantifier(
    Z3_context c,
    bool is_forall,
    unsigned weight,
    unsigned num_patterns, Z3_pattern const patterns[],
    unsigned num_decls, Z3_sort const sorts[],
    Z3_symbol const decl_names[],
    Z3_ast body);
Z3_ast Z3_mk_quantifier_ex(
    Z3_context c,
    bool is_forall,
    unsigned weight,
    Z3_symbol quantifier_id,
    Z3_symbol skolem_id,
    unsigned num_patterns, Z3_pattern const patterns[],
    unsigned num_no_patterns, Z3_ast const no_patterns[],
    unsigned num_decls, Z3_sort const sorts[],
    Z3_symbol const decl_names[],
    Z3_ast body);
Z3_ast Z3_mk_forall_const(
    Z3_context c,
    unsigned weight,
    unsigned num_bound,
    Z3_app const bound[],
    unsigned num_patterns,
    Z3_pattern const patterns[],
    Z3_ast body
    );
Z3_ast Z3_mk_exists_const(
    Z3_context c,
    unsigned weight,
    unsigned num_bound,
    Z3_app const bound[],
    unsigned num_patterns,
    Z3_pattern const patterns[],
    Z3_ast body
    );
Z3_ast Z3_mk_quantifier_const(
    Z3_context c,
    bool is_forall,
    unsigned weight,
    unsigned num_bound,  Z3_app const bound[],
    unsigned num_patterns, Z3_pattern const patterns[],
    Z3_ast body
    );
Z3_ast Z3_mk_quantifier_const_ex(
    Z3_context c,
    bool is_forall,
    unsigned weight,
    Z3_symbol quantifier_id,
    Z3_symbol skolem_id,
    unsigned num_bound,  Z3_app const bound[],
    unsigned num_patterns, Z3_pattern const patterns[],
    unsigned num_no_patterns, Z3_ast const no_patterns[],
    Z3_ast body
    );
Z3_ast Z3_mk_lambda(Z3_context c, 
                            unsigned num_decls, Z3_sort const sorts[],
                            Z3_symbol const decl_names[],
                            Z3_ast body);
Z3_ast Z3_mk_lambda_const(Z3_context c, 
                                    unsigned num_bound, Z3_app const bound[],
                                    Z3_ast body);
Z3_symbol_kind Z3_get_symbol_kind(Z3_context c, Z3_symbol s);
int Z3_get_symbol_int(Z3_context c, Z3_symbol s);
Z3_string Z3_get_symbol_string(Z3_context c, Z3_symbol s);
Z3_symbol Z3_get_sort_name(Z3_context c, Z3_sort d);
unsigned Z3_get_sort_id(Z3_context c, Z3_sort s);
Z3_ast Z3_sort_to_ast(Z3_context c, Z3_sort s);
bool Z3_is_eq_sort(Z3_context c, Z3_sort s1, Z3_sort s2);
Z3_sort_kind Z3_get_sort_kind(Z3_context c, Z3_sort t);
unsigned Z3_get_bv_sort_size(Z3_context c, Z3_sort t);
Z3_bool Z3_get_finite_domain_sort_size(Z3_context c, Z3_sort s, uint64_t* r);
Z3_sort Z3_get_array_sort_domain(Z3_context c, Z3_sort t);
Z3_sort Z3_get_array_sort_range(Z3_context c, Z3_sort t);
Z3_func_decl Z3_get_tuple_sort_mk_decl(Z3_context c, Z3_sort t);
unsigned Z3_get_tuple_sort_num_fields(Z3_context c, Z3_sort t);
Z3_func_decl Z3_get_tuple_sort_field_decl(Z3_context c, Z3_sort t, unsigned i);
unsigned Z3_get_datatype_sort_num_constructors(
    Z3_context c, Z3_sort t);
Z3_func_decl Z3_get_datatype_sort_constructor(
    Z3_context c, Z3_sort t, unsigned idx);
Z3_func_decl Z3_get_datatype_sort_recognizer(
    Z3_context c, Z3_sort t, unsigned idx);
Z3_func_decl Z3_get_datatype_sort_constructor_accessor(Z3_context c,
                                                                Z3_sort t,
                                                                unsigned idx_c,
                                                                unsigned idx_a);
Z3_ast Z3_datatype_update_field(Z3_context c, Z3_func_decl field_access,
                                        Z3_ast t, Z3_ast value);
unsigned Z3_get_relation_arity(Z3_context c, Z3_sort s);
Z3_sort Z3_get_relation_column(Z3_context c, Z3_sort s, unsigned col);
Z3_ast Z3_mk_atmost(Z3_context c, unsigned num_args,
                            Z3_ast const args[], unsigned k);
Z3_ast Z3_mk_atleast(Z3_context c, unsigned num_args,
                            Z3_ast const args[], unsigned k);
Z3_ast Z3_mk_pble(Z3_context c, unsigned num_args,
                            Z3_ast const args[], int const coeffs[],
                            int k);
Z3_ast Z3_mk_pbge(Z3_context c, unsigned num_args,
                            Z3_ast const args[], int const coeffs[],
                            int k);
Z3_ast Z3_mk_pbeq(Z3_context c, unsigned num_args,
                            Z3_ast const args[], int const coeffs[],
                            int k);
Z3_ast Z3_func_decl_to_ast(Z3_context c, Z3_func_decl f);
bool Z3_is_eq_func_decl(Z3_context c, Z3_func_decl f1, Z3_func_decl f2);
unsigned Z3_get_func_decl_id(Z3_context c, Z3_func_decl f);
Z3_symbol Z3_get_decl_name(Z3_context c, Z3_func_decl d);
Z3_decl_kind Z3_get_decl_kind(Z3_context c, Z3_func_decl d);
unsigned Z3_get_domain_size(Z3_context c, Z3_func_decl d);
unsigned Z3_get_arity(Z3_context c, Z3_func_decl d);
Z3_sort Z3_get_domain(Z3_context c, Z3_func_decl d, unsigned i);
Z3_sort Z3_get_range(Z3_context c, Z3_func_decl d);
unsigned Z3_get_decl_num_parameters(Z3_context c, Z3_func_decl d);
Z3_parameter_kind Z3_get_decl_parameter_kind(Z3_context c, Z3_func_decl d, unsigned idx);
int Z3_get_decl_int_parameter(Z3_context c, Z3_func_decl d, unsigned idx);
double Z3_get_decl_double_parameter(Z3_context c, Z3_func_decl d, unsigned idx);
Z3_symbol Z3_get_decl_symbol_parameter(Z3_context c, Z3_func_decl d, unsigned idx);
Z3_sort Z3_get_decl_sort_parameter(Z3_context c, Z3_func_decl d, unsigned idx);
Z3_ast Z3_get_decl_ast_parameter(Z3_context c, Z3_func_decl d, unsigned idx);
Z3_func_decl Z3_get_decl_func_decl_parameter(Z3_context c, Z3_func_decl d, unsigned idx);
Z3_string Z3_get_decl_rational_parameter(Z3_context c, Z3_func_decl d, unsigned idx);
Z3_ast Z3_app_to_ast(Z3_context c, Z3_app a);
Z3_func_decl Z3_get_app_decl(Z3_context c, Z3_app a);
unsigned Z3_get_app_num_args(Z3_context c, Z3_app a);
Z3_ast Z3_get_app_arg(Z3_context c, Z3_app a, unsigned i);
bool Z3_is_eq_ast(Z3_context c, Z3_ast t1, Z3_ast t2);
unsigned Z3_get_ast_id(Z3_context c, Z3_ast t);
unsigned Z3_get_ast_hash(Z3_context c, Z3_ast a);
Z3_sort Z3_get_sort(Z3_context c, Z3_ast a);
bool Z3_is_well_sorted(Z3_context c, Z3_ast t);
Z3_lbool Z3_get_bool_value(Z3_context c, Z3_ast a);
Z3_ast_kind Z3_get_ast_kind(Z3_context c, Z3_ast a);
bool Z3_is_app(Z3_context c, Z3_ast a);
bool Z3_is_numeral_ast(Z3_context c, Z3_ast a);
bool Z3_is_algebraic_number(Z3_context c, Z3_ast a);
Z3_app Z3_to_app(Z3_context c, Z3_ast a);
Z3_func_decl Z3_to_func_decl(Z3_context c, Z3_ast a);
Z3_string Z3_get_numeral_string(Z3_context c, Z3_ast a);
Z3_string Z3_get_numeral_decimal_string(Z3_context c, Z3_ast a, unsigned precision);
double Z3_get_numeral_double(Z3_context c, Z3_ast a);
Z3_ast Z3_get_numerator(Z3_context c, Z3_ast a);
Z3_ast Z3_get_denominator(Z3_context c, Z3_ast a);
bool Z3_get_numeral_small(Z3_context c, Z3_ast a, int64_t* num, int64_t* den);
bool Z3_get_numeral_int(Z3_context c, Z3_ast v, int* i);
bool Z3_get_numeral_uint(Z3_context c, Z3_ast v, unsigned* u);
bool Z3_get_numeral_uint64(Z3_context c, Z3_ast v, uint64_t* u);
bool Z3_get_numeral_int64(Z3_context c, Z3_ast v, int64_t* i);
bool Z3_get_numeral_rational_int64(Z3_context c, Z3_ast v, int64_t* num, int64_t* den);
Z3_ast Z3_get_algebraic_number_lower(Z3_context c, Z3_ast a, unsigned precision);
Z3_ast Z3_get_algebraic_number_upper(Z3_context c, Z3_ast a, unsigned precision);
Z3_ast Z3_pattern_to_ast(Z3_context c, Z3_pattern p);
unsigned Z3_get_pattern_num_terms(Z3_context c, Z3_pattern p);
Z3_ast Z3_get_pattern(Z3_context c, Z3_pattern p, unsigned idx);
unsigned Z3_get_index_value(Z3_context c, Z3_ast a);
bool Z3_is_quantifier_forall(Z3_context c, Z3_ast a);
bool Z3_is_quantifier_exists(Z3_context c, Z3_ast a);
bool Z3_is_lambda(Z3_context c, Z3_ast a);
unsigned Z3_get_quantifier_weight(Z3_context c, Z3_ast a);
unsigned Z3_get_quantifier_num_patterns(Z3_context c, Z3_ast a);
Z3_pattern Z3_get_quantifier_pattern_ast(Z3_context c, Z3_ast a, unsigned i);
unsigned Z3_get_quantifier_num_no_patterns(Z3_context c, Z3_ast a);
Z3_ast Z3_get_quantifier_no_pattern_ast(Z3_context c, Z3_ast a, unsigned i);
unsigned Z3_get_quantifier_num_bound(Z3_context c, Z3_ast a);
Z3_symbol Z3_get_quantifier_bound_name(Z3_context c, Z3_ast a, unsigned i);
Z3_sort Z3_get_quantifier_bound_sort(Z3_context c, Z3_ast a, unsigned i);
Z3_ast Z3_get_quantifier_body(Z3_context c, Z3_ast a);
Z3_ast Z3_simplify(Z3_context c, Z3_ast a);
Z3_ast Z3_simplify_ex(Z3_context c, Z3_ast a, Z3_params p);
Z3_string Z3_simplify_get_help(Z3_context c);
Z3_param_descrs Z3_simplify_get_param_descrs(Z3_context c);
Z3_ast Z3_update_term(Z3_context c, Z3_ast a, unsigned num_args, Z3_ast const args[]);
Z3_ast Z3_substitute(Z3_context c,
                            Z3_ast a,
                            unsigned num_exprs,
                            Z3_ast const from[],
                            Z3_ast const to[]);
Z3_ast Z3_substitute_vars(Z3_context c,
                                    Z3_ast a,
                                    unsigned num_exprs,
                                    Z3_ast const to[]);
Z3_ast Z3_translate(Z3_context source, Z3_ast a, Z3_context target);
Z3_model Z3_mk_model(Z3_context c);
void Z3_model_inc_ref(Z3_context c, Z3_model m);
void Z3_model_dec_ref(Z3_context c, Z3_model m);
Z3_bool Z3_model_eval(Z3_context c, Z3_model m, Z3_ast t, bool model_completion, Z3_ast * v);
Z3_ast Z3_model_get_const_interp(Z3_context c, Z3_model m, Z3_func_decl a);
bool Z3_model_has_interp(Z3_context c, Z3_model m, Z3_func_decl a);
Z3_func_interp Z3_model_get_func_interp(Z3_context c, Z3_model m, Z3_func_decl f);
unsigned Z3_model_get_num_consts(Z3_context c, Z3_model m);
Z3_func_decl Z3_model_get_const_decl(Z3_context c, Z3_model m, unsigned i);
unsigned Z3_model_get_num_funcs(Z3_context c, Z3_model m);
Z3_func_decl Z3_model_get_func_decl(Z3_context c, Z3_model m, unsigned i);
unsigned Z3_model_get_num_sorts(Z3_context c, Z3_model m);
Z3_sort Z3_model_get_sort(Z3_context c, Z3_model m, unsigned i);
Z3_ast_vector Z3_model_get_sort_universe(Z3_context c, Z3_model m, Z3_sort s);
Z3_model Z3_model_translate(Z3_context c, Z3_model m, Z3_context dst);
bool Z3_is_as_array(Z3_context c, Z3_ast a);
Z3_func_decl Z3_get_as_array_func_decl(Z3_context c, Z3_ast a);
Z3_func_interp Z3_add_func_interp(Z3_context c, Z3_model m, Z3_func_decl f, Z3_ast default_value);
void Z3_add_const_interp(Z3_context c, Z3_model m, Z3_func_decl f, Z3_ast a);
void Z3_func_interp_inc_ref(Z3_context c, Z3_func_interp f);
void Z3_func_interp_dec_ref(Z3_context c, Z3_func_interp f);
unsigned Z3_func_interp_get_num_entries(Z3_context c, Z3_func_interp f);
Z3_func_entry Z3_func_interp_get_entry(Z3_context c, Z3_func_interp f, unsigned i);
Z3_ast Z3_func_interp_get_else(Z3_context c, Z3_func_interp f);
void Z3_func_interp_set_else(Z3_context c, Z3_func_interp f, Z3_ast else_value);
unsigned Z3_func_interp_get_arity(Z3_context c, Z3_func_interp f);
void Z3_func_interp_add_entry(Z3_context c, Z3_func_interp fi, Z3_ast_vector args, Z3_ast value);
void Z3_func_entry_inc_ref(Z3_context c, Z3_func_entry e);
void Z3_func_entry_dec_ref(Z3_context c, Z3_func_entry e);
Z3_ast Z3_func_entry_get_value(Z3_context c, Z3_func_entry e);
unsigned Z3_func_entry_get_num_args(Z3_context c, Z3_func_entry e);
Z3_ast Z3_func_entry_get_arg(Z3_context c, Z3_func_entry e, unsigned i);
bool Z3_open_log(Z3_string filename);
void Z3_append_log(Z3_string string);
void Z3_close_log();
void Z3_toggle_warning_messages(bool enabled);
void Z3_set_ast_print_mode(Z3_context c, Z3_ast_print_mode mode);
Z3_string Z3_ast_to_string(Z3_context c, Z3_ast a);
Z3_string Z3_pattern_to_string(Z3_context c, Z3_pattern p);
Z3_string Z3_sort_to_string(Z3_context c, Z3_sort s);
Z3_string Z3_func_decl_to_string(Z3_context c, Z3_func_decl d);
Z3_string Z3_model_to_string(Z3_context c, Z3_model m);
Z3_string Z3_benchmark_to_smtlib_string(Z3_context c,
                                                Z3_string name,
                                                Z3_string logic,
                                                Z3_string status,
                                                Z3_string attributes,
                                                unsigned num_assumptions,
                                                Z3_ast const assumptions[],
                                                Z3_ast formula);
Z3_ast_vector Z3_parse_smtlib2_string(Z3_context c,
                                        Z3_string str,
                                        unsigned num_sorts,
                                        Z3_symbol const sort_names[],
                                        Z3_sort const sorts[],
                                        unsigned num_decls,
                                        Z3_symbol const decl_names[],
                                        Z3_func_decl const decls[]);
Z3_ast_vector Z3_parse_smtlib2_file(Z3_context c,
                                    Z3_string file_name,
                                    unsigned num_sorts,
                                    Z3_symbol const sort_names[],
                                    Z3_sort const sorts[],
                                    unsigned num_decls,
                                    Z3_symbol const decl_names[],
                                    Z3_func_decl const decls[]);
Z3_string Z3_eval_smtlib2_string(Z3_context, Z3_string str);
Z3_error_code Z3_get_error_code(Z3_context c);
void Z3_set_error_handler(Z3_context c, Z3_error_handler h);
void Z3_set_error(Z3_context c, Z3_error_code e);
Z3_string Z3_get_error_msg(Z3_context c, Z3_error_code err);
void Z3_get_version(unsigned * major, unsigned * minor, unsigned * build_number, unsigned * revision_number);
Z3_string Z3_get_full_version();
void Z3_enable_trace(Z3_string tag);
void Z3_disable_trace(Z3_string tag);
void Z3_reset_memory();
void Z3_finalize_memory();
Z3_goal Z3_mk_goal(Z3_context c, bool models, bool unsat_cores, bool proofs);
void Z3_goal_inc_ref(Z3_context c, Z3_goal g);
void Z3_goal_dec_ref(Z3_context c, Z3_goal g);
Z3_goal_prec Z3_goal_precision(Z3_context c, Z3_goal g);
void Z3_goal_assert(Z3_context c, Z3_goal g, Z3_ast a);
bool Z3_goal_inconsistent(Z3_context c, Z3_goal g);
unsigned Z3_goal_depth(Z3_context c, Z3_goal g);
void Z3_goal_reset(Z3_context c, Z3_goal g);
unsigned Z3_goal_size(Z3_context c, Z3_goal g);
Z3_ast Z3_goal_formula(Z3_context c, Z3_goal g, unsigned idx);
unsigned Z3_goal_num_exprs(Z3_context c, Z3_goal g);
bool Z3_goal_is_decided_sat(Z3_context c, Z3_goal g);
bool Z3_goal_is_decided_unsat(Z3_context c, Z3_goal g);
Z3_goal Z3_goal_translate(Z3_context source, Z3_goal g, Z3_context target);
Z3_model Z3_goal_convert_model(Z3_context c, Z3_goal g, Z3_model m);
Z3_string Z3_goal_to_string(Z3_context c, Z3_goal g);
Z3_string Z3_goal_to_dimacs_string(Z3_context c, Z3_goal g);
Z3_tactic Z3_mk_tactic(Z3_context c, Z3_string name);
void Z3_tactic_inc_ref(Z3_context c, Z3_tactic t);
void Z3_tactic_dec_ref(Z3_context c, Z3_tactic g);
Z3_probe Z3_mk_probe(Z3_context c, Z3_string name);
void Z3_probe_inc_ref(Z3_context c, Z3_probe p);
void Z3_probe_dec_ref(Z3_context c, Z3_probe p);
Z3_tactic Z3_tactic_and_then(Z3_context c, Z3_tactic t1, Z3_tactic t2);
Z3_tactic Z3_tactic_or_else(Z3_context c, Z3_tactic t1, Z3_tactic t2);
Z3_tactic Z3_tactic_par_or(Z3_context c, unsigned num, Z3_tactic const ts[]);
Z3_tactic Z3_tactic_par_and_then(Z3_context c, Z3_tactic t1, Z3_tactic t2);
Z3_tactic Z3_tactic_try_for(Z3_context c, Z3_tactic t, unsigned ms);
Z3_tactic Z3_tactic_when(Z3_context c, Z3_probe p, Z3_tactic t);
Z3_tactic Z3_tactic_cond(Z3_context c, Z3_probe p, Z3_tactic t1, Z3_tactic t2);
Z3_tactic Z3_tactic_repeat(Z3_context c, Z3_tactic t, unsigned max);
Z3_tactic Z3_tactic_skip(Z3_context c);
Z3_tactic Z3_tactic_fail(Z3_context c);
Z3_tactic Z3_tactic_fail_if(Z3_context c, Z3_probe p);
Z3_tactic Z3_tactic_fail_if_not_decided(Z3_context c);
Z3_tactic Z3_tactic_using_params(Z3_context c, Z3_tactic t, Z3_params p);
Z3_probe Z3_probe_const(Z3_context x, double val);
Z3_probe Z3_probe_lt(Z3_context x, Z3_probe p1, Z3_probe p2);
Z3_probe Z3_probe_gt(Z3_context x, Z3_probe p1, Z3_probe p2);
Z3_probe Z3_probe_le(Z3_context x, Z3_probe p1, Z3_probe p2);
Z3_probe Z3_probe_ge(Z3_context x, Z3_probe p1, Z3_probe p2);
Z3_probe Z3_probe_eq(Z3_context x, Z3_probe p1, Z3_probe p2);
Z3_probe Z3_probe_and(Z3_context x, Z3_probe p1, Z3_probe p2);
Z3_probe Z3_probe_or(Z3_context x, Z3_probe p1, Z3_probe p2);
Z3_probe Z3_probe_not(Z3_context x, Z3_probe p);
unsigned Z3_get_num_tactics(Z3_context c);
Z3_string Z3_get_tactic_name(Z3_context c, unsigned i);
unsigned Z3_get_num_probes(Z3_context c);
Z3_string Z3_get_probe_name(Z3_context c, unsigned i);
Z3_string Z3_tactic_get_help(Z3_context c, Z3_tactic t);
Z3_param_descrs Z3_tactic_get_param_descrs(Z3_context c, Z3_tactic t);
Z3_string Z3_tactic_get_descr(Z3_context c, Z3_string name);
Z3_string Z3_probe_get_descr(Z3_context c, Z3_string name);
double Z3_probe_apply(Z3_context c, Z3_probe p, Z3_goal g);
Z3_apply_result Z3_tactic_apply(Z3_context c, Z3_tactic t, Z3_goal g);
Z3_apply_result Z3_tactic_apply_ex(Z3_context c, Z3_tactic t, Z3_goal g, Z3_params p);
void Z3_apply_result_inc_ref(Z3_context c, Z3_apply_result r);
void Z3_apply_result_dec_ref(Z3_context c, Z3_apply_result r);
Z3_string Z3_apply_result_to_string(Z3_context c, Z3_apply_result r);
unsigned Z3_apply_result_get_num_subgoals(Z3_context c, Z3_apply_result r);
Z3_goal Z3_apply_result_get_subgoal(Z3_context c, Z3_apply_result r, unsigned i);
Z3_solver Z3_mk_solver(Z3_context c);
Z3_solver Z3_mk_simple_solver(Z3_context c);
Z3_solver Z3_mk_solver_for_logic(Z3_context c, Z3_symbol logic);
Z3_solver Z3_mk_solver_from_tactic(Z3_context c, Z3_tactic t);
Z3_solver Z3_solver_translate(Z3_context source, Z3_solver s, Z3_context target);
void Z3_solver_import_model_converter(Z3_context ctx, Z3_solver src, Z3_solver dst);
Z3_string Z3_solver_get_help(Z3_context c, Z3_solver s);
Z3_param_descrs Z3_solver_get_param_descrs(Z3_context c, Z3_solver s);
void Z3_solver_set_params(Z3_context c, Z3_solver s, Z3_params p);
void Z3_solver_inc_ref(Z3_context c, Z3_solver s);
void Z3_solver_dec_ref(Z3_context c, Z3_solver s);
void Z3_solver_push(Z3_context c, Z3_solver s);
void Z3_solver_pop(Z3_context c, Z3_solver s, unsigned n);
void Z3_solver_reset(Z3_context c, Z3_solver s);
unsigned Z3_solver_get_num_scopes(Z3_context c, Z3_solver s);
void Z3_solver_assert(Z3_context c, Z3_solver s, Z3_ast a);
void Z3_solver_assert_and_track(Z3_context c, Z3_solver s, Z3_ast a, Z3_ast p);
void Z3_solver_from_file(Z3_context c, Z3_solver s, Z3_string file_name);
void Z3_solver_from_string(Z3_context c, Z3_solver s, Z3_string file_name);
Z3_ast_vector Z3_solver_get_assertions(Z3_context c, Z3_solver s);
Z3_ast_vector Z3_solver_get_units(Z3_context c, Z3_solver s);
Z3_ast_vector Z3_solver_get_trail(Z3_context c, Z3_solver s);
Z3_ast_vector Z3_solver_get_non_units(Z3_context c, Z3_solver s);
void Z3_solver_get_levels(Z3_context c, Z3_solver s, Z3_ast_vector literals, unsigned sz,  unsigned levels[]);
Z3_lbool Z3_solver_check(Z3_context c, Z3_solver s);
Z3_lbool Z3_solver_check_assumptions(Z3_context c, Z3_solver s,
                                            unsigned num_assumptions, Z3_ast const assumptions[]);
Z3_lbool Z3_get_implied_equalities(Z3_context c,
                                            Z3_solver  s,
                                            unsigned num_terms,
                                            Z3_ast const terms[],
                                            unsigned class_ids[]);
Z3_lbool Z3_solver_get_consequences(Z3_context c,
                                            Z3_solver s,
                                            Z3_ast_vector assumptions,
                                            Z3_ast_vector variables,
                                            Z3_ast_vector consequences);
Z3_ast_vector Z3_solver_cube(Z3_context c, Z3_solver s, Z3_ast_vector vars, unsigned backtrack_level);
Z3_model Z3_solver_get_model(Z3_context c, Z3_solver s);
Z3_ast Z3_solver_get_proof(Z3_context c, Z3_solver s);
Z3_ast_vector Z3_solver_get_unsat_core(Z3_context c, Z3_solver s);
Z3_string Z3_solver_get_reason_unknown(Z3_context c, Z3_solver s);
Z3_stats Z3_solver_get_statistics(Z3_context c, Z3_solver s);
Z3_string Z3_solver_to_string(Z3_context c, Z3_solver s);
Z3_string Z3_solver_to_dimacs_string(Z3_context c, Z3_solver s);
Z3_string Z3_stats_to_string(Z3_context c, Z3_stats s);
void Z3_stats_inc_ref(Z3_context c, Z3_stats s);
void Z3_stats_dec_ref(Z3_context c, Z3_stats s);
unsigned Z3_stats_size(Z3_context c, Z3_stats s);
Z3_string Z3_stats_get_key(Z3_context c, Z3_stats s, unsigned idx);
bool Z3_stats_is_uint(Z3_context c, Z3_stats s, unsigned idx);
bool Z3_stats_is_double(Z3_context c, Z3_stats s, unsigned idx);
unsigned Z3_stats_get_uint_value(Z3_context c, Z3_stats s, unsigned idx);
double Z3_stats_get_double_value(Z3_context c, Z3_stats s, unsigned idx);
uint64_t Z3_get_estimated_alloc_size();
