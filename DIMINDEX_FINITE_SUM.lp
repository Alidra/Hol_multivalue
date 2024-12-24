require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.DIMINDEX_FINITE_SUM_term_abbrevs;
require open hol-light.thm7640410_spec;
require open hol-light.thm7640437_spec;
opaque symbol lem7640438 [M N] : Prf (= ((@dimindex (finite_sum M N)) (@UNIV (finite_sum M N))) (term0 M N)) ≔ EQ_MP (@lem7640410 M N) (@lem7640437 M N);
