require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.FINITE_CROSS_UNIV_term_abbrevs;
require open hol-light.thm0_spec;
require open hol-light.thm4333669_spec;
opaque symbol lem4333670 [A B] : Prf (= ((@FINITE (prod A B)) (@UNIV (prod A B))) (term0 A B)) ≔ EQ_MP (@lem4333669 A B) (@lem0);
