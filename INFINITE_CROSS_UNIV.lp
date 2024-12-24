require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.INFINITE_CROSS_UNIV_term_abbrevs;
require open hol-light.thm4333782_spec;
require open hol-light.thm4334154_spec;
opaque symbol lem4334155 [A B] : Prf (= ((@INFINITE (prod A B)) (@UNIV (prod A B))) (term0 A B)) ≔ EQ_MP (@lem4333782 A B) (@lem4334154 A B);
