require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1009213_term_abbrevs;
require open hol-light.thm0_spec;
require open hol-light.thm1009212_spec;
opaque symbol lem1009213 (m : El num) (n : El num) : Prf (= (term0 m n) (EXP m n)) ≔ EQ_MP (@lem1009212 m n) (@lem0);
