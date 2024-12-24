require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2318544_term_abbrevs;
require open hol-light.int_of_num_th_spec;
opaque symbol lem2318544 (n : El num) : Prf (term0 n) ≔ (@lem2271980) n;
