require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm516656_term_abbrevs;
require open hol-light.thm82_spec;
opaque symbol lem516656 (n : El num) : Prf (term0 n) ≔ (@lem82 (= (SUC n) _0));
