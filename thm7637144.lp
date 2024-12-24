require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm7637144_term_abbrevs;
require open hol-light.thm7_spec;
opaque symbol lem7637144 (n : El num) : Prf (= (term0 n) (= (term0 n) T)) ≔ (@lem7 (term0 n));
