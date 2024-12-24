require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3070931_term_abbrevs;
require open hol-light.thm7_spec;
opaque symbol lem3070931 (x : El int) : Prf (= (term0 x) (= (term0 x) T)) ≔ (@lem7 (term0 x));
