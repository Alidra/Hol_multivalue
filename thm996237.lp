require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm996237_term_abbrevs;
require open hol-light.thm996236_spec;
opaque symbol lem996237 (m : El num) : Prf (= (term0 m) m) ≔ ∧ₑ₂ (@lem996236 (@el num) m);
