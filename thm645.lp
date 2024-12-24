require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm645_term_abbrevs;
require open hol-light.thm643_spec;
require open hol-light.thm644_spec;
opaque symbol lem645 (p : El bool) (q : El bool) : Prf (= (term0 p q) (∧ p q)) ≔ EQ_MP (@lem644 p q) (@lem643 p q);
