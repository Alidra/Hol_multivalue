require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm21180_term_abbrevs;
require open hol-light.thm21138_spec;
require open hol-light.thm21160_spec;
opaque symbol lem21180 (p : El bool) (h1 : Prf (= p T)) : Prf (= (term0 p) p) ≔ EQ_MP (@lem21138 p h1) (@lem21160);
