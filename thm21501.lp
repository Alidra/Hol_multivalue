require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm21501_term_abbrevs;
opaque symbol lem21501 (b : El bool) (a : El bool) : Prf (= (term0 b a) (term0 b a)) ≔ REFL (term0 b a);
