require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2267741_term_abbrevs;
opaque symbol lem2267741 (r : El real) : Prf (= (term0 r) (= (integer r) (= (term1 r) r))) ≔ REFL (term0 r);
