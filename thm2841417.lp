require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2841417_term_abbrevs;
opaque symbol lem2841417 (m : El num) : Prf (= (term0 m) (= (SUC m) (term1 m))) ≔ REFL (term0 m);
