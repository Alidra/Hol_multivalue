require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm10417_term_abbrevs;
opaque symbol lem10417 (t : El bool) : Prf (= (term0 t) (= (term1 t) t)) ≔ REFL (term0 t);
