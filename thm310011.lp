require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm310011_term_abbrevs;
opaque symbol lem310011 (t1 : El bool) (t2 : El bool) : Prf (= (term0 t1 t2) (= (term1 t1 t2) (term2 t1 t2))) ≔ REFL (term0 t1 t2);
