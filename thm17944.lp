require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm17944_term_abbrevs;
opaque symbol lem17944 (t1 : El bool) (t2 : El bool) (t3 : El bool) : Prf (= (term0 t1 t2 t3) (= (term1 t1 t2 t3) (term2 t1 t2 t3))) ≔ REFL (term0 t1 t2 t3);
