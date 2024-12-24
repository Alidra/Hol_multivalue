require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm522120_term_abbrevs;
opaque symbol lem522120 (m : El num) : Prf (= (term0 m) (= (SUC m) (term1 m))) ≔ REFL (term0 m);
