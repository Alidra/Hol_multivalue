require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm18899_term_abbrevs;
opaque symbol lem18899 [A B] (P : El (type1413 A B)) : Prf (= (term0 A B P) (= (term1 A B P) (term2 A B P))) ≔ REFL (term0 A B P);
