require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1094347_term_abbrevs;
opaque symbol lem1094347 [A] (P : El (type1143 A)) : Prf (= (term0 A P) (term1 A P)) ≔ REFL (term0 A P);
