require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1066572_term_abbrevs;
opaque symbol lem1066572 [A B] (INR' : El (type1479 A B)) (h1 : Prf (= INR' (term0 A B))) : Prf (= INR' (term0 A B)) ≔ h1;
