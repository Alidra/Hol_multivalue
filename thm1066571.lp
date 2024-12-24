require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1066571_term_abbrevs;
opaque symbol lem1066571 [A B] (INL' : El (type1431 A B)) (h1 : Prf (= INL' (term0 A B))) : Prf (= INL' (term0 A B)) ≔ h1;
