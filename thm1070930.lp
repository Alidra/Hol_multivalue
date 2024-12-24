require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1070930_term_abbrevs;
require open hol-light.thm1070927_spec;
opaque symbol lem1070930 [A] (list' : El (type1338 A)) (NIL' : El (recspace A)) (CONS' : El (type1399 A)) (h1 : Prf (= list' (term0 A NIL' CONS'))) : Prf (list' NIL') ≔ ∧ₑ₁ (@lem1070927 A list' NIL' CONS' h1);
