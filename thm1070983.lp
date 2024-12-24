require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1070983_term_abbrevs;
require open hol-light.thm1070978_spec;
require open hol-light.thm1070982_spec;
opaque symbol lem1070983 [A] (r : El (recspace A)) (list' : El (type1338 A)) (CONS' : El (type1399 A)) (NIL' : El (recspace A)) (h1 : Prf (= CONS' (term0 A))) (h2 : Prf (= list' (term1 A NIL' CONS'))) (h3 : Prf (= NIL' (term2 A))) : Prf (= (list' r) (= (term3 A r) r)) ≔ TRANS (@lem1070982 A r list' CONS' NIL' h1 h2 h3) (@lem1070978 A r);
