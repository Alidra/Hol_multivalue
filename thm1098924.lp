require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1098924_term_abbrevs;
opaque symbol lem1098924 [_25251] (h : El _25251) (t : El (list _25251)) : Prf (= (term0 _25251 h t) (= (term1 _25251 h t) (term2 _25251 h t))) ≔ REFL (term0 _25251 h t);
