require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1102440_term_abbrevs;
opaque symbol lem1102440 [_25350 _25351] (h : El _25351) (f : El (type1467 _25350 _25351)) (t : El (list _25351)) (b : El _25350) : Prf (= (term0 _25350 _25351 h f t b) (= (term1 _25350 _25351 f h t b) (term2 _25350 _25351 h f t b))) ≔ REFL (term0 _25350 _25351 h f t b);
