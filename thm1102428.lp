require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1102428_term_abbrevs;
opaque symbol lem1102428 [_25350 _25351] (f : El (type1467 _25350 _25351)) (b : El _25350) : Prf (= (term0 _25350 _25351 f b) (= ((@ITLIST _25350 _25351) f (@NIL _25351) b) b)) ≔ REFL (term0 _25350 _25351 f b);
