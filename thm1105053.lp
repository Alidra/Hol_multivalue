require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1105053_term_abbrevs;
opaque symbol lem1105053 [_25498 _25501 _25508] (f : El (type1475 _25498 _25501 _25508)) (l : El (list _25508)) : Prf (= (term0 _25498 _25501 _25508 f l) (= ((@MAP2 _25498 _25501 _25508) f (@NIL _25501) l) (@NIL _25498))) ≔ REFL (term0 _25498 _25501 _25508 f l);
