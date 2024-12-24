require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1102427_spec;
require open hol-light.thm1102428_spec;
opaque symbol lem1102429 [_25350 _25351] (f : El (type1467 _25350 _25351)) (b : El _25350) : Prf (= ((@ITLIST _25350 _25351) f (@NIL _25351) b) b) ≔ EQ_MP (@lem1102428 _25350 _25351 f b) (@lem1102427 _25350 _25351 f b);
