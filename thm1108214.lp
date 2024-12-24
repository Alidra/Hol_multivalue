require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1108214_term_abbrevs;
opaque symbol lem1108214 [_25645 _25647 _25655] (f : El (type1474 _25645 _25647 _25655)) (l2 : El (list _25655)) (b : El _25645) : Prf (= (term0 _25645 _25647 _25655 f l2 b) (= ((@ITLIST2 _25645 _25647 _25655) f (@NIL _25647) l2 b) b)) ≔ REFL (term0 _25645 _25647 _25655 f l2 b);
