require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1108229_term_abbrevs;
opaque symbol lem1108229 [_25645 _25647 _25655] (h1' : El _25647) (f : El (type1474 _25645 _25647 _25655)) (t1 : El (list _25647)) (l2 : El (list _25655)) (b : El _25645) : Prf (= (term0 _25645 _25647 _25655 h1' f t1 l2 b) (= (term1 _25645 _25647 _25655 f h1' t1 l2 b) (term2 _25645 _25647 _25655 h1' f t1 l2 b))) ≔ REFL (term0 _25645 _25647 _25655 h1' f t1 l2 b);
