require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1109885_term_abbrevs;
opaque symbol lem1109885 [_25786 _25787] (h : El _25787) (f : El (type1470 _25786 _25787)) (t : El (list _25787)) (l : El (list _25786)) : Prf (= (term0 _25786 _25787 h f t l) (= (term1 _25786 _25787 f h t l) (term2 _25786 _25787 h f t l))) ≔ REFL (term0 _25786 _25787 h f t l);
