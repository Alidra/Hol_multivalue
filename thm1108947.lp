require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1108947_term_abbrevs;
opaque symbol lem1108947 [_25719 _25727] (h1' : El _25719) (t1 : El (list _25719)) (l2 : El (list _25727)) : Prf (= (term0 _25719 _25727 h1' t1 l2) (= (term1 _25719 _25727 h1' t1 l2) (term2 _25719 _25727 h1' t1 l2))) ≔ REFL (term0 _25719 _25727 h1' t1 l2);
