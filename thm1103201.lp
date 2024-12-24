require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1103201_term_abbrevs;
opaque symbol lem1103201 [_25376] (h : El _25376) (x : El _25376) (t : El (list _25376)) : Prf (= (term0 _25376 h x t) (= (term1 _25376 x h t) (term2 _25376 h x t))) ≔ REFL (term0 _25376 h x t);
