require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1103192_term_abbrevs;
opaque symbol lem1103192 [_25376] (x : El _25376) : Prf (= (term0 _25376 x) (= ((@MEM _25376) x (@NIL _25376)) F)) ≔ REFL (term0 _25376 x);
