require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1103191_term_abbrevs;
require open hol-light.thm1103188_spec;
opaque symbol lem1103190 [_25376] : Prf (term0 _25376) ≔ ∧ₑ₁ (@lem1103188 _25376);
opaque symbol lem1103191 [_25376] (x : El _25376) : Prf (term1 _25376 x) ≔ (@lem1103190 _25376) x;
