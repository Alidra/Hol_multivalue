require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3453894_term_abbrevs;
opaque symbol lem3453894 [_83064] (P : El (type919 _83064)) (x : El _83064) : Prf (= (term0 _83064 P x) (= (term1 _83064 x P) (term2 _83064 P x))) ≔ REFL (term0 _83064 P x);
