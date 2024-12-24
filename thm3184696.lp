require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3184696_term_abbrevs;
require open hol-light.thm3183195_spec;
require open hol-light.thm3184692_spec;
opaque symbol lem3184696 [_83123] (P : El (type919 _83123)) (x : El _83123) : Prf (= (term0 _83123 P x) (term1 _83123 P x)) ≔ EQ_MP (@lem3183195 _83123 P x) (@lem3184692 _83123 P x);
