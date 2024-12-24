require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3184698_term_abbrevs;
require open hol-light.thm3183120_spec;
require open hol-light.thm3184694_spec;
opaque symbol lem3184698 [_83064] (P : El (type919 _83064)) (x : El _83064) : Prf (= (term0 _83064 x P) (term1 _83064 P x)) ≔ EQ_MP (@lem3183120 _83064 P x) (@lem3184694 _83064 P x);
