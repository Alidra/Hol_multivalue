require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.EMPTY_GSPEC_term_abbrevs;
require open hol-light.thm3399706_spec;
require open hol-light.thm3399757_spec;
opaque symbol lem3399758 [_88295] : Prf (= (term0 _88295) (@EMPTY _88295)) ≔ EQ_MP (@lem3399706 _88295) (@lem3399757 _88295);
