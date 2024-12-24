require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.UNIV_GSPEC_term_abbrevs;
require open hol-light.thm3399787_spec;
require open hol-light.thm3399835_spec;
opaque symbol lem3399836 [_88312] : Prf (= (term0 _88312) (@UNIV _88312)) ≔ EQ_MP (@lem3399787 _88312) (@lem3399835 _88312);
