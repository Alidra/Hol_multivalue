require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.MATCH_SEQPATTERN_term_abbrevs;
require open hol-light.thm8096294_spec;
require open hol-light.thm8099922_spec;
opaque symbol lem8099923 [_143642 _143649] (r : El (type1470 _143642 _143649)) (x : El _143649) (s : El (type1470 _143642 _143649)) : Prf (= (term0 _143642 _143649 x r s) (term1 _143642 _143649 r x s)) ≔ EQ_MP (@lem8096294 _143642 _143649 r x s) (@lem8099922 _143642 _143649 r s x);
