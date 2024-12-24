require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.EXISTS_IN_PCROSS_term_abbrevs;
require open hol-light.thm0_spec;
require open hol-light.thm8004099_spec;
opaque symbol lem8004100 [_141895 _141896 _141897] (s : El (type24 _141895 _141896)) (t : El (type24 _141895 _141897)) (P : El (type16 _141895 _141896 _141897)) : Prf (= (term0 _141895 _141896 _141897 s t P) (term1 _141895 _141896 _141897 s t P)) ≔ EQ_MP (@lem8004099 _141895 _141896 _141897 s t P) (@lem0);
