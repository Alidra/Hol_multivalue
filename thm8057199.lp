require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm8057199_term_abbrevs;
require open hol-light.thm8057155_spec;
opaque symbol lem8057194 [_143007 _143008 _143009] (s : El (type24 _143007 _143008)) : Prf (term0 _143007 _143008 _143009 s) ≔ λ f : El (type56 _143007 _143009), (@lem8057155 _143007 _143008 _143009 f s);
opaque symbol lem8057199 [_143007 _143008 _143009] : Prf (term1 _143007 _143008 _143009) ≔ λ s : El (type24 _143007 _143008), (@lem8057194 _143007 _143008 _143009 s);
