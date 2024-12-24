require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm8057189_term_abbrevs;
require open hol-light.thm8057143_spec;
opaque symbol lem8057184 [_143061 _143062 _143063] (f : El (type56 _143061 _143062)) : Prf (term0 _143061 _143062 _143063 f) ≔ λ t : El (type24 _143061 _143063), (@lem8057143 _143061 _143062 _143063 f t);
opaque symbol lem8057189 [_143061 _143062 _143063] : Prf (term1 _143061 _143062 _143063) ≔ λ f : El (type56 _143061 _143062), (@lem8057184 _143061 _143062 _143063 f);
