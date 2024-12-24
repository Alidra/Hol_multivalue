require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm8057205_term_abbrevs;
require open hol-light.thm8057179_spec;
opaque symbol lem8057205 [_142951 _142952 _142953] (f : El (type56 _142951 _142952)) : Prf (term0 _142951 _142952 _142953 f) ≔ λ g : El (type56 _142951 _142953), (@lem8057179 _142951 _142952 _142953 f g);
