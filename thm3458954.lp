require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3458954_term_abbrevs;
require open hol-light.thm3458942_spec;
opaque symbol lem3458949 [_89646 _89670 _89671 _89672] (P : El (type1517 _89670 _89671 _89672)) : Prf (term0 _89646 _89670 _89671 _89672 P) ≔ λ f : El (type1524 _89646 _89670 _89671 _89672), (@lem3458942 _89646 _89670 _89671 _89672 P f);
opaque symbol lem3458954 [_89646 _89670 _89671 _89672] : Prf (term1 _89646 _89670 _89671 _89672) ≔ λ P : El (type1517 _89670 _89671 _89672), (@lem3458949 _89646 _89670 _89671 _89672 P);
