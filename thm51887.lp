require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm51887_term_abbrevs;
opaque symbol lem51887 [_5106 _5107] (P : El (type1223 _5106 _5107)) : Prf (= (term0 _5106 _5107 P) (= (term1 _5106 _5107 P) (term2 _5106 _5107 P))) ≔ REFL (term0 _5106 _5107 P);
