require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3464388_term_abbrevs;
require open hol-light.thm3464376_spec;
opaque symbol lem3464383 [_89837 _89861 _89862 _89863] (P : El (type1517 _89861 _89862 _89863)) : Prf (term0 _89837 _89861 _89862 _89863 P) ≔ λ f : El (type1524 _89837 _89861 _89862 _89863), (@lem3464376 _89837 _89861 _89862 _89863 P f);
opaque symbol lem3464388 [_89837 _89861 _89862 _89863] : Prf (term1 _89837 _89861 _89862 _89863) ≔ λ P : El (type1517 _89861 _89862 _89863), (@lem3464383 _89837 _89861 _89862 _89863 P);
