require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3464376_term_abbrevs;
require open hol-light.thm3459051_spec;
require open hol-light.thm3464373_spec;
opaque symbol lem3464376 [_89837 _89861 _89862 _89863] (P : El (type1517 _89861 _89862 _89863)) (f : El (type1524 _89837 _89861 _89862 _89863)) : Prf (= (term0 _89837 _89861 _89862 _89863 P f) (term1 _89837 _89861 _89862 _89863 P f)) ≔ EQ_MP (@lem3459051 _89837 _89861 _89862 _89863 P f) (@lem3464373 _89837 _89861 _89862 _89863 P f);
