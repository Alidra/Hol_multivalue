require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3464374_term_abbrevs;
require open hol-light.thm3459338_spec;
require open hol-light.thm3462445_spec;
opaque symbol lem3464374 [_89769 _89788 _89789] (P : El (type1470 _89788 _89789)) (f : El (type1517 _89769 _89788 _89789)) : Prf (term0 _89769 _89788 _89789 P f) ≔ EQ_MP (@lem3459338 _89769 _89788 _89789 P f) (@lem3462445 _89769 _89788 _89789 P f);
