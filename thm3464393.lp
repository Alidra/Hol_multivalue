require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3464393_term_abbrevs;
require open hol-light.thm3464377_spec;
opaque symbol lem3464393 [_89769 _89788 _89789] (P : El (type1470 _89788 _89789)) : Prf (term0 _89769 _89788 _89789 P) ≔ λ f : El (type1517 _89769 _89788 _89789), (@lem3464377 _89769 _89788 _89789 P f);
