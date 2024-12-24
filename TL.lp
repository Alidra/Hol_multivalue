require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.TL_term_abbrevs;
require open hol-light.thm1095388_spec;
require open hol-light.thm1095389_spec;
opaque symbol lem1095390 [A] (h : El A) (t : El (list A)) : Prf (= (term0 A h t) t) ≔ EQ_MP (@lem1095389 A h t) (@lem1095388 A h t);
