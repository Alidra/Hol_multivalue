require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.INTERS_1_term_abbrevs;
require open hol-light.thm3354723_spec;
require open hol-light.thm3355403_spec;
opaque symbol lem3355404 [_87240] (s : El (fun _87240 bool)) : Prf (= (term0 _87240 s) s) ≔ EQ_MP (@lem3354723 _87240 s) (@lem3355403 _87240 s);
