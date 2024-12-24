require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.INTERS_INSERT_term_abbrevs;
require open hol-light.thm3356591_spec;
require open hol-light.thm3358011_spec;
opaque symbol lem3358012 [_87274] (s : El (fun _87274 bool)) (u : El (type686 _87274)) : Prf (= (term0 _87274 s u) (term1 _87274 s u)) ≔ EQ_MP (@lem3356591 _87274 s u) (@lem3358011 _87274 s u);
