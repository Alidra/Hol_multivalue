require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1337991_term_abbrevs;
require open hol-light.thm1337985_spec;
require open hol-light.thm1337990_spec;
opaque symbol lem1337991 (x1 : El (prod hreal hreal)) (y1 : El (prod hreal hreal)) : Prf (= (treal_le x1 y1) (term0 x1 y1)) ≔ EQ_MP (@lem1337990 x1 y1) (@lem1337985 x1 y1);
