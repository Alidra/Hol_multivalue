require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm6920431_spec;
require open hol-light.thm6921992_spec;
opaque symbol lem6921993 : Prf (= ((@neutral num) +) (NUMERAL _0)) ≔ EQ_MP (@lem6920431) (@lem6921992);
