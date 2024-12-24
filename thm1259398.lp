require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1259398_term_abbrevs;
require open hol-light.thm1248646_spec;
require open hol-light.thm1259354_spec;
opaque symbol lem1259398 (d' : El num) (d : El num) (n : El num) (d'' : El num) (h1 : Prf (= (term0 n d' d) (+ n d''))) : Prf (term1 d d' d'') ≔ EQ_MP (@lem1248646 d d' d'') (@lem1259354 d' d n d'' h1);
