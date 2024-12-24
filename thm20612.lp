require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm20612_term_abbrevs;
require open hol-light.thm20440_spec;
require open hol-light.thm20530_spec;
opaque symbol lem20612 (x : El bool) (x1 : El bool) (x0 : El bool) (b : El bool) (h1 : Prf (= b T)) : Prf (term0 x x1 b x0) ≔ EQ_MP (@lem20440 x x1 x0 b h1) (@lem20530 x x1 x0);
