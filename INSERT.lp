require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.INSERT_term_abbrevs;
require open hol-light.thm0_spec;
require open hol-light.thm3192217_spec;
opaque symbol lem3192218 [A] (s : El (fun A bool)) (x : El A) : Prf (= ((@INSERT A) x s) (term0 A s x)) ≔ EQ_MP (@lem3192217 A s x) (@lem0);
