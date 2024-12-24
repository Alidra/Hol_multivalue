require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
opaque symbol lem21506 (a : El bool) (h1 : Prf (= a F)) : Prf (= a F) ≔ h1;
