require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
opaque symbol lem20235 (b : El bool) (h1 : Prf (= b T)) : Prf (= b T) ≔ h1;
