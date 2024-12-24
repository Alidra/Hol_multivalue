require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
opaque symbol lem21118 (p : El bool) (h1 : Prf (= p T)) : Prf (= p T) ≔ h1;
