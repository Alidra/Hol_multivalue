require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm7_spec;
opaque symbol lem3211725 [A] (x : El A) : Prf (= ((@IN A) x (@UNIV A)) (= ((@IN A) x (@UNIV A)) T)) ≔ (@lem7 ((@IN A) x (@UNIV A)));
