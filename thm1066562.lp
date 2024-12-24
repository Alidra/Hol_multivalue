require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1066562_term_abbrevs;
opaque symbol lem1066562 [A] (a : El A) (f : El (fun num A)) (n : El num) : Prf (= (term0 A a f n) (= (term1 A a f n) (f n))) ≔ REFL (term0 A a f n);
