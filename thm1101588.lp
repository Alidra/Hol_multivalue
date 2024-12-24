require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1101588_term_abbrevs;
opaque symbol lem1101588 [_25328] (P : El (fun _25328 bool)) : Prf (= (term0 _25328 P) (= ((@EX _25328) P (@NIL _25328)) F)) ≔ REFL (term0 _25328 P);
