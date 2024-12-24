require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1106563_term_abbrevs;
opaque symbol lem1106563 [_25594] (P : El (fun _25594 bool)) : Prf (= (term0 _25594 P) (= ((@FILTER _25594) P (@NIL _25594)) (@NIL _25594))) ≔ REFL (term0 _25594 P);
