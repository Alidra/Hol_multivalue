require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1106572_term_abbrevs;
opaque symbol lem1106572 [_25594] (h : El _25594) (P : El (fun _25594 bool)) (t : El (list _25594)) : Prf (= (term0 _25594 h P t) (= (term1 _25594 P h t) (term2 _25594 h P t))) ≔ REFL (term0 _25594 h P t);
