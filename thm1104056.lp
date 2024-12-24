require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1104056_term_abbrevs;
opaque symbol lem1104056 [_25409 _25416] (h1' : El _25409) (P : El (type1413 _25409 _25416)) (t1 : El (list _25409)) (l2 : El (list _25416)) : Prf (= (term0 _25409 _25416 h1' P t1 l2) (= (term1 _25409 _25416 P h1' t1 l2) (term2 _25409 _25416 h1' P t1 l2))) ≔ REFL (term0 _25409 _25416 h1' P t1 l2);
