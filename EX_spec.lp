require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1101599 [_25328] (h : El _25328) (P : El (fun _25328 bool)) (t : El (list _25328)) : Prf (∧ (= ((@EX _25328) P (@NIL _25328)) F) (= ((@EX _25328) P ((@CONS _25328) h t)) (∨ (P h) ((@EX _25328) P t))));
