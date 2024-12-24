require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem512702 [_17389] (P : El (fun _17389 bool)) (e : El _17389) (Q : El bool) : Prf (⇒ (¬ (= (∀ (λ m : El _17389, (⇒ (P m) (⇒ (= m e) Q)))) (⇒ (P e) Q))) F);
