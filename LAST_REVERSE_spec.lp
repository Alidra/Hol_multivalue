require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1203967 [A] : Prf (∀ (λ l : El (list A), (⇒ (¬ (= l (@NIL A))) (= ((@LAST A) ((@REVERSE A) l)) ((@HD A) l)))));
