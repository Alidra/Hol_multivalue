require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1205492 [A] : Prf (∀ (λ l : El (list A), (⇒ (¬ (= l (@NIL A))) (= ((@HD A) ((@REVERSE A) l)) ((@LAST A) l)))));
