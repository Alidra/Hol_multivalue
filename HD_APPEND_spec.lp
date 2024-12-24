require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1206885 [A] : Prf (∀ (λ l : El (list A), (∀ (λ m : El (list A), (= ((@HD A) ((@APPEND A) l m)) ((@COND A) (= l (@NIL A)) ((@HD A) m) ((@HD A) l)))))));
