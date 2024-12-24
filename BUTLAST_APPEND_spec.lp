require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1201817 [A] : Prf (∀ (λ l : El (list A), (∀ (λ m : El (list A), (= ((@BUTLAST A) ((@APPEND A) l m)) ((@COND (list A)) (= m (@NIL A)) ((@BUTLAST A) l) ((@APPEND A) l ((@BUTLAST A) m))))))));
