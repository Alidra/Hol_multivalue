require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1112107 [A] : Prf (∀ (λ l : El (list A), (∀ (λ m : El (list A), (= ((@REVERSE A) ((@APPEND A) l m)) ((@APPEND A) ((@REVERSE A) m) ((@REVERSE A) l)))))));
