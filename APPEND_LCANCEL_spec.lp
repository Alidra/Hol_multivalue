require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1187628 [A] : Prf (∀ (λ l1 : El (list A), (∀ (λ l2 : El (list A), (∀ (λ l3 : El (list A), (= (= ((@APPEND A) l1 l2) ((@APPEND A) l1 l3)) (= l2 l3))))))));
