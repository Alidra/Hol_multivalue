require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1222739 [A] : Prf (∀ (λ x : El A, (∀ (λ l : El (list A), (= ((@MEM A) x l) (∃ (λ l1 : El (list A), (∃ (λ l2 : El (list A), (= l ((@APPEND A) l1 ((@CONS A) x l2))))))))))));
