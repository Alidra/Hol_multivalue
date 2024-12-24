require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1111914 [A] : Prf (∀ (λ l : El (list A), (∀ (λ m : El (list A), (∀ (λ n : El (list A), (= ((@APPEND A) l ((@APPEND A) m n)) ((@APPEND A) ((@APPEND A) l m) n))))))));
