require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1116558 [A] : Prf (∀ (λ l : El (list A), (∀ (λ m : El (list A), (= ((@LENGTH A) ((@APPEND A) l m)) (+ ((@LENGTH A) l) ((@LENGTH A) m)))))));
