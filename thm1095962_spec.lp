require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1095962 [A] : Prf (∧ (∀ (λ l : El (list A), (= ((@APPEND A) (@NIL A) l) l))) (∀ (λ h : El A, (∀ (λ t : El (list A), (∀ (λ l : El (list A), (= ((@APPEND A) ((@CONS A) h t) l) ((@CONS A) h ((@APPEND A) t l))))))))));
