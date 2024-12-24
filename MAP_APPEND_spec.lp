require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1116758 [A B] : Prf (∀ (λ f : El (fun A B), (∀ (λ l1 : El (list A), (∀ (λ l2 : El (list A), (= ((@MAP A B) f ((@APPEND A) l1 l2)) ((@APPEND B) ((@MAP A B) f l1) ((@MAP A B) f l2)))))))));
