require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1116924 [A B] : Prf (∀ (λ l : El (list A), (∀ (λ f : El (fun A B), (= ((@LENGTH B) ((@MAP A B) f l)) ((@LENGTH A) l))))));
