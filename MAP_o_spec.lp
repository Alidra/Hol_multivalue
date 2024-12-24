require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1118652 [A B C] : Prf (∀ (λ f : El (fun A B), (∀ (λ g : El (fun B C), (∀ (λ l : El (list A), (= ((@MAP A C) ((@o A B C) g f) l) ((@MAP B C) g ((@MAP A B) f l)))))))));
