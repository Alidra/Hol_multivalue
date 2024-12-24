require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4393235 [A B C] : Prf (∀ (λ f : El (fun A B), (∀ (λ g : El (fun B C), (∀ (λ s : El (fun A bool), (= ((@RESTRICTION A C) s ((@o A B C) g ((@RESTRICTION A B) s f))) ((@RESTRICTION A C) s ((@o A B C) g f)))))))));
