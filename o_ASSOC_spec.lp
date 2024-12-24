require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem15542 [A B C D] : Prf (∀ (λ f : El (fun C D), (∀ (λ g : El (fun B C), (∀ (λ h : El (fun A B), (= ((@o A C D) f ((@o A B C) g h)) ((@o A B D) ((@o B C D) f g) h))))))));
