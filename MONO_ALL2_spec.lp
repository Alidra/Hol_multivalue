require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1239854 [A B] (P : El (fun A (fun B bool))) (Q : El (fun A (fun B bool))) (l : El (list A)) (l' : El (list B)) : Prf (⇒ (∀ (λ x : El A, (∀ (λ y : El B, (⇒ (P x y) (Q x y)))))) (⇒ ((@ALL2 A B) P l l') ((@ALL2 A B) Q l l')));
