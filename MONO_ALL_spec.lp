require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1238507 [A] (P : El (fun A bool)) (Q : El (fun A bool)) (l : El (list A)) : Prf (⇒ (∀ (λ x : El A, (⇒ (P x) (Q x)))) (⇒ ((@ALL A) P l) ((@ALL A) Q l)));
