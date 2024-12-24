require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1187163 [A B] (R : El (fun A (fun B bool))) (R' : El (fun A (fun B bool))) : Prf (∀ (λ l : El (list A), (∀ (λ m : El (list B), (∀ (λ P : El (fun A bool), (∀ (λ Q : El (fun B bool), (⇒ (∧ ((@ALL A) P l) (∧ ((@ALL B) Q m) (∀ (λ p : El A, (∀ (λ q : El B, (⇒ (∧ (P p) (Q q)) (= (R p q) (R' p q))))))))) (= ((@ALLPAIRS B A) R l m) ((@ALLPAIRS B A) R' l m)))))))))));
