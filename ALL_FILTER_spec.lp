require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1207937 [A] : Prf (∀ (λ P : El (fun A bool), (∀ (λ Q : El (fun A bool), (∀ (λ l : El (list A), (= ((@ALL A) P ((@FILTER A) Q l)) ((@ALL A) (λ x : El A, (⇒ (Q x) (P x))) l))))))));
